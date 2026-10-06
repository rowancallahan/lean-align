#!/usr/bin/env python3
"""Benchmark only.  Final statistics for the freeze, mode RTX vs minibwa, one command:

   python3 bench/final_stats.py [--out DIR] [--bin whole_genome] [--sets hiseq,nova,mason]
        [--rounds 3] [--env K=V ...] [--no-timing] [--no-dump] [--keep]

Per set (HiSeq HG002 2x250, NovaSeq HG002 2x151, mason 2.0.9 2x150; 200k pairs each):
  1. tier shares (suffixes x / z folded in; any new tag in the dump, e.g. T1u / T1um / T2b, gets a row),
  2. what each tier proves (TierOk in codecs/TierRouter.lean, codecs/TierOpt.lean),
  3. per tier vs minibwa: our pair penalty better / equal / worse than minibwa's re-scored pair
     (bench/tier_vs_mb.py join: both mappers scored on our trimmed mates, end to end), claim
     violations (floors, T1 / T1g / T1gm / T2b best-pair claims; must be 0), mason truth "correct",
  4. T1gm split: from the dump's `gm` columns (bench/WholeGenome.lean, WG_TIEROUT=1, T1gm lines: every
     proper pair within G0 of the guarantee's enumeration, no early stop): exact ties vs close-unequal,
     and where the tied pairs are,
  5. T2 pair floor-ceiling gap: ceil1 + ceil2 - max(fl1 + fl2, pfFloor(pf)) (bench/t2_opt.py),
  6. timing: median of `--rounds` interleaved rounds, 4 threads, wall and CPU; mapping only (index
     load excluded: our RESULT line, minibwa worker end - index loaded, bench/budget_sweep.py mbtime)
     and the whole process (wait4 rusage).
Every heavy step (mapper runs, minibwa, joins) holds flock /home/user/data/BIG.lock.

Default config: WG_MODES=RTX WG_PG=4 WG_XBUD=5000 WG_TASKS=4, other knobs at the code defaults (e.g. the
exact pair search budget WG_XEBUD, 1500 since speed/t2-exact; --env WG_XEBUD=0 turns it off).  minibwa SAMs (for the join) are cached in DIR/mb_<set>.sam or
taken from MB_SAM_<set> / the earlier runs' copies; else minibwa writes one (not timed).
Output in DIR (default <scratchpad>/final): report.txt (text, TSV tables), tiers.tsv, vs_mb.tsv,
t1gm.tsv, t2gap.tsv, timing.tsv, logs/.  Dumps, joins and trimmed mates are deleted unless --keep.
"""
import argparse, collections, fcntl, os, re, shutil, statistics, subprocess, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import t2_opt            # noqa: E402  properPairU, pfFloor
from budget_sweep import mbtime  # noqa: E402

H = "/home/user/data"
SCR = "/tmp/claude-0/-home-user-lean-align/d87bb448-9ab8-5319-bbfa-cb99301234f2/scratchpad"
LOCK = f"{H}/BIG.lock"
MB = "/tmp/minibwa/minibwa"
MBIDX = f"{H}/mbwg/hg38"
FA = f"{H}/hg38.1l.fa"
CHROMS = f"{SCR}/wk/chroms.txt"
SETS = {
    "hiseq": (f"{H}/hg002/hg200k_cut_R1.fq", f"{H}/hg002/hg200k_cut_R2.fq", None, f"{SCR}/tvm/mb_hiseq.sam"),
    "nova": (f"{H}/novaseq/hg002_nova_200k_cut_1.fq", f"{H}/novaseq/hg002_nova_200k_cut_2.fq", None, f"{SCR}/tiers/mb_nv.sam"),
    "mason": (f"{H}/sim/mason/mason_200k_1.fq", f"{H}/sim/mason/mason_200k_2.fq", f"{H}/sim/mason/mason_200k.truth.tsv",
              f"{SCR}/tiers/mb_ms.sam"),
}
BASE_ENV = {"WG_PKLOAD": "1", "WG_TASKS": "4", "WG_MODES": "RTX", "WG_PG": "4", "WG_XBUD": "5000"}
INF = 1000000
TIER_ORDER = ["T0", "T1", "T1g", "T1u", "T1gm", "T1um", "T2b", "T2", "T3"]

# What each tag proves (TierOk / tierPair_sound, codecs/TierRouter.lean; t2Opt_sound and the T1u / T1um /
# T2b cases of TierOk, tierPair = tierPairB then tierUp, codecs/TierOpt.lean).  Penalties: mismatch 4, gap 6 + 2L, end to end on the trimmed mates.
PROVED = {
    "T0": "a mate was trimmed away (q25 trimmer); nothing else is claimed",
    "T1": "RT mapped it: each mate's placement is its unique best within its cap (pairSpecT at RT's caps), and the two form a proper pair",
    "T1g": "the pair guarantee (pairGQC at G0 <= 4) found the unique best proper pair, score >= -G0; it stays the unique best at any larger caps (pairSpecUT)",
    "T1u": "the exact pair search (pairGXE at G0 = pH1 + pH2 <= 16, under the WG_XEBUD bucket budget) found the unique best proper pair; it stays the unique best at any caps >= G0 (pairSpecUT); reported",
    "T1gm": "the pair guarantee proved a tie: at any caps >= G0 there are proper pairs, and the best score is shared by two pairs at different placements (PairTieOk); no placement reported",
    "T1um": "the exact pair search proved a tie: at any caps >= G0 = pH1 + pH2 the best proper pair is shared by two pairs at different placements (PairTieOk); not reported (the T2 ceilings stay in the dump)",
    "T2b": "the two ceiling placements form a proper pair that no proper pair at any caps outscores: a best pair, but it may tie (t2Opt_sound); not reported as unique",
    "T2": "proved per-mate floors (every placement has penalty >= fl) and ceilings (a placement within pH exists, its CIGAR re-checked by checkRuns); if the guarantee ran and saw no pair, every proper pair has penalty > G0",
    "T3": "proved floors only (per mate; pair > G0 when the guarantee saw no pair); no placement",
}
PLACED = {"T1", "T1g", "T1u"}            # exact pair penalty = pen1 + pen2
CEILED = {"T2", "T2b", "T1um"}           # pair penalty bound = ceil1 + ceil2
FLOORED = {"T2", "T3", "T2b", "T1um"}    # fl1 / fl2 (and pf) are proved floors (FloorOk); T1's cd is its cap


def base(tag):
    return "T0" if tag == "none" else tag.rstrip("xz")


def locked(fn):
    with open(LOCK, "a") as h:
        fcntl.flock(h, fcntl.LOCK_EX)
        try:
            return fn()
        finally:
            fcntl.flock(h, fcntl.LOCK_UN)


def run(cmd, env=None, stdout=None, stderr=None):
    """Run under BIG.lock; returns (rc, wall s, cpu s, maxrss GB) of the whole process."""
    def go():
        t = time.time()
        p = subprocess.Popen(cmd, env=env, stdout=stdout, stderr=stderr, stdin=subprocess.DEVNULL)
        _, st, ru = os.wait4(p.pid, 0)
        return os.waitstatus_to_exitcode(st), time.time() - t, ru.ru_utime + ru.ru_stime, ru.ru_maxrss / 1e6
    return locked(go)


def ours_cmd(binp):
    return [binp, "pmap", f"{H}/wg/hg38"] + open(CHROMS).read().split()


def ours_env(a, st, extra):
    r1, r2 = SETS[st][:2]
    e = dict(os.environ, **BASE_ENV)
    e["WG_READS"] = f"{st}={r1}:{r2}:0"
    e.pop("WG_OUT", None)
    e.pop("WG_TIEROUT", None)
    e.update(extra)
    return e


def parse_result(log):
    for l in open(log):
        m = re.search(r"RESULT set \S+ mode RTX .* ([0-9.]+) s, pairs/s [0-9.]+, cpu ([0-9.]+) s", l)
        if m:
            return float(m.group(1)), float(m.group(2))
    return None


# ---------------------------------------------------------------------------- runs

def do_dump(a, st, extra):
    d = os.path.join(a.out, "dump")
    os.makedirs(d, exist_ok=True)
    e = ours_env(a, st, extra)
    e.update(WG_OUT=d, WG_TIEROUT="1", WG_TRIMOUT=os.path.join(d, f"trim_{st}"))
    log = os.path.join(a.out, "logs", f"dump_{st}.log")
    rc = run(ours_cmd(a.bin), e, open(log, "w"), subprocess.STDOUT)[0]
    for f in os.listdir(d):
        if f.startswith("RTX_"):
            os.remove(os.path.join(d, f))
    print(f"dump {st}: rc {rc}", flush=True)
    return rc


def mb_sam(a, st):
    p = os.path.join(a.out, f"mb_{st}.sam")
    for q in (os.environ.get(f"MB_SAM_{st}"), p, SETS[st][3]):
        if q and os.path.exists(q):
            return q
    r1, r2 = SETS[st][:2]
    rc = run([MB, "map", "-t", "4", MBIDX, r1, r2], stdout=open(p, "w"),
             stderr=open(os.path.join(a.out, "logs", f"mb_sam_{st}.err"), "w"))[0]
    print(f"minibwa SAM {st}: rc {rc}", flush=True)
    return p


def do_joins(a):
    d = os.path.join(a.out, "dump")
    here = os.path.dirname(os.path.abspath(__file__))
    procs = []

    def go():
        for st in a.sets:
            r1, _, truth, _ = SETS[st]
            cmd = ["nice", sys.executable, os.path.join(here, "tier_vs_mb.py"), "join", st, FA, CHROMS,
                   os.path.join(d, f"tiers_{st}.tsv"), mb_sam(a, st), r1,
                   os.path.join(d, f"trim_{st}_R1.txt"), os.path.join(d, f"trim_{st}_R2.txt")] + ([truth] if truth else [])
            procs.append(subprocess.Popen(cmd, stdout=open(os.path.join(d, f"join_{st}.tsv"), "w"),
                                          stderr=open(os.path.join(a.out, "logs", f"join_{st}.err"), "w")))
        return [p.wait() for p in procs]
    print("joins: rc", locked(go), flush=True)


def do_timing(a, extra):
    rows = []
    for i in range(1, a.rounds + 1):
        for st in a.sets:
            r1, r2 = SETS[st][:2]
            err = os.path.join(a.out, "logs", f"mb_{st}.r{i}.err")
            rc, w, c, m = run([MB, "map", "-t", "4", MBIDX, r1, r2], stdout=subprocess.DEVNULL, stderr=open(err, "w"))
            mt = mbtime(err) or (float("nan"), float("nan"))
            rows.append(("minibwa", st, i, rc, mt[0], mt[1], w, c, m))
            log = os.path.join(a.out, "logs", f"rtx_{st}.r{i}.log")
            rc, w, c, m = run(ours_cmd(a.bin), ours_env(a, st, extra), open(log, "w"), subprocess.STDOUT)
            mt = parse_result(log) or (float("nan"), float("nan"))
            rows.append(("RTX", st, i, rc, mt[0], mt[1], w, c, m))
            print(f"round {i} {st}: minibwa {rows[-2][4]:.2f} s / RTX {rows[-1][4]:.2f} s (mapping wall)", flush=True)
    with open(os.path.join(a.out, "timing_runs.tsv"), "w") as h:
        h.write("mapper\tset\tround\trc\tmap_wall\tmap_cpu\tproc_wall\tproc_cpu\tpeak_rss_GB\n")
        for r in rows:
            h.write("\t".join(f"{x:.3f}" if isinstance(x, float) else str(x) for x in r) + "\n")


# ---------------------------------------------------------------------------- statistics

def pl(s):
    if s in ("-", ""):
        return None
    c, x, n, sd = s.split(":")
    return (c, int(x), int(n), sd)


def ov(x, y):
    return x is not None and y is not None and x[0] == y[0] and x[3] == y[3] and x[1] < y[1] + y[2] and y[1] < x[1] + x[2]


def proper(x, y):
    return x is not None and y is not None and t2_opt.proper(x, y)


def border(x, y, b=3):
    """A proper-pair margin of minibwa's re-aligned pair within b letters (fragment / dovetail)."""
    if x is None or y is None or x[0] != y[0] or x[3] == y[3]:
        return False
    f, r = (x, y) if x[3] == "+" else (y, x)
    fr = r[1] + r[2] - f[1]
    return min(abs(v) for v in (fr - t2_opt.LO, t2_opt.HI - fr, r[1] - f[1], r[1] + r[2] - f[1] - f[2])) <= b


def pct(a, b, d=1):
    return f"{100 * a / b:.{d}f}" if b else "-"


def pq(v, q):
    v = sorted(v)
    return v[min(len(v) - 1, len(v) * q // 100)] if v else "-"


def load_dump(path):
    """index -> dump fields (tag, ..., reason a[32], g0 a[33], pf a[34], gm columns a[35:])."""
    out = {}
    for L in open(path):
        a = L.rstrip("\n").split("\t")
        out[int(a[0][1:]) - 1] = a
    return out


def load_truth(path, names):
    idx = {n: i for i, n in enumerate(names)}
    tr = {}
    for l in open(path):
        n, v = l.split()
        c, x, y = v.split(":")
        tr[idx[n]] = (c, x, y)
    return tr


def fq_names(path):
    out = []
    with open(path) as h:
        for k, l in enumerate(h):
            if k % 4 == 0:
                n = l[1:].split()[0]
                out.append(n[:-2] if n.endswith(("/1", "/2")) else n)
    return out


def set_stats(a, st):
    d = os.path.join(a.out, "dump")
    D = load_dump(os.path.join(d, f"tiers_{st}.tsv"))
    chroms = [os.path.basename(x).split(".")[0] for x in open(CHROMS).read().split()]
    truth = None
    if SETS[st][2]:
        truth = load_truth(SETS[st][2], fq_names(SETS[st][0]))
    n = len(D)
    # 1. shares
    cnt, sfx = collections.Counter(), collections.Counter()
    for f in D.values():
        b = base(f[1])
        cnt[b] += 1
        sfx[b] += f[1] != b and f[1] != "none"
    # 3. vs minibwa, per tier, from the join
    V = collections.defaultdict(collections.Counter)
    viol = []
    gapv = collections.defaultdict(list)
    J = os.path.join(d, f"join_{st}.tsv")
    with open(J) as h:
        hdr = h.readline().rstrip("\n").split("\t")
        for l in h:
            r = dict(zip(hdr, l.rstrip("\n").split("\t")))
            i = int(r["i"])
            f = D[i]
            t = base(r["tier"])
            c = V[t]
            c["n"] += 1
            p1, p2 = pl(r["pl1"]), pl(r["pl2"])
            m1, m2 = pl(r["mbpl1"]), pl(r["mbpl2"])
            both = m1 is not None and m2 is not None
            mbt = int(r["mbpen1"]) + int(r["mbpen2"]) if both else None
            mbp = both and proper(m1, m2)
            bd = both and border(m1, m2)
            c["mb_both"] += both
            c["mb_proper"] += mbp
            gm = f[35:] if len(f) > 35 and f[35] == "gm" else None
            if t in PLACED:
                ours = int(r["pen1"]) + int(r["pen2"])
            elif t in CEILED and int(r["ceil1"]) < INF and int(r["ceil2"]) < INF:
                ours = int(r["ceil1"]) + int(r["ceil2"])
            elif t == "T1gm" and gm and gm[1] != "-":
                ours = int(gm[2])
            else:
                ours = None
            if ours is not None:
                c["scored"] += 1
                if both:
                    c["cmp"] += 1
                    c["better"] += ours < mbt
                    c["equal"] += ours == mbt
                    c["worse"] += ours > mbt
                    c["equal_elsewhere"] += ours == mbt and not (ov(p1, m1) and ov(p2, m2)) and p1 is not None
            elif both:
                c["mb_only"] += 1

            # claims: floors (every tier), then the tier's own best-pair claim
            def bad(kind, x, y):
                c["viol"] += 1
                c["viol_border"] += bd
                viol.append(f"{st}\t{r['name']}\t{r['tier']}\t{kind}\tminibwa {x} vs ours {y}" + ("\tborderline fragment" if bd else ""))
            fl = (int(r["fl1"]), int(r["fl2"]))
            for k, m, mp in ((0, m1, "mbpen1"), (1, m2, "mbpen2")):
                if t in FLOORED and m is not None and int(r[mp]) < fl[k]:
                    bad(f"mate{k + 1} floor", r[mp], fl[k])
            if both and t in FLOORED:
                pf = f[34] if len(f) > 34 else "-"
                pfl = fl[0] + fl[1]
                if mbp and pf != "-":
                    pfl = max(pfl, t2_opt.pf_floor(int(pf)))
                if mbt < pfl:
                    bad("pair floor", mbt, pfl)
            if t == "T1":
                for k, m in (("1", m1), ("2", m2)):
                    if m is not None:
                        if int(r["mbpen" + k]) < int(r["pen" + k]):
                            bad(f"T1 mate{k} better", r["mbpen" + k], r["pen" + k])
                        elif int(r["mbpen" + k]) == int(r["pen" + k]) and not ov(pl(r["pl" + k]), m):
                            bad(f"T1 mate{k} tie elsewhere", r["mbpen" + k], r["pen" + k])
            elif mbp and t in ("T1g", "T1u"):
                if mbt < ours:
                    bad("unique best pair beaten", mbt, ours)
                elif mbt == ours and not (ov(p1, m1) and ov(p2, m2)):
                    bad("unique best pair tied elsewhere", mbt, ours)
            elif mbp and t in ("T1gm", "T2b") and ours is not None and mbt < ours:
                bad("best pair beaten", mbt, ours)
            # mason truth
            if truth is not None and i in truth:
                c["truth_n"] += 1
                c["mb_ok"] += r["mbok1"] == "1" and r["mbok2"] == "1"
                if ours is not None and p1 is not None and p2 is not None:
                    c["ok"] += r["ok1"] == "1" and r["ok2"] == "1"
                elif t == "T1gm" and gm and len(gm) > 6:
                    tc, iv1, iv2 = truth[i]

                    def hit(s, iv, ln):
                        m = re.match(r"(\d+):(\d+)([+-])\d+", s)
                        a0, a1 = map(int, iv[:-1].split("-"))
                        x = int(m.group(2))
                        return chroms[int(m.group(1))] == tc and m.group(3) == iv[-1] and x < a1 and a0 < x + ln
                    c["tie_has_truth"] += any(hit(q.split("/")[0], iv1, int(r["len1"])) and hit(q.split("/")[1], iv2, int(r["len2"]))
                                              for q in gm[6].split(","))
    # 4. T1gm split, from the dump
    G = collections.Counter()
    for f in D.values():
        if base(f[1]) != "T1gm":
            continue
        G["n"] += 1
        gm = f[35:] if len(f) > 35 and f[35] == "gm" else None
        if gm is None:
            G["no gm columns"] += 1
            continue
        if gm[1] == "-":
            G["enumeration n/a"] += 1
            continue
        nb, b0, b1 = int(gm[3]), int(gm[2]), int(gm[4])
        G["exact tie" if nb >= 2 else "close, unequal"] += 1
        G[f"best pen {b0}"] += 1
        G[f"pairs at best {'2' if nb == 2 else '3-9' if nb < 10 else '>=10'}"] += 1
        G[f"tied pairs: {gm[5]}"] += 1
        G["next pen within G0" if b1 <= int(f[33]) else "next pen > G0 or none"] += 1
    # 5. T2 gap
    for f in D.values():
        t = base(f[1])
        if t not in ("T2", "T2b") or len(f) < 32:
            continue
        pf = f[34] if len(f) > 34 else "-"
        m1, m2 = f[2:17], f[17:32]
        c1, c2 = int(m1[11]), int(m2[11])
        if c1 >= INF or c2 >= INF:
            continue
        floor = int(m1[2]) + int(m2[2])
        if pf != "-":
            floor = max(floor, t2_opt.pf_floor(int(pf)))
        x, y = t2_opt.mpl(m1), t2_opt.mpl(m2)
        g = c1 + c2 - floor
        gapv[t].append((g, x is not None and y is not None and t2_opt.proper(x, y)))
        gapv["T2 all"].append(gapv[t][-1])
    if set(gapv) <= {"T2", "T2 all"}:
        gapv.pop("T2 all", None)
    return n, cnt, sfx, V, G, gapv, viol


def report(a):
    out = open(os.path.join(a.out, "report.txt"), "w")
    T = {k: open(os.path.join(a.out, f"{k}.tsv"), "w") for k in ("tiers", "vs_mb", "t1gm", "t2gap")}
    T["tiers"].write("set\ttier\tpairs\tpct\tof_which_x_or_z\n")
    T["vs_mb"].write("set\ttier\tpairs\tmb_maps_both\tours_scored\tcompared\tours_better\tequal\tworse\tequal_elsewhere\t"
                     "pct_better\tpct_equal\tpct_worse\tmb_only\tviolations\tviol_borderline\tours_correct_pct\tmb_correct_pct\ttie_has_truth\n")
    T["t1gm"].write("set\tclass\tpairs\tpct_of_T1gm\n")
    T["t2gap"].write("set\ttier\tpairs\tp50\tp90\tle0\tle8\tle16\tpct_le0\tpct_le8\tpct_le16\tceil_pair_proper_pct\tcertified_le0_proper\n")
    P = lambda *x: print(*x, file=out)
    P("Final statistics, mode RTX vs minibwa (bench/final_stats.py)")
    repo = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    git = subprocess.run(["git", "-C", repo, "describe", "--always", "--dirty"], capture_output=True, text=True).stdout.strip()
    P(f"code {git} ({repo}); binary {a.bin}; env {' '.join(f'{k}={v}' for k, v in {**BASE_ENV, **a.extra}.items())}; sets {','.join(a.sets)}; "
      f"{time.strftime('%Y-%m-%d %H:%M')}")
    P("Scores: penalties (mismatch 4, gap 6 + 2L), our trimmed mates end to end, both mappers (bench/tier_vs_mb.py).")
    P("Ours per tier: T1/T1g/T1u pen1 + pen2 (proved); T1gm best tied pair (gm columns); T2/T2b/T1um ceil1 + ceil2.")
    allv = []
    seen_tags = []
    S = {}
    for st in a.sets:
        S[st] = set_stats(a, st)
        for t in S[st][1]:
            if t not in seen_tags:
                seen_tags.append(t)
    tags = [t for t in TIER_ORDER if t in seen_tags] + [t for t in seen_tags if t not in TIER_ORDER]

    P("\n1. Tier shares (% of pairs; x / z suffixes folded in)")
    P("tier\t" + "\t".join(a.sets))
    for t in tags:
        P(t + "\t" + "\t".join(f"{pct(S[st][1][t], S[st][0], 2)}" for st in a.sets))
    P("pairs\t" + "\t".join(str(S[st][0]) for st in a.sets))
    for st in a.sets:
        for t in tags:
            T["tiers"].write(f"{st}\t{t}\t{S[st][1][t]}\t{pct(S[st][1][t], S[st][0], 3)}\t{S[st][2][t]}\n")

    P("\n2. What each tier proves (codecs/TierRouter.lean TierOk, tierPair_sound; codecs/TierOpt.lean)")
    for t in tags:
        P(f"{t}\t{PROVED.get(t, 'new tag: see TierOk in codecs/TierRouter.lean / TierOpt.lean')}")

    P("\n3. Per tier vs minibwa (pair penalty; violations = minibwa below a proved floor or beating a proved best pair; must be 0)")
    P("set\ttier\tpairs\tcompared\tbetter%\tequal%\tworse%\tmb_only\tviolations\tours_ok%\tmb_ok%")
    for st in a.sets:
        V = S[st][3]
        for t in tags:
            c = V.get(t)
            if c is None:
                continue
            okc = pct(c["ok"], c["truth_n"]) if c["truth_n"] else "-"
            if t == "T1gm" and c["truth_n"]:
                okc = f"{okc} (truth among tied best {pct(c['tie_has_truth'], c['truth_n'])})"
            P(f"{st}\t{t}\t{c['n']}\t{c['cmp']}\t{pct(c['better'], c['cmp'])}\t{pct(c['equal'], c['cmp'])}\t{pct(c['worse'], c['cmp'])}\t"
              f"{c['mb_only']}\t{c['viol']}\t{okc}\t{pct(c['mb_ok'], c['truth_n']) if c['truth_n'] else '-'}")
            T["vs_mb"].write("\t".join(str(x) for x in (
                st, t, c["n"], c["mb_both"], c["scored"], c["cmp"], c["better"], c["equal"], c["worse"], c["equal_elsewhere"],
                pct(c["better"], c["cmp"], 2), pct(c["equal"], c["cmp"], 2), pct(c["worse"], c["cmp"], 2), c["mb_only"],
                c["viol"], c["viol_border"], pct(c["ok"], c["truth_n"], 2) if c["truth_n"] else "-",
                pct(c["mb_ok"], c["truth_n"], 2) if c["truth_n"] else "-", c["tie_has_truth"])) + "\n")
        allv += S[st][6]
    P(f"total violations: {len(allv)}")
    for v in allv[:40]:
        P("VIOLATION\t" + v)

    P("\n4. T1gm: exact ties vs close-but-unequal (all proper pairs within G0 re-enumerated, no early stop)")
    keys = []
    for st in a.sets:
        for k in S[st][4]:
            if k != "n" and k not in keys:
                keys.append(k)
    P("class\t" + "\t".join(a.sets))
    P("T1gm pairs\t" + "\t".join(str(S[st][4]["n"]) for st in a.sets))
    for k in sorted(keys):
        P(k + "\t" + "\t".join(f"{S[st][4][k]} ({pct(S[st][4][k], S[st][4]['n'])}%)" for st in a.sets))
    for st in a.sets:
        for k in ["n"] + sorted(keys):
            T["t1gm"].write(f"{st}\t{k}\t{S[st][4][k]}\t{pct(S[st][4][k], S[st][4]['n'], 2)}\n")

    P("\n5. T2 pair floor-ceiling gap: ceil1 + ceil2 - max(fl1 + fl2, pfFloor(pf))")
    P("set\ttier\tpairs\tp50\tp90\t<=0%\t<=8%\t<=16%\tceiling pair proper%\t<=0 and proper (t2Opt certified)%")
    for st in a.sets:
        for t in ("T2", "T2b", "T2 all"):
            v = S[st][5].get(t)
            if not v:
                continue
            g = [x[0] for x in v]
            k0, k8, k16 = (sum(x <= y for x in g) for y in (0, 8, 16))
            pr = sum(x[1] for x in v)
            ce = sum(x[1] and x[0] <= 0 for x in v)
            P(f"{st}\t{t}\t{len(g)}\t{pq(g, 50)}\t{pq(g, 90)}\t{pct(k0, len(g))}\t{pct(k8, len(g))}\t{pct(k16, len(g))}\t{pct(pr, len(g))}\t{pct(ce, len(g))}")
            T["t2gap"].write(f"{st}\t{t}\t{len(g)}\t{pq(g, 50)}\t{pq(g, 90)}\t{k0}\t{k8}\t{k16}\t{pct(k0, len(g), 2)}\t"
                             f"{pct(k8, len(g), 2)}\t{pct(k16, len(g), 2)}\t{pct(pr, len(g), 2)}\t{ce}\n")

    tp = os.path.join(a.out, "timing_runs.tsv")
    if os.path.exists(tp):
        P(f"\n6. Timing, 4 threads, median of rounds (s); mapping = index load excluded; process = whole run")
        R = collections.defaultdict(list)
        with open(tp) as h:
            hdr = h.readline().rstrip("\n").split("\t")
            for l in h:
                r = dict(zip(hdr, l.rstrip("\n").split("\t")))
                R[(r["mapper"], r["set"])].append(r)
        tt = open(os.path.join(a.out, "timing.tsv"), "w")
        hd = "set\tmapper\trounds\tmap_wall\tmap_cpu\tproc_wall\tproc_cpu\tpeak_rss_GB\tmb/ours_map_wall\tmb/ours_map_cpu"
        P(hd)
        tt.write(hd + "\n")
        for st in a.sets:
            med = {}
            for m in ("minibwa", "RTX"):
                rs = R.get((m, st), [])
                if not rs:
                    continue
                med[m] = [statistics.median(float(r[k]) for r in rs) for k in ("map_wall", "map_cpu", "proc_wall", "proc_cpu", "peak_rss_GB")]
            for m, v in med.items():
                ratio = "\t-\t-"
                if m == "RTX" and "minibwa" in med:
                    ratio = f"\t{med['minibwa'][0] / v[0]:.2f}\t{med['minibwa'][1] / v[1]:.2f}"
                line = f"{st}\t{m}\t{len(R[(m, st)])}\t" + "\t".join(f"{x:.2f}" for x in v) + ratio
                P(line)
                tt.write(line + "\n")
    out.close()
    for h in T.values():
        h.close()
    print(open(os.path.join(a.out, "report.txt")).read())


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    here = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    ap.add_argument("--out", default=f"{SCR}/final")
    ap.add_argument("--bin", default=os.path.join(here, ".lake/build/bin/whole_genome"))
    ap.add_argument("--sets", default="hiseq,nova,mason")
    ap.add_argument("--rounds", type=int, default=3)
    ap.add_argument("--env", action="append", default=[], help="K=V for our mapper (repeatable)")
    ap.add_argument("--no-timing", action="store_true")
    ap.add_argument("--no-dump", action="store_true", help="reuse DIR/dump (tiers + trimmed mates + joins)")
    ap.add_argument("--keep", action="store_true", help="keep dumps, joins and trimmed mates")
    ap.add_argument("--report-only", action="store_true")
    a = ap.parse_args()
    a.sets = a.sets.split(",")
    a.extra = dict(x.split("=", 1) for x in a.env)
    os.makedirs(os.path.join(a.out, "logs"), exist_ok=True)
    if not a.report_only:
        # a private copy of the binary: a rebuild during the run does not change what is measured
        b = os.path.join(a.out, "whole_genome.bin")
        shutil.copy2(a.bin, b)
        a.bin = b
        if not a.no_dump:
            for st in a.sets:
                do_dump(a, st, a.extra)
            do_joins(a)
        if not a.no_timing:
            do_timing(a, a.extra)
    report(a)
    if not a.keep and not a.report_only:
        shutil.rmtree(os.path.join(a.out, "dump"), ignore_errors=True)
        for f in os.listdir(a.out):
            if f.endswith((".bin", ".sam")):
                os.remove(os.path.join(a.out, f))


if __name__ == "__main__":
    main()
