#!/usr/bin/env python3
"""Benchmark only.  Give-up budget (WG_XBUD) and tier 2 heuristic effort sweep, mode RTX vs minibwa.

Quality, from the joins of bench/tier_vs_mb.py (one per set):

   python3 bench/budget_sweep.py quality TAG set=join.tsv ... >> quality.tsv

one line per set: tier shares; "matches minibwa" (we place both mates and our pair score, the proved
pen for T1/T1g and the re-scored ceiling for T2, is <= minibwa's re-scored pair, or minibwa does not
map both mates), split by tier; class (a) (minibwa proper, both MAPQ >= 20, no XA) within 0 / <= 8 and
T3; mason pairs correct (both mates overlap the truth, same strand), all and per tier.

Speed, from the run logs (RESULT lines of WholeGenome RTX; minibwa stderr: mapping = worker end -
index loaded, CPU the same difference):

   python3 bench/budget_sweep.py speed DIR TAG ... > speed.tsv

medians over the rounds DIR/TAG.r<k>.txt and DIR/mb_<s>.r<k>.err (or MB=glob of minibwa logs).

   python3 bench/budget_sweep.py table quality.tsv speed.tsv [base_tag]   (markdown)"""
import glob, os, re, statistics, sys
from collections import Counter, defaultdict

TIERS = ("T1", "T1g", "T1gm", "T2", "T3")
SETN = {"mason": "mason", "nova": "nova", "hg200k": "hiseq", "hiseq": "hiseq",
        "ms": "mason", "nv": "nova", "hi": "hiseq"}


def rows(path):
    with open(path) as h:
        hdr = h.readline().rstrip("\n").split("\t")
        for l in h:
            r = dict(zip(hdr, l.rstrip("\n").split("\t")))
            r["base"] = r["tier"].rstrip("xz")
            yield r


def quality(tag, args):
    out = []
    for a in args:
        st, path = a.split("=", 1)
        c = Counter()
        n = 0
        for r in rows(path):
            n += 1
            t = r["base"]
            c["t_" + t] += 1
            placed = r["pl1"] != "-" and r["pl2"] != "-"
            if t in ("T1", "T1g"):
                ours = int(r["pen1"]) + int(r["pen2"])
            elif t == "T2":
                ours = int(r["ceil1"]) + int(r["ceil2"])
            else:
                ours = None
                placed = False
            both = r["mbpl1"] != "-" and r["mbpl2"] != "-"
            mb = int(r["mbpen1"]) + int(r["mbpen2"]) if both else None
            match = placed and (mb is None or ours <= mb)
            if match:
                c["m_" + t] += 1
                c["m_strict_" + t] += mb is not None
            xa = r["xa1"] == "1" or r["xa2"] == "1"
            mq = min(int(r["mapq1"]) if r["mapq1"] != "-" else -1, int(r["mapq2"]) if r["mapq2"] != "-" else -1)
            if both and r["mbproper"] == "1" and mq >= 20 and not xa:
                c["a"] += 1
                if placed and ours <= mb:
                    c["a0"] += 1
                if placed and ours <= mb + 8:
                    c["a8"] += 1
                if t == "T3":
                    c["a3"] += 1
                if t == "T1gm":
                    c["agm"] += 1
            if r["ok1"] != "":
                ok = r["ok1"] == "1" and r["ok2"] == "1" and placed
                c["ok"] += ok
                c["ok_" + t] += ok
                c["mbok"] += r["mbok1"] == "1" and r["mbok2"] == "1"
                c["mbok_" + t] += r["mbok1"] == "1" and r["mbok2"] == "1"
        f = {"tag": tag, "set": SETN.get(st, st), "n": n}
        for t in TIERS:
            f[t] = c["t_" + t]
            f["m" + t] = c["m_" + t]
            f["ok" + t] = c["ok_" + t]
            f["mbok" + t] = c["mbok_" + t]
        for k in ("a", "a0", "a8", "a3", "agm", "ok", "mbok"):
            f[k] = c[k]
        out.append(f)
    keys = list(out[0].keys())
    if not os.environ.get("NOHDR"):
        print("\t".join(keys))
    for f in out:
        print("\t".join(str(f[k]) for k in keys))


def mbtime(path):
    s = open(path).read()
    a = re.search(r"main_map::([0-9.]+)\*([0-9.]+)\] index loaded", s)
    b = re.search(r"worker_pipeline::([0-9.]+)\*([0-9.]+)\] mapped", s)
    if not a or not b:
        return None
    t0, r0, t1, r1 = map(float, (a.group(1), a.group(2), b.group(1), b.group(2)))
    return t1 - t0, t1 * r1 - t0 * r0


def speed(d, tags):
    print("tag\tset\twall\tcpu\trounds")
    mb = defaultdict(list)
    for p in glob.glob(os.environ.get("MB", os.path.join(d, "mb_*.r*.err"))):
        st = re.sub(r"\.r\d+$", "", os.path.basename(p)[:-4]).split("_")[-1].split(".")[-1]
        v = mbtime(p)
        if v:
            mb[SETN.get(st, st)].append(v)
    for st, v in sorted(mb.items()):
        print(f"minibwa\t{st}\t{statistics.median(x[0] for x in v):.3f}\t{statistics.median(x[1] for x in v):.2f}\t{len(v)}")
    for tag in tags:
        v = defaultdict(list)
        for p in sorted(glob.glob(os.path.join(d, f"{tag}.r*.txt")) + glob.glob(os.path.join(d, f"{tag}.*.r[0-9].log"))):
            for l in open(p):
                m = re.search(r"RESULT set (\S+) mode RTX .* ([0-9.]+) s, pairs/s [0-9.]+, cpu ([0-9.]+) s", l)
                if m:
                    v[SETN.get(m.group(1), m.group(1))].append((float(m.group(2)), float(m.group(3))))
        for st, x in sorted(v.items()):
            print(f"{tag}\t{st}\t{statistics.median(y[0] for y in x):.3f}\t{statistics.median(y[1] for y in x):.2f}\t{len(x)}")


def load_tsv(path):
    out = []
    hdr = None
    for l in open(path):
        f = l.rstrip("\n").split("\t")
        if f[0] == "tag":
            hdr = f
            continue
        out.append(dict(zip(hdr, f)))
    return out


def pc(a, b):
    return f"{100 * a / b:.1f}" if b else "-"


def table(qp, sp, base):
    Q = load_tsv(qp)
    S = {(r["tag"], r["set"]): r for r in load_tsv(sp)}
    sets = [s for s in ("hiseq", "nova", "mason") if any(q["set"] == s for q in Q)]
    for st in sets:
        mbw = S.get(("minibwa", st))
        bw = S.get((base, st))
        print(f"\n#### {st}" + (f" (minibwa mapping {float(mbw['wall']):.2f} s wall, {float(mbw['cpu']):.1f} s CPU)" if mbw else ""))
        print("| setting | wall s | ×mb | vs base | CPU s | ×mb CPU | T1 | T1g | T1gm | T2 | T3 | proved T1+T1g+T1gm | "
              "match: proved | match: T2 | match: all | (a) ≤0 | (a) ≤8 | (a) T3 |" + (" mason ok: all (mb) | ok T1/T1g/T2 |" if st == "mason" else ""))
        print("|---" * (17 + 2 * (st == "mason")) + "|")
        for q in Q:
            if q["set"] != st:
                continue
            g = lambda k: int(q[k])
            n = g("n")
            sp = S.get((q["tag"], st))
            if sp and mbw:
                w, c = float(sp["wall"]), float(sp["cpu"])
                ws = f"{w:.2f} | {float(mbw['wall']) / w:.2f} | {(w / float(bw['wall']) - 1) * 100:+.0f}% | {c:.1f} | {float(mbw['cpu']) / c:.2f}" if bw else f"{w:.2f} | | | {c:.1f} |"
            else:
                ws = "- | - | - | - | -"
            pr = g("mT1") + g("mT1g")
            line = (f"| {q['tag']} | {ws} | " + " | ".join(pc(g(t), n) for t in TIERS) + f" | {pc(g('T1') + g('T1g') + g('T1gm'), n)} | "
                    f"{pc(pr, n)} | {pc(g('mT2'), n)} | **{pc(pr + g('mT2'), n)}** | {pc(g('a0'), g('a'))} | {pc(g('a8'), g('a'))} | {pc(g('a3'), g('a'))} |")
            if st == "mason":
                line += (f" {pc(g('ok'), n)} ({pc(g('mbok'), n)}) | "
                         + "/".join(pc(g("ok" + t), g(t)) for t in ("T1", "T1g", "T2")) + " |")
            print(line)


def losses(args):
    """Pairs that do not match minibwa (see `quality`), by tier and by what minibwa's alignment has."""
    print("| set | not matched | T1gm (no placement) | T2 worse | of which: mb indel | mb soft clip | mb mate pen > 16 | "
          "other place | T3 | of which: a mate < 50 bp | mb soft clip | mb maps < 2 mates | mb MAPQ < 20 |")
    print("|---" * 14 + "|")
    for a in args:
        st, path = a.split("=", 1)
        c = Counter()
        n = 0
        for r in rows(path):
            n += 1
            t = r["base"]
            both = r["mbpl1"] != "-" and r["mbpl2"] != "-"
            mb = int(r["mbpen1"]) + int(r["mbpen2"]) if both else None
            indel = any(x in r["cigar" + k] for k in "12" for x in "ID")
            clip = any("S" in r["cigar" + k] for k in "12")
            if t in ("T1", "T1g"):
                continue
            if t == "T1gm":
                c["gm"] += 1
                continue
            if t == "T2":
                ours = int(r["ceil1"]) + int(r["ceil2"])
                if mb is None or ours <= mb:
                    continue
                c["t2"] += 1
                c["t2i"] += indel
                c["t2c"] += clip
                c["t2h"] += max(int(r["mbpen1"]), int(r["mbpen2"])) > 16
                same = all(r["pl" + k] != "-" and r["mbpl" + k] != "-" and ovs(r["pl" + k], r["mbpl" + k]) for k in "12")
                c["t2o"] += not same
                continue
            c["t3"] += 1
            c["t3s"] += min(int(r["len1"]), int(r["len2"])) < 50
            c["t3c"] += clip
            c["t3u"] += not both
            mq = min(int(r["mapq1"]) if r["mapq1"] != "-" else -1, int(r["mapq2"]) if r["mapq2"] != "-" else -1)
            c["t3q"] += both and mq < 20
        tot = c["gm"] + c["t2"] + c["t3"]
        print(f"| {SETN.get(st, st)} | {pc(tot, n)}% | {pc(c['gm'], n)}% | {pc(c['t2'], n)}% | {pc(c['t2i'], c['t2'])}% | {pc(c['t2c'], c['t2'])}% | "
              f"{pc(c['t2h'], c['t2'])}% | {pc(c['t2o'], c['t2'])}% | {pc(c['t3'], n)}% | {pc(c['t3s'], c['t3'])}% | {pc(c['t3c'], c['t3'])}% | "
              f"{pc(c['t3u'], c['t3'])}% | {pc(c['t3q'], c['t3'])}% |")


def ovs(a, b):
    a, b = a.split(":"), b.split(":")
    return a[0] == b[0] and a[3] == b[3] and int(a[1]) < int(b[1]) + int(b[2]) and int(b[1]) < int(a[1]) + int(a[2])


def main():
    cmd = sys.argv[1]
    if cmd == "losses":
        losses(sys.argv[2:])
        return
    if cmd == "quality":
        quality(sys.argv[2], sys.argv[3:])
    elif cmd == "speed":
        speed(sys.argv[2], sys.argv[3:])
    elif cmd == "table":
        table(sys.argv[2], sys.argv[3], sys.argv[4] if len(sys.argv) > 4 else "b5000")


if __name__ == "__main__":
    main()
