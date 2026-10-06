#!/usr/bin/env python3
"""Benchmark only.  Mode RTX tiers (WG_TIEROUT=1 dump, tiers_<set>.tsv) against minibwa.

Joins, per pair, our tier dump (per mate: st cap floor pen | chr start len strand cpen | pU pC
ceil pD src rs, see MateX.show in bench/WholeGenome.lean on speed/tiers) with minibwa's primary
records, and re-scores both mappers with the spec penalty (mismatch 4, gap 6 + 2L, no clipping).

Scoring rule (the same for both mappers): OUR trimmed mate (the q25 trimmer's window, from the
WG_TRIMOUT files) aligned end to end.  Ours: global alignment on our window [start, start+len)
(checks the dumped ceiling / pen).  minibwa: semi-global (whole mate, free reference ends) in
minibwa's reference span +- PAD (soft clips are thereby re-aligned, not dropped); `mbpl` is that
re-alignment's exact reference window (used for same-place and proper-pair tests), `mbraw` minibwa's.
parasail: match 0, mismatch -4, gap open 8 / extend 2 (= 6 + 2L).

   python3 bench/tier_vs_mb.py join <set> <genome.1l.fa> <chroms.txt> <tiers.tsv> <mb.sam>
        <R1.fq> <trim_R1.txt> <trim_R2.txt> [truth.tsv] > join_<set>.tsv
The join is read back by bench/tier_vs_mb_report.py."""
import mmap, os, re, sys
import parasail

PAD = 40
M = parasail.matrix_create("ACGTN", 0, -4)
INF = 1000000
CMP = str.maketrans("ACGTN", "TGCAN")


def rc(s):
    return s.translate(CMP)[::-1]


def load_genome(fa):
    f = open(fa, "rb")
    G = mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ)
    chrom, i = {}, 0
    while i < len(G):
        j = G.find(b"\n", i)
        name = G[i + 1:j].split()[0].decode()
        k = G.find(b"\n", j + 1)
        k = len(G) if k < 0 else k
        chrom[name] = (j + 1, k - j - 1)
        i = k + 1
    return G, chrom


def trimmed(path):
    out = []
    with open(path) as h:
        for ln, l in enumerate(h):
            if ln % 2 == 1:
                out.append(l.strip())
    return out


def fq_names(path):
    out = []
    with open(path) as h:
        for ln, l in enumerate(h):
            if ln % 4 == 0:
                n = l[1:].split()[0]
                out.append(n[:-2] if n.endswith(("/1", "/2")) else n)
    return out


def ref_span(cig):
    return sum(int(n) for n, op in re.findall(r"(\d+)([MDN=X])", cig))


def main():
    (_, _, st, fa, chf, tiers, sam, fq1, t1, t2) = sys.argv[:10]
    truth = sys.argv[10] if len(sys.argv) > 10 else None
    G, chrom = load_genome(fa)
    chroms = [os.path.basename(x).split(".")[0] for x in open(chf).read().split()]
    T1, T2 = trimmed(t1), trimmed(t2)
    names = fq_names(fq1)
    assert len(T1) == len(T2) == len(names), (len(T1), len(T2), len(names))
    idx = {n: i for i, n in enumerate(names)}
    # minibwa primaries
    mb = [[None, None] for _ in names]
    for line in open(sam):
        if line[0] == "@":
            continue
        f = line.rstrip("\n").split("\t")
        fl = int(f[1])
        if fl & 0x900:
            continue
        mb[idx[f[0]]][0 if fl & 64 else 1] = f
    tr = {}
    if truth:
        for l in open(truth):
            n, v = l.split()
            c, x, y = v.split(":")
            tr[idx[n]] = (c, x, y)

    def ourpen(seq, pl):
        c, s0, ln, sd = pl
        s, n = chrom[c]
        ref = G[s + s0:s + s0 + ln].decode().upper()
        q = seq if sd == "+" else rc(seq)
        return -parasail.nw_scan_16(q, ref, 8, 2, M).score

    def mbpen(seq, f, n0):
        s, n = chrom[f[2]]
        lead = re.match(r"(\d+)[SH]", f[5])
        p = int(f[3]) - 1 - (int(lead.group(1)) if lead else 0)
        dels = sum(int(x) for x in re.findall(r"(\d+)[DN]", f[5]))
        a, b = max(0, p - PAD), min(n, p + max(len(f[9]), n0) + dels + PAD)
        ref = G[s + a:s + b].decode().upper()
        q = rc(seq) if int(f[1]) & 16 else seq
        r = parasail.sg_dx_trace_scan_16(q, ref, 8, 2, M)
        lead = re.match(rb"(\d+)D", r.cigar.decode)
        b0 = int(lead.group(1)) if lead else 0
        return -r.score, a + b0, r.end_ref + 1 - b0

    hdr = ["i", "name", "tier", "len1", "len2"]
    for k in (1, 2):
        hdr += [x + str(k) for x in ("st", "cap", "fl", "pen", "pl", "ceil", "src", "rs", "ours",
                                     "mbmap", "mbpl", "mbraw", "mapq", "cigar", "xa", "sa", "mbpen", "ok", "mbok")]
    hdr += ["mbproper"]
    print("\t".join(hdr))
    for line in open(tiers):
        f = line.rstrip("\n").split("\t")
        i = int(f[0][1:]) - 1
        if len(f) < 32:
            continue  # trimmed away ("none")
        tier = f[1]
        seqs = (T1[i], T2[i])
        row = [str(i), names[i], tier, str(len(T1[i])), str(len(T2[i]))]
        rec = mb[i]
        for k in (0, 1):
            g = f[2 + 15 * k:17 + 15 * k]
            pl = None if g[4] == "-" else (chroms[int(g[4])], int(g[5]), int(g[6]), g[7])
            ours = ourpen(seqs[k], pl) if pl else -1
            r = rec[k]
            mapped = r is not None and not int(r[1]) & 4
            if mapped:
                sd = "-" if int(r[1]) & 16 else "+"
                mbraw = f"{r[2]}:{int(r[3]) - 1}:{ref_span(r[5])}:{sd}"
                tags = r[11:]
                xa = int(any(t.startswith("XA:") for t in tags))
                sa = int(any(t.startswith("SA:") for t in tags))
                mp, ms0, ml = mbpen(seqs[k], r, len(seqs[k]))
                mbpl = f"{r[2]}:{ms0}:{ml}:{sd}"
            else:
                mbpl, mbraw, xa, sa, mp = "-", "-", 0, 0, -1
            ok = mbok = ""
            if i in tr:
                c, iv = tr[i][0], tr[i][1 + k]
                a0, a1 = map(int, iv[:-1].split("-"))
                sd0 = iv[-1]

                def hit(cc, s0, ln, sd):
                    return int(cc == c and sd == sd0 and s0 < a1 and a0 < s0 + ln)
                ok = str(hit(*pl)) if pl else "0"
                if mapped:
                    mc, ms_, ml, msd = mbraw.split(":")
                    mbok = str(hit(mc, int(ms_), int(ml), msd))
                else:
                    mbok = "0"
            row += [g[0], g[1], g[2], g[3], f"{pl[0]}:{pl[1]}:{pl[2]}:{pl[3]}" if pl else "-", g[11], g[13], g[14],
                    str(ours), str(int(mapped)), mbpl, mbraw, r[4] if mapped else "-", r[5] if mapped else "-",
                    str(xa), str(sa), str(mp), ok, mbok]
        proper = int(rec[0] is not None and bool(int(rec[0][1]) & 2) and not int(rec[0][1]) & 4
                     and rec[1] is not None and not int(rec[1][1]) & 4)
        row.append(str(proper))
        print("\t".join(row))


if __name__ == "__main__":
    main()
