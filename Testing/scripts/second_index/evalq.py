"""Which bound-only complete-search pairs a finer pigeonhole settles, and at what lookup cost.
usage: python3 evalq.py SCRATCH  (reads bound.*.txt and kc/c{k}.txt)

Model, per pair (cap c from the dump, e = c // 4 seeds a pair within the cap can spoil):
- seeds: disjoint grid k-mers per mate, m = n // k, at offsets j * (n // m) (as the 25-mer index does);
- scheme (k, r): look up the r rarest seeds of each mate (r >= e + 1); a placement within the cap keeps >= r - e of
  them clean on its diagonal, so a candidate is a (strand, diagonal) supported by >= r - e distinct seeds within
  +-e letters (indels shift the diagonal); r = e + 1 is today's 1-of-(e+1) join;
- settled: no mate-1 candidate has a mate-2 candidate on the other strand within the insert window (|d1 - d2| <= 1000 + n);
- cost: the summed occurrence counts of the looked-up seeds (index entries scanned); a seed seen > CAP times has no
  positions here, so a scheme needing it is counted as "too heavy".
"""
import sys, collections
S = sys.argv[1]
CAP = 500
HI = 1000

def load_counts(k):
    d = {}
    for l in open(f'{S}/kc/c{k}.txt'):
        p = l.split()
        w, cnt = p[0], int(p[1])
        pos = None
        if cnt <= CAP:
            pos = []
            for t in p[2:]:
                g, s = t.split(':'); pos.append((int(g), int(s)))
        d[w] = (cnt, pos)
    return d

def seeds(R, k):
    n = len(R); m = n // k
    if m == 0: return []
    Ls = n // m
    return [(j * Ls, R[j * Ls: j * Ls + k]) for j in range(m)]

def cands(R, k, cnt, r, e):
    """(candidate set or None if too heavy, cost)"""
    n = len(R)
    sd = []
    for o, w in seeds(R, k):
        if len(w) < k or not set(w) <= set('ACGT'):
            continue  # a seed with an N is never clean: left out (e unchanged, conservative)
        c, pos = cnt[w]
        sd.append((c, o, w, pos))
    if len(sd) < r: return None, None
    sd.sort(key=lambda x: x[0])
    use = sd[:r]
    cost = sum(x[0] for x in use)
    if any(x[3] is None for x in use): return None, cost
    need = r - e
    if need < 1: return None, cost
    hits = []  # (strand, diag, seed index)
    for si, (c, o, w, pos) in enumerate(use):
        for g, s in pos:
            if s == 0: hits.append((0, g - o, si))
            else: hits.append((1, g - (n - o - k), si))
    hits.sort()
    out = []
    i = 0
    # sliding window per strand over diagonals within +-e: candidate when >= need distinct seeds
    for st in (0, 1):
        hs = [h for h in hits if h[0] == st]
        j = 0; win = collections.Counter()
        for a in range(len(hs)):
            while j < len(hs) and hs[j][1] <= hs[a][1] + 2 * e:
                win[hs[j][2]] += 1; j += 1
            if len(win) >= need: out.append((st, hs[a][1]))
            win[hs[a][2]] -= 1
            if win[hs[a][2]] == 0: del win[hs[a][2]]
    return out, cost

def settled(c1, c2, n):
    if not c1 or not c2: return True
    by = {0: sorted(d for s, d in c2 if s == 0), 1: sorted(d for s, d in c2 if s == 1)}
    import bisect
    for s, d in c1:
        L = by[1 - s]
        i = bisect.bisect_left(L, d - HI - n)
        if i < len(L) and L[i] <= d + HI + n: return False
    return True

pairs = {}
for name, f in (('NovaSeq', 'bound.novaseq_200k.txt'), ('HiSeq', 'bound.hg002_200k.txt')):
    pairs[name] = [l.rstrip('\n').split('\t') for l in open(f'{S}/{f}') if l.startswith('BOUND')]

for k in (25, 20, 18, 16):
    cnt = load_counts(k)
    for name, ps in pairs.items():
        tot_us = sum(int(p[4]) for p in ps)
        res = collections.Counter(); us_set = 0; cost_set = []; heavy = 0
        best_r = collections.Counter()
        for p in ps:
            c = int(p[2]); e = c // 4; R1, R2 = p[5], p[6]; us = int(p[4])
            m = min(len(R1), len(R2)) // k
            done = False
            for r in range(e + 1, m + 1):
                c1, k1 = cands(R1, k, cnt, r, e)
                c2, k2 = cands(R2, k, cnt, r, e)
                if c1 is None or c2 is None:
                    continue
                if settled(c1, c2, max(len(R1), len(R2))):
                    done = True; best_r[r - e] += 1; cost_set.append(k1 + k2); us_set += us
                    break
            if done: res['settled'] += 1
            else:
                # too heavy for every r?
                c1, _ = cands(R1, k, cnt, e + 1, e); c2, _ = cands(R2, k, cnt, e + 1, e)
                res['open (too heavy)' if (c1 is None or c2 is None) else 'open'] += 1
        cs = sorted(cost_set)
        med = cs[len(cs) // 2] if cs else 0
        p90 = cs[int(len(cs) * 0.9)] if cs else 0
        print(f'k={k} {name}: pairs {len(ps)}, settled {res["settled"]} ({100*res["settled"]/len(ps):.1f}%), '
              f'open {res["open"]}, too heavy {res["open (too heavy)"]}; agreeing seeds needed (r-e) {dict(sorted(best_r.items()))}; '
              f'lookup cost of settled: median {med}, p90 {p90}; lookAt time of settled {us_set/1e6:.2f} s of {tot_us/1e6:.2f} s')
