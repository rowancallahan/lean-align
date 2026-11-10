"""trimsim.py DIR SET: model the adapter cut + quality window on SET_R{1,2}.fq; compare with ours_SET.sam lengths."""
import sys, collections
D, P = sys.argv[1], sys.argv[2]; A = 'AGATCGGAAGAGC'
def cut(r):
    n = len(r)
    for i in range(n):
        L = min(13, n - i)
        if L < 6: break
        mm = sum(r[i + j] != A[j] for j in range(L))
        if mm <= (1 if L == 13 else 0): return i, L, mm
    return n, 0, 0
def win(seq, q):  # best window of (q-25), N = -1e6; returns (s,e) (ties: not modelled)
    best, bs, be, cur, cs = None, 0, 0, 0, 0
    for i, (b, c) in enumerate(zip(seq, q)):
        v = (ord(c) - 33 - 25) if b in 'ACGT' else -10**6
        if cur <= 0: cur, cs = v, i
        else: cur += v
        if best is None or cur > best: best, bs, be = cur, cs, i + 1
    return bs, be
def fq(p):
    f = open(p)
    while True:
        h = f.readline()
        if not h: return
        s = f.readline().strip(); f.readline(); q = f.readline().strip()
        n = h[1:].split()[0]; yield (n[:-2] if n[-2:] in ('/1', '/2') else n), s, q
ours = {}
for l in open(f'{D}/ours_{P}.sam'):
    if l[0] == '@': continue
    x = l.split('\t'); fl = int(x[1])
    if fl & 0x900: continue
    ours[(x[0], 1 if fl & 64 else 2)] = (x[9], fl, x[4], [t for t in x[11:] if t[:2] in ('XU', 'XT')])
c = collections.Counter(); ex = collections.defaultdict(list)
for m in (1, 2):
    for name, s, q in fq(f'{D}/{P}_R{m}.fq'):
        i, L, mm = cut(s)
        s2, q2 = s[:i], q[:i]
        ws, we = win(s2, q2) if s2 else (0, 0)
        k = we - ws
        if k < 25: k = 0
        got = ours[(name, m)][0]; got = 0 if got == '*' else len(got)
        cls = 'none' if i == len(s) else ('full13' if L == 13 else f'tail{L}')
        c[(cls, 'match' if got == k else 'MODEL-MISMATCH', 'gone' if got == 0 else ('trimmed' if got < len(s) else 'kept'))] += 1
        if cls != 'none' and len(ex[cls]) < 3: ex[cls].append((name, m, i, s[i:i + L], mm, got, s[max(0, i - 5):i + 13]))
for k, v in sorted(c.items()): print(P, k, v)
for k in ex:
    for e in ex[k]: print('  ex', k, e)
if len(sys.argv) > 3:
    want = set(sys.argv[3].split(','))
    for m in (1, 2):
        for name, s, q in fq(f'{D}/{P}_R{m}.fq'):
            if name not in want: continue
            i, L, mm = cut(s); ws, we = win(s[:i], q[:i]) if i else (0, 0)
            print('DETAIL', name, m, 'len', len(s), 'cut', i, 'match', s[i:i + L], 'mm', mm, 'window', (ws, we), 'kept', we - ws if we - ws >= 25 else 0)
            print('  seq ', s); print('  qual', q)
