"""writetrim.py DIR SET: SET_R{1,2}.fq -> tr_SET_R{1,2}.fq with the modelled trim; pairs with a mate trimmed away dropped."""
import sys
sys.argv = sys.argv[:3]
exec(open(sys.argv[0].replace('writetrim', 'trimsim')).read().split('ours = {}')[0])
D, P = sys.argv[1], sys.argv[2]
def t(s, q):
    i, L, mm = cut(s); s, q = s[:i], q[:i]
    if not s: return None
    ws, we = win(s, q)
    return None if we - ws < 25 else (s[ws:we], q[ws:we])
r1, r2 = list(fq(f'{D}/{P}_R1.fq')), list(fq(f'{D}/{P}_R2.fq')); drop = 0
with open(f'{D}/tr_{P}_R1.fq', 'w') as o1, open(f'{D}/tr_{P}_R2.fq', 'w') as o2:
    for (n, s, q), (n2, s2, q2) in zip(r1, r2):
        assert n == n2
        a, b = t(s, q), t(s2, q2)
        if a is None or b is None: drop += 1; continue
        o1.write(f'@{n}\n{a[0]}\n+\n{a[1]}\n'); o2.write(f'@{n}\n{b[0]}\n+\n{b[1]}\n')
print(P, 'pairs', len(r1), 'dropped', drop)
