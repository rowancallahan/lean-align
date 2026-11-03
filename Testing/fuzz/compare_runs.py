#!/usr/bin/env python3
"""Compare two lean-align SAMs of the same reads (a base build and a branch build), pair by pair.
   python3 compare_runs.py base.sam branch.sam [label]
Classes (base -> branch). EXPECTED for the report-floor change: a placeholder (a mapped mate whose CIGAR has no aligned base) or a
real pair with AS1+AS2 < -50 becomes unmapped. NEW: an unmapped (or placeholder, or < -50) pair becomes a real pair >= -50 (the exact
search at 16). Everything else that differs is SUSPICIOUS and listed with examples. Also prints, per build, mapped / unmapped /
unique counts and the number of mapped pairs with AS1+AS2 < -50 (must be 0 on the branch)."""
import re, sys, collections
base_p, br_p = sys.argv[1:3]
label = sys.argv[3] if len(sys.argv) > 3 else ''
def load(p):
    pairs, cur = [], []
    for l in open(p):
        if l[0] == '@': continue
        cur.append(l.rstrip('\n').split('\t'))
        if len(cur) == 2: pairs.append(tuple(cur)); cur = []
    assert not cur
    return pairs
A, B = load(base_p), load(br_p)
assert len(A) == len(B) and all(a[0][0] == b[0][0] for a, b in zip(A, B)), 'different reads'
def state(p):   # (kind, pair score or None)
    m = [not int(r[1]) & 4 for r in p]
    if not any(m): return ('trimmed-away' if 'trimmedAway' in p[0][-1] else 'unmapped'), None
    if not all(m): return 'half', None
    sc = sum(int(next(t[5:] for t in r[11:] if t[:2] == 'AS')) for r in p)
    if any(not re.search(r'\d+[M=X]', r[5]) for r in p): return 'placeholder', sc
    return ('mapped<-50' if sc < -50 else 'mapped'), sc
def unique(p): return any(t == 'XU:Z:unique' for r in p for t in r[11:])
def key(p): return [(r[2], r[3], r[5], r[1]) for r in p]
cls, ex = collections.Counter(), collections.defaultdict(list)
def note(c, msg):
    cls[c] += 1
    if len(ex[c]) < 4: ex[c].append(msg)
tot = {}
for nm, S in (('base', A), ('branch', B)):
    st = collections.Counter(state(p)[0] for p in S)
    tot[nm] = dict(pairs=len(S), mapped_real=st['mapped'] + st['mapped<-50'], unique=sum(unique(p) for p in S), placeholder=st['placeholder'], below_minus50=st['mapped<-50'],
                   unmapped=st['unmapped'] + st['trimmed-away'], half=st['half'])
for a, b in zip(A, B):
    if a == b: cls['unchanged'] += 1; continue
    (ka, sa), (kb, sb) = state(a), state(b)
    name = a[0][0]; info = f'{name} base {ka} {sa} -> branch {kb} {sb}'
    if ka in ('placeholder', 'mapped<-50') and kb == 'unmapped': note('EXPECTED: ' + ka + ' -> unmapped', info)
    elif ka in ('unmapped', 'placeholder', 'mapped<-50') and kb == 'mapped': note('NEW: ' + ka + ' -> real pair >= -50', info + ' ' + ' / '.join(f'{r[2]}:{r[3]} {r[5]}' for r in b))
    elif ka == 'unmapped' and kb == 'unmapped': note('info: unmapped -> unmapped, tags differ (bound/tier)', info)
    elif ka == 'mapped' and kb == 'mapped':
        if key(a) != key(b): note('SUSPICIOUS: real pair -> different placement/CIGAR', info + f' {key(a)} -> {key(b)}')
        elif unique(a) != unique(b): note(f'SUSPICIOUS: label {"unique -> not unique" if unique(a) else "not unique -> unique"}', info)
        else: note('SUSPICIOUS: real pair -> same placement, tags differ', info + f' {a[0][11:]} -> {b[0][11:]}')
    elif ka == 'mapped' and kb == 'unmapped': note('SUSPICIOUS: real pair >= -50 -> unmapped', info)
    else: note(f'SUSPICIOUS: {ka} -> {kb}', info)
print(f'== {label}: {len(A)} pairs')
print('  ' + 'build   pairs mapped(real incl <-50) unique placeholder(no M) mapped<-50 unmapped half')
for nm, t in tot.items(): print(f"  {nm:7s} {t['pairs']} {t['mapped_real']} {t['unique']} {t['placeholder']} {t['below_minus50']} {t['unmapped']} {t['half']}")
for c, n in sorted(cls.items(), key=lambda x: (x[0].startswith('SUSPICIOUS'), x[0])): print(f'  {n:8d}  {c}' + (f'   e.g. {ex[c][0]}' if ex[c] else ''))
for c in ex:
    if c.startswith('SUSPICIOUS') or c.startswith('NEW'):
        for e in ex[c][1:]: print(f'            {c}: {e}')
bad = sum(n for c, n in cls.items() if c.startswith('SUSPICIOUS')) + tot['branch']['below_minus50'] + tot['branch']['placeholder']
print(f"  branch pairs with a placeholder or AS1+AS2 < -50: {tot['branch']['placeholder'] + tot['branch']['below_minus50']} (must be 0); suspicious changes: {sum(n for c, n in cls.items() if c.startswith('SUSPICIOUS'))}")
sys.exit(1 if bad else 0)
