#!/usr/bin/env python3
"""Pair shares for a lean-align SAM: mapped (both mates, not degenerate), degenerate last-resort pairs (all-I CIGARs),
XU:Z:unique, and, among mapped pairs, pair score (AS mate 1 + AS mate 2) below -50 and below -100.
   python3 -I pair_score_stats.py OUT.sam"""
import re, sys
n = mapped = degen = uniq = b50 = b100 = 0
cur = []
for l in open(sys.argv[1]):
    if l[0] == '@': continue
    r = l.rstrip('\n').split('\t'); f = int(r[1])
    if f & 0x900: continue
    cur.append((f, r[5], {t[:2]: t[5:] for t in r[11:]}))
    if len(cur) < 2: continue
    n += 1
    if all(not a[0] & 4 for a in cur):
        if all(re.fullmatch(r'\d+I', a[1]) for a in cur): degen += 1
        else:
            mapped += 1
            s = sum(int(a[2]['AS']) for a in cur)
            b50 += s < -50; b100 += s < -100
    uniq += any(a[2].get('XU') == 'unique' for a in cur)
    cur = []
assert not cur
p = lambda x, d: f"{100 * x / d:.3f}%"
print(f"pairs {n} mapped {mapped} ({p(mapped, n)}) degenerate {degen} ({p(degen, n)}) unique {uniq} ({p(uniq, n)}) "
      f"mapped<-50 {b50} ({p(b50, mapped)}) mapped<-100 {b100} ({p(b100, mapped)})")
