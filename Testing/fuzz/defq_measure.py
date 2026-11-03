#!/usr/bin/env python3
"""Counts for one SAM of the shim (one defQ build): mapped / unique / repetitive-unknown pairs, pairs below -50 / -100.
   python3 -I defq_measure.py LABEL ours.sam > one_line.txt
mapped = both mates mapped and not an all-insertion pair; unique = both mates XU:Z:unique; repetitive-unknown = no mapping and label gaveUp
(the repeat / places rule); degenerate = all-insertion pair; score shares are over mapped pairs (AS1 + AS2)."""
import re, sys
label, p = sys.argv[1:3]
OPS = re.compile(r'(\d+)([MIDNSHP=X])')
n = mapped = uniq = gave = deg = lt50 = lt100 = nomap = 0
rec = {}
for l in open(p):
    if l[0] == '@': continue
    r = l.split('\t'); f = int(r[1])
    if f & 0x900: continue
    k = r[0]
    ops = OPS.findall(r[5]) if r[5] != '*' else []
    rec.setdefault(k, []).append((not f & 4, bool(ops) and all(o == 'I' for _, o in ops), next((t[5:] for t in r[11:] if t.startswith('XU:Z:')), ''),
                                  next((int(t[5:]) for t in r[11:] if t.startswith('AS:i:')), None)))
for k, (a, b) in rec.items():
    n += 1
    if a[0] and b[0] and not a[1] and not b[1]:
        mapped += 1; s = a[3] + b[3]; lt50 += s < -50; lt100 += s < -100
        uniq += a[2].strip() == 'unique' and b[2].strip() == 'unique'
    elif a[0] and b[0]: deg += 1
    else:
        nomap += 1; gave += a[2].strip() == 'gaveUp'
print(f'{label}\tpairs {n}\tmapped {mapped}\tunique {uniq}\tdegenerate {deg}\tunmapped {nomap}\trepetitiveUnknown(gaveUp) {gave}\tscore<-50 {lt50}\tscore<-100 {lt100}')
