#!/usr/bin/env python3
"""python3 -I cg_cost.py ANNOTATE_TEXT [TOP=25]   Parse `callgrind_annotate --threshold=100 --show=Ir,D1mr,D1mw,DLmr,DLmw` output and rank functions by
estimated cost = 10 * (D1 read+write misses) + 100 * (LL read+write misses), in cycles (usual rule of thumb; no overlap, no prefetch)."""
import re, sys
top = int(sys.argv[2]) if len(sys.argv) > 2 else 25
rows = []; tot = None
for l in open(sys.argv[1]):
    m = re.match(r'\s*([\d,]+) \(\s*[\d.]+%\)\s+([\d,.]+)(?: \(\s*[\d.]+%\))?\s+([\d,.]+)(?: \(\s*[\d.]+%\))?\s+([\d,.]+)(?: \(\s*[\d.]+%\))?\s+([\d,.]+)(?: \(\s*[\d.]+%\))?\s+(.*)', l)
    if not m: continue
    v = [0 if x == '.' else int(x.replace(',', '')) for x in m.groups()[:5]]; name = m.group(6)
    if 'PROGRAM TOTALS' in name: tot = v; continue
    rows.append((10 * (v[1] + v[2]) + 100 * (v[3] + v[4]), v, name.split(' [')[0].replace('???:', '').replace('lp_lean__align_', '')))
rows.sort(key=lambda r: -r[0])
est = 10 * (tot[1] + tot[2]) + 100 * (tot[3] + tot[4])
print(f'TOTAL Ir {tot[0]:,}  D1 miss rd {tot[1]:,} wr {tot[2]:,}  LL miss rd {tot[3]:,} wr {tot[4]:,}  est miss cycles {est:,} = {100 * est / tot[0]:.1f} % of Ir')
print(f'{"est cycles":>14} {"%miss":>6} {"Ir":>15} {"D1mr":>11} {"D1mw":>10} {"LLmr":>10} {"LLmw":>10}  function')
for c, v, n in rows[:top]:
    print(f'{c:14,} {100 * c / est:6.1f} {v[0]:15,} {v[1]:11,} {v[2]:10,} {v[3]:10,} {v[4]:10,}  {n[:90]}')
