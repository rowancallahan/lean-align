#!/usr/bin/env python3
"""Facts about a FASTA / FASTQ pair for the spec audit (findings 5, 6, 10): header spaces/tabs, letter histogram, case, N runs,
and reads containing N or non-ACGT.   python3 input_audit.py genome.fa [R1.fq R2.fq]"""
import sys, collections, re
def fasta(path):
    hist = collections.Counter(); names = []
    for line in open(path, 'rb'):
        line = line.rstrip(b'\r\n')
        if line.startswith(b'>'):
            names.append(line[1:].decode()); continue
        hist.update(line)
    return names, hist
def nruns(path):
    runs = []; cur = 0
    for line in open(path, 'rb'):
        line = line.rstrip(b'\r\n')
        if line.startswith(b'>'):
            if cur: runs.append(cur); cur = 0
            continue
        for ch in line:
            if ch in b'Nn': cur += 1
            elif cur: runs.append(cur); cur = 0
    if cur: runs.append(cur)
    return runs
g = sys.argv[1]
names, hist = fasta(g)
tot = sum(hist.values())
print(f'{g}: {len(names)} sequences, {tot} letters')
print('  headers with space/tab:', sum(1 for n in names if re.search(r'[ \t]', n)), '; first 3:', names[:3])
print('  letters:', {chr(k): v for k, v in sorted(hist.items())})
low = sum(v for k, v in hist.items() if 97 <= k <= 122)
print(f'  lowercase: {low} ({100*low/tot:.1f} %)')
odd = {chr(k): v for k, v in hist.items() if chr(k) not in 'ACGTNacgtn'}
print('  not ACGTN (either case):', odd)
r = nruns(g)
print(f'  N runs: {len(r)}, total N {sum(r)}, longest {max(r) if r else 0}, runs >= 100: {sum(1 for x in r if x >= 100)}')
for fq in sys.argv[2:]:
    n = withN = allN = nonacgt = lower = 0
    for i, line in enumerate(open(fq, 'rb')):
        if i % 4 != 1: continue
        s = line.rstrip(b'\r\n'); n += 1
        c = s.count(b'N') + s.count(b'n')
        withN += c > 0; allN += c == len(s)
        nonacgt += bool(s.translate(None, b'ACGTN'))
        lower += s != s.upper()
    print(f'{fq}: {n} reads; with N {withN}; all N {allN}; letters outside ACGTN {nonacgt}; with lowercase {lower}')
