#!/usr/bin/env python3
"""Inputs over 16 MB around the 8 MB flush: python3 -I fuzz_big.py WORK(with g/all.fa, idx_new) REF_BIN BIN [BIN ...]
Builds a ~20 MB pair of FASTQ files (many fuzz_reads sets, names prefixed to stay unique, the last record cut at no
particular place: files stay valid), maps with REF_BIN and every BIN, outputs must be byte-identical (XT tags kept)."""
import os, subprocess, sys
work = os.path.abspath(sys.argv[1]); ref = os.path.abspath(sys.argv[2]); bins = [os.path.abspath(x) for x in sys.argv[3:]]
idx = f'{work}/idx_new'; f1, f2 = f'{work}/big1.fq', f'{work}/big2.fq'
if not (os.path.exists(f1) and os.path.getsize(f1) > 20e6):
    with open(f1, 'wb') as o1, open(f2, 'wb') as o2:
        s = 100
        while os.path.getsize(f1) < 20e6 or os.path.getsize(f2) < 20e6:
            o1.flush(); o2.flush(); s += 1
            subprocess.run(['python3', '-I', 'Testing/scripts/fuzz_reads.py', f'{work}/g/all.fa', f'{work}/bg', '150', str(s)], check=True, capture_output=True)
            for o, r in [(o1, 1), (o2, 2)]:
                L = open(f'{work}/bg_R{r}.fq', 'rb').read().split(b'\n')[:-1]
                for i in range(0, len(L), 4): L[i] = b'@s%d_' % s + L[i][1:]
                o.write(b'\n'.join(L) + b'\n')
print('input sizes', os.path.getsize(f1), os.path.getsize(f2), 'bytes')
mapit = lambda b, out: (subprocess.run([b, 'map', idx, f1, f2, out, '100', '1000'], check=True), open(out, 'rb').read())[1]
want = mapit(ref, f'{work}/big_ref.sam'); bad = 0
for b in bins:
    got = mapit(b, f'{work}/big_o.sam'); ok = got == want; bad += not ok
    print(('ok   ' if ok else 'FAIL ') + f'big: {os.path.basename(b)} == ref ({len(want)} SAM bytes)', flush=True)
    if not ok: os.replace(f'{work}/big_o.sam', f'{work}/FAIL_big_{os.path.basename(b)}.sam')
sys.exit(1 if bad else 0)
