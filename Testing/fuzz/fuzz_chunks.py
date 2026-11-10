#!/usr/bin/env python3
"""Chunk-size stress: python3 -I fuzz_chunks.py WORK(with g/all.fa and idx_new from fuzz_stream.py) BIN_DEFAULT BIN_1 BIN_7 BIN_4096
(a) random valid sets (fuzz_reads.py seeds): every build's SAM byte-identical to the default build's;
(b) uneven files: mate 1 of 250 letters, mate 2 of 50 (and the reverse), with adapters, N and low-quality tails."""
import os, random, re, subprocess, sys
work = os.path.abspath(sys.argv[1]); bins = [os.path.abspath(x) for x in sys.argv[2:6]]
names = ['default', '1', '7', '4096']; idx = f'{work}/idx_new'
G = ''.join(l for l in open(f'{work}/g/all.fa').read().split('\n') if not l.startswith('>')).replace('N', '')
RC = str.maketrans('ACGT', 'TGCA'); rc = lambda s: s.translate(RC)[::-1]
AD = 'AGATCGGAAGAGC'
def uneven(n, l1, l2, seed):
    random.seed(seed); a, b = [], []
    for i in range(n):
        frag = random.randint(max(l1, l2) + 10, max(l1, l2) + 400); p = random.randrange(len(G) - frag); f = G[p:p + frag]
        s1, s2 = f[:l1], rc(f)[:l2]
        if random.random() < .3: s1 = s1[:random.randint(20, l1)] + AD + ''.join(random.choices('ACGT', k=l1))
        if random.random() < .3: s2 = s2[:random.randint(20, l2)] + AD + ''.join(random.choices('ACGT', k=l2))
        s1, s2 = s1[:l1], s2[:l2]
        if random.random() < .1: s1 = s1[:5] + 'N' * 3 + s1[8:]
        q = lambda s: ''.join(random.choice('IIIIII5#') for _ in s) if random.random() < .2 else 'I' * len(s)
        nm = f'@read{i:07d}_uneven comment'
        a.append(f'{nm}\n{s1}\n+\n{q(s1)}\n'); b.append(f'{nm}\n{s2}\n+\n{q(s2)}\n')
    return ''.join(a).encode(), ''.join(b).encode()
def mapit(b, f1, f2, out):
    r = subprocess.run([b, 'map', idx, f1, f2, out, '100', '1000'], capture_output=True); assert r.returncode == 0, r.stderr
    return open(out, 'rb').read()
ok = bad = 0
def case(label, r1, r2, which):
    global ok, bad
    open(f'{work}/u1.fq', 'wb').write(r1); open(f'{work}/u2.fq', 'wb').write(r2)
    base = mapit(bins[0], f'{work}/u1.fq', f'{work}/u2.fq', f'{work}/u0.sam')
    for k in which:
        got = mapit(bins[k], f'{work}/u1.fq', f'{work}/u2.fq', f'{work}/uk.sam'); same = got == base
        ok += same; bad += not same; print(('ok   ' if same else 'FAIL ') + f'{label}: chunk {names[k]} == default ({len(base)} SAM bytes)', flush=True)
        if not same: open(f'{work}/FAIL_{label}_{names[k]}.1.fq', 'wb').write(r1); open(f'{work}/FAIL_{label}_{names[k]}.2.fq', 'wb').write(r2)
for seed in range(2, 6):
    subprocess.run(['python3', '-I', 'Testing/scripts/fuzz_reads.py', f'{work}/g/all.fa', f'{work}/cr{seed}', '40', str(seed)], check=True, capture_output=True)
    case(f'random{seed}', open(f'{work}/cr{seed}_R1.fq', 'rb').read(), open(f'{work}/cr{seed}_R2.fq', 'rb').read(), [2, 3] + ([1] if seed == 2 else []))
for l1, l2 in [(250, 50), (50, 250), (1000, 25), (101, 101)]:
    case(f'uneven{l1}x{l2}', *uneven(300, l1, l2, l1), [1, 2, 3] if l1 < 1000 else [2, 3])
print(f'pass {ok} fail {bad}'); sys.exit(1 if bad else 0)
