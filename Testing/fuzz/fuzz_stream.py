#!/usr/bin/env python3
"""Fuzz the streaming lean-align against the reference build.
   python3 -I fuzz_stream.py WORK REF_BIN NEW_DEFAULT_BIN [CHUNKBIN ...] [--pairs N] [--rounds N]
REF_BIN: the old build (festive); NEW_DEFAULT_BIN: the build under test; CHUNKBINs: builds with other chunkSize
(build_chunks.sh). XT:Z:<tier> tags are removed from every SAM before comparing. Any mismatch aborts with the files kept."""
import os, random, re, subprocess, sys
S = 'Testing/scripts'
a, opt, it = [], {}, iter(sys.argv[1:])
for x in it:
    if x.startswith('--'): opt[x] = next(it)
    else: a.append(x)
work, ref, new, chunk_bins = os.path.abspath(a[0]), os.path.abspath(a[1]), os.path.abspath(a[2]), [os.path.abspath(x) for x in a[3:]]
os.makedirs(work, exist_ok=True)
run = lambda *c: subprocess.run(c, capture_output=True)
strip = lambda b: re.sub(rb'\tXT:Z:\S+', b'', b)
npass = nfail = 0
def check(ok, what, info=''):
    global npass, nfail
    npass += ok; nfail += not ok
    print(('ok   ' if ok else 'FAIL ') + what + ('' if ok else f'  {info}'), flush=True)
def mapit(bin, idx, f1, f2, out):
    if os.path.exists(out): os.remove(out)
    r = run(bin, 'map', idx, f1, f2, out, '100', '1000')
    return r.returncode, (open(out, 'rb').read() if os.path.exists(out) else None), os.path.exists(out + '.tmp'), r.stderr
# genome + index (both builds read the same index format; build with each)
g = f'{work}/g'
if not os.path.exists(f'{g}/all.fa'): run('python3', '-I', f'{S}/sim_genome_dup.py', g, '2', '2', '7').check_returncode()
idx = {}
for name, b in [('ref', ref), ('new', new)]:
    idx[name] = f'{work}/idx_{name}'; assert run(b, 'build', f'{g}/all.fa', idx[name]).returncode == 0
assert open(idx['ref'], 'rb').read() == open(idx['new'], 'rb').read(), 'index files differ'
def reads(prefix, per, seed):
    run('python3', '-I', f'{S}/fuzz_reads.py', f'{g}/all.fa', prefix, str(per), str(seed)).check_returncode()
    return open(prefix + '_R1.fq', 'rb').read(), open(prefix + '_R2.fq', 'rb').read()
# 1. chunk boundaries
r1, r2 = reads(f'{work}/small', int(opt.get('--pairs', 3)), 1)
f1, f2 = f'{work}/s1.fq', f'{work}/s2.fq'; open(f1, 'wb').write(r1); open(f2, 'wb').write(r2)
print(f'chunk test: {r1.count(b"@") and len(r1.split(bytes([10])))//4} records, {len(r1)} bytes')
rc, want, _, _ = mapit(ref, idx['ref'], f1, f2, f'{work}/ref.sam'); assert rc == 0
for b in [new] + chunk_bins:
    rc, got, tmp, err = mapit(b, idx['new'], f1, f2, f'{work}/o.sam')
    check(rc == 0 and got is not None and not tmp and strip(got) == strip(want), f'chunks: {os.path.basename(b)} == ref', (rc, err[:200]))
    if b != new and rc == 0:
        _, base, _, _ = mapit(new, idx['new'], f1, f2, f'{work}/n.sam')
        check(got == base, f'chunks: {os.path.basename(b)} byte-identical to default build')
# 2. validity: one case per rule
recs = lambda d: [d.split(b'\n')[i:i + 4] for i in range(0, len(d.split(b'\n')) - 1, 4)]
R1, R2 = recs(r1), recs(r2)
keep = [i for i in range(len(R1)) if len(R1[i][1]) >= 12 and len(R2[i][1]) >= 12][:40]
A, B = [R1[i] for i in keep], [R2[i] for i in keep]
assert len(A) == 40
j = lambda rs, eol=b'\n': b''.join(eol.join(r) + eol for r in rs)
def mod(i, k, v, both=False):
    a_ = [list(r) for r in A]; b_ = [list(r) for r in B]
    for x in ([a_, b_] if both else [a_]): x[i][k] = v(x[i]) if callable(v) else v
    return j(a_), j(b_)
def seqq(i, s, q=None):
    a_ = [list(r) for r in A]; a_[i][1] = s; a_[i][3] = q if q is not None else b'I' * len(s); return j(a_), j(B)
N = lambda n, q=100: b'@' + b'n' * (q - 1) + b' ' + b'c' * (n - q - 1) if n > q else b'@' + b'n' * (n - 1)   # name of n bytes with '@', QNAME of q bytes
C = [  # (name, file1, file2, want exit)
 ('valid', j(A), j(B), 0), ('empty files', b'', b'', 0),
 ('bad @', *mod(3, 0, lambda r: b'>' + r[0][1:], True), 1),
 ('name 9 bytes', *mod(3, 0, N(9), True), 1), ('name 10 bytes', *mod(3, 0, N(10), True), 0),
 ('name 501 bytes', *mod(3, 0, N(501), True), 0), ('name 502 bytes', *mod(3, 0, N(502), True), 1),
 ('non-ASCII', *mod(3, 0, lambda r: r[0] + b'\xc3\xa9', True), 1),
 ('CR in name', *mod(3, 0, lambda r: r[0] + b'\r', True), 1), ('CRLF everywhere', j(A, b'\r\n'), j(B, b'\r\n'), 1),
 ("'+other'", *mod(4, 2, b'+otherread'), 1), ("'+' repeats the name", *mod(4, 2, lambda r: b'+' + r[0][1:]), 0),
 ("'+' alone", *mod(4, 2, b'+'), 0),
 ('lowercase', *mod(5, 1, lambda r: r[1][:10].lower() + r[1][10:]), 1),
 ('letter R', *mod(5, 1, lambda r: b'R' + r[1][1:]), 1), ('letter U', *mod(5, 1, lambda r: b'U' + r[1][1:]), 1),
 ('quality space', *mod(6, 3, lambda r: b' ' + r[3][1:]), 1), ('quality DEL', *mod(6, 3, lambda r: b'\x7f' + r[3][1:]), 1),
 ("quality '!' and '~'", *mod(6, 3, lambda r: b'!~' + r[3][2:]), 0),
 ('quality short', *mod(7, 3, lambda r: r[3][:-1]), 1), ('quality long', *mod(7, 3, lambda r: r[3] + b'I'), 1),
 ('1001 bases', *seqq(2, b'A' * 1001), 1), ('1000 bases', *seqq(2, b'A' * 1000), 0),
 ('empty sequence', *seqq(2, b''), 0),
 ('no final newline', j(A)[:-1], j(B), 1), ('cut record', j(A)[:-30], j(B), 1),
 ('empty line between', j(A[:5]) + b'\n' + j(A[5:]), j(B), 1), ('trailing empty line', j(A) + b'\n', j(B), 1),
 ('mate names differ', *mod(9, 0, b'@otherread1'), 1), ('one file longer', j(A), j(B[:-1]), 1),
 ('QNAME with tab', *mod(8, 0, lambda r: r[0].split(b' ')[0] + b'\tq', True), 1),
 ('QNAME with @', *mod(8, 0, lambda r: r[0].split(b' ')[0] + b'@q', True), 1),
 ('QNAME 255 bytes', *mod(8, 0, lambda r: N(256, 256), True), 1),
 ('QNAME 254 bytes', *mod(8, 0, lambda r: N(255, 255), True), 0),
 ('name /1 /2 mates', *mod(10, 0, lambda r: r[0].split(b' ')[0] + b'/1', False)[:1], mod(10, 0, lambda r: r[0].split(b' ')[0] + b'/2')[0] and j([list(r) for r in B[:10]] + [[B[10][0].split(b' ')[0] + b'/2'] + B[10][1:]] + [list(r) for r in B[11:]]), 0),
]
for b in [ref, new] + chunk_bins:
    for name, x, y, want in C:
        open(f'{work}/c1.fq', 'wb').write(x); open(f'{work}/c2.fq', 'wb').write(y)
        idxb = idx['ref'] if b == ref else idx['new']
        rc, got, tmp, err = mapit(b, idxb, f'{work}/c1.fq', f'{work}/c2.fq', f'{work}/c.sam')
        ok = rc == want and (b == ref or ((got is None) == (want == 1) and not tmp))   # the old build leaves OUT behind; only the exit code is checked there
        check(ok, f'valid[{os.path.basename(b)}]: {name}', f'exit {rc} want {want}, out exists {got is not None}, tmp exists {tmp}')
# 3. random valid pairs vs ref
for seed in range(2, 2 + int(opt.get('--rounds', 5))):
    r1, r2 = reads(f'{work}/rnd{seed}', int(opt.get('--pairs', 40)), seed)
    open(f1, 'wb').write(r1); open(f2, 'wb').write(r2)
    rc, want, _, _ = mapit(ref, idx['ref'], f1, f2, f'{work}/ref.sam'); assert rc == 0, (seed, rc)
    rc, got, _, err = mapit(new, idx['new'], f1, f2, f'{work}/o.sam')
    check(rc == 0 and strip(got) == strip(want), f'random seed {seed}: {r1.count(bytes([10]))//4} pairs == ref', (rc, err[:200]))
print(f'pass {npass} fail {nfail}'); sys.exit(1 if nfail else 0)
