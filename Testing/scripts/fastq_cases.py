#!/usr/bin/env python3
"""FASTQ edge cases for `lean-align map`: Spec/Fastq.lean's Record.valid decides each one.
   fastq_cases.py LEAN_ALIGN INDEX R1.fq R2.fq TMPDIR      (R1/R2: valid pairs; the first 20 records are used)
Each case is a pair of files and the exit code it must give (0: mapped, 1: rejected). Exit 1 if any case differs."""
import os, subprocess, sys
lean, idx, f1, f2, d = sys.argv[1:6]
def recs(p): L = open(p, 'rb').read().split(b'\n'); return [L[i:i + 4] for i in range(0, 80, 4)]
A, B = recs(f1), recs(f2)
def j(rs, eol=b'\n'): return b''.join(eol.join(r) + eol for r in rs)
def mod(i, k, v, both=False):
    a = [list(r) for r in A]; b = [list(r) for r in B]
    a[i][k] = v(a[i]) if callable(v) else v
    if both: b[i][k] = v(b[i]) if callable(v) else v
    return j(a), j(b)
long = lambda r: (r[1] * 20)[:1001]
C = {
    'valid': (j(A), j(B), 0),
    'empty files': (b'', b'', 0),
    'CRLF line ends': (j(A, b'\r\n'), j(B, b'\r\n'), 1),
    'no final newline': (j(A)[:-1], j(B)[:-1], 1),
    'last record cut': (j(A)[:-30], j(B), 1),
    'empty line between records': (j(A[:5]) + b'\n' + j(A[5:]), j(B[:5]) + b'\n' + j(B[5:]), 1),
    'name of 9 bytes': (*mod(3, 0, b'@abcdefgh', True), 1),
    'name of 10 bytes': (*mod(3, 0, b'@abcdefghi', True), 0),
    "'+' line with the same name": (*mod(4, 2, lambda r: b'+' + r[0][1:]), 0),
    "'+' line with another name": (*mod(4, 2, b'+otherread'), 1),
    'lowercase letter': (*mod(5, 1, lambda r: r[1][:10].lower() + r[1][10:]), 1),
    'quality shorter than letters': (*mod(6, 3, lambda r: r[3][:-1]), 1),
    'quality byte space': (*mod(7, 3, lambda r: b' ' + r[3][1:]), 1),
    'non-ASCII name byte': (*mod(8, 0, lambda r: r[0] + b'\xc3\xa9'), 1),
    'tab in the comment': (*mod(8, 0, lambda r: r[0] + b' x\ty', True), 0),
    'tab in the QNAME': (*mod(8, 0, lambda r: r[0].split(b' ')[0] + b'\tq', True), 1),
    'mates out of step': (*mod(9, 0, b'@otherread1'), 1),
    'R1 has one more read': (j(A), j(B[:-1]), 1),
}
a = [list(r) for r in A]; b = [list(r) for r in B]
a[2][1] = (a[2][1] * 20)[:1001]; a[2][3] = (a[2][3] * 20)[:1001]
C['read of 1001 bases'] = (j(a), j(b), 1)
a = [list(r) for r in A]; a[2][1] = (a[2][1] * 20)[:1000]; a[2][3] = (a[2][3] * 20)[:1000]
C['read of 1000 bases'] = (j(a), j(B), 0)
bad = 0
for name, (r1, r2, want) in C.items():
    p1, p2 = f'{d}/c1.fq', f'{d}/c2.fq'
    open(p1, 'wb').write(r1); open(p2, 'wb').write(r2)
    got = subprocess.run([lean, 'map', idx, p1, p2, f'{d}/c.sam', '100', '1000'], capture_output=True).returncode
    ok = got == want; bad += not ok
    print(f"{'ok  ' if ok else 'FAIL'} {name}: exit {got} (want {want})")
print(f"FASTQ cases: {len(C) - bad}/{len(C)} as the spec says")
sys.exit(1 if bad else 0)
