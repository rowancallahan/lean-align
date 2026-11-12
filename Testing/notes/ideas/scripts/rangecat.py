#!/usr/bin/env python3
"""python3 -I rangecat.py URL > stdout   Write URL's bytes to stdout; after a dropped connection resume with an HTTP Range request.
Every drop is logged on stderr. Exits non-zero unless exactly Content-Length bytes were written."""
import subprocess, sys, time
url = sys.argv[1]
head = subprocess.run(['curl', '-sSIL', url], capture_output=True, text=True, check=True).stdout.lower().splitlines()
size = int([l for l in head if l.startswith('content-length:')][-1].split(':')[1])
off = 0; tries = 0; out = sys.stdout.buffer
while off < size:
    p = subprocess.Popen(['curl', '-sS', '-f', '-L', '-r', f'{off}-', url], stdout=subprocess.PIPE)
    while chunk := p.stdout.read(1 << 20):
        out.write(chunk); off += len(chunk)
    rc = p.wait()
    if off < size:
        tries += 1; print(f'rangecat: drop at {off}/{size} (curl exit {rc}), resume #{tries}', file=sys.stderr, flush=True)
        assert tries < 200; time.sleep(2)
out.flush(); assert off == size, (off, size)
print(f'rangecat: {url.rsplit("/", 1)[1]} done, {off} bytes, {tries} resumes', file=sys.stderr, flush=True)
