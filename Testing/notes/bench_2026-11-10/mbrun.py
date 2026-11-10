#!/usr/bin/env python3
"""python3 mbrun.py LABEL T MINIBWA MBINDEX R1 R2 : prints TIME line like timed_load.py (load from minibwa's log)"""
import re, resource, subprocess, sys, time, tempfile
lab, T, mb, idx, r1, r2 = sys.argv[1:7]
err = tempfile.NamedTemporaryFile('w+')
t0 = time.monotonic()
p = subprocess.run(['taskset', '-c', f'0-{int(T)-1}', mb, 'map', '-t', T, idx, r1, r2], stdout=subprocess.DEVNULL, stderr=err)
wall = time.monotonic() - t0
assert p.returncode == 0
err.seek(0); m = re.search(r'::([0-9.]+)\*([0-9.]+)\].*index loaded', err.read()); assert m
load, ratio = float(m[1]), float(m[2])
r = resource.getrusage(resource.RUSAGE_CHILDREN)
print(f"TIME {lab}: wall {wall:.1f} s, cpu {r.ru_utime + r.ru_stime:.1f} s, user {r.ru_utime:.1f} s, sys {r.ru_stime:.1f} s, load {load:.2f} s, loadcpu {load*ratio:.2f} s, peak {r.ru_maxrss / 1e6:.2f} GB, exit 0", flush=True)
