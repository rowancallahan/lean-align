#!/usr/bin/env python3
"""Run a command; print its wall time, CPU time and peak memory.   python3 timed.py LABEL CMD ARGS..."""
import resource, subprocess, sys, time
t = time.monotonic()
rc = subprocess.run(sys.argv[2:]).returncode
wall = time.monotonic() - t
r = resource.getrusage(resource.RUSAGE_CHILDREN)
print(f"TIME {sys.argv[1]}: wall {wall:.1f} s, cpu {r.ru_utime + r.ru_stime:.1f} s, peak {r.ru_maxrss / 1e6:.2f} GB, exit {rc}", flush=True)
sys.exit(rc)
