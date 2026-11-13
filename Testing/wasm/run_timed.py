#!/usr/bin/env python3
"""run_timed.py CMD...  runs CMD, asserts exit 0, prints wall seconds, CPU seconds and peak RSS (MB) of CMD."""
import os, subprocess, sys, time
t = time.time()
p = subprocess.Popen(sys.argv[1:])
_, status, ru = os.wait4(p.pid, 0)
assert status == 0, status
print(f"wall_s={time.time() - t:.2f} cpu_s={ru.ru_utime + ru.ru_stime:.2f} peak_MB={ru.ru_maxrss / 1024:.0f}", file=sys.stderr)
