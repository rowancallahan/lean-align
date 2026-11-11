#!/usr/bin/env python3
"""Time one aligner run.   bench.py ours|minibwa THREADS WORKDIR SET [OUT.sam]
SET = reads | cmp (files WORKDIR/SET_R1.fq.gz, SET_R2.fq.gz). Without OUT.sam the output is thrown away.

What is measured, the same way for both tools:
  - Everything is pinned to cores 0..THREADS-1 (Linux): the aligner and the two `gzip -dc` that feed it.
  - wall    = from start to exit of the aligner. Index load is included.
  - output  = without OUT.sam, written to a pipe drained by `cat` for both tools (cat's CPU is not counted).
  - cpu     = user + system time of the aligner plus both gzips (from the kernel, via wait4).
  - peak    = largest resident memory of the aligner (from the kernel, via wait4).
  - Gbp     = letters in both read files (WORKDIR/SET.bases, counted by setup.sh).
  - Gbp/hr  = Gbp / wall hours.     Gbp/core-hr = Gbp / cpu hours.
Prints one tab-separated row: tool threads set wall_s cpu_s peak_GB Gbp Gbp/hr Gbp/core-hr"""
import os, subprocess, sys, time
tool, threads, W, name = sys.argv[1], int(sys.argv[2]), os.path.abspath(sys.argv[3]), sys.argv[4]
sam = sys.argv[5] if len(sys.argv) > 5 else None
linux = sys.platform == "linux"
if linux: os.sched_setaffinity(0, range(threads))                      # inherited by every child
index = [W + "/ours.idx"] if tool == "ours" else [W + "/" + f for f in os.listdir(W) if f.startswith("mb.")]
for f in index: subprocess.run(["cat", f], stdout=subprocess.DEVNULL, check=True)   # index in the page cache

start = time.perf_counter()
gz = [subprocess.Popen(["gzip", "-dc", f"{W}/{name}_R{r}.fq.gz"], stdout=subprocess.PIPE) for r in (1, 2)]
fds = [g.stdout.fileno() for g in gz]
r1, r2 = (f"/dev/fd/{fd}" for fd in fds)
# Without OUT.sam the output goes through a pipe drained by `cat` (pinned like everything else), the same for both tools.
# Our tool writes OUT.tmp and renames it to OUT, so for it the pipe is OUT.tmp; minibwa writes to stdout.
sink, out = None, sam
if not sam:
    out = W + "/discard.sam"
    if tool == "ours":
        if os.path.exists(out + ".tmp"): os.remove(out + ".tmp")
        os.mkfifo(out + ".tmp")
        sink = subprocess.Popen(["cat", out + ".tmp"], stdout=subprocess.DEVNULL)
    else:
        sink = subprocess.Popen(["cat"], stdin=subprocess.PIPE, stdout=subprocess.DEVNULL)
if tool == "ours":
    env = dict(os.environ, LEAN_NUM_THREADS=str(threads))
    run = subprocess.Popen(["./.lake/build/bin/lean-align", "map", index[0], r1, r2, out, "100", "1000"], pass_fds=fds, env=env)
else:
    run = subprocess.Popen([W + "/minibwa/minibwa", "map", "-t", str(threads), W + "/mb", r1, r2], pass_fds=fds,
                           stdout=sink.stdin if sink else open(sam, "w"), stderr=open(W + "/minibwa.log", "w"))
    if sink: sink.stdin.close()                                          # the child holds the only write end now
try:
    _, status, use = os.wait4(run.pid, 0)
    wall = time.perf_counter() - start
    assert status == 0, f"{tool} failed with status {status}" + (f" (see {W}/minibwa.log)" if tool == "minibwa" else "")
    cpu = use.ru_utime + use.ru_stime
    for g in gz:
        _, status, u = os.wait4(g.pid, 0)
        assert status == 0, f"gzip failed with status {status}"
        cpu += u.ru_utime + u.ru_stime
    if sink: assert sink.wait() == 0, "output sink failed"
finally:                                                                   # also on failure: no stray gzip / cat / FIFO
    for p in gz + ([sink] if sink else []):
        if p.poll() is None: p.kill()
    if tool == "ours" and not sam and os.path.exists(out + ".tmp"): os.remove(out + ".tmp")
    if tool == "ours" and not sam and os.path.exists(out): os.remove(out)

gbp = int(open(f"{W}/{name}.bases").read()) / 1e9
peak = use.ru_maxrss / (1e6 if linux else 1e9)                           # Linux reports kB, macOS bytes
print(tool, threads, name, f"{wall:.1f}", f"{cpu:.1f}", f"{peak:.2f}", f"{gbp:.3f}",
      f"{gbp / (wall / 3600):.2f}", f"{gbp / (cpu / 3600):.2f}", sep="\t")
