#!/usr/bin/env python3
"""Time one aligner run.   time_one.py ours|minibwa THREADS WORKDIR SET [OUT.sam]
SET = reads | sample (files WORKDIR/SET_R1.fq.gz, SET_R2.fq.gz). Without OUT.sam the output is thrown away.

What is measured, the same way for both tools:
  - On Linux everything is pinned to cores 0..THREADS-1: the aligner and the two `gzip -dc` that feed it.
    (Cores here are what Linux lists as CPUs, i.e. hyperthreads on most servers. Not pinned on macOS.)
  - Before the start the index files are read once, so the index comes from the page cache, not from the disk.
  - wall    = from start to exit of the aligner. Index load into memory is included.
  - output  = without OUT.sam, written to a pipe drained by `cat` for both tools (cat's CPU is not counted).
  - cpu     = user + system time of the aligner plus both gzips (from the kernel, via wait4).
  - peak    = largest resident memory of the aligner (from the kernel, via wait4).
  - Gbp     = letters in both read files (WORKDIR/SET.bases, counted by bench.sh).
  - Gbp/hr  = Gbp / wall hours.     Gbp/core-hr = Gbp / cpu hours.
Prints one tab-separated row: tool threads set wall_s cpu_s peak_GB Gbp Gbp/hr Gbp/core-hr"""
import os
import subprocess
import sys
import time

assert len(sys.argv) in (5, 6), __doc__
tool = sys.argv[1]
threads = int(sys.argv[2])
workdir = os.path.abspath(sys.argv[3])
name = sys.argv[4]
if len(sys.argv) == 6:
    sam = sys.argv[5]
else:
    sam = None
assert tool in ("ours", "minibwa"), __doc__

on_linux = sys.platform == "linux"
if on_linux:
    os.sched_setaffinity(0, range(threads))      # every process started below inherits this

# our binary: two folders above this script's folder is the repository
ours_binary = os.path.abspath(os.path.dirname(__file__) + "/../../.lake/build/bin/lean-align")
minibwa_binary = workdir + "/minibwa/minibwa"

if tool == "ours":
    index_files = [workdir + "/ours.idx"]
else:
    index_files = []
    for f in sorted(os.listdir(workdir)):
        if f.startswith("mb."):                  # mb.mbw, mb.l2b: minibwa's index files
            index_files.append(workdir + "/" + f)
assert index_files != []
for f in index_files:
    subprocess.run(["cat", f], stdout=subprocess.DEVNULL, check=True)

start = time.perf_counter()

# the two decompressors; the aligner reads their pipes as files named /dev/fd/N
gz1 = subprocess.Popen(["gzip", "-dc", workdir + "/" + name + "_R1.fq.gz"], stdout=subprocess.PIPE)
gz2 = subprocess.Popen(["gzip", "-dc", workdir + "/" + name + "_R2.fq.gz"], stdout=subprocess.PIPE)
gz = [gz1, gz2]
fd1 = gz1.stdout.fileno()
fd2 = gz2.stdout.fileno()
reads1 = "/dev/fd/" + str(fd1)
reads2 = "/dev/fd/" + str(fd2)

# Without OUT.sam the output goes through a pipe drained by `cat` (pinned like everything else), for both tools.
# Our tool writes OUT.tmp and renames it to OUT when it is done, so for it the pipe is the file OUT.tmp (a FIFO).
# minibwa writes to its standard output, so for it the pipe is the standard input of `cat`.
sink = None
if sam is None:
    discard = workdir + "/discard.sam"
    if tool == "ours":
        if os.path.exists(discard + ".tmp"):
            os.remove(discard + ".tmp")
        os.mkfifo(discard + ".tmp")
        sink = subprocess.Popen(["cat", discard + ".tmp"], stdout=subprocess.DEVNULL)
    else:
        sink = subprocess.Popen(["cat"], stdin=subprocess.PIPE, stdout=subprocess.DEVNULL)

if tool == "ours":
    if sam is None:
        out = discard
    else:
        out = sam
    env = dict(os.environ, LEAN_NUM_THREADS=str(threads))
    # arguments: index, mate 1, mate 2, output, smallest fragment length, largest fragment length
    run = subprocess.Popen([ours_binary, "map", index_files[0], reads1, reads2, out, "100", "1000"],
                           pass_fds=[fd1, fd2], env=env)
else:
    if sam is None:
        minibwa_stdout = sink.stdin
    else:
        minibwa_stdout = open(sam, "w")
    minibwa_log = open(workdir + "/minibwa.log", "w")
    run = subprocess.Popen([minibwa_binary, "map", "-t", str(threads), workdir + "/mb", reads1, reads2],
                           pass_fds=[fd1, fd2], stdout=minibwa_stdout, stderr=minibwa_log)
    if sink is not None:
        sink.stdin.close()                       # the aligner holds the only write end now, so cat sees the end of the output

try:
    _, status, use = os.wait4(run.pid, 0)
    wall = time.perf_counter() - start
    assert status == 0, tool + " failed with status " + str(status) + " (minibwa's messages: " + workdir + "/minibwa.log)"
    cpu = use.ru_utime + use.ru_stime
    for g in gz:
        _, gz_status, gz_use = os.wait4(g.pid, 0)
        assert gz_status == 0, "gzip failed with status " + str(gz_status)
        cpu += gz_use.ru_utime + gz_use.ru_stime
    if sink is not None:
        assert sink.wait() == 0, "output sink failed"
finally:
    # also after a failure: no gzip or cat left running, no FIFO left behind
    # (a process that wait4 already collected counts as finished for poll())
    for p in gz + ([sink] if sink is not None else []):
        if p.poll() is None:
            p.kill()
    if tool == "ours" and sam is None:
        if os.path.exists(discard + ".tmp"):
            os.remove(discard + ".tmp")
        if os.path.exists(discard):
            os.remove(discard)

bases = int(open(workdir + "/" + name + ".bases").read())
gbp = bases / 1e9
if on_linux:
    peak_gb = use.ru_maxrss / 1e6                # Linux reports kilobytes
else:
    peak_gb = use.ru_maxrss / 1e9                # macOS reports bytes
gbp_per_hour = gbp / (wall / 3600)
gbp_per_core_hour = gbp / (cpu / 3600)
print(tool, threads, name, round(wall, 1), round(cpu, 1), round(peak_gb, 2), round(gbp, 3),
      round(gbp_per_hour, 2), round(gbp_per_core_hour, 2), sep="\t")
