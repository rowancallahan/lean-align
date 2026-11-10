# gz probe
`v.sh` runs one mapping on two gz files the way S-T's sinkrun.sh does (zcat into FIFOs, OUT.tmp a FIFO drained by
`cat > /dev/null`, `taskset -c 0-3 python3 timed_load.py`), and `samp.py` samples per thread CPU, run-queue wait
(schedstat), context switches, the same for gzip/cat, and the box's idle fraction.

    T=<this dir> I=<index> R=<repo with Testing/scripts/timed_load.py> \
      ./v.sh LABEL BIN R1.gz R2.gz ZPIN(0|1) SINK(cat|md5) WRAP(tl|none)

A BIN whose path contains `festive` or `fb2` writes OUT itself (no OUT.tmp).
