#!/bin/bash
# cache_hp.sh BIN INDEX R1 R2 TAG OUTDIR : huge-page variants, 3 interleaved reps, 1 core and 4 cores; one TSV row per run.
# Needs root (writes /sys/kernel/mm/transparent_hugepage/enabled and /proc/sys/vm/nr_hugepages); restores madvise / 0 at the end.
BIN=$1; IDX=$2; R1=$3; R2=$4; TAG=$5; O=$6; mkdir -p $O; H=$(dirname $0)
thp() { echo $1 > /sys/kernel/mm/transparent_hugepage/enabled; }
pool() { echo $1 > /proc/sys/vm/nr_hugepages; }
run() { # variant cores envs...
  v=$1; c=$2; shift 2
  env "$@" python3 -I $H/cache_run.py $c "$TAG $v c$c" $O/x.sam $BIN map $IDX $R1 $R2 $O/x.sam 100 1000
}
cat $IDX > /dev/null
for rep in 1 2 3; do for c in 0 0-3; do
  thp madvise; pool 0;  run base $c A=1
  thp madvise; pool 0;  run mi_large $c MIMALLOC_ALLOW_LARGE_OS_PAGES=1
  thp always;  pool 0;  run thp_always $c A=1
  thp always;  pool 0;  run thp_always+mi_large $c MIMALLOC_ALLOW_LARGE_OS_PAGES=1
  thp madvise; pool 2800; run hugetlb+mi_large $c MIMALLOC_ALLOW_LARGE_OS_PAGES=1
done; done
thp madvise; pool 0
