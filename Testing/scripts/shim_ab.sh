#!/bin/sh
# A/B timing vs minibwa:  sh Testing/scripts/shim_ab.sh OUT "label:binary ..." "set:prefix ..."
# A binary whose label starts with "mb" is minibwa (map -t THREADS INDEX_MB, SAM to a file; its stderr has the
# "index loaded" time). Per set and rep (REPEAT, default 3; order rotated each rep), for lean-align: an untimed
# empty-FASTQ run (warms the index in the page cache), then the set, timed by timed_load.py (load measured in the run:
# a separate empty run's load varies 2-9 s on a 15 GB box and does not predict the next run's).
# Prints TIME lines (timed.py) and, for minibwa, MBLOAD lines. Summary: python3 Testing/scripts/ab_med.py LOG
set -u
cd "$(dirname "$0")/../.."
O=$1; bins=$2; sets=$3; R=${REPEAT:-3}; t=${THREADS:-4}
I=${INDEX:-Testing/data/prebuilt/shim.idx}; M=${INDEX_MB:-Testing/data/prebuilt/mb}; D=${READS:-Testing/data/prebuilt}
T="python3 Testing/scripts/timed.py"; mkdir -p "$O"; : > "$O/empty.fq"
C="taskset -c 0-$((t - 1))"
for s in $sets; do n=${s%%:*}; f=${s#*:}; r=1
  while [ $r -le $R ]; do
    list=$bins; [ $((r % 2)) = 0 ] && list=$(echo $bins | tr ' ' '\n' | tac | tr '\n' ' ')
    for b in $list; do l=${b%%:*}; x=${b#*:}
      case $l in
        mb*) $C $T "$n $l r$r" sh -c "'$x' map -t $t '$M' '$D/${f}_R1.fq' '$D/${f}_R2.fq' > '$O/$n.$l.sam' 2> '$O/$n.$l.err'"
             echo "MBLOAD $n $l r$r $(grep 'index loaded' "$O/$n.$l.err" | sed 's/.*::\([0-9.]*\)\*\([0-9.]*\)\].*/\1 \2/')";;
        *) $C "$x" map "$I" "$O/empty.fq" "$O/empty.fq" "$O/e.sam" 100 1000
           $C python3 Testing/scripts/timed_load.py "$n $l r$r" "$x" map "$I" "$D/${f}_R1.fq" "$D/${f}_R2.fq" "$O/$n.$l.sam" 100 1000;;
      esac
    done; r=$((r + 1)); done; done
