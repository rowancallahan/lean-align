#!/bin/sh
# Headline timing, one tool at a time:  sh Testing/scripts/headline.sh OUT "label:binary ..." "set:prefix ..."
# Labels starting with "mb" are minibwa. Per set: all lean-align runs, then all minibwa runs (never interleaved).
# Before a tool's group the other tool's index is dropped from the page cache (posix_fadvise DONTNEED); before every
# run the tool's own index is read once (cat > /dev/null). lean-align: an empty-FASTQ run (timed) right before each
# timed run, which is timed_load.py (load measured in the run too). REPEAT (default 3) reps, rotated order.
set -u
cd "$(dirname "$0")/../.."
O=$1; bins=$2; sets=$3; R=${REPEAT:-3}; t=${THREADS:-4}
I=${INDEX:-Testing/data/prebuilt/shim.idx}; M=${INDEX_MB:-Testing/data/prebuilt/mb}; D=${READS:-Testing/data/prebuilt}
mkdir -p "$O"; : > "$O/empty.fq"; C="taskset -c 0-$((t - 1))"
drop() { python3 -c "import os,sys
for f in sys.argv[1:]:
    fd = os.open(f, os.O_RDONLY); os.posix_fadvise(fd, 0, 0, os.POSIX_FADV_DONTNEED); os.close(fd)" "$@"; }
ours=$(echo $bins | tr ' ' '\n' | grep -v '^mb' | tr '\n' ' '); mbs=$(echo $bins | tr ' ' '\n' | grep '^mb' | tr '\n' ' ')
for s in $sets; do n=${s%%:*}; f=${s#*:}
  for grp in ours mbs; do
    eval list0=\$$grp; [ -z "$list0" ] && continue
    if [ $grp = ours ]; then drop $M.*; else drop $I; fi
    r=1; while [ $r -le $R ]; do
      list=$list0; [ $((r % 2)) = 0 ] && list=$(echo $list0 | tr ' ' '\n' | tac | tr '\n' ' ')
      for b in $list; do l=${b%%:*}; x=${b#*:}
        case $l in
          mb*) cat $M.* > /dev/null
               $C python3 Testing/scripts/timed.py "$n $l r$r" sh -c "'$x' map -t $t '$M' '$D/${f}_R1.fq' '$D/${f}_R2.fq' > '$O/$n.$l.sam' 2> '$O/$n.$l.err'"
               echo "MBLOAD $n $l r$r $(grep 'index loaded' "$O/$n.$l.err" | sed 's/.*::\([0-9.]*\)\*\([0-9.]*\)\].*/\1 \2/')";;
          *) cat $I > /dev/null
             $C python3 Testing/scripts/timed.py "$n $l r$r empty" "$x" map "$I" "$O/empty.fq" "$O/empty.fq" "$O/e.sam" 100 1000
             $C python3 Testing/scripts/timed_load.py "$n $l r$r" "$x" map "$I" "$D/${f}_R1.fq" "$D/${f}_R2.fq" "$O/$n.$l.sam" 100 1000;;
        esac
      done; r=$((r + 1)); done
  done; done
