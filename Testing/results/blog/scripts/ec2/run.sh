#!/bin/bash
# Timing and agreement, ours vs minibwa.   bash Testing/ec2/run.sh tiny|full WORKDIR
# Needs setup.sh run first with the same arguments. THREADS and REPS can be set from outside.
set -euo pipefail
MODE=$1; W=$(cd "$2" && pwd); cd "$(dirname "$0")/../.."
case $MODE in tiny) THREADS=${THREADS:-2}; REPS=${REPS:-1} ;; full) THREADS=${THREADS:-"16 32"}; REPS=${REPS:-3} ;; esac
PY=$W/venv/bin/python; B=Testing/ec2

# 1. timing: output thrown away, one tool at a time
printf "tool\tthreads\tset\twall_s\tcpu_s\tpeak_GB\tGbp\tGbp/hr\tGbp/core-hr\n" | tee "$W/timing.tsv"
for t in $THREADS; do for tool in ours minibwa; do for i in $(seq "$REPS"); do
  $PY $B/bench.py $tool "$t" "$W" reads | tee -a "$W/timing.tsv"
done; done; done

# 2. agreement: the cmp read set, SAM kept
t=${THREADS##* }
$PY $B/bench.py ours "$t" "$W" cmp "$W/ours.sam" > /dev/null
$PY $B/bench.py minibwa "$t" "$W" cmp "$W/minibwa.sam" > /dev/null
$PY $B/compare.py "$W/ours.sam" "$W/minibwa.sam" | tee "$W/compare.txt"

# 3. tiny only: on the unique genome the two SAM files must be the same in columns 1-11 (name ... quality)
if [ "$MODE" = tiny ]; then
  cmp <(grep -v '^@' "$W/ours.sam" | cut -f1-11) <(grep -v '^@' "$W/minibwa.sam" | cut -f1-11)
  echo "IDENTICAL: columns 1-11 of every record"
fi
