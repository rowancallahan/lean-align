#!/bin/bash
# Where does our extra CPU time at more threads go?   bash Testing/bench/scaling_diag.sh DIR
# DIR is the folder of a finished `bench.sh full` run. Our aligner on the timed reads at each thread count,
# once as it is and once with the allocator told not to hand memory back to the system (MIMALLOC_PURGE_DELAY=-1).
# One DETAIL line per run: user and system seconds of the aligner alone, page faults, context switches.
set -euo pipefail
W=$(cd "$1" && pwd)
cd "$(dirname "$0")/../.."
if [ -z "${THREADS:-}" ]; then THREADS="4 8 16"; fi
if [ -z "${SET:-}" ]; then SET=reads; fi
for t in $THREADS; do
  DETAIL=1 "$W/venv/bin/python" Testing/bench/time_one.py ours "$t" "$W" "$SET" 2>&1 | sed 's/^/as it is      /'
  DETAIL=1 MIMALLOC_PURGE_DELAY=-1 "$W/venv/bin/python" Testing/bench/time_one.py ours "$t" "$W" "$SET" 2>&1 | sed 's/^/no purge      /'
done
