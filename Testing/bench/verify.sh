#!/bin/bash
# Is this checkout proved, and does it give the right output?
#   bash Testing/bench/verify.sh DIR                 normal: minutes (uses the existing build)
#   PARANOID=1 bash Testing/bench/verify.sh DIR      deletes the build and rebuilds everything first, then more checks
# DIR is a work folder. For the hg38 checks (PARANOID only) it must be the DIR of a finished `bench.sh full` run.
# Stops at the first failure. The last line is VERIFY PASSED.
set -euo pipefail
mkdir -p "$1"; W=$(cd "$1" && pwd); cd "$(dirname "$0")/../.."; B=Testing/bench
export PATH=$HOME/.elan/bin:$PATH
PARANOID=${PARANOID:-0}

echo "== 1. the specification files are the frozen ones"
sha256sum -c Spec/FROZEN.sha256

echo "== 2. everything builds: every proof is checked by Lean"
if [ "$PARANOID" = 1 ]; then rm -rf .lake/build; fi          # paranoid: no cached result is trusted
lake build

echo "== 3. the main theorems depend on the three standard axioms only (a 'sorry' anywhere below them would show as sorryAx)"
cat > "$W/axioms.lean" <<'LEAN'
import Proofs.MapFiles
import Proofs.MapJobEq
import Proofs.Aligner
import Proofs.Fastq
import Proofs.Trim
import Proofs.TrimFast
import Proofs.SamFused
#print axioms Spec.alignPairs_correct
#print axioms Spec.alignPairs_end_to_end
#print axioms Spec.FQ.parse_correct
#print axioms Spec.Trim.trim_correct
#print axioms Spec.Total.process_correct
#print axioms Spec.MapCopy.job_eq
#print axioms Spec.SamFused.samChunkF_eq
LEAN
lake env lean "$W/axioms.lean" | tee "$W/axioms.txt"
[ "$(grep -c 'depends on axioms: \[propext, Classical.choice, Quot.sound\]$' "$W/axioms.txt")" = 7 ]
[ "$(grep -c . "$W/axioms.txt")" = 7 ]

echo "== 4. small genome with a known answer: our output equals minibwa's in columns 1-11"
bash $B/bench.sh tiny "$W/tiny"
grep "IDENTICAL: columns 1-11 of every record" "$W/tiny/all.log"

if [ "$PARANOID" = 1 ]; then
  PY=$W/venv/bin/python; T=$(getconf _NPROCESSORS_ONLN)
  echo "== 5. the index in use is what this code builds"
  .lake/build/bin/lean-align build "$W/genome.fa" "$W/ours_again.idx"
  cmp "$W/ours.idx" "$W/ours_again.idx"

  echo "== 6. same output with 1 thread, with all threads, and when run twice"
  $PY $B/time_one.py ours 1    "$W" cmp "$W/v1.sam"
  $PY $B/time_one.py ours "$T" "$W" cmp "$W/v2.sam"
  $PY $B/time_one.py ours "$T" "$W" cmp "$W/v3.sam"
  cmp "$W/v1.sam" "$W/v2.sam"; cmp "$W/v2.sam" "$W/v3.sam"

  echo "== 7. the Spec copies in Proofs/ mirror Spec/ up to the holes, and no forbidden word is used"
  python3 $B/mirror_check.py

  echo "== 8. hg38 fuzz against minibwa: none of our claims is false (rules A-D must be 0)"
  python3 $B/fuzz_hg38.py "$W/genome.fa" .lake/build/bin/lean-align "$W/ours.idx" "$W/minibwa/minibwa" "$W/mb" \
    "$W/fuzz" 10000 "$T"
fi
echo "VERIFY PASSED"
