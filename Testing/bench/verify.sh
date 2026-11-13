#!/bin/bash
# Is this checkout proved, and does it give the right output?
#   bash Testing/bench/verify.sh DIR                 normal: minutes (uses the existing build)
#   PARANOID=1 bash Testing/bench/verify.sh DIR      deletes the build and rebuilds everything first, then more checks,
#                                                    ending with `lake check --paranoid` (needs: sudo apt-get install bubblewrap)
# DIR is a work folder. For the hg38 checks (PARANOID only) it must be the DIR of a finished `bench.sh full` run.
# Stops at the first failure. The last line is VERIFY PASSED.
# Normal mode checks the Spec files (hashes), that every proof builds, the axioms of seven theorems, and the tiny run.
# It does NOT check that the copies of the Spec inside Proofs/ say the same as Spec/: that is step 7, PARANOID only.
set -euo pipefail

if [ $# != 1 ]; then
  echo "usage: [PARANOID=1] bash Testing/bench/verify.sh DIR"
  exit 1
fi
mkdir -p "$1"
W=$(cd "$1" && pwd)
cd "$(dirname "$0")/../.."
B=Testing/bench
export PATH=$HOME/.elan/bin:$PATH
if [ -z "${PARANOID:-}" ]; then PARANOID=0; fi

if [ "$PARANOID" = 1 ]; then
  # fail now, not after an hour: what steps 5 to 9 need
  command -v bwrap
  bwrap --ro-bind / / true                        # needs unprivileged user namespaces (bench.sh sets the sysctl)
  ls -l "$W/genome.fa" "$W/ours.idx" "$W/minibwa/minibwa" "$W/venv/bin/python"
fi

echo "== 1. the specification files are the frozen ones"
sha256sum -c Spec/FROZEN.sha256

echo "== 2. everything builds: every proof is checked by Lean"
if [ "$PARANOID" = 1 ]; then
  rm -rf .lake/build                              # paranoid: no cached result is trusted
fi
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
# every one of the 7 lines must name exactly the three standard axioms, and there must be no other line
STANDARD=$(grep -c 'depends on axioms: \[propext, Classical.choice, Quot.sound\]$' "$W/axioms.txt")
LINES=$(grep -c . "$W/axioms.txt")
if [ "$STANDARD" != 7 ] || [ "$LINES" != 7 ]; then
  echo "FAIL: expected 7 lines, all with the three standard axioms; found $LINES lines, $STANDARD of them standard"
  exit 1
fi

echo "== 4. small genome with a known answer: our output equals minibwa's in columns 1-11, and is at the true positions"
mkdir -p "$W/tiny"
# reuse minibwa and pysam from DIR if they are there (otherwise bench.sh builds them inside DIR/tiny)
if [ -d "$W/minibwa" ]; then ln -sfn "$W/minibwa" "$W/tiny/minibwa"; fi
if [ -d "$W/venv" ];    then ln -sfn "$W/venv"    "$W/tiny/venv"; fi
bash "$B/bench.sh" tiny "$W/tiny"
grep "IDENTICAL: columns 1-11 of every record" "$W/tiny/all.log"

if [ "$PARANOID" = 1 ]; then
  PY=$W/venv/bin/python
  T=$(getconf _NPROCESSORS_ONLN)
  echo "== 5. the index in use is what this code builds"
  .lake/build/bin/lean-align build "$W/genome.fa" "$W/ours_again.idx"
  cmp "$W/ours.idx" "$W/ours_again.idx"

  echo "== 6. same output with 1 thread, with all threads, and when run twice"
  $PY $B/time_one.py ours 1    "$W" sample "$W/v1.sam"
  $PY $B/time_one.py ours "$T" "$W" sample "$W/v2.sam"
  $PY $B/time_one.py ours "$T" "$W" sample "$W/v3.sam"
  cmp "$W/v1.sam" "$W/v2.sam"
  cmp "$W/v2.sam" "$W/v3.sam"

  echo "== 7. the Spec copies in Proofs/ mirror Spec/ up to the holes, and no forbidden word is used"
  python3 $B/mirror_check.py

  echo "== 8. hg38 fuzz against minibwa: none of our claims is false (rules A-D must be 0)"
  # arguments of fuzz_hg38.py in order: genome, our binary, our index, minibwa binary, minibwa index prefix,
  #                                     work folder, pairs per seed, threads
  python3 $B/fuzz_hg38.py \
    "$W/genome.fa" \
    .lake/build/bin/lean-align \
    "$W/ours.idx" \
    "$W/minibwa/minibwa" \
    "$W/mb" \
    "$W/fuzz" \
    10000 \
    "$T"

  echo "== 9. lake check --paranoid: rebuild in a sandbox, export, and replay every proof through Lean's kernel"
  echo "      and the other bundled checkers (leanchecker-paranoid, lean4lean, nanoda, con-leche, con-ron);"
  echo "      it fails on any axiom other than the three standard ones. Needs bubblewrap; nanoda needs a lot of memory."
  lake check --paranoid
fi
echo "VERIFY PASSED"
