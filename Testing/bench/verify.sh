#!/bin/bash
# Is this checkout proved, and does it give the right output?
#   bash Testing/bench/verify.sh DIR                 normal: minutes (uses the existing build)
#   PARANOID=1 bash Testing/bench/verify.sh DIR      deletes the build and rebuilds everything first, then more checks,
#                                                    ending with `lake check --paranoid` (needs: sudo apt-get install bubblewrap)
# DIR is a work folder. For the hg38 checks (PARANOID only) it must be the DIR of a finished `bench.sh full` run.
# Stops at the first failure. The last line is VERIFY PASSED.
# Normal mode: Spec and contract hashes, every proof builds, the axioms of seven theorems, the tiny run.
# PARANOID adds: index rebuilt, same output at 1 and all threads, axioms of the certificates, the checks in extra/,
# the comparator on every Spec file, and `lake check --paranoid`.
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
  ls -l "$W/genome.fa" "$W/ours.idx" "$W/minibwa/minibwa" "$W/venv/bin/python" "$W/sample_R1.fq.gz" "$W/ours.sam"
fi

echo "== 1. the specification files are the frozen ones"
sha256sum -c Spec/FROZEN.sha256
(cd Aligner/trimmer && sha256sum -c FROZEN_CONTRACT.sha256)

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

  echo "== 7. the kernel, core and trimmer certificates use the three standard axioms only"
  # Lean may break an axiom list over several lines, so the output is joined into one line first.
  for c in \
    Aligner/kernels/band/Certificate.lean \
    Aligner/kernels/gotoh/Certificate.lean \
    Aligner/kernels/wfa/Certificate.lean \
    Aligner/kernels/wfa_fast/Certificate.lean \
    Aligner/kernels/wfa_offsets/Certificate.lean \
    Aligner/kernels/wfa_runs/Certificate.lean \
    Aligner/kernels/wfa_small_errors/Certificate.lean \
    Aligner/kernels/wfa_u32/Certificate.lean \
    Proofs/core/Certificate.lean \
    Aligner/trimmer/Certificate.lean \
    Proofs/core/Cli.lean \
    Proofs/core/Run.lean \
    Aligner/trimmer/ReadWindowProofAudit.lean
  do
    echo "$c"
    lake env lean "$c" > "$W/cert.txt"
    # one axiom list per line: "depends on axioms: [a, b, c]"
    if ! tr -s ' \n' ' ' < "$W/cert.txt" | grep -o 'depends on axioms: \[[^]]*\]' > "$W/cert_lists.txt"; then
      echo "FAIL: $c prints no axiom list"
      exit 1
    fi
    # one axiom name per line
    sed 's/.*\[//; s/\]//; s/, /\n/g' "$W/cert_lists.txt" > "$W/cert_names.txt"
    if grep -vx -e propext -e Classical.choice -e Quot.sound "$W/cert_names.txt"; then
      echo "FAIL: $c uses an axiom other than the three standard ones (listed above)"
      exit 1
    fi
  done

  echo "== 8. the certified-kernel check file elaborates"
  lake env lean Testing/checks/CheckCertified.lean

  echo "== 9. extra checks, for completeness (Testing/bench/extra/)"
  echo "-- no escape hatch in the entry point: Main.lean has no extern, unsafe or implemented_by"
  if grep -n -E "@\[extern|unsafe|implemented_by" Main.lean; then
    echo "FAIL: Main.lean uses a construct that bypasses the proofs"
    exit 1
  fi
  echo "-- the tiny run: every record of our SAM is well formed and comes from the input reads"
  python3 $B/extra/sam_check.py "$W/tiny/ours.sam" "$W/tiny/sample_R1.fq.gz" "$W/tiny/sample_R2.fq.gz"
  echo "-- the 1M-pair hg38 sample: the same check"
  python3 $B/extra/sam_check.py "$W/ours.sam" "$W/sample_R1.fq.gz" "$W/sample_R2.fq.gz"
  echo "-- hg38 fuzz against minibwa: none of our claims is false (rules A-D must be 0)"
  # arguments of fuzz_hg38.py in order: genome, our binary, our index, minibwa binary, minibwa index prefix,
  #                                     work folder, pairs per seed, threads
  python3 $B/extra/fuzz_hg38.py \
    "$W/genome.fa" \
    .lake/build/bin/lean-align \
    "$W/ours.idx" \
    "$W/minibwa/minibwa" \
    "$W/mb" \
    "$W/fuzz" \
    10000 \
    "$T"

  echo "== 10. lake comparator: each Proofs/ file states the same theorems as its Spec/ file"
  lake comparator --config $B/comparator/alignment.json
  lake comparator --config $B/comparator/mapping.json
  lake comparator --config $B/comparator/aligner.json
  lake comparator --config $B/comparator/fastq.json
  lake comparator --config $B/comparator/trim.json
  lake comparator --config $B/comparator/mapfiles.json

  echo "== 11. lake check --paranoid: rebuild in a sandbox, export, and replay every proof through Lean's kernel"
  echo "       and the other bundled checkers (leanchecker-paranoid, lean4lean, nanoda, con-leche, con-ron);"
  echo "       it fails on any axiom other than the three standard ones. Needs bubblewrap; nanoda needs a lot of memory."
  lake check --paranoid
fi
echo "VERIFY PASSED"
