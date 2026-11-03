#!/bin/bash
# Are the statements of alignPairs_correct and alignPairs_end_to_end the same at two commits? (the claim of PROOF_CHANGES)
#   bash Testing/repro/statements.sh REV_A REV_B        e.g. 5c309c3 2b496d6
# Extracts each theorem's text (from `theorem alignPairs_...` to its `:= by`) from Spec/Aligner.lean and Proofs/Aligner.lean at both revisions and diffs.
set -u
cd "$(dirname "$0")/../.."
a=$1; b=$2; rc=0
ext() { git show "$1:$2" | awk '/^theorem alignPairs_correct|^theorem alignPairs_end_to_end/{p=1} p{print} /:= by/{if(p){p=0; print "-----"}}'; }
for f in Spec/Aligner.lean Proofs/Aligner.lean; do
  if diff <(ext $a $f) <(ext $b $f) > /tmp/stmt.diff; then echo "$f: the two theorem statements are IDENTICAL at $a and $b"; else echo "$f: DIFFER between $a and $b:"; cat /tmp/stmt.diff; rc=1; fi
done
# the theorem TEXT can stay the same while the definitions it uses change (e.g. PairAnswer.Correct): compare the whole statement files too
for f in Spec/Alignment.lean Spec/Mapping.lean Spec/Aligner.lean; do
  if git diff --quiet $a $b -- $f; then echo "$f: unchanged"; else echo "$f: CHANGED (the statements mean something different if a definition they use changed):"; git diff $a $b -- $f | grep '^[+-][^+-]' | head -12; rc=1; fi
done
echo "other Spec/ files changed:"; git diff --stat $a $b -- Spec/Fasta.lean Spec/Fastq.lean Spec/Sam.lean Spec/Shim.lean Spec/FROZEN.sha256 | tail -6
exit $rc
