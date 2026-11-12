#!/bin/bash
# The proof facts of PROOF_CHANGES and the CI line "N theorems, standard axioms only": runs CI_check.sh and prints the axioms of the two main theorems.
#   bash Testing/repro/proofs.sh        (about a minute with a cached build; a clean build is much longer)
set -u
cd "$(dirname "$0")/../.."
sh Testing/scripts/CI_check.sh > /tmp/ci_repro.log 2>&1; rc=$?
grep -E "^ok   [0-9]+ theorems|ALL CHECKS|SOME CHECKS|FAIL" /tmp/ci_repro.log
f=$(mktemp "${TMPDIR:-/tmp}/ax.XXXXXX.lean")
printf 'import Proofs.Aligner\n#print axioms Spec.alignPairs_correct\n#print axioms Spec.alignPairs_end_to_end\n' > "$f"
lake env lean "$f" 2>&1 | grep axioms; rm -f "$f"
lake env lean Testing/checks/AuditAlignPairs.lean 2>&1 | tail -2
exit $rc
