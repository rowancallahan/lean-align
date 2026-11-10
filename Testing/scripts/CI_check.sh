#!/bin/sh
# The developer check.   sh Testing/scripts/CI_check.sh        (FUZZ=1 also runs the tiny-genome output fuzz, ~20 s)
# Exit 0 = frozen files match their checksums, everything builds, every theorem uses only the standard axioms,
# sorry appears only in Spec/ (the statements), the Proofs/ and Main.lean copies mirror Spec/, and the executable checks pass.
# Uses the cached lake build, so unchanged files are not re-elaborated.
set -u
cd "$(dirname "$0")/../.." || exit 1
fail=0
tmp="${TMPDIR:-/tmp}/lean_align_ci"; mkdir -p "$tmp"
step() { printf '\n== %s\n' "$1"; }
bad()  { echo "FAIL: $1"; fail=1; }

# the theorems that must be in the build, with standard axioms only
HEADLINE="Spec.alignPairs_correct Spec.alignPairs_end_to_end
  Spec.trimBytes_window Spec.trimBytes_acgt Spec.trimBytes_size Spec.cutAt_spec
  Spec.trimRead_quality_bytes Spec.trimRead_correct Spec.parse_trim_quality Spec.trimChunk_eq
  Spec.trimRead_best Spec.trimRead_best_none Spec.trimRead_contract Spec.trimRead_valid Spec.parse_trim_valid
  Spec.trimReadB_toRead Spec.FQ.parse_correct Spec.FQ.parseFastqB_eq Spec.qnameB_eq Spec.qnameOkB_eq
  Spec.Trim.trim_correct Spec.Trim.cut_eq Spec.Trim.cut_eq_cutF Spec.Trim.trimB_eq
  Spec.SamFast.samHeaderB_eq Spec.SamFast.samChunkS_eq Spec.SamFast.samFileS_eq"

step "frozen files (checksums)"
(cd Aligner/trimmer && shasum -a 256 -c FROZEN_CONTRACT.sha256) || fail=1
shasum -a 256 -c Spec/FROZEN.sha256 || fail=1

step "lake build"
lake build > "$tmp/build.log" 2>&1 && echo "build ok" || { tail -20 "$tmp/build.log"; bad "lake build"; }

step "axioms in the build (Lake replays the messages of cached modules)"
python3 -I Testing/scripts/axioms.py "$tmp/build.log" --build $HEADLINE || fail=1

step "certificates and audits (not build modules)"
for c in Aligner/kernels/*/Certificate.lean Proofs/core/Certificate.lean Aligner/trimmer/Certificate.lean \
         Proofs/core/Cli.lean Proofs/core/Run.lean Aligner/trimmer/ReadWindowProofAudit.lean; do
  log="$tmp/$(echo "$c" | tr '/' '_').log"
  lake env lean "$c" > "$log" 2>&1 || { bad "$c does not elaborate (see $log)"; continue; }
  python3 -I Testing/scripts/axioms.py "$log" || bad "$c"
done

step "executable cross-codec check"
lake env lean Testing/checks/CheckCertified.lean > "$tmp/cross.log" 2>&1 || bad "cross-codec check"
tail -3 "$tmp/cross.log"

step "forbidden tokens"
before=$fail
grep -nE "sorry|native_decide|@\[extern|unsafe|IO.println|IO.eprintln|IO.print |IO.Process|getStdout|getStderr" \
  Aligner/PairwiseMain.lean Aligner/LeanAlign/*.lean && bad "forbidden token in the executables"
grep -nE "IO\." Aligner/LeanAlign/*.lean && bad "IO in the pure library LeanAlign/"
grep -nE "sorry|native_decide|@\[extern|unsafe|implemented_by" \
  Main.lean Spec/Draft/Main.lean Proofs/MapFast.lean Spec/Fasta.lean Spec/Sam.lean Proofs/Fasta.lean Proofs/Fastq.lean Proofs/Sam.lean \
  Aligner/io/FastqIO.lean Proofs/Draft/*.lean \
  && bad "forbidden token in the shim files"
[ $fail -eq $before ] && echo "none"

step "copies mirror Spec/"
python3 -I Testing/scripts/fastq_mirror.py Spec/Fastq.lean Proofs/Fastq.lean \
  && echo "Proofs/Fastq.lean mirrors Spec/Fastq.lean (up to the holes)" || bad "Proofs/Fastq.lean differs from Spec/Fastq.lean"
python3 -I Testing/scripts/draft_mirror.py Spec/Draft/Trim.lean Proofs/Draft/Trim.lean trim trim_correct \
  && echo "Proofs/Draft/Trim.lean mirrors Spec/Draft/Trim.lean (up to the holes)" || bad "Proofs/Draft/Trim.lean differs from Spec/Draft/Trim.lean"
sed -e "s/^import Proofs.Answer$/import Spec.Aligner/" -e "s/^import Proofs.Fasta$/import Spec.Fasta/" \
  -e "s/^import Proofs.Fastq$/import Spec.Fastq/" Proofs/Draft/Sam.lean | cmp -s - Spec/Draft/Sam.lean \
  && echo "Proofs/Draft/Sam.lean mirrors Spec/Draft/Sam.lean" || bad "Proofs/Draft/Sam.lean differs from Spec/Draft/Sam.lean"
for f in Fasta Sam; do
  sed "s/^import Proofs\./import Spec./" Proofs/$f.lean | cmp -s - Spec/$f.lean \
    && echo "Proofs/$f.lean mirrors Spec/$f.lean" || bad "Proofs/$f.lean differs from Spec/$f.lean"
done
n=$(grep -n '^/-! ## The index and the aligner' Spec/Aligner.lean | cut -d: -f1)
head -n $((n - 1)) Spec/Aligner.lean > "$tmp/spec_answer.lean"
[ -n "$n" ] && sed "1d; \$d; s/^import Proofs.Mapping$/import Spec.Mapping/" Proofs/Answer.lean | cmp -s - "$tmp/spec_answer.lean" \
  && echo "Proofs/Answer.lean mirrors Spec/Aligner.lean (up to the holes)" || bad "Proofs/Answer.lean differs from Spec/Aligner.lean"
for f in MapFiles; do
  python3 -I Testing/scripts/holes_mirror.py Spec/Draft/$f.lean Proofs/Draft/$f.lean \
    && echo "Proofs/Draft/$f.lean mirrors Spec/Draft/$f.lean (up to the holes)" || bad "Proofs/Draft/$f.lean differs from Spec/Draft/$f.lean"
done
sed "s/^import Proofs.Draft.MapFiles$/import Spec.Draft.MapFiles/" Main.lean | cmp -s - Spec/Draft/Main.lean \
  && echo "Main.lean mirrors Spec/Draft/Main.lean" || bad "Main.lean differs from Spec/Draft/Main.lean"

if [ "${FUZZ:-0}" = 1 ]; then
  step "output fuzz (tiny generated genome)"
  sh Testing/scripts/fuzz_ci.sh || bad "output fuzz"
fi

step "result"
[ $fail -eq 0 ] && echo "ALL CHECKS PASSED" || echo "SOME CHECKS FAILED"
exit $fail
