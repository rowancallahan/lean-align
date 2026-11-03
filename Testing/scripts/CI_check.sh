#!/bin/sh
# Developer check: uses the cached lake build, so unchanged files are not re-elaborated.   sh Testing/scripts/CI_check.sh
# Exit 0 = frozen files match their checksums, everything builds, every
# certificate and spec file elaborates with standard axioms only and no sorry,
# and the executable cross-codec check passes.
# FUZZ=1 sh Testing/scripts/CI_check.sh  also runs the output-fuzz regression (fuzz_ci.sh: tiny generated genome, ~20 s, no hg38).
set -u
cd "$(dirname "$0")/../.." || exit 1
fail=0
tmp="${TMPDIR:-/tmp}"
step() { printf '\n== %s\n' "$1"; }

step "frozen files (checksums)"
(cd Aligner/trimmer && shasum -a 256 -c FROZEN_CONTRACT.sha256) || fail=1
shasum -a 256 -c Spec/FROZEN.sha256 || fail=1

step "lake build"
lake build >"$tmp/lean_align_build.log" 2>&1 && echo "build ok" || { tail -20 "$tmp/lean_align_build.log"; fail=1; }

step "axioms in the build (every module; Lake replays the messages of cached modules)"
python3 - "$tmp/lean_align_build.log" <<'PY' || fail=1
import re, sys
out = open(sys.argv[1]).read()
flat = re.sub(r"\s+", " ", out)
lists = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", flat)
none = re.findall(r"'([^']+)' does not depend on any axioms", flat)
bad = [(n, a) for n, a in lists if not set(x.strip() for x in a.split(",") if x.strip()) <= {"propext", "Classical.choice", "Quot.sound"}]
errors = re.findall(r"^error.*$|^\S+:\d+:\d+: error.*$", out, re.M)
sorries = [l for l in re.findall(r"^warning: (\S+):\d+:\d+: declaration uses .sorry.", out, re.M) if not l.startswith("Spec/")]
for n, a in bad: print(f"FAIL non-standard axioms: {n}: [{a}]")
for e in errors: print(f"FAIL {e}")
for f in sorries: print(f"FAIL sorry outside Spec/: {f}")
need = ["Spec.alignPairs_correct", "Spec.alignPairs_end_to_end", "Spec.trimBytes_window", "Spec.trimBytes_acgt", "Spec.trimBytes_size", "Spec.cutAt_spec", "Spec.trimRecord_quality_bytes", "Spec.trimRecord_correct", "Spec.parseRecord_trim_quality", "Spec.trimChunk_eq"]
for n in need:
    if not any(x == n for x, _ in lists): print(f"FAIL no axiom line for the headline theorem {n}"); bad.append(n)
if bad or errors or sorries or not lists: sys.exit(1)
print(f"ok   {len(lists) + len(none)} theorems, standard axioms only; sorry only in Spec/ (the statements)")
PY

step "certificates (not build modules: they share the name Certificate)"
for c in Aligner/kernels/*/Certificate.lean Proofs/core/Certificate.lean Aligner/trimmer/Certificate.lean Proofs/core/Cli.lean Proofs/core/Run.lean; do
  log="$tmp/lean_align_$(echo "$c" | tr '/' '_').log"
  lake env lean "$c" >"$log" 2>&1
  rc=$?
  python3 - "$c" "$log" "$rc" <<'PY' || fail=1
import re, sys
c, log, rc = sys.argv[1], sys.argv[2], int(sys.argv[3])
out = open(log).read()
flat = re.sub(r"\s+", " ", out)
lists = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", flat)
none = re.findall(r"'([^']+)' does not depend on any axioms", flat)
bad = [(n, a) for n, a in lists if not set(x.strip() for x in a.split(",") if x.strip()) <= {"propext", "Classical.choice", "Quot.sound"}]
if rc != 0 or re.search(r":\d+:\d+: error", out) or "sorryAx" in out or bad:
    print(f"FAIL {c}  (exit {rc}; see {log})")
    for n, a in bad: print(f"      non-standard axioms: {n}: [{a}]")
    sys.exit(1)
print(f"ok   {c}: {len(lists) + len(none)} theorems, standard axioms only")
PY
done

step "trimmer proof audit"
if lake env lean Aligner/trimmer/ReadWindowProofAudit.lean >"$tmp/lean_align_trimmer_audit.log" 2>&1 &&
    ! grep -q "sorryAx" "$tmp/lean_align_trimmer_audit.log"; then echo "audit ok"; else echo "FAIL trimmer audit"; fail=1; fi

step "executable cross-codec check"
lake env lean Testing/checks/CheckCertified.lean >"$tmp/lean_align_cross.log" 2>&1 || fail=1
tail -3 "$tmp/lean_align_cross.log"

step "forbidden tokens in the executables and LeanAlign/"
if grep -nE "sorry|native_decide|@\[extern|unsafe|IO.println|IO.eprintln|IO.print |IO.Process|getStdout|getStderr" Aligner/PairwiseMain.lean Aligner/LeanAlign/*.lean; then fail=1; else echo "none"; fi
if grep -nE "IO\." Aligner/LeanAlign/*.lean; then echo "FAIL: IO in the pure library"; fail=1; else echo "LeanAlign/ is IO-free"; fi
if grep -nE "sorry|native_decide|@\[extern|unsafe|implemented_by" Main.lean Spec/Shim.lean Spec/Fasta.lean Spec/Fastq.lean Spec/Sam.lean Proofs/Fasta.lean Proofs/Fastq.lean Proofs/Sam.lean; then fail=1; else echo "shim files: no sorry / native_decide / extern / unsafe / implemented_by"; fi
for f in Fasta Fastq Sam; do sed "s/^import Proofs\./import Spec./" Proofs/$f.lean | cmp -s - Spec/$f.lean && echo "Proofs/$f.lean mirrors Spec/$f.lean" || { echo "FAIL: Proofs/$f.lean differs from Spec/$f.lean"; fail=1; }; done
n=$(grep -n '^/-! ## The index and the aligner' Spec/Aligner.lean | cut -d: -f1)
head -n $((n-1)) Spec/Aligner.lean >"$tmp/lean_align_spec_answer.lean"
[ -n "$n" ] && sed "1d; \$d; s/^import Proofs.Mapping$/import Spec.Mapping/" Proofs/Answer.lean | cmp -s - "$tmp/lean_align_spec_answer.lean" && echo "Proofs/Answer.lean mirrors Spec/Aligner.lean (up to the holes)" || { echo "FAIL: Proofs/Answer.lean differs from Spec/Aligner.lean"; fail=1; }
sed "1d; s/^import Proofs.Sam$/import Spec.Sam/" Main.lean | cmp -s - Spec/Shim.lean && echo "Main.lean mirrors Spec/Shim.lean" || { echo "FAIL: Main.lean differs from Spec/Shim.lean"; fail=1; }

if [ "${FUZZ:-0}" = 1 ]; then
  step "output fuzz (tiny generated genome; known problems print XFAIL and do not fail)"
  sh Testing/scripts/fuzz_ci.sh || fail=1
fi

step "result"
[ $fail -eq 0 ] && echo "ALL CHECKS PASSED" || echo "SOME CHECKS FAILED"
exit $fail
