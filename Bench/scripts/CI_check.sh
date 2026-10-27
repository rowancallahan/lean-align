#!/bin/sh
# Developer check: uses the cached lake build, so unchanged files are not re-elaborated.   sh Bench/scripts/CI_check.sh
# Exit 0 = frozen files match their checksums, everything builds, every
# certificate and spec file elaborates with standard axioms only and no sorry,
# and the executable cross-codec check passes.
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
lake env lean Bench/checks/CheckCertified.lean >"$tmp/lean_align_cross.log" 2>&1 || fail=1
tail -3 "$tmp/lean_align_cross.log"

step "forbidden tokens in Main.lean and LeanAlign/"
if grep -nE "sorry|native_decide|@\[extern|unsafe|IO.println|IO.eprintln|IO.print |IO.Process|getStdout|getStderr" Main.lean Aligner/LeanAlign/*.lean; then fail=1; else echo "none"; fi
if grep -nE "IO\." Aligner/LeanAlign/*.lean; then echo "FAIL: IO in the pure library"; fail=1; else echo "LeanAlign/ is IO-free"; fi

step "result"
[ $fail -eq 0 ] && echo "ALL CHECKS PASSED" || echo "SOME CHECKS FAILED"
exit $fail
