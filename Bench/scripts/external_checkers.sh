#!/bin/sh
# Replays the proof through every checker `lake check --paranoid` runs, invoked exactly as
# Lake's src/lean/lake/Lake/CLI/Check.lean does (bundledKernels, runExternalKernel), for boxes
# without `bwrap` where `lake check` cannot start.   sh Bench/scripts/external_checkers.sh [full|target]
#   full   (default) export Proofs.Aligner and everything it imports
#   target export only what alignPairs_correct, alignPairs and buildIndex depend on
# Differences from `lake check --paranoid`: no sandbox around build/export, and the export is
# Proofs.Aligner rather than every default target.  Run `lake build` first.
set -eu
cd "$(dirname "$0")/../.."
mode="${1:-full}"
B="$(dirname "$(elan which lean)")"
out="${TMPDIR:-/tmp}/lean_align_checkers"
mkdir -p "$out"
E="$out/$mode.ndjson"
export LEAN_ABORT_ON_PANIC=1

if [ "$mode" = target ]; then
  lake env "$B/leanexport" Proofs.Aligner -- Spec.alignPairs_correct Spec.alignPairs Spec.buildIndex > "$E"
else
  lake env "$B/leanexport" Proofs.Aligner > "$E"
fi

# the nanoda-style config Lake writes for every external kernel
cat > "$out/nanoda.json" <<EOF
{"use_stdin": false, "export_file_path": "$E", "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"], "unpermitted_axiom_hard_error": false, "num_threads": 1, "nat_extension": true, "string_extension": true}
EOF

fail=0
run() {
  name=$1; shift
  start=$(date +%s)
  if "$@" > "$out/$name.log" 2>&1; then rc=0; else rc=$?; fail=1; fi
  echo "$name rc=$rc $(( $(date +%s) - start ))s  $(tail -1 "$out/$name.log")"
}
run leanchecker-paranoid "$B/leanchecker-paranoid" --silent --from-export "$E"
run lean4lean            "$B/lean4lean" --import "$E"
run nanoda               "$B/nanoda_bin" "$out/nanoda.json"
run con-leche            "$B/con-leche" "$E"
run con-ron              "$B/con-ron" "$E"
run leanchecker          "$B/leanchecker" --silent --from-export "$E"
exit $fail
