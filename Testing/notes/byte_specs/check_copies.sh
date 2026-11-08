#!/bin/bash
# CutAfter.lean imports Spec.Shim, FastqSlices.lean imports Proofs.Fastq (they define the same names, so they cannot be imported together):
# the shared definitions must be textually identical.
cd "$(dirname "$0")"
blk() { sed -n '/^def splitNl/,/^theorem cutLines_spec/p' "$1"; }
diff <(blk FastqSlices.lean) <(blk CutAfter.lean) && echo "splitNl/cutLines: identical"
