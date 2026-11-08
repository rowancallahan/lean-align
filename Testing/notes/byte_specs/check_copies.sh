#!/bin/bash
# CutAfter.lean imports Spec.Shim, FastqSlices.lean imports Proofs.Fastq (they define the same names, so they cannot be imported together):
# the shared definitions must be textually identical.
cd "$(dirname "$0")"
blk() { sed -n '/^def splitNl/,/^theorem cutLines_spec/p' "$1"; }
diff <(blk FastqSlices.lean) <(blk CutAfter.lean) && echo "splitNl/cutLines: identical"
blk2() { sed -n '/^def sliceAt/,/^  rw \[h1, List.length_append\]; omega/p' "$1"; }
diff <(blk2 FastqSlices.lean) <(blk2 CutAfter.lean) && echo "sliceAt: identical"
