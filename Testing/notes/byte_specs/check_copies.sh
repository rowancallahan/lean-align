#!/bin/bash
cd "$(dirname "$0")/../../.."
# Proofs/MapDefs.lean (used by the proof modules) must be a copy of the definitions in Proofs/MapFiles.lean
blk3() { sed -n '/^-- the mates of every pair/,/^-- `process`, run exactly as Main runs it/p' "$1" | grep -v '^-- `process`, run exactly'; }
diff <(blk3 Proofs/MapFiles.lean) <(blk3 Proofs/MapDefs.lean) && echo "MapDefs: identical to MapFiles"
