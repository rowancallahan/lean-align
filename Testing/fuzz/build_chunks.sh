#!/bin/sh
# Build lean-align with chunkSize 1, 7, 4096 and the default into OUTDIR/lean-align-{1,7,4096,default}.
#   sh Testing/fuzz/build_chunks.sh OUTDIR       (run on the branch under test; restores Main.lean afterwards)
set -eu
cd "$(dirname "$0")/../.."
out=$1; mkdir -p "$out"
cp Main.lean "$out/Main.lean.orig"
grep -q '^def chunkSize : USize := 8 \* 1024 \* 1024$' Main.lean
for n in ${SIZES:-1 7 4096 default}; do
  cp "$out/Main.lean.orig" Main.lean
  [ $n = default ] || sed -i "s/^def chunkSize : USize := .*/def chunkSize : USize := $n/" Main.lean
  lake build lean-align
  cp .lake/build/bin/lean-align "$out/lean-align-$n"
done
cp "$out/Main.lean.orig" Main.lean
