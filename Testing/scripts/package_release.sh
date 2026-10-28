#!/bin/sh
# Bundle what a benchmark box needs, so it only maps: both indexes, the reads and the genome, and (CACHE=1)
# the Lean build cache, executables included. Files over 1.9 GB are split under GitHub's 2 GB asset limit.
# Usually run by make_release.sh:
#   GENOME=... SHIM_IDX=... MB_IDX=... READS="a_R1.fq ..." [CACHE=1] sh Testing/scripts/package_release.sh OUTDIR
set -eu
cd "$(dirname "$0")/../.."
out=$1; mkdir -p "$out"
P=${PART_MB:-1900}   # split size in MB (GitHub's asset limit is 2 GB)
part() {  # file name: copy, or split into name.partaa, name.partab, ...; the hash is of the whole file
  if [ "$(wc -c < "$1")" -gt $((P * 1048576)) ]; then split -b ${P}m -a 2 "$1" "$out/$2.part"; else cp "$1" "$out/$2"; fi
  shasum -a 256 "$1" | awk -v n="$2" '{print $1 "  " n}' >> "$out/SHA256"
}
: > "$out/SHA256"
if [ "${CACHE:-0}" = 1 ]; then
  tar czf "$out/.lake-build.tar.gz" .lake/build   # Lean build cache: lake then rebuilds only what changed
  part "$out/.lake-build.tar.gz" lake-build.tar.gz; rm "$out/.lake-build.tar.gz"
fi
part "$SHIM_IDX" shim.idx; part "$SHIM_IDX.chromosomes" shim.idx.chromosomes
for f in "$MB_IDX".*; do part "$f" "mb.${f##*.}"; done          # minibwa index files (mb.mbw, mb.l2b, ...)
part "$GENOME" genome.fa
for r in $READS; do part "$r" "$(basename "$r")"; done
{ echo "commit $(git rev-parse --short HEAD)"; echo "toolchain $(cat lean-toolchain)"
  echo "genome $(basename "$GENOME")"; echo "minibwa ${MB_COMMIT:-?}"; echo "built on $(uname -sm)"
  echo "cache ${CACHE:-0}"; } > "$out/MANIFEST"
ls -la "$out"
