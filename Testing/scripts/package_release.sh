#!/bin/sh
# Bundle everything a benchmark box needs, so it only maps: the Lean build cache, our executables,
# both indexes, the reads and the genome. Big files are split under GitHub's 2 GB asset limit.
#   GENOME=... SHIM_IDX=... MB_IDX=... READS="a_R1.fq a_R2.fq ..." sh Testing/scripts/package_release.sh OUTDIR
# Then upload OUTDIR/* as one GitHub release (e.g. gh release create bench-<commit> OUTDIR/*).
set -eu
cd "$(dirname "$0")/../.."
out=$1; mkdir -p "$out"
commit=$(git rev-parse --short HEAD)
part() { size=$(stat -c %s "$1"); if [ "$size" -gt 1900000000 ]; then split -b 1900M -d "$1" "$out/$2.part"; else cp "$1" "$out/$2"; fi; }

tar czf "$out/lake-build.tar.gz" .lake/build                  # Lean build cache: lake rebuilds only what changed
cp .lake/build/bin/lean-align .lake/build/bin/whole_genome "$out/"
part "$SHIM_IDX" shim.idx; cp "$SHIM_IDX.chromosomes" "$out/shim.idx.chromosomes"
for f in "$MB_IDX".*; do part "$f" "mb.${f##*.}"; done          # minibwa index files (mb.l2b, mb.mbw, ...)
part "$GENOME" genome.fa
for r in $READS; do part "$r" "$(basename "$r")"; done

# manifest: what was built from what, and the hash of every whole file (checked after joining parts)
{ echo "commit $commit"; echo "toolchain $(cat lean-toolchain)"; echo "genome $(basename "$GENOME")"
  for f in "$out"/*; do case $f in *.part*) ;; *) case "$(basename "$f")" in MANIFEST*) ;; *) echo "file $(basename "$f")";; esac;; esac; done
  for p in $(ls "$out" | grep '\.part' | sed 's/\.part.*//' | sort -u); do echo "file $p"; done
} > "$out/MANIFEST.tmp"
( cd "$out"; for p in $(ls | grep '\.part00$' | sed 's/\.part00$//'); do cat "$p".part* > "$p"; done
  for f in $(awk '$1=="file"{print $2}' MANIFEST.tmp); do sha256sum "$f"; done > SHA256
  for p in $(ls | grep '\.part00$' | sed 's/\.part00$//'); do rm "$p"; done )
mv "$out/MANIFEST.tmp" "$out/MANIFEST"
ls -la "$out"
