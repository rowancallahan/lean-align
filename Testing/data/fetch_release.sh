#!/bin/sh
# Fetch a benchmark release (Testing/scripts/make_release.sh) into Testing/data/prebuilt/, join split
# files, check every SHA-256, link the genome and reads into Testing/data/downloads/, and unpack the Lean
# build cache if the release has one. Then: PREBUILT=Testing/data/prebuilt sh Testing/scripts/compare.sh
#   sh Testing/data/fetch_release.sh <tag> [owner/repo]       (FROM_DIR=dir: copy from a local folder instead)
set -eu
cd "$(dirname "$0")/../.."
tag=$1; repo=${2:-rowancallahan/lean-align}; dst=Testing/data/prebuilt; dl=Testing/data/downloads
mkdir -p "$dst"
if [ -L "$dl" ] && [ ! -e "$dl" ]; then rm "$dl"; fi   # a dangling link (the repo once tracked one)
mkdir -p "$dl"
if [ -n "${FROM_DIR:-}" ]; then cp "$FROM_DIR"/* "$dst/"
elif command -v gh >/dev/null; then gh release download "$tag" -R "$repo" -D "$dst" --clobber
else echo "need gh (private repo) or FROM_DIR"; exit 1; fi
cd "$dst"
for p in $(ls | grep '\.partaa$' | sed 's/\.partaa$//'); do cat "$p".part* > "$p" && rm "$p".part*; done
shasum -a 256 -c SHA256
cd - >/dev/null
for f in "$dst"/*.fq; do ln -sf "$PWD/$f" "$dl/$(basename "$f")"; done
ln -sf "$PWD/$dst/genome.fa" "$dl/$(awk '$1=="genome"{print $2}' "$dst/MANIFEST")"
if [ -f "$dst/lake-build.tar.gz" ]; then tar xzf "$dst/lake-build.tar.gz"   # restores .lake/build; `lake build` is then incremental
else echo "no build cache in this release: run lake build lean-align"; fi
cat "$dst/MANIFEST"
