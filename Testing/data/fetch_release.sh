#!/bin/sh
# Fetch a benchmark release (see Testing/scripts/package_release.sh) into Testing/data/prebuilt/,
# join split files, check every SHA-256, and unpack the Lean build cache into .lake/build.
#   sh Testing/data/fetch_release.sh <tag> [owner/repo]       (FROM_DIR=dir: copy from a local folder instead)
set -eu
cd "$(dirname "$0")/../.."
tag=$1; repo=${2:-rowancallahan/lean-align}; dst=Testing/data/prebuilt
mkdir -p "$dst"
if [ -n "${FROM_DIR:-}" ]; then cp "$FROM_DIR"/* "$dst/"
elif command -v gh >/dev/null; then gh release download "$tag" -R "$repo" -D "$dst" --clobber
else echo "need gh (private repo) or FROM_DIR"; exit 1; fi
cd "$dst"
for p in $(ls | grep '\.part00$' | sed 's/\.part00$//'); do cat "$p".part* > "$p" && rm "$p".part*; done
sha256sum -c SHA256
cd - >/dev/null
tar xzf "$dst/lake-build.tar.gz"                                  # restores .lake/build; then `lake build` is incremental
chmod +x "$dst/lean-align" "$dst/whole_genome"
cat "$dst/MANIFEST" | head -3
