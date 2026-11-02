#!/bin/sh
# Rebuild Testing/examples/sam_compare: run the shim, the bench whole_genome (mode RTX, WG_TIEROUT) and minibwa on the
# 28 example pairs (ex_R1.fq / ex_R2.fq) and print a side-by-side table (one row per mate).
#   sh Testing/scripts/compare_sam_example.sh
# NOTE: the shim is at milestone M1: its SAM has bounds only, every pair is unmapped (answerOf found := none).
# Needs: lake build lean-align whole_genome; Testing/data/fetch_release.sh bench-release (shim.idx, mb.*, genome);
#        MINIBWA = the minibwa binary (c07de5c). The bench index (wg.*) is built once into $WG (~20 min build + ~16 min
#        check, ~5 GB disk) when $WG.hash is missing.  Env: PREBUILT GENOME MINIBWA WG OUT
set -eu
cd "$(dirname "$0")/../.."
P=${PREBUILT:-Testing/data/prebuilt}; G=${GENOME:-Testing/data/downloads/hg38.upper.fa}; MINIBWA=${MINIBWA:-minibwa}
WG=${WG:-${TMPDIR:-/tmp}/lean_align_wg/wg}; E=Testing/examples/sam_compare; OUT=${OUT:-$E}; B=.lake/build/bin
R1=$E/ex_R1.fq; R2=$E/ex_R2.fq
mkdir -p "$(dirname "$WG")" "$OUT"
if [ ! -s "$WG.hash" ]; then
  $B/whole_genome build "$WG" "$G"
  WG_CHECK=1 WG_MODES=RTX WG_READS= $B/whole_genome pmap "$WG" "$G" >/dev/null
fi
# 1. the shim
$B/lean-align map "$P/shim.idx" "$R1" "$R2" "$OUT/shim.sam" 100 1000
# 2. the bench: the found pair's positions (RTX dump) and the router's tier (tiers dump); WG_XH=0 as alignPairs runs
tmp=$(mktemp -d)
WG_MODES=RTX WG_TIEROUT=1 WG_XH=0 WG_TASKS=1 WG_OUT=$tmp WG_READS="ex=$PWD/$R1:$PWD/$R2:0" $B/whole_genome pmap "$WG" "$G" >/dev/null
cp "$tmp/RTX_ex.tsv" "$OUT/bench_pairs.tsv"; cp "$tmp/tiers_ex.tsv" "$OUT/bench_tiers.tsv"; rm -r "$tmp"
# 3. minibwa
"$MINIBWA" map -t 2 "$P/mb" "$R1" "$R2" > "$OUT/minibwa.sam" 2>/dev/null
python3 -I Testing/scripts/sam_example_table.py "$OUT" "$P/shim.idx.chromosomes" | tee "$OUT/table.txt"
