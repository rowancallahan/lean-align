#!/bin/sh
# Synthetic data for loop-shape A/B runs (speed only; see scripts/sim_genome.py).
#   sh scripts/bench_data.sh [dir=out/bench] [whole_genome binary=.lake/build/bin/whole_genome]
# Writes <dir>/g (8 Mb, 2 chromosomes, index g/ix.* checked once with WG_CHECK=1, 20k 2x150 pairs p150_1/_2)
# and <dir>/k (4 Mb, 1 chromosome, 3k pairs; for k250_bench, which wants one chromosome).
set -eu
D=${1:-out/bench}
WG=${2:-.lake/build/bin/whole_genome}
S=$(dirname "$0")
test -x "$WG"
python3 "$S/sim_genome.py" "$D/g" 8 2 7
SIM_PAIRED=1 python3 "$S/sim_reads.py" "$D/g/all.fa" "$D/g/p150" 20000 150 0.005 0.1 11
python3 "$S/sim_genome.py" "$D/k" 4 1 5
SIM_PAIRED=1 python3 "$S/sim_reads.py" "$D/k/chr1.fa" "$D/k/k" 3000 150 0.005 0.1 3
"$WG" build "$D/g/ix" "$D/g/chr1.fa" "$D/g/chr2.fa" | tail -2
WG_CHECK=1 WG_READS="warm=$D/k/k_1.reads.txt:$D/k/k_2.reads.txt:200" WG_MODES=RTX \
  "$WG" pmap "$D/g/ix" "$D/g/chr1.fa" "$D/g/chr2.fa" | grep -E "index check|hash of"
echo "data ready in $D"
