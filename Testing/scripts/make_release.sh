#!/bin/sh
# Build a benchmark release on any machine (Linux or macOS): data, both indexes, the reads, packaged
# for one GitHub release, so a benchmark box only maps (Testing/data/fetch_release.sh, then
# PREBUILT=Testing/data/prebuilt sh Testing/scripts/compare.sh).
#   sh Testing/scripts/make_release.sh OUTDIR            whole hg38 (needs >= 16 GB RAM, ~70 GB disk, ~1.5-2 h)
#   MODE=small sh Testing/scripts/make_release.sh OUTDIR chr21 only (a few minutes; to test the pipeline)
# Needs: elan (lean-toolchain), git, curl, make, a C compiler, python3 with numpy.
# The Lean build cache and our executables go in only when built on Linux x86_64 (the boxes' platform);
# otherwise the box runs `lake build` itself.
# Then: gh release create bench-<commit> OUTDIR/* -R rowancallahan/lean-align
set -eu
cd "$(dirname "$0")/../.."
out=$1; mode=${MODE:-full}; D=Testing/data/downloads; W=${WORK:-$PWD/.release-work}
MB_COMMIT=c07de5c   # lh3/minibwa, the version benchmarked on 2026-10-27
mkdir -p "$W" "$out"

sh Testing/data/fetch.sh "$mode"
if [ "$mode" = full ]; then G=$D/hg38.upper.fa; src=$D/hg38.fa; sims=hg38; else G=$D/chr21.fa; src=$D/chr21.fa; sims=chr21; fi
for r in 1 2; do [ -s $D/hg002_200k_R$r.fq ] || head -n 800000 $D/hg002_1M_R$r.fq > $D/hg002_200k_R$r.fq; done
# simulated pairs, as on 2026-10-27: one line per chromosome, then sim_pairs.py seed 7
[ -s $W/$sims.1l.fa ] || awk '/^>/{if(n)print ""; print; n=1; next}{printf "%s", $0} END{print ""}' $src > $W/$sims.1l.fa
for m in mason low; do [ -s $D/${sims}_${m}_R1.fq ] || python3 Testing/benches/sim_pairs.py $W/$sims.1l.fa $D/${sims}_$m 200000 $m 7; done

lake build lean-align
[ -s $W/shim.idx ] || .lake/build/bin/lean-align build $G $W/shim.idx
test -s $W/shim.idx   # an empty index means buildIndex's check failed

[ -d $W/minibwa ] || git clone -q https://github.com/lh3/minibwa $W/minibwa
( cd $W/minibwa && git checkout -q $MB_COMMIT && make -s )
[ -s $W/mb.mbw ] || $W/minibwa/minibwa index -l -t ${MB_THREADS:-4} $G $W/mb

reads="$D/hg002_200k_R1.fq $D/hg002_200k_R2.fq $D/hg002_1M_R1.fq $D/hg002_1M_R2.fq
  $D/novaseq_200k_R1.fq $D/novaseq_200k_R2.fq
  $D/${sims}_mason_R1.fq $D/${sims}_mason_R2.fq $D/${sims}_low_R1.fq $D/${sims}_low_R2.fq"
case "$(uname -sm)" in "Linux x86_64") cache=1 ;; *) cache=0 ;; esac
CACHE=$cache GENOME=$G SHIM_IDX=$W/shim.idx MB_IDX=$W/mb READS="$reads" MB_COMMIT=$MB_COMMIT \
  sh Testing/scripts/package_release.sh "$out"
