#!/bin/bash
# Our SAM (the shim) vs minibwa's on read sets, with samtools.   sh Testing/scripts/output_vs_minibwa.sh OUTDIR SET...
# SET = a file prefix in Testing/data/prebuilt (hg38_mason hg38_low hg002_200k novaseq_200k).
# Needs: lean-align and the minibwa binary ($MINIBWA), samtools ($SAMTOOLS), the release (fetch_release.sh), python3.
# Per set it writes OUTDIR/SET/{ours.sam,mb.sam kept only with KEEP=1, analysis.md, flagstat_*.txt, stats_*.txt, idxstats_diff.txt}.
set -eu
cd "$(dirname "$0")/../.."
out=$1; shift
P=Testing/data/prebuilt; G=${GENOME:-Testing/data/downloads/hg38.upper.fa}
MB=${MINIBWA:-minibwa}; ST=${SAMTOOLS:-samtools}; T=${THREADS:-4}
for set in "$@"; do
  d=$out/$set; mkdir -p "$d"; r1=$P/${set}_R1.fq; r2=$P/${set}_R2.fq
  TIMEFORMAT="wall %R s, user %U s, sys %S s"   # end-to-end including index load; the analysis does not use these
  { time .lake/build/bin/lean-align map $P/shim.idx $r1 $r2 $d/ours.sam 100 1000 ; } 2> $d/time_ours.txt
  { time $MB map -t $T $P/mb $r1 $r2 > $d/mb.sam ; } 2> $d/time_mb.txt
  python3 -I Testing/scripts/output_vs_minibwa.py $set $d/ours.sam $d/mb.sam > $d/analysis.md
  for x in ours mb; do
    $ST flagstat $d/$x.sam > $d/flagstat_$x.txt
    $ST sort -@ $T -o $d/$x.sorted.bam $d/$x.sam && $ST index $d/$x.sorted.bam
    $ST idxstats $d/$x.sorted.bam > $d/idxstats_$x.txt
  done
  # NM/MD for our records, recomputed from the reference (ours has none); minibwa's own NM is kept
  $ST calmd -b $d/ours.sorted.bam $G > $d/ours.calmd.bam 2>/dev/null
  $ST stats $d/ours.calmd.bam | grep '^SN' > $d/stats_ours.txt
  $ST stats $d/mb.sorted.bam | grep '^SN' > $d/stats_mb.txt
  python3 -I - $d/idxstats_ours.txt $d/idxstats_mb.txt > $d/idxstats_diff.txt <<'PY'
import sys
r = lambda p: {l.split('\t')[0]: int(l.split('\t')[2]) for l in open(p) if l.strip() and not l.startswith('*')}
a, b = r(sys.argv[1]), r(sys.argv[2])
print('mapped reads per chromosome, ours vs minibwa: sum over chromosomes |ours-minibwa| =', sum(abs(a.get(c, 0) - b.get(c, 0)) for c in set(a) | set(b)), 'of', sum(b.values()), 'minibwa mapped reads')
for c in sorted(set(a) | set(b), key=lambda c: -abs(a.get(c, 0) - b.get(c, 0)))[:6]: print(c, a.get(c, 0), b.get(c, 0))
PY
  rm -f $d/*.bam $d/*.bai; [ "${KEEP:-0}" = 1 ] || rm -f $d/ours.sam $d/mb.sam   # KEEP=1 keeps the SAMs
done
