#!/bin/bash
# Unique-genome validation, end to end.   bash Testing/unique/run.sh OUTDIR
# Needs: lake build (lean-align, kmer_check, bam_write), $MINIBWA (c07de5c), $SAMTOOLS (1.24), python3.
set -eu
cd "$(dirname "$0")/../.."
o=$1; mkdir -p "$o"; B=.lake/build/bin; U=Testing/unique; MB=${MINIBWA:-minibwa}; ST=${SAMTOOLS:-samtools}
python3 -I $U/gen_unique_genome.py $o/unique.fa 1
$B/kmer_check $o/unique.fa 15                                  # exit 1 = some 15-mer twice
$B/lean-align build $o/unique.fa $o/shim.idx
$MB index -t 4 $o/unique.fa $o/mb 2> $o/mb_index.log
for set in "sim 40 7" "sim2 17 11"; do
  read p step seed <<< "$set"
  python3 -I $U/sim_unique_pairs.py $o/unique.fa $o/$p $step $seed
  taskset -c 0-3 $B/lean-align map $o/shim.idx $o/${p}_R1.fq $o/${p}_R2.fq $o/ours_$p.sam 100 1000
  $MB map -t 4 $o/mb $o/${p}_R1.fq $o/${p}_R2.fq > $o/mb_$p.sam 2> $o/mb_$p.log
  python3 -I $U/compare_unique.py $o/ours_$p.sam $o/mb_$p.sam > $o/compare_$p.txt
  for x in ours mb; do $ST quickcheck -v $o/${x}_$p.sam; $ST flagstat $o/${x}_$p.sam > $o/flagstat_${x}_$p.txt; done
  diff $o/flagstat_ours_$p.txt $o/flagstat_mb_$p.txt
  cmp <($ST view $o/ours_$p.sam | cut -f1-11) <($ST view $o/mb_$p.sam | cut -f1-11)   # QNAME..QUAL identical
  $B/bam_write $o/shim.idx $o/${p}_R1.fq $o/${p}_R2.fq $o/bw_$p 1 real > /dev/null
  cmp $o/bw_$p.sam $o/ours_$p.sam
  $ST quickcheck -v $o/bw_$p.bam
  diff <($ST view -h $o/bw_$p.bam | grep -v '^@PG.ID:samtools') $o/ours_$p.sam
  python3 -I Testing/scripts/bam_check.py $o/bw_$p.bam $o/bw_$p.sam
done
echo "ALL UNIQUE-GENOME CHECKS PASSED"
