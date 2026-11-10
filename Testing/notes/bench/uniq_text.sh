#!/bin/bash
# Testing/unique/run.sh without samtools / bam_write: columns 1-11 compared on the SAM text (header lines dropped).
set -eu
S=${S:?set S to a scratch dir}; REPO=${REPO:?set REPO to the festive checkout}
cd ${REPO:?set REPO to the festive checkout}; o=$S/uniq; rm -rf $o; mkdir -p $o; B=.lake/build/bin; U=Testing/unique; MB=$S/bin/minibwa
python3 -I $U/gen_unique_genome.py $o/unique.fa 1
$B/kmer_check $o/unique.fa 15
$B/lean-align build $o/unique.fa $o/shim.idx
$MB index -t 4 $o/unique.fa $o/mb 2> $o/mb_index.log
for set in "sim 40 7" "sim2 17 11"; do
  read p step seed <<< "$set"
  python3 -I $U/sim_unique_pairs.py $o/unique.fa $o/$p $step $seed
  taskset -c 0-3 $B/lean-align map $o/shim.idx $o/${p}_R1.fq $o/${p}_R2.fq $o/ours_$p.sam 100 1000
  $MB map -t 4 $o/mb $o/${p}_R1.fq $o/${p}_R2.fq > $o/mb_$p.sam 2> $o/mb_$p.log
  python3 -I $U/compare_unique.py $o/ours_$p.sam $o/mb_$p.sam > $o/compare_$p.txt; echo "compare_unique $p rc=$?"; tail -3 $o/compare_$p.txt
  for x in ours mb; do grep -v '^@' $o/${x}_$p.sam | cut -f1-11 > $o/c11_${x}_$p; done
  echo "records ours $(wc -l < $o/c11_ours_$p) mb $(wc -l < $o/c11_mb_$p)"
  cmp $o/c11_ours_$p $o/c11_mb_$p && echo "UNIQUE $p columns 1-11 IDENTICAL" || echo "UNIQUE $p columns 1-11 DIFFER"
done
