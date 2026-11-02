#!/bin/bash
# Malformed-output checks on our SAM and BAM for read sets.  bash Testing/scripts/output_fuzz.sh OUTDIR SET...
# SET = a file prefix in Testing/data/prebuilt, or a path prefix to SET_R1.fq/SET_R2.fq. Needs OUTDIR/SET/ours.sam
# (from output_vs_minibwa.sh with KEEP=1) or maps it itself; bam_write, samtools ($SAMTOOLS), the release, hg38.upper.fa.
# Per set: sam_fuzz_check.py on the SAM (with samtools calmd NM for the AS cross-check); bam_write on the same reads;
# SAM records vs bam_write's SAM byte for byte; bam_check.py; samtools quickcheck, view -c, flagstat, stats, view round trip.
set -u
cd "$(dirname "$0")/../.."
out=$1; shift
P=Testing/data/prebuilt; G=${GENOME:-Testing/data/downloads/hg38.upper.fa}; ST=${SAMTOOLS:-samtools}
for set in "$@"; do
  case $set in */*) r=$set; name=$(basename $set) ;; *) r=$P/$set; name=$set ;; esac
  d=$out/$name; mkdir -p $d; r1=${r}_R1.fq; r2=${r}_R2.fq
  [ -s $d/ours.sam ] || .lake/build/bin/lean-align map $P/shim.idx $r1 $r2 $d/ours.sam 100 1000
  echo "=== $name"
  $ST calmd $d/ours.sam $G > $d/ours.calmd.sam 2> /dev/null
  python3 -I Testing/scripts/sam_fuzz_check.py $d/ours.sam $r1 $r2 $P/shim.idx.chromosomes $d/ours.calmd.sam; echo "sam_fuzz_check exit $?"
  rm -f $d/ours.calmd.sam
  .lake/build/bin/bam_write $P/shim.idx $r1 $r2 $d/bw 1 real > $d/bam_write.txt 2>&1 || { echo "bam_write FAILED"; tail -3 $d/bam_write.txt; continue; }
  # records of bam_write's SAM equal ours (same results, different chunking and code path)
  cmp <(grep -v '^@' $d/bw.sam) <(grep -v '^@' $d/ours.sam) && echo "bam_write SAM records == shim SAM records" || echo "bam_write SAM records DIFFER from the shim's"
  python3 -I Testing/scripts/bam_check.py $d/bw.bam $d/bw.sam; echo "bam_check exit $?"
  $ST quickcheck -v $d/bw.bam; echo "quickcheck exit $?"
  echo "view -c: BAM $($ST view -c $d/bw.bam), SAM records $(grep -vc '^@' $d/ours.sam)"
  cmp <($ST view $d/bw.bam) <(grep -v '^@' $d/ours.sam) && echo "samtools view of the BAM == SAM records, byte for byte" || echo "samtools view of the BAM DIFFERS from the SAM"
  diff <($ST view -h $d/bw.bam | grep -v '^@PG') <(grep -v '^@PG' $d/ours.sam) > /dev/null && echo "view -h round trip == SAM (except @PG)" || echo "view -h round trip DIFFERS"
  diff <($ST flagstat $d/bw.bam) <($ST flagstat $d/ours.sam) > /dev/null && echo "flagstat BAM == SAM" || echo "flagstat BAM DIFFERS from SAM"
  diff <($ST stats $d/bw.bam | grep '^SN' | grep -v 'filtered\|^SN	raw') <($ST stats $d/ours.sam | grep '^SN' | grep -v 'filtered\|^SN	raw') > /dev/null && echo "stats SN BAM == SAM" || echo "stats SN BAM DIFFERS from SAM"
  $ST flagstat $d/ours.sam | sed -n '1p;7p;12p;13p'
  rm -f $d/bw.sam $d/bw.bam
done
