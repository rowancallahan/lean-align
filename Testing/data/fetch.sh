#!/bin/sh
# Downloads the benchmark data into Testing/data/downloads/ (not in git).
#   sh Testing/data/fetch.sh small   chr21 (47 MB) + 1M HG002 HiSeq pairs (2x250 bp) + 200k HG002 NovaSeq pairs (2x151 bp)
#   sh Testing/data/fetch.sh full    the above + whole hg38 (3.1 GB)
# Genome: UCSC hg38 via the nf-core iGenomes mirror on S3 (same sequence as hgdownload.soe.ucsc.edu).
# Reads: GIAB HG002 (NA24385) NIST HiSeq 2500 2x250 bp, PCR-free, lane 1 file 004 (first 1M pairs);
#        HG002 NovaSeq 2x151 PCR-free 30x (Google brain-genomics-public, the minibwa paper's data),
#        pairs 1,000,001-1,200,000 as in the earlier benchmarks.
# Checksums of what was downloaded are written to downloads/SHA256 and verified on later runs.
set -eu
cd "$(dirname "$0")"
mode="${1:-small}"
mkdir -p downloads
cd downloads
IG=https://ngi-igenomes.s3.amazonaws.com/igenomes/Homo_sapiens/UCSC/hg38/Sequence
GIAB=https://giab.s3.amazonaws.com/data/AshkenazimTrio/HG002_NA24385_son/NIST_Illumina_2x250bps/reads

get() {  # url file
  [ -s "$2" ] && { echo "have $2"; return; }
  echo "fetch $2"
  curl -sSfL -o "$2.part" "$1"
  mv "$2.part" "$2"
}

get "$IG/Chromosomes/chr21.fa" chr21.fa
for r in 1 2; do
  f=hg002_1M_R$r.fq
  [ -s $f ] && { echo "have $f"; continue; }
  echo "fetch $f (first 1M reads)"
  # head closes the pipe early, so curl exits non-zero by design
  { curl -sSfL "$GIAB/D1_S1_L001_R${r}_004.fastq.gz" 2>/dev/null || true; } | gunzip -c 2>/dev/null | head -n 4000000 > $f
done
NOVA=https://storage.googleapis.com/brain-genomics-public/research/sequencing/fastq/novaseq/wgs_pcr_free/30x/HG002.novaseq.pcr-free.30x
for r in 1 2; do
  f=novaseq_200k_R$r.fq
  [ -s $f ] && { echo "have $f"; continue; }
  echo "fetch $f (pairs 1,000,001-1,200,000)"
  { curl -sSfL "$NOVA.R$r.fastq.gz" 2>/dev/null || true; } | gunzip -c 2>/dev/null | head -n 4800000 | tail -n 800000 > $f
done
[ "$mode" = full ] && get "$IG/WholeGenomeFasta/genome.fa" hg38.fa
# Soft-masked repeats are lowercase; the spec compares letters exactly and the packer would store every
# lowercase letter as an exception. minibwa folds case too, so both tools get the uppercase copy.
[ "$mode" = full ] && { [ -s hg38.upper.fa ] || awk '/^>/{print; next}{print toupper($0)}' hg38.fa > hg38.upper.fa; }

if [ -f SHA256 ]; then shasum -a 256 -c SHA256; else shasum -a 256 *.fa *.fq > SHA256; cat SHA256; fi
