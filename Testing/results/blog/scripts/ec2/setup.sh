#!/bin/bash
# Builds both aligners, fetches the data, builds both indexes.   bash Testing/ec2/setup.sh tiny|full WORKDIR
#   tiny: generated 4 Mb genome in which every 15-letter word is unique + simulated pairs. No download. Laptop.
#   full: hg38 + the first PAIRS pairs (default 40M) of the minibwa paper's HG002 NovaSeq 30x reads.
# Leaves in WORKDIR: genome.fa, ours.idx, mb.*, reads_R{1,2}.fq.gz (timed), cmp_R{1,2}.fq.gz (compared), *.bases
set -euo pipefail
MODE=$1; mkdir -p "$2"; W=$(cd "$2" && pwd); cd "$(dirname "$0")/../.."
PAIRS=${PAIRS:-40000000}; CMP_PAIRS=1000000
ZIP=$(command -v pigz || command -v gzip)

# tools: Lean and our aligner, minibwa at the paper's commit, pysam
if command -v apt-get > /dev/null; then sudo apt-get install -y build-essential git curl zlib1g-dev pigz python3-venv; fi
[ -x "$HOME/.elan/bin/lake" ] || curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
export PATH=$HOME/.elan/bin:$PATH
lake build lean-align
[ -x "$W/minibwa/minibwa" ] || { git clone https://github.com/lh3/minibwa "$W/minibwa"; (cd "$W/minibwa" && git checkout c07de5c && make); }
[ -x "$W/venv/bin/python" ] || { python3 -m venv "$W/venv"; "$W/venv/bin/pip" install pysam; }

# data
first_pairs() {  # URL N OUT.gz : the first N pairs of a gzipped FASTQ on the web. head closes the pipe, so curl may exit non-zero.
  { curl -sSfL "$1" || true; } | gzip -dc 2>/dev/null | head -n $((4 * $2)) | $ZIP -c > "$3" || true
}
case $MODE in
tiny)
  python3 Testing/unique/gen_unique_genome.py "$W/genome.fa" 1
  python3 Testing/unique/sim_unique_pairs.py "$W/genome.fa" "$W/sim" 40 7
  python3 Testing/ec2/drop_adapter_pairs.py "$W/sim_R1.fq" "$W/sim_R2.fq" "$W/keep_R1.fq" "$W/keep_R2.fq"
  for r in 1 2; do gzip -c "$W/keep_R$r.fq" > "$W/reads_R$r.fq.gz"; cp "$W/reads_R$r.fq.gz" "$W/cmp_R$r.fq.gz"; done ;;
full)
  # hg38 in upper case for both tools (lower case marks repeats; the spec compares letters exactly)
  curl -sSfL https://ngi-igenomes.s3.amazonaws.com/igenomes/Homo_sapiens/UCSC/hg38/Sequence/WholeGenomeFasta/genome.fa \
    | awk '/^>/{print; next}{print toupper($0)}' > "$W/genome.fa"
  NOVA=https://storage.googleapis.com/brain-genomics-public/research/sequencing/fastq/novaseq/wgs_pcr_free/30x/HG002.novaseq.pcr-free.30x
  for r in 1 2; do
    first_pairs "$NOVA.R$r.fastq.gz" "$PAIRS" "$W/reads_R$r.fq.gz"
    gzip -dc "$W/reads_R$r.fq.gz" | head -n $((4 * CMP_PAIRS)) | gzip -c > "$W/cmp_R$r.fq.gz" || true
  done ;;
esac

# bases in each read set (the Gbp in Gbp/hr), and a check that both mates have the same number of reads
for s in reads cmp; do
  n1=$(gzip -dc "$W/${s}_R1.fq.gz" | wc -l); n2=$(gzip -dc "$W/${s}_R2.fq.gz" | wc -l)
  [ "$n1" = "$n2" ] || { echo "FAIL: $s mates differ: $n1 vs $n2 lines"; exit 1; }
  gzip -dc "$W/${s}_R1.fq.gz" "$W/${s}_R2.fq.gz" | awk 'NR%4==2{n+=length($0)} END{print n}' > "$W/$s.bases"
  echo "$s: $((n1 / 4)) pairs, $(cat "$W/$s.bases") bases"
done

# indexes
.lake/build/bin/lean-align build "$W/genome.fa" "$W/ours.idx"
"$W/minibwa/minibwa" index -t "$(getconf _NPROCESSORS_ONLN)" "$W/genome.fa" "$W/mb"
echo "SETUP DONE: $W"
