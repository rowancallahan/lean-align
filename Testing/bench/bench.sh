#!/bin/bash
# The whole benchmark, top to bottom: tools, data, indexes, timing, agreement, results.
#   bash Testing/bench/bench.sh tiny DIR     laptop: generated 4 Mb genome, no download, about a minute after the build
#   nohup bash Testing/bench/bench.sh full DIR > ~/bench.out 2>&1 &     server: hg38 + NovaSeq reads, powers off at the end
# Settings (environment): PAIRS (40000000) read pairs to time; THREADS (half and all cores); REPS (3);
#   POWER_OFF=0 keeps a `full` machine on; MAX_MIN (720) powers it off after that many minutes whatever happens.
# Stops at the first failing step. Result: DIR/results.tgz = all.log, timing.tsv, compare.txt, threads.log.
set -euo pipefail
MODE=$1; mkdir -p "$2"; W=$(cd "$2" && pwd); cd "$(dirname "$0")/../.."; B=Testing/bench
CORES=$(getconf _NPROCESSORS_ONLN)
case $MODE in
tiny) THREADS=${THREADS:-2};                       REPS=${REPS:-1}; POWER_OFF=0 ;;
full) THREADS=${THREADS:-"$((CORES / 2)) $CORES"}; REPS=${REPS:-3}; POWER_OFF=${POWER_OFF:-1} ;;
esac
PAIRS=${PAIRS:-40000000}

# ---- 0. logging, and what happens when the script ends (also when a step fails) ----
exec > "$W/all.log" 2>&1                          # everything below goes to all.log; watch it with: tail -f DIR/all.log
# for diagnosis: every 10 seconds, write the 40 threads that have used the most CPU time so far
sample_threads() {
  while true; do
    date +%s
    ps -eLo pid,tid,comm,time,pcpu --sort=-time | head -41
    sleep 10
  done
}
sample_threads > "$W/threads.log" &
SAMPLER=$!
finish() {
  echo "EXIT CODE $?"; date; kill $SAMPLER
  cd "$W"
  touch timing.tsv compare.txt
  tar czf results.tgz all.log threads.log timing.tsv compare.txt
  if [ "$POWER_OFF" = 1 ]; then sudo shutdown -h now; fi
}
trap finish EXIT
if [ "$POWER_OFF" = 1 ]; then sudo shutdown -h +"${MAX_MIN:-720}"; fi
date; git rev-parse HEAD; echo "cores $CORES, threads $THREADS, reps $REPS"

# ---- a `full` run needs about 60 GB in DIR (genome, two indexes, reads, build); stop now if the disk is too small ----
if [ "$MODE" = full ]; then
  FREE_GB=$(df --output=avail -BG "$W" | tail -1 | tr -dc '0-9')
  echo "free disk in $W: $FREE_GB GB"
  [ "$FREE_GB" -ge 80 ]
fi

# ---- 1. tools: system packages, Lean and our aligner, minibwa at the paper's commit, pysam ----
if [ "$MODE" = full ]; then
  sudo apt-get update
  sudo DEBIAN_FRONTEND=noninteractive NEEDRESTART_MODE=a apt-get install -y build-essential git curl zlib1g-dev pigz python3-venv
  lscpu; free -g
fi
[ -x "$HOME/.elan/bin/lake" ] || curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
export PATH=$HOME/.elan/bin:$PATH
lake build lean-align
[ -x "$W/minibwa/minibwa" ] || { git clone https://github.com/lh3/minibwa "$W/minibwa"; (cd "$W/minibwa" && git checkout c07de5c && make); }
[ -x "$W/venv/bin/python" ] || { python3 -m venv "$W/venv"; "$W/venv/bin/pip" install pysam; }
PY=$W/venv/bin/python

# ---- 2. data: genome.fa, reads_R{1,2}.fq.gz (timed), cmp_R{1,2}.fq.gz (compared, at most 1M pairs) ----
if [ "$MODE" = tiny ]; then
  python3 $B/tiny_data.py "$W"
else
  # hg38 in upper case for both tools (lower case marks repeats; the spec compares letters exactly)
  curl -sSfL https://ngi-igenomes.s3.amazonaws.com/igenomes/Homo_sapiens/UCSC/hg38/Sequence/WholeGenomeFasta/genome.fa \
    | awk '/^>/{print; next}{print toupper($0)}' > "$W/genome.fa"
  # the first PAIRS pairs of the minibwa paper's reads. head closes the pipe early, so the pipeline's exit code is ignored;
  # the line counts are checked in section 3.
  NOVA=https://storage.googleapis.com/brain-genomics-public/research/sequencing/fastq/novaseq/wgs_pcr_free/30x/HG002.novaseq.pcr-free.30x
  for r in 1 2; do
    curl -sSfL "$NOVA.R$r.fastq.gz" | gzip -dc | head -n $((4 * PAIRS)) | pigz -c > "$W/reads_R$r.fq.gz" || true
  done
fi
for r in 1 2; do
  gzip -dc "$W/reads_R$r.fq.gz" | head -n 4000000 | gzip -c > "$W/cmp_R$r.fq.gz" || true
done

# ---- 3. both mates must have the same number of reads; count the letters (the Gbp in Gbp/hr) ----
for s in reads cmp; do
  n1=$(gzip -dc "$W/${s}_R1.fq.gz" | wc -l); n2=$(gzip -dc "$W/${s}_R2.fq.gz" | wc -l)
  echo "$s: $((n1 / 4)) and $((n2 / 4)) pairs"
  [ "$n1" = "$n2" ]
  [ "$MODE" = tiny ] || [ "$s" = cmp ] || [ "$n1" = $((4 * PAIRS)) ]
  gzip -dc "$W/${s}_R1.fq.gz" "$W/${s}_R2.fq.gz" | awk 'NR%4==2{n+=length($0)} END{print n}' > "$W/$s.bases"
done

# ---- 4. indexes ----
.lake/build/bin/lean-align build "$W/genome.fa" "$W/ours.idx"
"$W/minibwa/minibwa" index -t "$CORES" "$W/genome.fa" "$W/mb"

# ---- 5. timing: one tool at a time, output thrown away, one line per run ----
printf "tool\tthreads\tset\twall_s\tcpu_s\tpeak_GB\tGbp\tGbp/hr\tGbp/core-hr\n" > "$W/timing.tsv"
for t in $THREADS; do for i in $(seq "$REPS"); do for tool in ours minibwa; do
  $PY $B/time_one.py $tool "$t" "$W" reads >> "$W/timing.tsv"
done; done; done
cat "$W/timing.tsv"

# ---- 6. agreement on the cmp set: both SAM files kept, then compared ----
for t in $THREADS; do LAST=$t; done                  # the largest thread count
$PY $B/time_one.py ours    "$LAST" "$W" cmp "$W/ours.sam"
$PY $B/time_one.py minibwa "$LAST" "$W" cmp "$W/minibwa.sam"
$PY $B/compare.py "$W/ours.sam" "$W/minibwa.sam" > "$W/compare.txt"
cat "$W/compare.txt"
if [ "$MODE" = tiny ]; then    # on the unique genome the two files must be the same in columns 1-11 (name ... quality)
  grep -v '^@' "$W/ours.sam"    | cut -f1-11 > "$W/ours.cols"
  grep -v '^@' "$W/minibwa.sam" | cut -f1-11 > "$W/minibwa.cols"
  cmp "$W/ours.cols" "$W/minibwa.cols"
  echo "IDENTICAL: columns 1-11 of every record"
fi
echo "BENCH DONE"
