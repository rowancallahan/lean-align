#!/bin/bash
# The whole benchmark, top to bottom: tools, data, indexes, timing, agreement, results.
#   bash Testing/bench/bench.sh tiny DIR     laptop: generated 4 Mb genome, no download, about a minute after the build
#   nohup bash Testing/bench/bench.sh full DIR > ~/bench.out 2>&1 &     server: hg38 + NovaSeq reads, powers off at the end
# Settings (environment variables, all optional):
#   SETS       read sets to time and compare: nova, hiseq, mason, e.g. "nova hiseq mason"   (default nova)
#   PAIRS      read pairs to time, of nova and of hiseq   (default 40000000; "all" = every pair: for nova it needs WHOLE=1,
#              for hiseq it takes all 17 files of lane 1, about 200M pairs)
#   MASON_PAIRS  read pairs that mason simulates for the set mason   (default 1000000)
#   WHOLE      1: save the whole nova reads files to disk first (52 GB), then cut PAIRS from disk; PAIRS=all times every pair   (default 0)
#   NATIVE     1: also time minibwa built with -march=native (same index, a third row per run)   (default 0)
#   THREADS    thread counts to time, e.g. "8 16"    (default: a quarter, half and all of the cores)
#   REPS       runs per tool and thread count        (default 3)
#   POWER_OFF  0 keeps a `full` machine on           (default 1)
#   MAX_MIN    a `full` machine powers off after this many minutes whatever happens (default 720)
#   VERIFY     1 runs `PARANOID=1 verify.sh` at the end (adds an hour or more)    (default 0)
# Stops at the first failing step. Result: DIR/results.tgz = all.log, timing.tsv, compare.txt (nova; compare_hiseq.txt, compare_mason.txt),
# mason_accuracy.txt, threads.log, verify.log.
# Files already in DIR (genome, reads, indexes, minibwa, venv) are used as they are, not fetched or built again.
# Per set two read sets: the timed one (nova: reads, hiseq: hiseq, mason: mason) and its sample (nova: sample, others: hiseq_sample,
# mason_sample) = the first 1M pairs, compared with minibwa. The set name is the third column of timing.tsv (reads = nova).
set -euo pipefail

if [ $# != 2 ]; then
  echo "usage: bash Testing/bench/bench.sh tiny|full DIR"
  exit 1
fi
MODE=$1
if [ "$MODE" != tiny ] && [ "$MODE" != full ]; then
  echo "usage: bash Testing/bench/bench.sh tiny|full DIR"
  exit 1
fi
mkdir -p "$2"
W=$(cd "$2" && pwd)
cd "$(dirname "$0")/../.."
B=Testing/bench
CORES=$(getconf _NPROCESSORS_ONLN)

# ---- settings: the environment variable if it is set, otherwise the default ----
if [ -z "${PAIRS:-}" ]; then PAIRS=40000000; fi
if [ -z "${MAX_MIN:-}" ]; then MAX_MIN=720; fi
if [ -z "${SETS:-}" ]; then SETS=nova; fi
if [ -z "${MASON_PAIRS:-}" ]; then MASON_PAIRS=1000000; fi
if [ -z "${NATIVE:-}" ]; then NATIVE=0; fi        # 1: also time minibwa built with -march=native
TOOLS="ours minibwa"
if [ "$NATIVE" = 1 ]; then TOOLS="ours minibwa minibwa_native"; fi
if [ -z "${WHOLE:-}" ]; then WHOLE=0; fi          # 1: download the whole reads files to disk (52 GB), then cut PAIRS from disk
if [ "$PAIRS" = all ] && [ "$WHOLE" != 1 ]; then echo "PAIRS=all needs WHOLE=1"; exit 1; fi
if [ -z "${VERIFY:-}" ]; then VERIFY=0; fi
if [ -z "${MIN_GB:-}" ]; then MIN_GB=80; fi       # lower it for a re-run in a folder that already holds the big files
if [ "$MODE" = tiny ]; then
  if [ -z "${THREADS:-}" ]; then THREADS=2; fi
  if [ -z "${REPS:-}" ]; then REPS=1; fi
  POWER_OFF=0                                     # a tiny run never powers the machine off
  VERIFY=0                                        # and never starts verify.sh (verify.sh runs this mode itself)
  SETS=nova                                       # (and has only the small genome's reads)
else
  if [ -z "${THREADS:-}" ]; then THREADS="$((CORES / 4)) $((CORES / 2)) $CORES"; fi
  if [ -z "${REPS:-}" ]; then REPS=3; fi
  if [ -z "${POWER_OFF:-}" ]; then POWER_OFF=1; fi
fi
# the file names of a set. nova keeps the names reads, sample, ours.sam, minibwa.sam, compare.txt
use_set() {
  S=$1
  if [ "$S" = nova ]; then
    READS=reads; SAMPLE=sample; OURS_SAM=ours.sam; MB_SAM=minibwa.sam; CMP=compare.txt
  else
    READS=$S; SAMPLE=${S}_sample; OURS_SAM=ours_$S.sam; MB_SAM=minibwa_$S.sam; CMP=compare_$S.txt
  fi
}
MAX_THREADS=0                                     # the largest number in THREADS
for t in $THREADS; do                             # (unquoted on purpose: one word per thread count)
  if [ "$t" -gt "$MAX_THREADS" ]; then MAX_THREADS=$t; fi
done

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
  EXIT_CODE=$?                                    # how the script ended; must be the first line here
  set +e                                          # from here on nothing may stop the packing and the power off
  echo "EXIT CODE $EXIT_CODE"
  date
  kill "$SAMPLER"
  cd "$W"
  touch timing.tsv compare.txt mason_accuracy.txt verify.log   # so that tar finds these files, also after an early failure
  tar czf results.tgz all.log threads.log timing.tsv compare*.txt mason_accuracy.txt verify.log
  if [ "$POWER_OFF" = 1 ]; then sudo shutdown -h now; fi
}
trap finish EXIT
if [ "$POWER_OFF" = 1 ]; then
  sudo -n true                                    # fails at once if sudo would ask for a password
  sudo shutdown -h +"$MAX_MIN"                    # the 12-hour backstop; the normal power off is in finish
fi
date
git rev-parse HEAD
git status --short                                # lists files changed since that commit (nothing is the normal case)
uname -m
echo "cores $CORES, threads $THREADS, reps $REPS"

# ---- a `full` run needs about 60 GB in DIR (genome, two indexes, reads, build); stop now if less than MIN_GB (80) GB are free ----
if [ "$MODE" = full ]; then
  if [ "$CORES" -lt 4 ]; then echo "FAIL: need at least 4 cores"; exit 1; fi
  if [ "$(uname -m)" != x86_64 ]; then echo "FAIL: minibwa is built here with SSE4.2, needs an x86_64 machine"; exit 1; fi
  FREE_KB=$(df --output=avail -k "$W" | tail -1 | tr -d ' ')
  echo "free disk in $W: $((FREE_KB / 1000000)) GB"
  if [ "$FREE_KB" -lt $((MIN_GB * 1000000)) ]; then echo "FAIL: less than $MIN_GB GB free"; exit 1; fi
fi

# ---- 1. tools: system packages, Lean and our aligner, minibwa at the paper's commit, pysam ----
if [ "$MODE" = full ]; then
  sudo apt-get update
  # DEBIAN_FRONTEND and NEEDRESTART_MODE make apt install without asking questions
  sudo DEBIAN_FRONTEND=noninteractive NEEDRESTART_MODE=a apt-get install -y build-essential git curl zlib1g-dev pigz python3-venv bubblewrap seqan-apps
  # `lake check --paranoid` (in verify.sh) runs in a bubblewrap sandbox, which needs unprivileged user namespaces
  # (the setting exists on Ubuntu 24.04 only; on a kernel without it sysctl would fail and stop the run)
  if [ -e /proc/sys/kernel/apparmor_restrict_unprivileged_userns ]; then
    sudo sysctl -w kernel.apparmor_restrict_unprivileged_userns=0
  fi
  lscpu
  free -g
fi
if [ ! -x "$HOME/.elan/bin/lake" ]; then
  curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
fi
export PATH=$HOME/.elan/bin:$PATH
lake build lean-align
if [ ! -x "$W/minibwa/minibwa" ]; then
  git clone https://github.com/lh3/minibwa "$W/minibwa"
  git -C "$W/minibwa" checkout c07de5c
  make -C "$W/minibwa"
fi
if [ "$NATIVE" = 1 ] && [ ! -x "$W/minibwa_native/minibwa" ]; then
  # the same source built for this machine's processor; its Makefile still adds -msse4.2 -mpopcnt and OpenMP itself
  git clone "$W/minibwa" "$W/minibwa_native"
  git -C "$W/minibwa_native" checkout c07de5c
  make -C "$W/minibwa_native" CFLAGS="-std=c99 -g -Wall -O3 -march=native"
fi
if [ ! -x "$W/venv/bin/python" ]; then
  python3 -m venv "$W/venv"
  "$W/venv/bin/pip" install pysam==0.24.1
fi
PY=$W/venv/bin/python
"$PY" --version
"$PY" -c "import pysam; print('pysam', pysam.__version__)"
git -C "$W/minibwa" rev-parse HEAD

# ---- 2. data: genome.fa and, per set, the timed reads and the sample (at most 1M pairs) ----
if [ "$MODE" = tiny ]; then
  python3 $B/tiny_data.py make "$W"
else
  # hg38 in upper case for both tools (lower case marks repeats; the spec compares letters exactly)
  if [ ! -s "$W/genome.fa" ]; then
    curl -sSfL https://ngi-igenomes.s3.amazonaws.com/igenomes/Homo_sapiens/UCSC/hg38/Sequence/WholeGenomeFasta/genome.fa \
      | awk '/^>/{print; next}{print toupper($0)}' > "$W/genome.fa.tmp"
    mv "$W/genome.fa.tmp" "$W/genome.fa"
    GENOME_BASES=$(grep -v '^>' "$W/genome.fa" | tr -d '\n' | wc -c)
    echo "genome.fa: $GENOME_BASES letters"
    if [ "$GENOME_BASES" -lt 3000000000 ]; then echo "FAIL: genome.fa has fewer than 3 billion letters"; exit 1; fi
  fi
  for S in $SETS; do
    use_set $S
    if [ "$S" = nova ]; then
      # the minibwa paper's NovaSeq reads (two files, 25.7 GB and 26.6 GB).
      NOVA=https://storage.googleapis.com/brain-genomics-public/research/sequencing/fastq/novaseq/wgs_pcr_free/30x/HG002.novaseq.pcr-free.30x
      for r in 1 2; do
        if [ "$WHOLE" = 1 ] && [ ! -s "$W/whole_R$r.fq.gz" ]; then
          # the whole file to disk first. -C - continues a partial download, so after a dropped connection run again.
          curl -sSfL -C - -o "$W/whole_R$r.fq.gz.part" "$NOVA.R$r.fastq.gz"
          mv "$W/whole_R$r.fq.gz.part" "$W/whole_R$r.fq.gz"
        fi
        if [ -s "$W/reads_R$r.fq.gz" ]; then continue; fi
        if [ "$PAIRS" = all ]; then
          ln -s "whole_R$r.fq.gz" "$W/reads_R$r.fq.gz"
          continue
        fi
        # the first PAIRS pairs. head closes the pipe early, which makes the pipeline report an error even when it
        # worked, so the exit code is ignored here; section 3 counts the lines instead.
        if [ "$WHOLE" = 1 ]; then
          gzip -dc "$W/whole_R$r.fq.gz" | head -n $((4 * PAIRS)) | pigz -c > "$W/reads_R$r.fq.gz" || true
        else
          curl -sSfL "$NOVA.R$r.fastq.gz" | gzip -dc | head -n $((4 * PAIRS)) | pigz -c > "$W/reads_R$r.fq.gz" || true
        fi
      done
    elif [ "$S" = hiseq ]; then
      # GIAB HG002 HiSeq 2x250, lane 1: the 17 files of each mate in this order, the first PAIRS pairs (all, if PAIRS=all)
      GIAB=https://giab.s3.amazonaws.com/data/AshkenazimTrio/HG002_NA24385_son/NIST_Illumina_2x250bps/reads
      HISEQ_LINES=4000000000
      if [ "$PAIRS" != all ]; then HISEQ_LINES=$((4 * PAIRS)); fi
      for r in 1 2; do
        if [ -s "$W/hiseq_R$r.fq.gz" ]; then continue; fi
        # one file after the other into one pipe; `|| break` ends the loop when head has closed the pipe (exit code ignored, as above)
        for n in 001 002 003 004 005 006 007 008 009 010 011 012 013 014 015 016 017; do
          curl -sSfL "$GIAB/D1_S1_L001_R${r}_$n.fastq.gz" || break
        done | gzip -dc | head -n "$HISEQ_LINES" | pigz -c > "$W/hiseq_R$r.fq.gz" || true
      done
    elif [ "$S" = mason ]; then
      # mason2 (package seqan-apps) simulates MASON_PAIRS pairs of 2x150 from hg38; mason_truth.sam holds the true places
      if [ ! -s "$W/mason_R1.fq.gz" ]; then
        /usr/lib/seqan/bin/mason_simulator -ir "$W/genome.fa" -n "$MASON_PAIRS" -o "$W/mason_R1.fq" -or "$W/mason_R2.fq" \
          -oa "$W/mason_truth.sam" --seed 1 --illumina-read-length 150 --illumina-prob-mismatch-scale 2.5
        pigz "$W/mason_R1.fq" "$W/mason_R2.fq"
      fi
    else
      echo "FAIL: unknown set $S (nova, hiseq or mason)"; exit 1
    fi
  done
fi
for S in $SETS; do
  use_set $S
  for r in 1 2; do
    gzip -dc "$W/${READS}_R$r.fq.gz" | head -n 4000000 | gzip -c > "$W/${SAMPLE}_R$r.fq.gz" || true      # same reason for `|| true`
  done
done

# ---- 3. line counts (the pipelines above ignored their exit codes); count the letters (the Gbp in Gbp/hr) ----
for S in $SETS; do
  use_set $S
  WANT=$PAIRS                                      # how many pairs the timed reads of this set must have
  if [ "$S" = mason ]; then WANT=$MASON_PAIRS; fi
  for s in $READS $SAMPLE; do
    n1=$(gzip -dc "$W/${s}_R1.fq.gz" | wc -l)
    n2=$(gzip -dc "$W/${s}_R2.fq.gz" | wc -l)
    echo "$s: $((n1 / 4)) and $((n2 / 4)) pairs"
    if [ "$n1" != "$n2" ]; then echo "FAIL: the two mates have different numbers of lines"; exit 1; fi
    if [ "$n1" = 0 ]; then echo "FAIL: no reads"; exit 1; fi
    if [ "$s" = "$READS" ]; then
      READS_LINES=$n1
      if [ "$MODE" = full ] && [ "$WANT" != all ] && [ "$n1" != $((4 * WANT)) ]; then echo "FAIL: expected $WANT pairs"; exit 1; fi
    else
      EXPECTED=$READS_LINES                        # sample = the first 1M pairs of the timed reads, or all of them if that is less
      if [ "$EXPECTED" -gt 4000000 ]; then EXPECTED=4000000; fi
      if [ "$n1" != "$EXPECTED" ]; then echo "FAIL: sample should have $EXPECTED lines"; exit 1; fi
    fi
    gzip -dc "$W/${s}_R1.fq.gz" "$W/${s}_R2.fq.gz" | awk 'NR%4==2{n+=length($0)} END{print n}' > "$W/$s.bases"
  done
done

# ---- 4. indexes ----
if [ ! -s "$W/ours.idx" ]; then .lake/build/bin/lean-align build "$W/genome.fa" "$W/ours.idx"; fi
if [ ! -s "$W/mb.mbw" ]; then
  # minibwa's default index build needs about 60 GB for hg38 and is killed on a smaller machine. -l is its
  # low-memory method: one thread, slower, the same index bytes (compared on the small genome).
  RAM_GB=$(awk '/MemTotal/ {print int($2 / 1000000)}' /proc/meminfo)
  if [ "$RAM_GB" -ge 96 ]; then
    "$W/minibwa/minibwa" index -t "$CORES" "$W/genome.fa" "$W/mb"
  else
    "$W/minibwa/minibwa" index -l "$W/genome.fa" "$W/mb"
  fi
fi

# ---- 5. timing: one tool at a time, output thrown away, one line per run ----
printf "tool\tthreads\tset\twall_s\tcpu_s\tpeak_GB\tGbp\tGbp/hr\tGbp/core-hr\n" > "$W/timing.tsv"
for S in $SETS; do
  use_set $S
  for t in $THREADS; do
    for i in $(seq "$REPS"); do
      for tool in $TOOLS; do
        $PY $B/time_one.py $tool "$t" "$W" $READS >> "$W/timing.tsv"
      done
    done
  done
done
cat "$W/timing.tsv"

# ---- 6. agreement on the sample of each set: both SAM files kept, then compared ----
for S in $SETS; do
  use_set $S
  $PY $B/time_one.py ours    "$MAX_THREADS" "$W" $SAMPLE "$W/$OURS_SAM"
  $PY $B/time_one.py minibwa "$MAX_THREADS" "$W" $SAMPLE "$W/$MB_SAM"
  $PY $B/compare.py "$W/$OURS_SAM" "$W/$MB_SAM" > "$W/$CMP"
  cat "$W/$CMP"
  if [ "$S" = mason ]; then
    # the true places are known: how many pairs does each tool put there
    $PY $B/mason_score.py "$W/mason_truth.sam" "$W/$OURS_SAM" "$W/$MB_SAM" > "$W/mason_accuracy.txt"
    cat "$W/mason_accuracy.txt"
  fi
done
if [ "$MODE" = tiny ]; then
  # the read names hold the true position: every mate must be where it was cut from
  $PY $B/tiny_data.py check "$W/ours.sam"
  # on the unique genome the two files must be the same in columns 1-11 (name ... quality)
  grep -v '^@' "$W/ours.sam"    | cut -f1-11 > "$W/ours.cols"
  grep -v '^@' "$W/minibwa.sam" | cut -f1-11 > "$W/minibwa.cols"
  cmp "$W/ours.cols" "$W/minibwa.cols"
  echo "IDENTICAL: columns 1-11 of every record"
fi
echo "BENCH DONE"

# ---- 7. optional: the full verification in the same run (VERIFY=1); its output is DIR/verify.log ----
if [ "$VERIFY" = 1 ]; then
  PARANOID=1 bash $B/verify.sh "$W" > "$W/verify.log" 2>&1
  tail -5 "$W/verify.log"
fi
