#!/bin/bash
# Rowan's one-command check: proofs, fuzzing, exactness, speed vs minibwa. Stops at the first failure.
#
#   bash Testing/verify.sh OUTDIR                 # all steps
#   STEPS="1 2 5" bash Testing/verify.sh OUTDIR   # only some steps
#
# Needs (see Testing/repro/README.md "Setup"): Lean on PATH, the bench release in Testing/data/prebuilt,
# MINIBWA=path/to/minibwa (c07de5c), SAMTOOLS=path/to/samtools (step 4 only).
# Optional: INDEX (default Testing/data/prebuilt/shim.idx), MBINDEX (default Testing/data/prebuilt/mb),
#           SETS (default "novaseq_200k hg002_200k", files Testing/data/prebuilt/SET_R{1,2}.fq), THREADS (4), REPEAT (3).
#
# Steps:
#   1  build + every proof + tiny-genome output fuzz        (CI_check.sh with FUZZ=1)
#   2  the index was built by THIS code                      (an old index silently maps nothing)
#   3  hg38 fuzz vs minibwa: are any of our claims false?    (rules A-D must all be 0)
#   4  unique genome: identical to minibwa byte for byte     (columns 1-11)
#   5  speed: index load timed separately; map-only seconds, Gbp/hr, Gbp per core-hour, ours vs minibwa
set -euo pipefail
cd "$(dirname "$0")/.."
O=$1; mkdir -p "$O"
STEPS=${STEPS:-"1 2 3 4 5"}
P=Testing/data/prebuilt
IDX=${INDEX:-$P/shim.idx}; MBI=${MBINDEX:-$P/mb}
SETS=${SETS:-"novaseq_200k hg002_200k"}; T=${THREADS:-4}; R=${REPEAT:-3}
LA=.lake/build/bin/lean-align
MB=${MINIBWA:?set MINIBWA to the minibwa binary}
export PATH=$HOME/.elan/bin:$PATH
want() { case " $STEPS " in *" $1 "*) return 0;; *) return 1;; esac; }
step() { echo; echo "=== step $1: $2"; }
fail() { echo "FAIL: $*"; exit 1; }

if want 1; then
  step 1 "build + proofs + tiny-genome fuzz (10-15 min)"
  FUZZ=1 sh Testing/scripts/CI_check.sh > "$O/ci.log" 2>&1 || { tail -40 "$O/ci.log"; fail "CI_check (log: $O/ci.log)"; }
  grep -q 'ALL CHECKS PASSED' "$O/ci.log" || fail "CI_check did not print ALL CHECKS PASSED"
  grep -q 'VIOLATIONS: none' "$O/ci.log" || fail "output fuzz found violations"
  grep -E 'standard axioms only' "$O/ci.log" | head -1
  echo "ok: proofs, axioms, Spec mirrors, FROZEN hashes, output fuzz"
fi

if want 2; then
  step 2 "index freshness (2,000 NovaSeq pairs must mostly map)"
  head -n 8000 $P/novaseq_200k_R1.fq > "$O/s_R1.fq"; head -n 8000 $P/novaseq_200k_R2.fq > "$O/s_R2.fq"
  $LA map "$IDX" "$O/s_R1.fq" "$O/s_R2.fq" "$O/s.sam" 100 1000
  mapped=$(awk '!/^@/ && int($2/4)%2==0' "$O/s.sam" | wc -l); total=$(awk '!/^@/' "$O/s.sam" | wc -l)
  echo "mapped records: $mapped / $total"
  [ $((mapped * 100)) -ge $((total * 85)) ] || fail "under 85% mapped: the index is stale. Rebuild: $LA build GENOME.fa $IDX (~30 min, ~14 GB RAM)"
  echo "ok: index matches this code"
fi

if want 3; then
  step 3 "hg38 fuzz vs minibwa, 3 seeds x 3 modes (~5 min)"
  INDEX="$IDX" MBINDEX="$MBI" MINIBWA="$MB" bash Testing/repro/fuzz_audit.sh "$O/fuzz" > "$O/fuzz.log" 2>&1 || { tail -20 "$O/fuzz.log"; fail "fuzz_audit.sh"; }
  grep -E 'HARD' "$O/fuzz.log" | sort | uniq -c | sed 's/^/  /'
  # lines read "HARD A: <rule>: <count>"
  if grep -qE 'HARD [A-D]:.*: [1-9][0-9]*$' "$O/fuzz.log"; then fail "a HARD rule is nonzero (see $O/fuzz.log)"; fi
  [ "$(grep -cE 'HARD [A-D]:.*: 0$' "$O/fuzz.log")" -gt 0 ] || fail "no HARD lines found (did the audit run?)"
  echo "ok: rules A-D are 0 on every seed and mode"
fi

if want 4; then
  step 4 "unique genome, ours == minibwa (~5 min)"
  : "${SAMTOOLS:?set SAMTOOLS for step 4}"
  bash Testing/unique/run.sh "$O/unique" > "$O/unique.log" 2>&1 || { tail -20 "$O/unique.log"; fail "unique/run.sh"; }
  echo "ok: flagstat equal, columns 1-11 identical"
fi

if want 5; then
  step 5 "speed: $T threads, SAM to /dev/null, index load separate, median of $R"
  : > "$O/empty.fq"; : > "$O/speed.txt"
  med() { sort -g | awk '{a[NR]=$1} END{print a[int((NR+1)/2)]}'; }
  # prints "wall user sys" of a command (bash's time, children included)
  tm() { { TIMEFORMAT='%R %U %S'; time "$@" > /dev/null 2> "$O/err.txt"; } 2>&1 | tail -1; }
  printf "\n%-14s %-8s %8s %8s %9s %10s %12s\n" set tool load_s map_s cpu_s Gbp/hr Gbp/core-hr
  for s in $SETS; do
    r1=$P/${s}_R1.fq; r2=$P/${s}_R2.fq
    bases=$(awk 'NR%4==2{n+=length($0)} END{print n}' "$r1" "$r2")
    for tool in ours minibwa; do
      : > "$O/runs.txt"
      for i in $(seq $R); do
        if [ $tool = ours ]; then
          cat "$IDX" > /dev/null
          load=$(tm taskset -c 0-$((T-1)) $LA map "$IDX" "$O/empty.fq" "$O/empty.fq" /dev/null 100 1000 | cut -d' ' -f1)
          read w u y <<< "$(tm taskset -c 0-$((T-1)) $LA map "$IDX" "$r1" "$r2" /dev/null 100 1000)"
          lcpu=$(tm taskset -c 0-$((T-1)) $LA map "$IDX" "$O/empty.fq" "$O/empty.fq" /dev/null 100 1000 | awk '{print $2+$3}')
        else
          cat $MBI.* > /dev/null
          read w u y <<< "$(tm taskset -c 0-$((T-1)) $MB map -t $T "$MBI" "$r1" "$r2")"
          load=$(grep 'index loaded' "$O/err.txt" | sed 's/.*::\([0-9.]*\)\*\([0-9.]*\)\].*/\1/')
          lcpu=$(grep 'index loaded' "$O/err.txt" | sed 's/.*::\([0-9.]*\)\*\([0-9.]*\)\].*/\1 \2/' | awk '{print $1*$2}')
          [ -n "$load" ] || fail "no 'index loaded' line in minibwa's stderr"
        fi
        echo "$load $(echo "$w $load" | awk '{print $1-$2}') $(echo "$u $y $lcpu" | awk '{print $1+$2-$3}')" >> "$O/runs.txt"
      done
      load=$(cut -d' ' -f1 "$O/runs.txt" | med); map=$(cut -d' ' -f2 "$O/runs.txt" | med); cpu=$(cut -d' ' -f3 "$O/runs.txt" | med)
      printf "%-14s %-8s %8.1f %8.1f %9.1f %10.1f %12.2f\n" $s $tool $load $map $cpu \
        "$(echo "$bases $map" | awk '{print $1/1e9/($2/3600)}')" "$(echo "$bases $cpu" | awk '{print $1/1e9/($2/3600)}')" | tee -a "$O/speed.txt"
    done
  done
  echo
  awk '{k=$1; if($2=="ours"){m[k]=$4; c[k]=$5} else printf "%-14s minibwa/ours: map %.2fx, CPU %.2fx\n", k, $4/m[k], $5/c[k]}' "$O/speed.txt"
  echo "(minibwa paper: 135.8 Gbp/hr on 32 threads, 2x Xeon Gold 6130 = ~4.2 Gbp per thread-hour)"
fi
echo; echo "ALL REQUESTED STEPS PASSED ($STEPS)"
