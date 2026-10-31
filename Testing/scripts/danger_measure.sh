#!/bin/bash
# n29 danger regions, step 1 (Testing/notes/DANGER_REGIONS_N29.md), on one genome and its read sets:
#   bash Testing/scripts/danger_measure.sh GENOME.fa WGPREFIX OUTDIR name:R1prefix ...
# GENOME.fa: the genome the bench index WGPREFIX was built from (whole_genome build WGPREFIX GENOME.fa, then
# the WG_CHECK=1 step); name:R1prefix e.g. mason:Testing/data/downloads/chr21_mason (reads <prefix>_R1.fq/_R2.fq).
# Writes OUTDIR/dup150.mask and per set: tie / danger tallies, CPU of tie vs other and flagged vs other pairs
# (median of 3), and the twin prototype's fires plus a dump identity check (WG_TWIN on vs off).
set -eu
G=$1; WG=$2; O=$3; shift 3
B=.lake/build/bin; T=${TASKS:-4}; C=0-$((T - 1))
mkdir -p "$O"
python3 Testing/benches/dup_mask.py "$G" 150 "$O/dup150.mask"
cpu() {  # label R1 R2 [env...]: median CPU of 3 bench runs
  l=$1; a=$2; b=$3; shift 3
  for i in 1 2 3; do env "$@" WG_XH=0 WG_MODES=RTX WG_TASKS=$T WG_READS="x=$a:$b:0" taskset -c $C $B/whole_genome pmap "$WG" "$G" 2>/dev/null |
    grep RESULT | sed 's/.*cpu \([0-9.]*\) s.*/\1/'; done | sort -n | sed -n 2p | sed "s/^/CPU $l /"
}
for s in "$@"; do n=${s%%:*}; p=${s#*:}; r1=${p}_R1.fq; r2=${p}_R2.fq
  for d in base twin; do mkdir -p "$O/$d"; done
  WG_DANGER="$O/dup150.mask" WG_XH=0 WG_MODES=RTX WG_TASKS=$T WG_TIEROUT=1 WG_OUT="$O/base" WG_READS="$n=$r1:$r2:0" \
    taskset -c $C $B/whole_genome pmap "$WG" "$G" >/dev/null 2>&1
  WG_TWIN=2 WG_XH=0 WG_MODES=RTX WG_TASKS=$T WG_TIEROUT=1 WG_OUT="$O/twin" WG_READS="$n=$r1:$r2:0" \
    taskset -c $C $B/whole_genome pmap "$WG" "$G" >/dev/null 2>&1
  echo "== $n: pairs by flag (both mates all-danger / one / none), tie or other, final tag"
  paste <(cut -f2- "$O/base/danger_$n.tsv") <(cut -f2,33 "$O/base/tiers_$n.tsv") | awk -F'\t' '{f1=($1>0&&$1==$2); f2=($3>0&&$3==$4)
    print ((f1&&f2)?"both":((f1||f2)?"one":"none")), (($6 ~ /tie/)?"tie":"other"), $5}' | sort | uniq -c | sort -k2,2 -k3,3 -k1,1rn
  echo "== $n: twin prototype (w fired, n no twin, o no t2Opt), tie pairs only: base tag, twin tag"
  paste <(cut -f2,33 "$O/base/tiers_$n.tsv") <(cut -f2 "$O/twin/tiers_$n.tsv") | awk -F'\t' '$2 ~ /tie/ {print $1, $3}' | sort | uniq -c | sort -rn
  mkdir -p "$O/twin1_$n"
  WG_TWIN=1 WG_XH=0 WG_MODES=RTX WG_TASKS=$T WG_TIEROUT=1 WG_OUT="$O/twin1_$n" WG_READS="$n=$r1:$r2:0" \
    taskset -c $C $B/whole_genome pmap "$WG" "$G" >/dev/null 2>&1
  cmp "$O/base/tiers_$n.tsv" "$O/twin1_$n/tiers_$n.tsv" && cmp "$O/base/RTX_$n.tsv" "$O/twin1_$n/RTX_$n.tsv" && echo "$n: WG_TWIN=1 dumps identical"
  python3 Testing/benches/split_by_dump.py tie "$O/base/tiers_$n.tsv" "$r1" "$r2" "$O/$n"
  python3 Testing/benches/split_by_dump.py danger "$O/base/danger_$n.tsv" "$r1" "$r2" "$O/$n"
  for k in tie rest dng safe; do echo "$k pairs: $(($(wc -l < "$O/${n}_${k}_R1.fq") / 4))"; cpu "$n $k" "$O/${n}_${k}_R1.fq" "$O/${n}_${k}_R2.fq"; done
  cpu "$n all" "$r1" "$r2"
  cpu "$n all WG_TWIN=1" "$r1" "$r2" WG_TWIN=1
  rm -f "$O/${n}"_*_R?.fq
done
