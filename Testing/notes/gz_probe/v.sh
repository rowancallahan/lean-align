#!/bin/bash
# v.sh LABEL BIN R1GZ R2GZ ZPIN(0/1) SINK(cat/md5) WRAP(tl/none)
L=$1; BIN=$2; Z1=$3; Z2=$4; ZP=$5; SK=$6; W=$7
T=${T:?dir holding samp.py}; I=${I:?index}; R=${R:?repo with Testing/scripts/timed_load.py}
rm -f $T/a $T/b $T/o $T/o.tmp; S=$T/o.tmp; case $BIN in *fb2*|*festive*) S=$T/o;; esac
mkfifo $T/a $T/b $S
cat $I > /dev/null
pre=""; [ $ZP = 1 ] && pre="taskset -c 0-3"
$pre zcat $Z1 > $T/a & $pre zcat $Z2 > $T/b &
if [ $SK = cat ]; then cat < $S > /dev/null & else md5sum < $S > $T/md5 & fi
python3 -I $T/samp.py $(basename $BIN | cut -c1-15) $T/samp.out &
if [ $W = tl ]; then r=$(taskset -c 0-3 python3 $R/Testing/scripts/timed_load.py "$L" $BIN map $I $T/a $T/b $T/o 100 1000 | sed 's/.*: wall/wall/; s/, load.*//')
else s=$(date +%s.%N); taskset -c 0-3 $BIN map $I $T/a $T/b $T/o 100 1000; r="wall $(echo "$(date +%s.%N) - $s" | bc | cut -c1-6)"; fi
wait
echo "RES $L | $r"; cat $T/samp.out
rm -f $T/a $T/b $T/o $T/o.tmp
