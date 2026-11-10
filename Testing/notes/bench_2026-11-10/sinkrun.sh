#!/bin/bash
# sinkrun.sh LABEL T BIN R1 R2 : OUT is a FIFO drained by cat. mapfiles writes OUT.tmp then renames, so for it the FIFO is OUT.tmp.
R=/home/user/lean-align; I=/root/idx/ic.idx; F=/root/fifo-out; mkdir -p $F; rm -f $F/o $F/o.tmp
case $3 in *mapfiles*) S=$F/o.tmp;; *) S=$F/o;; esac
mkfifo $S
cat < $S > /dev/null &
SK=$!
taskset -c 0-$(($2-1)) python3 $R/Testing/scripts/timed_load.py "$1" $3 map $I $4 $5 $F/o 100 1000
rc=$?; wait $SK; rm -f $F/o; exit $rc
