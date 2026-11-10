#!/bin/bash
# usage: run.sh LABEL SET(n1m|h1m) [ENV=VAL ...]   -> res/LABEL.{log,md5,time}
L=$1; SET=$2; shift 2
S=/home/user/S; BIN=${BIN:-$S/bin/instr}
cat $S/idx/ic.idx $S/p1m/${SET}_R1.fq $S/p1m/${SET}_R2.fq > /dev/null
rm -f $S/fifo/o; mkfifo $S/fifo/o
md5sum < $S/fifo/o > $S/res/$L.md5 &
env "$@" python3 $S/timed.py $L $BIN map $S/idx/ic.idx $S/p1m/${SET}_R1.fq $S/p1m/${SET}_R2.fq $S/fifo/o 100 1000 2> $S/res/$L.log
wait
