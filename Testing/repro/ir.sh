#!/bin/bash
# Instruction counts (callgrind Ir) of the shim on the first PAIRS pairs of a set, index load included: the measure of N32_KERNELS / N33_CPU.
# Ir is deterministic: compare two builds by running this with each binary (build each commit first and copy .lake/build/bin/lean-align).
#   bash Testing/repro/ir.sh BINARY SET [PAIRS=2000]        SET = a prefix in Testing/data/prebuilt
set -eu
cd "$(dirname "$0")/../.."
bin=$1; set=$2; n=${3:-2000}; P=Testing/data/prebuilt
d=$(mktemp -d "${TMPDIR:-/tmp}/ir.XXXXXX"); trap 'rm -rf "$d"' EXIT
for r in 1 2; do head -n $((4 * n)) $P/${set}_R$r.fq > "$d/R$r.fq"; done
valgrind --tool=callgrind --callgrind-out-file="$d/cg.out" "$bin" map $P/shim.idx "$d/R1.fq" "$d/R2.fq" "$d/o.sam" 100 1000 2> "$d/err.txt"
grep -E "Collected" "$d/err.txt" | sed "s/^==[0-9]*== //;s/^/$set $n pairs: /"
