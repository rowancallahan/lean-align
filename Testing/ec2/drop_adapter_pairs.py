#!/usr/bin/env python3
"""Drop simulated pairs that our adapter rule would cut.   drop_adapter_pairs.py IN_R1.fq IN_R2.fq OUT_R1.fq OUT_R2.fq
Our tool cuts a read where the adapter AGATCGGAAGAGC starts (all 13 letters with at most 1 mismatch, or its first
6 or more letters exactly at the read's end; Spec/Trim.lean `cut`). minibwa does not cut. Random reads hit this
rule by chance about once in 1,500 pairs, so those pairs are left out of the "identical output" check."""
import sys
ADAPTER = "AGATCGGAAGAGC"
def is_cut(read):
    for i in range(len(read)):
        rest = read[i:]
        if len(rest) >= len(ADAPTER):
            if sum(a != b for a, b in zip(ADAPTER, rest)) <= 1: return True
        elif len(rest) >= 6 and rest == ADAPTER[:len(rest)]: return True
    return False
in1, in2, out1, out2 = (open(p, "w" if i > 1 else "r") for i, p in enumerate(sys.argv[1:5]))
kept = dropped = 0
while True:
    a = [in1.readline() for _ in range(4)]; b = [in2.readline() for _ in range(4)]
    if not a[0]: break
    if is_cut(a[1].strip()) or is_cut(b[1].strip()): dropped += 1; continue
    out1.writelines(a); out2.writelines(b); kept += 1
print(f"kept {kept} pairs, dropped {dropped} that the adapter rule would cut")
