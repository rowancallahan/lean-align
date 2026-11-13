#!/usr/bin/env python3
"""How many mason pairs does each tool put at the true place?   mason_score.py truth.sam ours.sam minibwa.sam

truth.sam is mason's -oa file (one record per mate, the true place). The rule of the minibwa paper: a mate is correct if
it is on the true chromosome and intersection / union of the aligned and the true interval is at least 10 %;
a pair is correct if both mates are. Only the pairs that are in ours.sam are scored (the sample can be smaller than the set)."""
import re
import sys


def places(path):
    """(read name, mate 1 or 2) -> (chromosome, start, end) of the primary record; None if the mate is unmapped"""
    result = {}
    for line in open(path):
        if line[0] == "@":
            continue
        f = line.split("\t")
        flag = int(f[1])
        if flag & 0x900:                                   # secondary or supplementary
            continue
        mate = 1 if flag & 64 else 2
        if flag & 4:
            result[f[0], mate] = None
            continue
        length = sum(int(n) for n in re.findall(r"(\d+)[MDN=X]", f[5]))
        result[f[0], mate] = (f[2], int(f[3]), int(f[3]) + length)
    return result


def is_correct(found, true):
    if found is None or found[0] != true[0]:
        return False
    intersection = min(found[2], true[2]) - max(found[1], true[1])
    union = max(found[2], true[2]) - min(found[1], true[1])
    return intersection > 0 and intersection / union >= 0.1


truth = places(sys.argv[1])
for tool, path in (("ours", sys.argv[2]), ("minibwa", sys.argv[3])):
    found = places(path)
    names = sorted({name for name, mate in found})
    mapped = 0
    correct = 0
    for name in names:
        if found[name, 1] is not None and found[name, 2] is not None:
            mapped += 1
        if is_correct(found[name, 1], truth[name, 1]) and is_correct(found[name, 2], truth[name, 2]):
            correct += 1
    print(tool, len(names), "pairs scored,",
          mapped, "of", len(names), "=", round(100 * mapped / len(names), 2), "% have both mates mapped,",
          correct, "of", len(names), "=", round(100 * correct / len(names), 2), "% pairs correct")
