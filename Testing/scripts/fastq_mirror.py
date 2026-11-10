#!/usr/bin/env python3
"""Proofs/Fastq.lean mirrors Spec/Fastq.lean up to the holes.   fastq_mirror.py SPEC PROOFS

Spec/Fastq.lean has two holes: `def parse ... := sorry` and the proof of `parse_correct` (`:= by` then `sorry`).
Proofs/Fastq.lean must be: its imports, then every line of the spec before `def parse` unchanged, then `def parse`
with the same signature, and the statement of `parse_correct` word for word (its proof may differ), inside the
same namespace. Exit 1 on any difference."""
import sys

spec = open(sys.argv[1]).read().split("\n")
proofs = open(sys.argv[2]).read().split("\n")
bad = []
assert not any(l.startswith("import") for l in spec), "Spec/Fastq.lean has no imports"
body = proofs[next(i for i, l in enumerate(proofs) if not (l.startswith("import") or l == "")):]
d = next(i for i, l in enumerate(spec) if l.startswith("def parse "))
if body[:d] != spec[:d]:
    bad.append("the lines before `def parse` differ")
sig = spec[d]
if not sig.endswith(":= sorry"): bad.append("Spec/Fastq.lean: `def parse` is not a hole")
if not any(l == sig[: -len("sorry")].rstrip() for l in body[d:]):
    bad.append("`def parse` with the spec's signature is missing")
t = next(i for i, l in enumerate(spec) if l.startswith("theorem parse_correct"))
e = next(i for i in range(t, len(spec)) if spec[i].endswith(":= by"))
stmt = spec[t : e + 1]
if [l.strip() for l in spec[e + 1 :] if l.strip()] != ["sorry", "end Spec.FQ"]:
    bad.append("Spec/Fastq.lean: after the statement of `parse_correct` comes more than its `sorry` hole")
if not any(body[i : i + len(stmt)] == stmt for i in range(len(body))):
    bad.append("the statement of `parse_correct` differs")
if "end Spec.FQ" not in body: bad.append("Proofs/Fastq.lean does not end the namespace Spec.FQ")
for b in bad: print(f"FAIL {b}")
sys.exit(1 if bad else 0)
