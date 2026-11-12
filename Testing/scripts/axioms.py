#!/usr/bin/env python3
"""Read a Lean output log and check its `#print axioms` lines.

    axioms.py LOG                       every theorem uses only the standard axioms
    axioms.py LOG --build NAME ...      also: no errors, no sorry outside Spec/, and each NAME has an axiom line

Standard axioms: propext, Classical.choice, Quot.sound. Exit 1 on any failure."""
import re, sys

STANDARD = {"propext", "Classical.choice", "Quot.sound"}
log, build, need = sys.argv[1], "--build" in sys.argv, sys.argv[3:]
text = open(log).read()
flat = re.sub(r"\s+", " ", text)
uses = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", flat)
plain = re.findall(r"'([^']+)' does not depend on any axioms", flat)

problems = [f"non-standard axioms: {n}: [{a}]" for n, a in uses
            if not {x.strip() for x in a.split(",") if x.strip()} <= STANDARD]
if build:
    problems += re.findall(r"^error.*$|^\S+:\d+:\d+: error.*$", text, re.M)
    problems += [f"sorry outside Spec/: {f}" for f in re.findall(r"^warning: (\S+):\d+:\d+: declaration uses .sorry.", text, re.M)
                 if not f.startswith("Spec/")]
    names = {n for n, _ in uses}
    problems += [f"no axiom line for the headline theorem {n}" for n in need if n not in names]
    if not uses: problems.append("no #print axioms lines at all")
else:
    if re.search(r":\d+:\d+: error", text): problems.append("elaboration error")
    if "sorryAx" in text: problems.append("sorryAx used")

for p in problems: print(f"FAIL {p}")
if problems: sys.exit(1)
print(f"ok   {log.split('/')[-1]}: {len(uses) + len(plain)} theorems, standard axioms only")
