#!/usr/bin/env python3
"""A Proofs/ copy mirrors its Spec/ file up to the holes.   holes_mirror.py SPEC PROOFS

The copy is the Spec text line for line, with `import Spec.X` read as `import Proofs.X` (extra imports allowed), and:
* a line ending in `:= sorry` (a definition hole) may be filled: the copy has the same line up to `:=`, then any
  body, on that line and on the indented lines after it;
* a `sorry` line that is the proof of a theorem (after a line ending in `:= by`) may be any indented proof;
* extra declarations may stand just before a `theorem` line (lemmas for its proof).
Exit 1 on any difference."""
import sys

spec = open(sys.argv[1]).read().split("\n")
proofs = [l for l in open(sys.argv[2]).read().split("\n") if not l.startswith("#print axioms")]
imp = lambda l: l.replace("import Spec.", "import Proofs.", 1) if l.startswith("import Spec.") else l
spec = [imp(l) for l in spec]
p = 0
# extra imports at the top of the copy
spec_imports = [l for l in spec if l.startswith("import ")]
while p < len(proofs) and proofs[p].startswith("import ") and proofs[p] not in spec_imports:
    p += 1

def fail(msg):
    print(f"FAIL {sys.argv[2]}: {msg}")
    sys.exit(1)

indented = lambda l: l.startswith(" ") or l == ""
i = 0
while i < len(spec):
    s = spec[i]
    if p >= len(proofs):
        fail(f"ends before spec line {i + 1}: {s!r}")
    if proofs[p].startswith("import ") and proofs[p] not in spec_imports:
        p += 1; continue
    if s.rstrip().endswith(":= sorry"):
        head = s.rstrip()[: -len("sorry")].rstrip()
        if not proofs[p].startswith(head):
            fail(f"hole at spec line {i + 1} not filled with the same head: {proofs[p]!r}")
        p += 1
        while p < len(proofs) and proofs[p].startswith(" "):
            p += 1
        i += 1; continue
    if s.strip() == "sorry" and i > 0 and spec[i - 1].rstrip().endswith(":= by"):
        while p < len(proofs) and indented(proofs[p]) and not (proofs[p] == "" and i + 1 < len(spec) and spec[i + 1] == ""):
            p += 1
        i += 1; continue
    if s.startswith("theorem ") and proofs[p] != s:
        # extra declarations before a theorem
        q = p
        while q < len(proofs) and proofs[q] != s:
            q += 1
        if q == len(proofs):
            fail(f"theorem at spec line {i + 1} missing: {s!r}")
        p = q
    if proofs[p] != s:
        fail(f"differs at spec line {i + 1}: spec {s!r} / copy {proofs[p]!r}")
    i += 1; p += 1
rest = [l for l in proofs[p:] if l.strip() and not l.startswith("#print axioms")]
if rest:
    fail(f"extra text after the spec: {rest[0]!r}")
