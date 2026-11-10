#!/usr/bin/env python3
"""A Proofs/ copy mirrors a Spec/ draft up to one def hole and one proof hole.
   draft_mirror.py SPEC PROOFS DEF THEOREM

Without their import lines: the copy has every spec line before `def DEF` unchanged, then `def DEF` with the same
signature (its body may differ, lemmas may follow), and the statement of THEOREM word for word (its proof may
differ). The spec's `def DEF` must be `:= sorry`, and after THEOREM's statement only `sorry` and `end ...`.
Exit 1 on any difference."""
import sys

spec_f, proofs_f, dname, tname = sys.argv[1:5]
noimp = lambda ls: [l for l in ls if not l.startswith("import ")]
spec = noimp(open(spec_f).read().split("\n"))
body = noimp(open(proofs_f).read().split("\n"))
bad = []
d = next(i for i, l in enumerate(spec) if l.startswith(f"def {dname} "))
if body[:d] != spec[:d]:
    bad.append(f"the lines before `def {dname}` differ")
sig = spec[d]
if not sig.endswith(":= sorry"): bad.append(f"{spec_f}: `def {dname}` is not a hole")
if not any(l == sig[: -len("sorry")].rstrip() for l in body[d:]):
    bad.append(f"`def {dname}` with the spec's signature is missing")
t = next(i for i, l in enumerate(spec) if l.startswith(f"theorem {tname} "))
e = next(i for i in range(t, len(spec)) if spec[i].endswith(":= by"))
stmt = spec[t : e + 1]
rest = [l.strip() for l in spec[e + 1 :] if l.strip()]
if len(rest) != 2 or rest[0] != "sorry" or not rest[1].startswith("end "):
    bad.append(f"{spec_f}: after the statement of `{tname}` comes more than its `sorry` hole")
if not any(body[i : i + len(stmt)] == stmt for i in range(len(body))):
    bad.append(f"the statement of `{tname}` differs")
if rest and rest[-1] not in [l.strip() for l in body]: bad.append(f"{proofs_f} does not `{rest[-1]}`")
for b in bad: print(f"FAIL {b}")
sys.exit(1 if bad else 0)
