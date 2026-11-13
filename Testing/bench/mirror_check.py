#!/usr/bin/env python3
"""Are the Proofs/ copies of the Spec/ files faithful, and are the forbidden words absent?

    python3 Testing/bench/mirror_check.py          (run from anywhere; prints one line per check)

Exit 0 only if every check passes; otherwise it prints FAIL lines and exits 1.

Checked:
 1. Proofs/Fastq.lean is Spec/Fastq.lean up to its two holes: after its import lines, every line before `def parse`
    is the same; `def parse` keeps the spec's signature (the spec has `:= sorry`, the copy any body); the statement of
    `parse_correct` appears word for word (its proof may differ); the copy ends the namespace `Spec.FQ`.
 2. Proofs/Trim.lean is Spec/Trim.lean the same way (import lines ignored), with `def trim` and `theorem trim_correct`.
 3. Proofs/Sam.lean is Spec/Sam.lean exactly, once its imports of Proofs.Answer / Proofs.Fasta / Proofs.Fastq are read
    as Spec.Aligner / Spec.Fasta / Spec.Fastq.
 4. Proofs/MapFiles.lean is Spec/MapFiles.lean line for line (`import Spec.X` read as `import Proofs.X`, extra imports
    allowed), except: a spec line ending in `:= sorry` may be filled with any body (same text up to `:=`); a `sorry`
    proof after `:= by` may be any indented proof; extra declarations may stand just before a `theorem` line.
    `#print axioms` lines in the copy are ignored.
 5. Proofs/Fasta.lean is Spec/Fasta.lean exactly, once `import Proofs.X` is read as `import Spec.X`.
 6. Proofs/Answer.lean, without its first and last line and with `import Proofs.Mapping` read as
    `import Spec.Mapping`, is exactly the part of Spec/Aligner.lean before `/-! ## The index and the aligner`.
 7. Proofs/MapDefs.lean has the same definitions as Proofs/MapFiles.lean: the block from the line
    `-- the mates of every pair` up to (not including) the line starting "-- `process`, run exactly as Main runs it",
    without `end Spec...` lines and without trailing blank lines, is the same in both.
 8. Main.lean has the line `import Proofs.MapFiles`.
 9. Forbidden words (any occurrence, also in comments, as the old grep did):
    - sorry, native_decide, @[extern, unsafe, IO.println, IO.eprintln, "IO.print ", IO.Process, getStdout, getStderr
      in Aligner/PairwiseMain.lean and Aligner/LeanAlign/*.lean;
    - "IO." in Aligner/LeanAlign/*.lean;
    - sorry, native_decide, @[extern, unsafe, implemented_by in Main.lean and the shim files listed in SHIM_FILES.
"""
import glob
import os
import sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))

SHIM_FILES = [
    "Main.lean", "Spec/Fasta.lean", "Proofs/Fasta.lean", "Proofs/Fastq.lean", "Aligner/io/FastqIO.lean",
    "Proofs/Trim.lean", "Proofs/TrimCore.lean", "Proofs/TrimFast.lean", "Proofs/Sam.lean", "Proofs/SamFast.lean",
    "Proofs/SamBytes.lean", "Proofs/MapFast.lean", "Proofs/MapFiles.lean",
]

failures = []


def lines_of(path):
    f = open(os.path.join(ROOT, path))
    text = f.read()
    f.close()
    return text.split("\n")


def report(ok, what):
    if ok:
        print("ok   " + what)
    else:
        print("FAIL " + what)
        failures.append(what)


def first_index(lines, start, test):
    """The first index i >= start with test(lines[i]); None if there is none."""
    i = start
    while i < len(lines):
        if test(lines[i]):
            return i
        i = i + 1
    return None


def contains_block(lines, block):
    """Does `block` appear in `lines` as consecutive lines?"""
    i = 0
    while i + len(block) <= len(lines):
        if lines[i:i + len(block)] == block:
            return True
        i = i + 1
    return False


def def_and_theorem_mirror(spec, body, dname, tname, end_line):
    """Checks 1 and 2: `body` (the copy, imports already removed) mirrors `spec` up to the hole of `def dname` and
    the proof of `theorem tname`. Returns a list of problems (empty: ok)."""
    problems = []
    d = first_index(spec, 0, lambda l: l.startswith("def " + dname + " "))
    assert d is not None, "the spec has no def " + dname
    if body[:d] != spec[:d]:
        problems.append("the lines before `def " + dname + "` differ")
    sig = spec[d]
    if not sig.endswith(":= sorry"):
        problems.append("the spec's `def " + dname + "` is not a hole")
    head = sig[:-len("sorry")].rstrip()
    found = False
    for l in body[d:]:
        if l == head:
            found = True
    if not found:
        problems.append("`def " + dname + "` with the spec's signature is missing")
    t = first_index(spec, 0, lambda l: l.startswith("theorem " + tname + " ") or l == "theorem " + tname)
    assert t is not None, "the spec has no theorem " + tname
    e = first_index(spec, t, lambda l: l.endswith(":= by"))
    assert e is not None, "the spec's theorem " + tname + " has no ':= by'"
    statement = spec[t:e + 1]
    rest = []
    for l in spec[e + 1:]:
        if l.strip() != "":
            rest.append(l.strip())
    if len(rest) != 2 or rest[0] != "sorry" or not rest[1].startswith("end "):
        problems.append("in the spec, more than a `sorry` follows the statement of " + tname)
    if not contains_block(body, statement):
        problems.append("the statement of `" + tname + "` differs")
    if end_line is not None:
        stripped = []
        for l in body:
            stripped.append(l.strip())
        if end_line not in stripped:
            problems.append("the copy does not have `" + end_line + "`")
    return problems


def check_fastq():
    spec = lines_of("Spec/Fastq.lean")
    proofs = lines_of("Proofs/Fastq.lean")
    for l in spec:
        assert not l.startswith("import"), "Spec/Fastq.lean was expected to have no imports"
    start = first_index(proofs, 0, lambda l: not (l.startswith("import") or l == ""))
    assert start is not None
    body = proofs[start:]
    problems = def_and_theorem_mirror(spec, body, "parse", "parse_correct", "end Spec.FQ")
    for p in problems:
        print("     " + p)
    report(problems == [], "Proofs/Fastq.lean mirrors Spec/Fastq.lean (up to the holes)")


def check_trim():
    spec = []
    for l in lines_of("Spec/Trim.lean"):
        if not l.startswith("import "):
            spec.append(l)
    body = []
    for l in lines_of("Proofs/Trim.lean"):
        if not l.startswith("import "):
            body.append(l)
    rest = []
    for l in spec:
        if l.strip() != "":
            rest.append(l.strip())
    end_line = rest[-1] if rest and rest[-1].startswith("end ") else None
    problems = def_and_theorem_mirror(spec, body, "trim", "trim_correct", end_line)
    for p in problems:
        print("     " + p)
    report(problems == [], "Proofs/Trim.lean mirrors Spec/Trim.lean (up to the holes)")


def check_sam():
    copy = []
    for l in lines_of("Proofs/Sam.lean"):
        if l == "import Proofs.Answer":
            l = "import Spec.Aligner"
        elif l == "import Proofs.Fasta":
            l = "import Spec.Fasta"
        elif l == "import Proofs.Fastq":
            l = "import Spec.Fastq"
        copy.append(l)
    report(copy == lines_of("Spec/Sam.lean"), "Proofs/Sam.lean is Spec/Sam.lean (imports read as Spec.)")


def check_mapfiles():
    """Check 4, the same walk as the old holes_mirror.py."""
    spec = []
    for l in lines_of("Spec/MapFiles.lean"):
        if l.startswith("import Spec."):
            l = "import Proofs." + l[len("import Spec."):]
        spec.append(l)
    proofs = []
    for l in lines_of("Proofs/MapFiles.lean"):
        if not l.startswith("#print axioms"):
            proofs.append(l)
    spec_imports = []
    for l in spec:
        if l.startswith("import "):
            spec_imports.append(l)
    problem = None
    p = 0
    while p < len(proofs) and proofs[p].startswith("import ") and proofs[p] not in spec_imports:
        p = p + 1
    i = 0
    while i < len(spec) and problem is None:
        s = spec[i]
        if p >= len(proofs):
            problem = "the copy ends before spec line " + str(i + 1)
            break
        if proofs[p].startswith("import ") and proofs[p] not in spec_imports:
            p = p + 1
            continue
        if s.rstrip().endswith(":= sorry"):
            head = s.rstrip()[:-len("sorry")].rstrip()
            if not proofs[p].startswith(head):
                problem = "the hole at spec line " + str(i + 1) + " is not filled with the same head"
                break
            p = p + 1
            while p < len(proofs) and proofs[p].startswith(" "):
                p = p + 1
            i = i + 1
            continue
        if s.strip() == "sorry" and i > 0 and spec[i - 1].rstrip().endswith(":= by"):
            while p < len(proofs):
                line = proofs[p]
                if not (line.startswith(" ") or line == ""):
                    break
                if line == "" and i + 1 < len(spec) and spec[i + 1] == "":
                    break
                p = p + 1
            i = i + 1
            continue
        if s.startswith("theorem ") and proofs[p] != s:
            q = p
            while q < len(proofs) and proofs[q] != s:
                q = q + 1
            if q == len(proofs):
                problem = "the theorem at spec line " + str(i + 1) + " is missing"
                break
            p = q
        if proofs[p] != s:
            problem = "spec line " + str(i + 1) + " differs: " + repr(s) + " / " + repr(proofs[p])
            break
        i = i + 1
        p = p + 1
    if problem is None:
        for l in proofs[p:]:
            if l.strip() != "":
                problem = "extra text after the spec: " + repr(l)
                break
    if problem is not None:
        print("     " + problem)
    report(problem is None, "Proofs/MapFiles.lean mirrors Spec/MapFiles.lean (up to the holes)")


def check_fasta():
    copy = []
    for l in lines_of("Proofs/Fasta.lean"):
        if l.startswith("import Proofs."):
            l = "import Spec." + l[len("import Proofs."):]
        copy.append(l)
    report(copy == lines_of("Spec/Fasta.lean"), "Proofs/Fasta.lean is Spec/Fasta.lean (imports read as Spec.)")


def check_answer():
    spec = lines_of("Spec/Aligner.lean")
    n = first_index(spec, 0, lambda l: l.startswith("/-! ## The index and the aligner"))
    assert n is not None, "Spec/Aligner.lean has no '/-! ## The index and the aligner' line"
    wanted = spec[:n]
    proofs = lines_of("Proofs/Answer.lean")
    # the file ends with a newline, so the split ends with an empty string that is not a line
    assert proofs[-1] == "", "Proofs/Answer.lean does not end with a newline"
    proofs = proofs[:-1]
    copy = []
    for l in proofs[1:-1]:          # without its first and its last line
        if l == "import Proofs.Mapping":
            l = "import Spec.Mapping"
        copy.append(l)
    report(copy == wanted, "Proofs/Answer.lean is the first part of Spec/Aligner.lean (up to the index and the aligner)")


def mapdefs_block(path):
    lines = lines_of(path)
    start = first_index(lines, 0, lambda l: l.startswith("-- the mates of every pair"))
    assert start is not None, path + " has no '-- the mates of every pair' line"
    block = []
    i = start
    while i < len(lines):
        l = lines[i]
        if l.startswith("-- `process`, run exactly as Main runs it"):
            break
        if not l.startswith("end Spec"):
            block.append(l)
        i = i + 1
    while block and block[-1].strip() == "":
        block.pop()
    return block


def check_mapdefs():
    report(mapdefs_block("Proofs/MapFiles.lean") == mapdefs_block("Proofs/MapDefs.lean"),
           "Proofs/MapDefs.lean has the same definitions as Proofs/MapFiles.lean")


def check_main_import():
    report("import Proofs.MapFiles" in lines_of("Main.lean"), "Main.lean imports Proofs.MapFiles")


def find_words(paths, words):
    """Every (file, line number, line) where one of `words` occurs."""
    hits = []
    for path in paths:
        number = 0
        for l in lines_of(path):
            number = number + 1
            for w in words:
                if w in l:
                    hits.append((path, number, l))
                    break
    return hits


def check_forbidden():
    executables = ["Aligner/PairwiseMain.lean"]
    library = []
    for path in sorted(glob.glob(os.path.join(ROOT, "Aligner/LeanAlign/*.lean"))):
        library.append(os.path.relpath(path, ROOT))
    hits1 = find_words(executables + library, ["sorry", "native_decide", "@[extern", "unsafe", "IO.println",
                                               "IO.eprintln", "IO.print ", "IO.Process", "getStdout", "getStderr"])
    hits2 = find_words(library, ["IO."])
    hits3 = find_words(SHIM_FILES, ["sorry", "native_decide", "@[extern", "unsafe", "implemented_by"])
    for h in hits1 + hits2 + hits3:
        print("     " + h[0] + ":" + str(h[1]) + ": " + h[2])
    report(hits1 == [], "no forbidden word in the executables (PairwiseMain, LeanAlign/)")
    report(hits2 == [], "no IO in the pure library LeanAlign/")
    report(hits3 == [], "no sorry / native_decide / @[extern / unsafe / implemented_by in Main.lean and the shim files")


check_fastq()
check_trim()
check_sam()
check_mapfiles()
check_fasta()
check_answer()
check_mapdefs()
check_main_import()
check_forbidden()
if failures:
    print("MIRROR CHECK FAILED")
    sys.exit(1)
print("MIRROR CHECK PASSED")
