#!/usr/bin/env python3
"""core_c.py LEAN_PREFIX OUTDIR ROOT...  writes OUTDIR/<Mod>.c for every module in the import closure of ROOTs,
using LEAN_PREFIX/bin/lean -c on LEAN_PREFIX/src/lean. Prints the module list to OUTDIR/modules.txt."""
import os, re, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
prefix, out, roots = sys.argv[1], sys.argv[2], sys.argv[3:]
src = f"{prefix}/src/lean"
imp = re.compile(r"^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.]+)", re.M)
def path(m):
    p = f"{src}/{m.replace('.', '/')}.lean"
    assert os.path.exists(p), p
    return p
seen, todo = set(), list(roots)
while todo:
    m = todo.pop()
    if m in seen: continue
    seen.add(m)
    todo += imp.findall(open(path(m)).read())
mods = sorted(seen)
os.makedirs(out, exist_ok=True)
open(f"{out}/modules.txt", "w").write("\n".join(mods) + "\n")
def one(m):
    c = f"{out}/{m}.c"
    if not os.path.exists(c):
        subprocess.run([f"{prefix}/bin/lean", "-R", src, "-c", c + ".tmp", path(m)], check=True, stdout=subprocess.DEVNULL)
        os.rename(c + ".tmp", c)
with ThreadPoolExecutor(os.cpu_count()) as ex:
    list(ex.map(one, mods))
print(len(mods), "modules")
