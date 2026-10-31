#!/usr/bin/env python3
"""Scan the generated C (.lake/build/ir/**/*.c) for loop-shape costs.
   python3 scripts/cscan.py [root_fn_substring=tierPair] [top=60] [ir_dir=.lake/build/ir]
Splits every .c file into functions, builds a call graph over the generated
functions, keeps those reachable from functions whose C name contains the root
substring, and counts per function:
  nat   lean_nat_* calls (incl. lean_nat_big_*) and Nat-literal helpers
  big   lean_nat_big_* / lean_cstr_to_nat / lean_uint64_to_nat (bignum or boxing paths)
  panic checked Nat-index access: a[i]! (lean_array_get[_borrowed], lean_byte_array_get,
        each a bounds test + panic path) and Array size reads (lean_array_get_size, a boxed Nat)
  rc    lean_inc*/lean_dec* reference-count ops
  clo   lean_alloc_closure + lean_apply_* (closure creation / calls)
  alloc lean_alloc_ctor / lean_alloc_object / array/bytearray push/mk
  box   lean_box_uint64 / lean_unbox_uint64 (boxed UInt64 elements)
  loop  1 if the function is a loop (`goto _start`, a compiled tail call)
Score = nat + 3*big + 2*panic + rc + 4*clo + 4*alloc + 2*box, x4 for loops.
Prints the ranked table and per-module totals."""
import os, re, sys
from collections import defaultdict

root = sys.argv[1] if len(sys.argv) > 1 else "tierPair"
top = int(sys.argv[2]) if len(sys.argv) > 2 else 60
ird = sys.argv[3] if len(sys.argv) > 3 else ".lake/build/ir"
assert os.path.isdir(ird), ird

FN = re.compile(r"^(?:LEAN_EXPORT |static )*(?:lean_object\*|[a-z_0-9]+) ((?:_init_)?(?:lp|l)_[A-Za-z0-9_]+)\(([^)]*)\) ?\{$", re.M)
PAT = {
    "nat": re.compile(r"\blean_nat_\w+\("),
    "big": re.compile(r"\b(lean_nat_big_\w+|lean_cstr_to_nat|lean_uint64_to_nat|lean_usize_to_nat|lean_big_\w+)\("),
    "panic": re.compile(r"\b(lean_array_get_panic|lean_panic_fn|lean_array_get_borrowed|lean_array_get|lean_byte_array_get|lean_array_get_size)\("),
    "rc": re.compile(r"\blean_(inc|dec)(_ref|_ref_n|_n)?\("),
    "clo": re.compile(r"\b(lean_alloc_closure|lean_apply_\w+)\("),
    "alloc": re.compile(r"\b(lean_alloc_ctor|lean_alloc_object|lean_array_push|lean_byte_array_push|lean_mk_empty_array\w*|lean_alloc_sarray|lean_mk_array|lean_array_mk)\("),
    "box": re.compile(r"\b(lean_box_uint64|lean_unbox_uint64)\("),
}
CALL = re.compile(r"\b((?:lp|l)_[A-Za-z0-9_]+)\(")

funcs = {}  # name -> (module, body)
for dp, _, fs in os.walk(ird):
    for f in fs:
        if not f.endswith(".c"): continue
        p = os.path.join(dp, f)
        src = open(p, errors="replace").read()
        mod = os.path.relpath(p, ird)[:-2].replace("/", ".")
        ms = list(FN.finditer(src))
        for i, m in enumerate(ms):
            end = ms[i + 1].start() if i + 1 < len(ms) else len(src)
            name = m.group(1)
            if name.startswith("_init_"): continue
            funcs[name] = (mod, src[m.end():end])
assert funcs, "no generated C found; run lake build first"

graph = {n: set(CALL.findall(b)) & funcs.keys() for n, (_, b) in funcs.items()}
seen, todo = set(), [n for n in funcs if root in n]
assert todo, f"no function contains {root!r}"
while todo:
    n = todo.pop()
    if n in seen: continue
    seen.add(n)
    todo.extend(graph[n] - seen)

rows = []
for n in seen:
    mod, b = funcs[n]
    c = {k: len(r.findall(b)) for k, r in PAT.items()}
    c["loop"] = 1 if "goto _start" in b else 0
    s = c["nat"] + 3 * c["big"] + 2 * c["panic"] + c["rc"] + 4 * c["clo"] + 4 * c["alloc"] + 2 * c["box"]
    rows.append((s * (4 if c["loop"] else 1), n, mod, c))
rows.sort(reverse=True)

def demangle(n):
    n = re.sub(r"^lp_lean__align_|^l_", "", n)
    return n.replace("___", ".").replace("__", "_")

print(f"generated C: {len(funcs)} functions; reachable from *{root}*: {len(seen)}")
print(f"{'score':>6} {'loop':>4} {'nat':>4} {'big':>4} {'pnc':>4} {'rc':>4} {'clo':>4} {'alc':>4} {'box':>4}  function  [module]")
for s, n, mod, c in rows[:top]:
    print(f"{s:>6} {c['loop']:>4} {c['nat']:>4} {c['big']:>4} {c['panic']:>4} {c['rc']:>4} {c['clo']:>4} {c['alloc']:>4} {c['box']:>4}  {demangle(n)}  [{mod}]")
tot = defaultdict(lambda: defaultdict(int))
for s, n, mod, c in rows:
    for k, v in c.items(): tot[mod][k] += v
    tot[mod]["score"] += s
print("\nper module (reachable functions only):")
for mod, c in sorted(tot.items(), key=lambda kv: -kv[1]["score"])[:25]:
    print(f"{c['score']:>7}  nat {c['nat']:>5} big {c['big']:>4} panic {c['panic']:>4} rc {c['rc']:>5} clo {c['clo']:>4} alloc {c['alloc']:>4} box {c['box']:>4} loops {c['loop']:>3}  {mod}")
