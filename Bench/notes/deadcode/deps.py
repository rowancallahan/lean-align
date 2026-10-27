import os, re, sys
root = sys.argv[1]; starts = sys.argv[2].split(',')
mods = {}
for d, _, fs in os.walk(root):
    if '/.lake' in d or '/.git' in d or '/new_spec' in d: continue
    for f in fs:
        if f.endswith('.lean'):
            p = os.path.join(d, f); rel = os.path.relpath(p, root)
            top = rel.split('/')[0]
            # module name = path relative to its lib srcDir; approximate by basename / nested path
            if rel.startswith(('spec/','codecs/','bench/','checks/')): name = rel.split('/',1)[1][:-5].replace('/','.')
            elif rel.startswith('pool/'): name = rel.split('/',2)[2][:-5].replace('/','.')
            elif rel.startswith('trimmer/'): name = rel.split('/',1)[1][:-5].replace('/','.')
            else: name = rel[:-5].replace('/','.')
            imps = re.findall(r'^\s*import\s+([\w.]+)', open(p, errors='ignore').read(), re.M)
            mods[name] = (rel, imps)
seen=set(); stack=list(starts)
while stack:
    m=stack.pop()
    if m in seen or m not in mods: continue
    seen.add(m); stack += mods[m][1]
def lines(rel): return sum(1 for _ in open(os.path.join(root,rel), errors='ignore'))
for grp in ['codecs/','pool/','spec/']:
    dead=[(mods[m][0], lines(mods[m][0])) for m in mods if mods[m][0].startswith(grp) and m not in seen]
    live=[(mods[m][0], lines(mods[m][0])) for m in mods if mods[m][0].startswith(grp) and m in seen]
    print(f"== {grp}: live {len(live)} files {sum(l for _,l in live)} lines; not reached {len(dead)} files {sum(l for _,l in dead)} lines")
    for r,l in sorted(dead): print(f"   {l:6d} {r}")
