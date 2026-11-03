# Regenerate the per-module table of Testing/notes/CODEMAP.md (written to Testing/notes/codemap_modules.md (paste it into CODEMAP.md §11, then delete it), then pasted).
#   python3 Testing/scripts/codemap_table.py
import re,os,collections
os.chdir(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))
lake=open('lakefile.lean').read()
srcdirs=sorted(set(re.findall(r'srcDir := "([^"]+)"', lake)),key=len,reverse=True)
fs=[]
for d in ['Aligner','Proofs']:
    for root,_,names in os.walk(d):
        fs+=[os.path.join(root,n) for n in names if n.endswith('.lean')]
fs=sorted(fs)
text={f:open(f).read() for f in fs}
defs={}
for f,s in text.items():
    defs[f]=re.findall(r'^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable )?(?:def|abbrev|structure|inductive|class)\s+([A-Za-z_][A-Za-z0-9_\'.!?]*)',s,re.M)
alltok=collections.Counter()
tokby={f:collections.Counter(re.findall(r"[A-Za-z_][A-Za-z0-9_'!?]*",s)) for f,s in text.items()}
def title(s):
    m=re.search(r'/-!\s*\n?\s*#+\s*([^\n]+)',s)
    if m: return m.group(1).strip()
    m=re.search(r'/-!\s*([^\n]+)',s)
    return m.group(1).strip()[:110] if m else ''
rows=[]
for f in fs:
    s=text[f]
    cs=re.findall(r'@\[csimp\]\s*theorem\s+([A-Za-z_][A-Za-z0-9_\'.]*)\s*:\s*@([A-Za-z_][\w.\']*)\s*=\s*@([A-Za-z_][\w.\']*)',s)
    use=[]
    for d in defs[f]:
        short=d.split('.')[-1]
        if len(short)<3: continue
        n=sum(tokby[g][short] for g in fs if g!=f)
        if n: use.append((n,short))
    use=[x for _,x in sorted(use,reverse=True)[:6]]
    rows.append((f,s.count('\n'),title(s),cs,use))
out=[]
cur=None
for f,n,t,cs,use in rows:
    d=os.path.dirname(f)
    if d!=cur:
        out.append(f"\n### {d}/\n"); cur=d
    line=f"- `{os.path.basename(f)}` ({n}) {t}"
    if use: line+=f" Key: {', '.join('`'+u+'`' for u in use)}."
    if cs: line+=" csimp: "+', '.join(f"`{a}`→`{c}`" for _,a,c in cs[:4])+('…' if len(cs)>4 else '')+'.'
    out.append(line)
open('Testing/notes/codemap_modules.md (paste it into CODEMAP.md §11, then delete it)','w').write('\n'.join(out))
print(len(rows), sum(len(l) for l in out))
