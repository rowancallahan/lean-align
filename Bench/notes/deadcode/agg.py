import os,re,sys,collections
root,tsv=sys.argv[1],sys.argv[2]
files={}
for d,_,fs in os.walk(root):
    if '/.lake' in d or '/.git' in d or 'new_spec' in d or '/bench' in d: continue
    for f in fs:
        if f.endswith('.lean'): files.setdefault(f[:-5],[]).append(os.path.relpath(os.path.join(d,f),root))
decl_re=re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+)*(def|theorem|lemma|abbrev|structure|inductive|instance|class)\s+([\w\'.₀-₉]+)',re.M)
src={}
for m,ps in files.items():
    if len(ps)!=1: continue
    s=open(os.path.join(root,ps[0]),errors='ignore').read()
    src[m]=(ps[0],{n.split('.')[-1]:k for k,n in decl_re.findall(s)})
stat=collections.defaultdict(lambda: collections.Counter()); deadnames=collections.defaultdict(list)
for line in open(tsv):
    parts=line.rstrip('\n').split('\t')
    if len(parts)!=3: continue
    mod,n,tag=parts
    if mod not in src: continue
    if '_private' in n or re.search(r'\.(_|match_|proof_|eq_\d|eq_def|induct|fun_cases|splitter|rec|recOn|casesOn|noConfusion|below|brecOn|binductionOn|ibelow|injEq|inj|sizeOf_spec|mk\.)',n): continue
    last=n.split('.')[-1]
    kind=src[mod][1].get(last)
    if kind is None: continue
    k='thm' if kind in('theorem','lemma') else 'def'
    stat[mod][(k,tag)]+=1
    if tag=='-': deadnames[mod].append((k,n))
rows=[]
for mod,c in stat.items():
    path=src[mod][0]; lines=sum(1 for _ in open(os.path.join(root,path),errors='ignore'))
    live=c[('def','R')]+c[('def','P')]+c[('thm','R')]+c[('thm','P')]; dead=c[('def','-')]+c[('thm','-')]
    rows.append((path,lines,c[('def','R')],c[('def','P')],c[('def','-')],c[('thm','P')]+c[('thm','R')],c[('thm','-')],live,dead))
rows.sort()
import json; json.dump({'rows':rows,'dead':deadnames},open(sys.argv[3],'w'))
tot=collections.Counter()
for r in rows:
    tot['lines']+=r[1]; 
    if r[7]==0: tot['deadfiles']+=1; tot['deadlines']+=r[1]
print("files with ZERO live declarations:")
for r in rows:
    if r[7]==0: print(f"  {r[1]:5d}  {r[0]}")
print(f"  total {tot['deadfiles']} files, {tot['deadlines']} lines")
print("\nfiles partly live (defs run/proof-only/dead, thms used/dead):")
for r in rows:
    if r[7]>0 and r[8]>0: print(f"  {r[1]:5d}  {r[0]:45s} defs {r[2]}/{r[3]}/{r[4]}  thms {r[5]}/{r[6]}")
