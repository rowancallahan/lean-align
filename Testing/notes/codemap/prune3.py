import re,os,sys,subprocess,collections,json
os.chdir('/home/user/lean-align')
area=sys.argv[1:]
lake=open('lakefile.lean').read()
srcdirs=set(re.findall(r'srcDir := "([^"]+)"', lake))|{'.'}
def path(m):
    for d in srcdirs:
        p=os.path.join(d,*m.split('.'))+'.lean'
        if os.path.exists(p): return os.path.normpath(p)
dead=collections.defaultdict(list); live=collections.defaultdict(list)
for l in open('/tmp/claude-0/codemap/all_decls.txt'):
    m,n,a,b,st=l.split()
    if a=='?': continue
    f=path(m)
    if not f or not any(f.startswith(x) for x in area) or '/kernels/wfa' in f or '/ReadWindowTrimmer/' in f: continue
    (dead if st=='DEAD' else live)[f].append((int(a),int(b),n))
PJ='/tmp/claude-0/codemap/protect.json'
protect=set(json.load(open(PJ))) if os.path.exists(PJ) else set()
orig={}
for f in dead:
    subprocess.run(['git','checkout','--',f]); orig[f]=open(f).read().split('\n')
DECL=re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:private |protected |noncomputable |partial |unsafe )*(theorem|lemma|def|abbrev|instance|structure|inductive|class)\b')
def plan(f):
    L=orig[f]
    lv=set()
    for a,b,n in live[f]: lv|=set(range(a,b+1))
    rm=set(); gone={}
    for a,b,n in dead[f]:
        short=n.split('.')[-1]
        if n in protect: continue
        if re.match(r'^\s*(?:@\[[^\]]*\]\s*)*(?:private |protected )*(instance|structure|inductive|class)\b', L[a-1]) or short.startswith('inst'): continue
        rng=set(range(a,b+1))
        if rng & lv: continue
        s=a
        while s-1>=1:
            prev=L[s-2].strip()
            if prev.startswith('@[') or (prev.split()[:1] in (['set_option'], ['omit'], ['include'], ['open']) and prev.endswith(' in')): s-=1; continue
            if prev.endswith('-/'):
                k=s-1
                while k>=1 and not L[k-1].lstrip().startswith('/-'): k-=1
                if k>=1 and L[k-1].lstrip().startswith('/--') and not (set(range(k,s))&lv): s=k; continue
            break
        rm|=set(range(s,b+1)); gone[n]=short
    return rm,gone
def write():
    allgone={}
    for f in dead:
        rm,gone=plan(f); allgone.update(gone)
        out=[x for i,x in enumerate(orig[f],1) if i not in rm]
        out=[x for x in out if not (x.startswith('#print axioms ') and x.split()[2].split('.')[-1] in set(gone.values()))]
        open(f,'w').write(re.sub(r'\n{3,}','\n\n','\n'.join(out)))
    return allgone
it=0
while True:
    it+=1
    gone=write()
    r=subprocess.run('lake build 2>&1 | grep -E "^error: [^ ]+\\.lean:[0-9]+"',shell=True,capture_output=True,text=True,env=dict(os.environ,PATH=os.path.expanduser('~/.elan/bin')+':'+os.environ['PATH']))
    errs=re.findall(r'^error: ([^:]+\.lean):(\d+):\d+: (.*)$',r.stdout,re.M)
    print(f"iter {it}: removed {len(gone)} decls, {len(errs)} errors", flush=True)
    if not errs: break
    shorts=collections.defaultdict(set)
    for n,sh in gone.items(): shorts[sh].add(n)
    new=set()
    for f,ln,msg in errs:
        ln=int(ln); f=os.path.normpath(f)
        for nm in re.findall(r"`([^`]+)`",msg):
            for n in shorts.get(nm.split('.')[-1],()): new.add(n)
        L=open(f).read().split('\n')
        a=ln-1
        while a>0 and not DECL.match(L[a]): a-=1
        b=ln
        while b<len(L) and not DECL.match(L[b]): b+=1
        for t in set(re.findall(r"[A-Za-z_][A-Za-z0-9_'!?]*",'\n'.join(L[a:b]))):
            for n in shorts.get(t,()): new.add(n)
    new-=protect
    if not new:
        print("stuck on:", errs[:5]); break
    protect|=new; json.dump(sorted(protect),open(PJ,'w'))
print("protected",len(protect))
