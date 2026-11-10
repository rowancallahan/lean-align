import sys,collections
L=sys.argv[1]; lines=open(f'/home/user/S/res/{L}.gz.samples').read().split('\n')
ld=float(lines[0].split()[1]); rows=[l.split() for l in lines[1:] if l]
rows=[(float(r[0]),[x.split(',') for x in r[1:]]) for r in rows]
rows=[r for r in rows if r[0]>=ld]
n=len(rows); end=rows[-1][0]; print(f"{L}: {n} samples over {end-ld:.1f}s (after index load)")
st=collections.defaultdict(lambda:[None,None,collections.Counter(),collections.Counter()])  # first cpu,last cpu,state,syscall
for t,ths in rows:
    for x in ths:
        k=x[0]; v=st[k]; c=int(x[2])+int(x[3])
        if v[0] is None: v[0]=c
        v[1]=c; v[2][x[1]]+=1; v[3][x[4].split(':')[0]]+=1
ck=100.
cpu=sorted(((v[1]-v[0])/ck,k) for k,v in st.items() if k.isdigit() or True)
print("per-thread CPU s (map phase), top:", ", ".join(f"{k}:{c:.1f}" for c,k in cpu[::-1][:10]))
lean=[(c,k) for c,k in cpu if k.isdigit()]
print(f"lean threads {len(lean)}; main-thread tid = min tid (pid)")
cands=sorted(((st[k][1]-st[k][0],k) for k in st if k.isdigit()),reverse=True); mt=cands[4][1]; v=st[mt]  # loop thread = 5th by CPU (after 4 workers)
tot=sum(v[3].values())
print(f"main thread {mt}: cpu {(v[1]-v[0])/ck:.1f}s; syscall share:", ", ".join(f"{k}:{c/tot:.2f}" for k,c in v[3].most_common(6)), "| state:", dict(v[2]))
for k in ('zcat1','zcat2','sink'):
    if k in st:
        v=st[k]; tot=sum(v[2].values()); print(f"{k}: cpu {(v[1]-v[0])/ck:.1f}s state {dict(v[2])} syscall {dict(v[3].most_common(3))}")
# workers = other threads with >1s cpu
w=[(c,k) for c,k in lean if k!=mt and c>1]
print("threads >1s cpu:", len(w), "cpu s:", [f"{c:.1f}" for c,k in sorted(w,reverse=True)])
# running threads per sample
run=collections.Counter()
for t,ths in rows: run[sum(1 for x in ths if x[1]=='R' and x[0].isdigit())]+=1
print("runnable lean threads per sample:", {k:round(v/n,2) for k,v in sorted(run.items())})
