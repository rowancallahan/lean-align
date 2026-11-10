# pairs.py TRACE [min_ms=1000]: slow pairs from P lines, with job idx, pair idx, class metrics; JSON to TRACE.pairs.json
import sys,json,collections,statistics as st,re
tr=sys.argv[1]; MIN=float(sys.argv[2]) if len(sys.argv)>2 else 1000
pend=collections.defaultdict(list); J=[]; P=[]
for l in open(tr):
    f=l.rstrip('\n').split(' ')
    if f[0]=='P': pend[f[1]].append((int(f[2]),int(f[3]),f[4],f[5]))
    elif f[0]=='J':
        J.append((int(f[1]),int(f[2]),int(f[3]),f[4],pend.pop(f[4],[])))
J.sort(key=lambda j:j[0])
def run(s):
    m=0;c=0;p=''
    for ch in s:
        c=c+1 if ch==p else 1; p=ch; m=max(m,c)
    return m
def kmers(s): return len({s[i:i+4] for i in range(len(s)-3)})
def period(s):
    # best small period p<=8: fraction of positions with s[i]==s[i+p]
    best=(0,0)
    for p in range(1,9):
        if len(s)>p:
            sc=sum(s[i]==s[i+p] for i in range(len(s)-p))/(len(s)-p)
            if sc>best[0]: best=(sc,p)
    return best
rows=[]
for idx,(ts,b,e,tid,ps) in enumerate(J):
    for ms,i,s1,s2 in ps:
        if ms>=MIN:
            r=dict(job=idx,inJob=i,pair=idx*16000+i,ms=ms,len1=len(s1),len2=len(s2),run1=run(s1),run2=run(s2),k1=kmers(s1),k2=kmers(s2),per1=period(s1),per2=period(s2),seq1=s1,seq2=s2)
            rows.append(r)
rows.sort(key=lambda r:-r['ms'])
allp=[(ms) for j in J for (ms,_,_,_) in j[4]]
dur=sorted((e-b)/1e9 for _,b,e,_,_ in J[:-1]); med=st.median(dur)
exc=sum(d-med for d in dur if d>5)
print(f"{tr}: jobs {len(J)} median {med:.2f}s; pairs>20ms {len(allp)} (sum {sum(allp)/1e3:.0f}s); pairs>={MIN:.0f}ms {len(rows)} sum {sum(r['ms'] for r in rows)/1e3:.0f}s; excess of >5s jobs over median {exc:.0f}s -> {sum(r['ms'] for r in rows)/1e3/exc:.0%} explained by >={MIN:.0f}ms pairs; all >20ms pairs {sum(allp)/1e3/exc:.0%}")
json.dump(rows,open(tr+'.pairs.json','w'))
def cls(r):
    lc=[]
    for m in ('1','2'):
        if r['len'+m]==0: continue
        if r['run'+m]>=20: lc.append('polyrun')
        elif r['k'+m]<=24: lc.append('few4mers')
        elif r['per'+m][0]>=0.9: lc.append(f"period{r['per'+m][1]}")
    return ','.join(sorted(set(lc))) or 'OTHER'
C=collections.Counter(cls(r) for r in rows); print("classes:",dict(C))
for r in rows[:int(sys.argv[3]) if len(sys.argv)>3 else 60]:
    print(f"{r['ms']:7d}ms job {r['job']:4d} pair {r['pair']:9d} len {r['len1']}/{r['len2']} run {r['run1']}/{r['run2']} 4mers {r['k1']}/{r['k2']} per {r['per1'][1]}:{r['per1'][0]:.2f}/{r['per2'][1]}:{r['per2'][0]:.2f} [{cls(r)}]")
