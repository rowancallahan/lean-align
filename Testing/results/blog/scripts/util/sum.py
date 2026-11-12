import re,glob,collections,statistics as st
R=collections.defaultdict(list); M={}
for f in glob.glob('/home/user/S/res/*_*_[123].an'):
    L=f.split('/')[-1][:-3]; c,s,_=L.rsplit('_',1)[0].rsplit('_',1)+[0] if False else (None,None,None)
    c,s,r=L.rsplit('_',2)
    t=open(f).read()
    m=re.search(r'wall ([\d.]+) load ([\d.]+) loadcpu ([\d.]+) cpu ([\d.]+)',t)
    sp=float(re.search(r'span ([\d.]+)s',t).group(1)); wall,load,lc,cpu=map(float,m.groups())
    busy=float(re.search(r'busy/span ([\d.]+)',t).group(1)); tail=float(re.search(r'tail ([\d.]+)s \(mean',t).group(1))
    md=open(f'/home/user/S/res/{L}.md5').read().split()[0]
    R[(s,c)].append((sp,(cpu-lc)/(sp*4),busy,tail,md))
print("set cfg: map_s(med) util(med) workerbusy tail_idle_s  md5ok")
ref={}
for (s,c),v in sorted(R.items()):
    ref.setdefault(s,[x[4] for x in R[(s,'base')]][0])
    print(f"{s} {c:8s} n={len(v)} map {st.median(x[0] for x in v):.1f} (rng {min(x[0] for x in v):.1f}-{max(x[0] for x in v):.1f}) util {st.median(x[1] for x in v):.3f} busy {st.median(x[2] for x in v):.3f} tail {st.median(x[3] for x in v):.2f} md5 {'OK' if all(x[4]==ref[s] for x in v) else 'DIFF'}")
