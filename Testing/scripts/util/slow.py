# slow.py TRACE [threshold_s]: jobs longer than threshold (index in start order), ana.py-style summary of running<4
import sys
J=[]
for l in open(sys.argv[1]):
    f=l.split()
    if f[0]=='J': J.append((int(f[1]),int(f[2]),int(f[3]),int(f[4]),int(f[5])))
th=float(sys.argv[2]) if len(sys.argv)>2 else 5
J.sort()  # spawn order == job index
print(f"jobs {len(J)}")
for i,(t,b,e,tid,sz) in enumerate(J):
    d=(e-b)/1e9
    if d>th: print(f"  job {i} pairs {i*16000}-{(i+1)*16000} dur {d:.1f}s started +{(b-J[0][1])/1e9:.0f}s slice {sz/1e6:.1f}MB")
ev=[]
for t,b,e,_,_ in J: ev+=[(b,1),(e,-1)]
ev.sort(); r=0; last=ev[0][0]; tr={}
for t,d in ev: tr[r]=tr.get(r,0)+t-last; last=t; r+=d
tot=sum(tr.values()); lt=sum(v for k,v in tr.items() if k<4)
print(f"span {tot/1e9:.0f}s; time with <4 jobs running {lt/1e9:.0f}s ({lt/tot:.1%}); hist {{k: s}} {{{', '.join(f'{k}:{v/1e9:.0f}' for k,v in sorted(tr.items()))}}}")
import statistics as st
dur=sorted((e-b)/1e9 for _,b,e,_,_ in J[:-1]); print(f"dur med {st.median(dur):.2f} p99 {dur[int(.99*len(dur))]:.2f} max {dur[-1]:.1f}")
