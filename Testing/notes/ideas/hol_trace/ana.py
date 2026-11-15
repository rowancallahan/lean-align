#!/usr/bin/env python3
# ana.py TRACE : summary of a hol-trace stderr log (J ts start end tid size / C waitstart waitend finished)
import sys
J=[];C=[]
for l in open(sys.argv[1]):
    f=l.split()
    if f[0]=='J': J.append(tuple(int(x) for x in f[1:6]))
    elif f[0]=='C': C.append((int(f[1]),int(f[2]),f[3]=='true'))
J.sort(); assert len(J)==len(C), (len(J),len(C))
T0=J[0][0]; s=lambda x:(x-T0)/1e9
dur=sorted((e-b)/1e9 for _,b,e,_,_ in J); q=lambda p:dur[min(len(dur)-1,int(p*len(dur)))]
print(f"jobs {len(J)} dur min {dur[0]:.2f} med {q(.5):.2f} p90 {q(.9):.2f} max {dur[-1]:.2f}")
full=[(e-b)/1e9 for _,b,e,_,sz in J[:-1]]
import statistics as st
for a,b in [(0,125),(125,len(full))]: x=full[a:b]; print(f"  jobs {a}-{b}: mean {st.mean(x):.2f} med {st.median(x):.2f} max {max(x):.2f}")
by={}
for t,b,e,tid,_ in J[:-1]: by.setdefault(tid,[]).append((e-b)/1e9)
for tid,x in sorted(by.items(), key=lambda kv: -sum(kv[1])):
    print(f"  thread {tid}: {len(x)} jobs, busy {sum(x):.1f} s, med {st.median(x):.2f} max {max(x):.2f}")
print(f"  queue wait (start-spawn): med {st.median((b-t)/1e9 for t,b,_,_,_ in J):.3f} max {max((b-t)/1e9 for t,b,_,_,_ in J):.3f}")
# timeline of running / unfinished
ev=[]
for t,b,e,_,_ in J: ev+= [(t,'u',1),(b,'r',1),(e,'u',-1),(e,'r',-1)]
ev.sort(); u=r=0; last=ev[0][0]; tu={};tr={}
for t,k,d in ev:
    tu[u]=tu.get(u,0)+t-last; tr[r]=tr.get(r,0)+t-last; last=t
    if k=='u': u+=d
    else: r+=d
tot=sum(tr.values())
print(f"span {tot/1e9:.1f} s; running<4 {sum(v for k,v in tr.items() if k<4)/1e9:.1f} s; unfinished<4 {sum(v for k,v in tu.items() if k<4)/1e9:.1f} s")
print("  running hist (s):", {k:round(v/1e9,1) for k,v in sorted(tr.items())})
print("  unfinished hist (s):", {k:round(v/1e9,1) for k,v in sorted(tu.items())})
# collect waits
def running_at_intervals(a,b):
    # time within [a,b] with running<4
    x=0; r=0; last=None
    for t,k,d in ev:
        if k!='r': continue
        if last is not None and r<4: x+=max(0,min(t,b)-max(last,a))
        r+=d; last=t
    return x
W=[(c0,c1,J[i][2]) for i,(c0,c1,f) in enumerate(C) if not f]
wt=sum(c1-c0 for c0,c1,_ in W)
wb={}
for i,(c0,c1,f) in enumerate(C):
    if not f: wb[J[i][3]]=wb.get(J[i][3],0)+(c1-c0)/1e9
print("collect wait by the waited job's thread (s):", {k: round(v,1) for k,v in sorted(wb.items(), key=lambda kv:-kv[1])})
under=sum(running_at_intervals(c0,c1) for c0,c1,_ in W)
lat=sorted((c1-e)/1e6 for c0,c1,e in W)
print(f"collect waits {len(W)} of {len(C)}; total wait {wt/1e9:.1f} s; of it with running<4: {under/1e9:.1f} s")
print(f"  wake latency (C return - job end) ms: med {lat[len(lat)//2]:.2f} p90 {lat[int(.9*len(lat))]:.2f} max {lat[-1]:.2f}")
