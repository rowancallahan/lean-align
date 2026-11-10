import sys,collections,statistics as st
L=sys.argv[1]; J=[];T0=TE=None
for l in open(f'/home/user/S/res/{L}.log'):
    p=l.split()
    if p[0]=='T0':T0=int(p[1])
    elif p[0]=='TEND':TE=int(p[1])
    elif p[0]=='J':J.append([int(p[1])]+[int(x) for x in p[2:8]]+[int(p[8])]) 
    elif p[0]=='TIME':print(l.strip())
# J: seq wid tw t0 t1 t2 t3 pairs
span=(TE-T0)/1e9; ws=collections.defaultdict(list)
for j in J: ws[j[1]].append(j)
dur=[(j[6]-j[3])/1e9 for j in J]; al=[(j[5]-j[4])/1e9 for j in J]
print(f"{L}: jobs {len(J)} span {span:.1f}s  job time s: min {min(dur):.2f} med {st.median(dur):.2f} p90 {sorted(dur)[int(.9*len(dur))]:.2f} max {max(dur):.2f}  align share {sum(al)/sum(dur):.2f}")
h=collections.Counter(min(int(d/ (max(dur)/8)),7) for d in dur); m=max(dur)/8
print("hist:", " ".join(f"[{i*m:.1f}-{(i+1)*m:.1f}):{h[i]}" for i in range(8)))
bs=[];st_=[];tl=[];mid=[]
for w,js in ws.items():
    js.sort(key=lambda j:j[3]); busy=sum((j[6]-j[3]) for j in js)/1e9
    a=(js[0][3]-T0)/1e9; t=(TE-js[-1][6])/1e9
    bs.append(busy); st_.append(a); tl.append(t); mid.append(span-busy-a-t)
n=len(ws); print(f"workers {n}: busy/span {sum(bs)/n/span:.3f}  idle start {sum(st_)/n:.2f}s steady {sum(mid)/n:.2f}s tail {sum(tl)/n:.2f}s (mean per worker)")
print(f"  tail range {min(tl):.2f}-{max(tl):.2f}; last-job end spread; slowest 3 jobs s: {sorted(dur)[-3:]}")
