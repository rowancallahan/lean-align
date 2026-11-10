import re,sys,statistics as st,subprocess,collections
bases={}
def nb(s):
    if s not in bases: bases[s]=int(subprocess.check_output(f"awk 'NR%4==2{{n+=length($0)}} END{{print n}}' /root/p1m/{s}_R1.fq /root/p1m/{s}_R2.fq",shell=True))
    return bases[s]
d=collections.defaultdict(list)
for l in open(sys.argv[1]):
    m=re.match(r'TIME (\w+) T(\d+) (\S+) r\d+: wall ([\d.]+) s, cpu ([\d.]+) s.*load ([\d.]+) s, loadcpu ([\d.]+) s',l)
    if m: d[(m[1],int(m[2]),m[3])].append(tuple(map(float,m.groups()[3:])))
print("set T tool | map_s cpu_s(map) util Gbp/hr Gbp/core-hr(map-cpu) Gbp/core-hr(whole) | wall_s load_s (medians, n)")
for (s,T,t),v in sorted(d.items()):
    med=lambda f: st.median(f(x) for x in v); B=nb(s)/1e9; T_=T
    mp=med(lambda x:x[0]-x[2]); cp=med(lambda x:x[1]-x[3]); w=med(lambda x:x[1])
    print(f"{s} {T} {t} | {mp:.1f} {cp:.1f} {cp/(mp*T_):.2f} {B/mp*3600:.2f} {B/cp*3600:.2f} {B/w*3600:.2f} | {med(lambda x:x[0]):.1f} {med(lambda x:x[2]):.1f} n={len(v)}")
