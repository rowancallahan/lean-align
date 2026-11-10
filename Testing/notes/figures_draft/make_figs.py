# python3 make_figs.py SAMDIR SIMDIR(not needed) -- reads out/ours_{m}.sam, out/mb_{m}.sam, writes roc.tsv, roc.png, speed_*.png/tsv
import re,sys,collections
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
S=sys.argv[1]; modes=['mason','low','high']
def load(p):
    out=[]
    for l in open(p):
        if l[0]=='@':continue
        f=l.split('\t',11); fl=int(f[1])
        if fl&0x900:continue
        n=f[0]; m=1 if fl&64 else 2
        ln=sum(int(a) for a,o in re.findall(r'(\d+)([MDN=X])',f[5])) if f[5]!='*' else 0
        out.append((n,m,fl,f[2],int(f[3])-1,int(f[3])-1+ln,int(f[4])))
    return out
def correct(r):
    n,m,fl,c,a,b,q=r
    g=re.match(r's\d+:(.+):(\d+)-(\d+)[+-]:(\d+)-(\d+)[+-]$',n).groups()
    tc=g[0]; ts,te=(int(g[1]),int(g[2])) if m==1 else (int(g[3]),int(g[4]))
    if c!=tc: return False
    i=max(0,min(b,te)-max(a,ts)); u=max(b,te)-min(a,ts)
    return i/u>=0.10
rows=[]; fig,ax=plt.subplots(1,3,figsize=(15,4.2))
for k,m in enumerate(modes):
    for tool in ('minibwa','ours'):
        R=load(f'{S}/{"mb" if tool=="minibwa" else "ours"}_{m}.sam'); N=len(R)
        mp=[(r[6],correct(r)) for r in R if not r[2]&4]
        pts=[]
        for t in ([60,59,58,57,56,55,50,45,40,35,30,25,20,15,10,5,4,3,2,1,0] if tool=='minibwa' else [60,0]):
            sel=[c for q,c in mp if q>=t]
            if sel: pts.append((t,len(sel)/N,sum(sel)/len(sel),len(sel),sum(sel)))
        for t,x,y,nm,nc in pts: rows.append((m,tool,t,N,nm,nc,round(x,5),round(y,5)))
        ax[k].plot([p[1] for p in pts],[p[2] for p in pts],'o-' if tool=='minibwa' else 's',ms=4 if tool=='minibwa' else 9,label=tool+(' (MAPQ thresholds)' if tool=='minibwa' else ' (MAPQ 60 = unique; MAPQ>=0 = all mapped)'))
    ax[k].set_title(f'{m}: 100k simulated pairs (200k reads)'); ax[k].set_xlabel('fraction of reads mapped'); ax[k].set_ylabel('fraction of mapped reads correct'); ax[k].legend(fontsize=7); ax[k].grid(alpha=.3)
plt.tight_layout(); plt.savefig('roc.png',dpi=130)
open('roc.tsv','w').write('set\ttool\tmapq_min\treads\tmapped\tcorrect\tmapped_frac\tcorrect_frac_of_mapped\n'+''.join('\t'.join(map(str,r))+'\n' for r in rows))
# Fig 3 style: paper numbers (WGS short reads), 32 threads
P=[l.split() for l in open('paper_perf.tsv') if l.startswith('WGS')]
P.sort(key=lambda r:-float(r[2]))
fig,ax=plt.subplots(1,2,figsize=(11,4))
ax[0].bar([r[1] for r in P],[float(r[2]) for r in P]); ax[0].set_ylabel('Gbp/hr'); ax[1].bar([r[1] for r in P],[float(r[3]) for r in P]); ax[1].set_ylabel('peak memory (GB)')
for a in ax: a.tick_params(axis='x',rotation=45)
fig.suptitle('paper (WGS NovaSeq), 32 threads, 2x Xeon Gold 6130 -- as published'); plt.tight_layout(); plt.savefig('speed_paper.png',dpi=130)
# ours measured, 4 threads, 1M NovaSeq plain (2x151, 0.302 Gbp)
Q=[('lean-align',17.2,16.8,5.9),('minibwa',44.3,6.2,None)]
rows=[(t,s,round(0.302/s*3600,1),g,r if r else 'n/a') for t,s,g,r in Q]
open('speed_4threads.tsv','w').write('tool\tmap_seconds\tGbp_per_hr_map(derived=0.302/s*3600)\tGbp_per_core_hr\tpeak_RSS_GB\n'+''.join('\t'.join(map(str,r))+'\n' for r in rows))
fig,ax=plt.subplots(1,3,figsize=(11,3.8))
ax[0].bar([r[0] for r in rows],[r[2] for r in rows]); ax[0].set_ylabel('Gbp/hr (map phase, 4 threads)')
ax[1].bar([r[0] for r in rows],[r[3] for r in rows]); ax[1].set_ylabel('Gbp per core-hour (whole run)')
ax[2].bar(['lean-align'],[5.9]); ax[2].set_ylabel('peak RSS (GB); minibwa not measured')
fig.suptitle('this box, 4 threads, 1M NovaSeq pairs (NOT comparable to paper 32-thread bars)'); plt.tight_layout(); plt.savefig('speed_4threads.png',dpi=130)
