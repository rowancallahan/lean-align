#!/usr/bin/env python3
"""score.py DIR GENOME_FA : score lean-align / minibwa SAMs against mason's truth SAM (all in DIR: truth.sam ours.sam mb.sam; GENOME_FA with .fai).
Prints (1) the pair-correct table (overlap rule |A∩B|/|A∪B| >= 10% per mate, same chromosome; and the start-within-10bp rule), all pairs and pairs without N,
(2) the reads that are wrong at ours MAPQ 60, with scores under the Spec's scoring (match 0, mismatch -4, gap of k letters -(6+2k)) at the true place and at ours,
(3) the N letters of the reads: at a reference N at the true position or not."""
import re,sys,collections,mmap
D,GEN=sys.argv[1],sys.argv[2]
fai={l.split()[0]:tuple(map(int,l.split()[1:5])) for l in open(GEN+'.fai')}   # len, offset, linebases, linewidth
GF=open(GEN,'rb'); G=mmap.mmap(GF.fileno(),0,access=mmap.ACCESS_READ)
def _fetch(c,a,b):
    n,off,lb,lw=fai[c]; out=[]; p=a
    while p<b:
        e=min(b,(p//lb+1)*lb); s=off+(p//lb)*lw+p%lb; out.append(G[s:s+(e-p)].decode()); p=e
    return ''.join(out)
def ref(c,a,b):
    n=fai[c][0]; return _fetch(c,max(a,0),min(b,n))
def span(c): return sum(int(a) for a,o in re.findall(r'(\d+)([MDN=X])',c)) if c!='*' else 0
def load(p):
    d=collections.defaultdict(dict)
    for l in open(p):
        if l[0]=='@':continue
        f=l.rstrip('\n').split('\t'); fl=int(f[1])
        if fl&0x900: continue
        m=1 if fl&64 else 2
        tags={t[:2]:t[5:] for t in f[11:]}
        d[f[0]][m]=dict(chr=f[2],pos=int(f[3])-1,flag=fl,mapq=int(f[4]),cigar=f[5],seq=f[9],span=span(f[5]),tags=tags)
    return d
T=load(D+'/truth.sam'); O=load(D+'/ours.sam'); B=load(D+'/mb.sam'); names=list(T); NP=len(names)
def rd(r,t):
    if r['flag']&4 or r['chr']!=t['chr']: return False
    a,b=r['pos'],r['pos']+r['span']; s,e=t['pos'],t['pos']+t['span']
    return max(0,min(b,e)-max(a,s))/(max(b,e)-min(a,s))>=0.1
def st10(r,t): return not r['flag']&4 and r['chr']==t['chr'] and abs(r['pos']-t['pos'])<=10
Nn={n for n in names if any('N' in T[n][m]['seq'] for m in (1,2))}
def table(sel,label):
    print(f'-- {label}: {len(sel)} pairs')
    for nm,R in (('lean-align',O),('minibwa',B)):
        pc=sum(all(rd(R[n][m],T[n][m]) for m in (1,2)) for n in sel); s10=sum(all(st10(R[n][m],T[n][m]) for m in (1,2)) for n in sel)
        mp=sum(all(not R[n][m]['flag']&4 for m in (1,2)) for n in sel)
        print(f'   {nm}: both mates mapped {100*mp/len(sel):.2f}%  pair-correct (overlap>=10%) {100*pc/len(sel):.2f}%  pair-correct (start within 10 bp) {100*s10/len(sel):.2f}%')
table(names,'all pairs'); table([n for n in names if n not in Nn],'pairs with no N in either mate'); table([n for n in names if n in Nn],'pairs with an N in either mate')
# spec scoring, read global, reference free ends
NEG=-10**9
def semiglobal(r,t):   # best score of r aligned end to end inside t (free ends in t)
    n,m=len(r),len(t); M=[0]*(m+1); X=[NEG]*(m+1); Y=[NEG]*(m+1)   # M: ends in match/mismatch; X: gap in ref (read letter vs gap); Y: gap in read
    Hprev=[0]*(m+1); Fprev=[NEG]*(m+1)   # row 0: free start in t
    for i in range(1,n+1):
        H=[NEG]*(m+1); F=[NEG]*(m+1); E=NEG
        H[0]=-(6+2*i); F[0]=-(6+2*i)
        for j in range(1,m+1):
            E=max(H[j-1]-8,E-2)                     # gap in read: consumes t letter
            F[j]=max(Hprev[j]-8,Fprev[j]-2)         # gap in ref: consumes read letter
            H[j]=max(Hprev[j-1]+(0 if r[i-1]==t[j-1] else -4),E,F[j])
        Hprev,Fprev=H,F
    return max(Hprev)
def cigar_score(rec):
    s=0; qi=0; ri=0; rs=ref(rec['chr'],rec['pos'],rec['pos']+rec['span'])
    for a,o in re.findall(r'(\d+)([MIDNSHX=])',rec['cigar']):
        a=int(a)
        if o in 'M=X': s+=sum(-4 for k in range(a) if rec['seq'][qi+k]!=rs[ri+k]); qi+=a; ri+=a
        elif o=='I': s-=6+2*a; qi+=a
        elif o in 'DN': s-=6+2*a; ri+=a
        elif o=='S': qi+=a
    return s
print('\n-- reads wrong (overlap rule) at ours MAPQ 60 (proper pair):')
wrong=[(n,m) for n in names for m in (1,2) if not O[n][m]['flag']&4 and O[n][m]['mapq']>=60 and not rd(O[n][m],T[n][m])]
print(len(wrong),'reads in pairs',sorted({n for n,_ in wrong}))
for n in sorted({n for n,_ in wrong}):
    print(f'pair {n}: ours proper={bool(O[n][1]["flag"]&2)}')
    tot_true=tot_ours=0
    for m in (1,2):
        t,o,b=T[n][m],O[n][m],B[n][m]
        win=ref(t['chr'],t['pos']-100,t['pos']+t['span']+100)
        st=semiglobal(o['seq'],win)   # our trimmed window (reference orientation) at the true place
        so=cigar_score(o)
        tot_true+=st; tot_ours+=so
        print(f"  mate {m}: truth {t['chr']}:{t['pos']+1} {t['cigar']} | ours {o['chr']}:{o['pos']+1} {o['cigar']} len(seq)={len(o['seq'])} MAPQ {o['mapq']} AS {o['tags'].get('AS')} XB {o['tags'].get('XB')} XU {o['tags'].get('XU')} | minibwa {b['chr']}:{b['pos']+1} {b['cigar']} MAPQ {b['mapq']} | spec score of our window: at true place {st}, at ours {so}")
    print(f'  pair total of our windows: at true place {tot_true}, at ours {tot_ours}')
# N letters
nr=nref=0; tot=0; where=collections.Counter()
for n in names:
    for m in (1,2):
        t=T[n][m]; seq=t['seq']
        if 'N' not in seq: continue
        rs=ref(t['chr'],t['pos'],t['pos']+t['span']); qi=ri=0
        for a,o in re.findall(r'(\d+)([MIDNSHX=])',t['cigar']):
            a=int(a)
            if o in 'M=X':
                for k in range(a):
                    if seq[qi+k]=='N':
                        tot+=1; nref+= rs[ri+k]=='N'
                qi+=a; ri+=a
            elif o=='I': nr+=0; tot+=seq[qi:qi+a].count('N'); qi+=a
            elif o in 'DN': ri+=a
            elif o=='S': qi+=a
print(f'\nN letters in reads (truth orientation): {tot}; at a reference N at the true position: {nref}; not: {tot-nref}')
print('reference letters in the FASTA given to mason (first 5 Mb of chr1 sample):',collections.Counter(ref('chr1',10_000_000,10_050_000)).most_common(6))
