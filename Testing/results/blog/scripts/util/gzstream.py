#!/usr/bin/env python3
"""gzrun.py LABEL BIN gz1 gz2 [new|old] [sink fifo|file]  (env passed through)
4 cores for everything (affinity set here, inherited): lean-align + 2 zcat + sink cat.
Writes res/LABEL.gz.{txt,samples,md5}. new: Main writes OUT.tmp then renames; old: writes OUT."""
import os,sys,subprocess,time,threading,resource,hashlib
L,BIN,g1,g2=sys.argv[1:5]; kind=sys.argv[5] if len(sys.argv)>5 else 'new'; sink=sys.argv[6] if len(sys.argv)>6 else 'fifo'
os.sched_setaffinity(0,{0,1,2,3})
S='/home/user/S'; W=f'{S}/fifo/{L}'; os.makedirs(W,exist_ok=True)
a,b,o=f'{W}/a',f'{W}/b',f'{W}/o'
tgt=o+'.tmp' if kind=='new' else o
for f in (a,b,o,o+'.tmp'):
    try: os.remove(f)
    except FileNotFoundError: pass
os.mkfifo(a); os.mkfifo(b)
if sink in('fifo','fifomd5'): os.mkfifo(tgt)
idx=f'{S}/idx/ic.idx'; isz=os.path.getsize(idx)
procs={}
NL=os.environ['NLINES']
procs['zcat1']=subprocess.Popen(['sh','-c',f'curl -sS {g1} | gunzip -c | head -n {NL} > {a}'])
procs['zcat2']=subprocess.Popen(['sh','-c',f'curl -sS {g2} | gunzip -c | head -n {NL} > {b}'])
if sink in('fifo','fifomd5'):
    cmd='md5sum' if sink=='fifomd5' else 'cat'
    procs['sink']=subprocess.Popen(['sh','-c',f'exec {cmd} < {tgt} > '+(f'{W}/md5' if sink=='fifomd5' else '/dev/null')])
t0=time.time()
lean=subprocess.Popen([BIN,'map',idx,a,b,o,'100','1000'],stderr=open(f'{S}/res/{L}.trace','w'))
procs['lean']=lean
pid=lean.pid; samples=[]; load=[None,None]; stop=False
def stat(path):
    f=open(path).read(); r=f.rsplit(')',1); return f[f.index('(')+1:f.rindex(')')],r[1].split()
def sampler():
    tck=os.sysconf('SC_CLK_TCK'); nxt=time.time()
    while not stop:
        t=time.time()-t0
        try:
            if load[0] is None:
                r=int([l for l in open(f'/proc/{pid}/io') if l.startswith('rchar')][0].split()[1])
                if r>=isz:
                    _,f=stat(f'/proc/{pid}/stat'); load[0]=t; load[1]=(int(f[11])+int(f[12]))/tck
            row=[]
            for tid in os.listdir(f'/proc/{pid}/task'):
                try:
                    _,f=stat(f'/proc/{pid}/task/{tid}/stat'); st=f[0]; u,s=int(f[11]),int(f[12])
                    sc=open(f'/proc/{pid}/task/{tid}/syscall').read().split()
                    w=sc[0]+('/fd'+str(int(sc[1],16)) if len(sc)>1 and sc[0] in('0','1') else '')
                    if tid==str(pid): w+=':'+open(f'/proc/{pid}/task/{tid}/wchan').read()
                    row.append(f'{tid},{st},{u},{s},{w}')
                except Exception: pass
            for n,p in procs.items():
                if n!='lean':
                    try:
                        _,f=stat(f'/proc/{p.pid}/stat'); sc=open(f'/proc/{p.pid}/syscall').read().split()
                        row.append(f'{n},{f[0]},{f[11]},{f[12]},{sc[0]}')
                    except Exception: pass
            samples.append(f'{t:.3f} '+' '.join(row))
        except Exception: pass
        nxt+=0.2; time.sleep(max(0,nxt-time.time()))
th=threading.Thread(target=sampler); th.start()
rss={}; ru={}; left=dict((p.pid,n) for n,p in procs.items())
tend={}
while left:
    p,_,r=os.wait4(-1,0); n=left.pop(p,None)
    if n: ru[n]=r.ru_utime+r.ru_stime; tend[n]=time.time()-t0; rss[n]=r.ru_maxrss/1024
stop=True; th.join()
if sink=='file' or kind=='new':
    pass
open(f'{S}/res/{L}.gz.samples','w').write(f'#load {load[0]} {load[1]}\n'+'\n'.join(samples))
wall=tend['lean']; ld=load[0] or 0; lc=load[1] or 0
mp=wall-ld
lean_cpu=ru['lean']-lc; zc=ru['zcat1']+ru['zcat2']; sk=ru.get('sink',0)
if sink=='fifomd5': md5=open(f'{W}/md5').read().split()[0]
else:
    md5='-'
    if sink=='file':
        fn=o if os.path.exists(o) else tgt
        md5=subprocess.run(['md5sum',fn],capture_output=True,text=True).stdout.split()[0]; os.remove(fn)
print(f"GZ {L} map {mp:.1f}s load {ld:.1f} lean_cpu {lean_cpu:.1f} zcat_cpu {zc:.1f} sink_cpu {sk:.1f} peakRSS_lean_MB {rss['lean']:.0f} wall_all {tend['lean']:.1f} util_lean {lean_cpu/(mp*4):.3f} util_all {(lean_cpu+zc+sk)/(mp*4):.3f} md5 {md5[:8]} rc {lean.returncode}")
