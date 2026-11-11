# wgrun3.py TOOL(ours|minibwa) N TAG : same pipeline for both tools (resuming downloader, cat sink, own index pre-cached, rchar load time for ours)
import os,sys,subprocess,time,resource,json,threading
tool,NP,TAG=sys.argv[1],int(sys.argv[2]),sys.argv[3]
W=f'/home/user/scratch/wg/h{NP}_{tool}{TAG}'; os.makedirs(W,exist_ok=True)
G='https://giab.s3.amazonaws.com/data/AshkenazimTrio/HG002_NA24385_son/NIST_Illumina_2x250bps/reads/D1_S1_L001'
IDX={'ours':['/home/user/scratch/idx/ic.idx'],'minibwa':['/home/user/scratch/mb/mb.l2b','/home/user/scratch/mb/mb.mbw']}[tool]
LA='/home/user/scratch/fast2/.lake/build/bin/lean-align'
for f in ('f1','f2','out.sam.tmp'):
    p=f'{W}/{f}'
    if os.path.exists(p): os.remove(p)
    os.mkfifo(p)
for f in IDX: subprocess.run(['cat',f],stdout=subprocess.DEVNULL,check=True)   # index in the page cache, outside the timing
AWK="awk 'NR%4==2{b+=length($0)}END{print NR/4,b}'"
t0=time.time()
prod=[subprocess.Popen(f"python3 -I /home/user/scratch/retrycat.py {G}_R{m}_001.fastq.gz 2>> {W}/fetch{m}.log | gunzip -c 2>/dev/null | head -n {4*NP} | tee {W}/f{m} | {AWK} > {W}/cnt{m}.txt",shell=True) for m in (1,2)]
if tool=='ours':
    cmd=['taskset','-c','0-3',LA,'map',IDX[0],f'{W}/f1',f'{W}/f2',f'{W}/out.sam','100','1000']
    drain=subprocess.Popen(f'cat < {W}/out.sam.tmp > /dev/null',shell=True)
    a=subprocess.Popen(cmd,stderr=open(f'{W}/stderr.log','w'))
else:
    cmd=['taskset','-c','0-3','/home/user/scratch/minibwa/minibwa','map','-t','4','/home/user/scratch/mb/mb',f'{W}/f1',f'{W}/f2']
    a=subprocess.Popen(cmd,stdout=subprocess.PIPE,stderr=open(f'{W}/mb.err','w'))
    drain=subprocess.Popen(['cat'],stdin=a.stdout,stdout=subprocess.DEVNULL); a.stdout.close()
done=threading.Event(); load={}
size=os.path.getsize(IDX[0]); tick=os.sysconf('SC_CLK_TCK')
def samp():
    f=open(f'{W}/threads.csv','w'); f.write('t_s,tid,cpu_ticks\n'); nxt=0
    while not done.is_set():
        t=time.time()-t0
        try:
            if tool=='ours' and 'load_s' not in load:
                rc=int([l for l in open(f'/proc/{a.pid}/io') if l.startswith('rchar')][0].split()[1])
                if rc>=size: load['load_s']=t-tstart
            if t>=nxt:
                nxt+=10
                for tid in os.listdir(f'/proc/{a.pid}/task'):
                    x=open(f'/proc/{a.pid}/task/{tid}/stat').read().rsplit(')',1)[1].split(); f.write(f'{t:.0f},{tid},{int(x[11])+int(x[12])}\n')
                f.flush()
        except OSError: pass
        time.sleep(0.1)
tstart=time.time()-t0
threading.Thread(target=samp,daemon=True).start()
pid,st,ru=os.wait4(a.pid,0); done.set()
wall=time.time()-t0
for p in prod: p.wait()
drain.wait()
tot=resource.getrusage(resource.RUSAGE_CHILDREN)
if tool=='minibwa':
    import re
    m=re.search(r'main_map::([\d.]+)\*',open(f'{W}/mb.err').read()); load['load_s']=float(m[1]) if m else None
cnt=[open(f'{W}/cnt{m}.txt').read().split() for m in (1,2)]
r=dict(tool=tool,commit='f465a57' if tool=='ours' else 'c07de5c',exit=os.waitstatus_to_exitcode(st),wall_s=wall,aligner_user_s=ru.ru_utime,aligner_sys_s=ru.ru_stime,peak_rss_GB=ru.ru_maxrss/1e6,
 all_children_user_s=tot.ru_utime,all_children_sys_s=tot.ru_stime,index_load_s=load.get('load_s'),pairs_R1=float(cnt[0][0]),bases_R1=float(cnt[0][1]),pairs_R2=float(cnt[1][0]),bases_R2=float(cnt[1][1]))
json.dump(r,open(f'{W}/result.json','w'),indent=1); print(r)
