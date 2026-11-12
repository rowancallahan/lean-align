import os,sys,subprocess,time,resource,json
tool=sys.argv[1]   # ours | minibwa
W='/home/user/scratch/wg'; G='https://storage.googleapis.com/brain-genomics-public/research/sequencing/fastq/novaseq/wgs_pcr_free/30x/HG002.novaseq.pcr-free.30x'
for f in ('f1','f2','out.sam.tmp'):
    p=f'{W}/{f}'
    if os.path.exists(p): os.remove(p)
    os.mkfifo(p)
AWK="awk 'NR%4==2{b+=length($0)}END{print NR/4,b}'"
t0=time.time()
prod=[subprocess.Popen(f"curl -sS {G}.R{m}.fastq.gz | gunzip -c | tee {W}/f{m} | {AWK} > {W}/cnt{m}.txt",shell=True) for m in (1,2)]
if tool=='ours':
    cmd=['taskset','-c','0-3','/home/user/scratch/hol/.lake/build/bin/lean-align','map','/home/user/scratch/idx/ic.idx',f'{W}/f1',f'{W}/f2',f'{W}/out.sam','100','1000']
    drain=subprocess.Popen(f'cat < {W}/out.sam.tmp > /dev/null',shell=True)
    a=subprocess.Popen(cmd,stderr=open(f'{W}/trace.log','w'))
else:
    cmd=['taskset','-c','0-3','/home/user/scratch/minibwa/minibwa','map','-t','4','/home/user/scratch/mb/mb',f'{W}/f1',f'{W}/f2']
    a=subprocess.Popen(cmd,stdout=subprocess.DEVNULL,stderr=open(f'{W}/mb.err','w'))
pid,st,ru=os.wait4(a.pid,0)
wall=time.time()-t0
for p in prod: p.wait()
if tool=='ours': drain.wait()
tot=resource.getrusage(resource.RUSAGE_CHILDREN)
cnt=[open(f'{W}/cnt{m}.txt').read().split() for m in (1,2)]
r=dict(tool=tool,exit=os.waitstatus_to_exitcode(st),wall_s=wall,aligner_user_s=ru.ru_utime,aligner_sys_s=ru.ru_stime,peak_rss_GB=ru.ru_maxrss/1e6,
 all_children_user_s=tot.ru_utime,all_children_sys_s=tot.ru_stime,pairs_R1=float(cnt[0][0]),bases_R1=float(cnt[0][1]),pairs_R2=float(cnt[1][0]),bases_R2=float(cnt[1][1]))
json.dump(r,open(f'{W}/result_{tool}.json','w'),indent=1); print(r)
