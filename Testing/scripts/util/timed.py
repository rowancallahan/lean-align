import sys,os,subprocess,time,resource
L=sys.argv[1]; t=time.time()
p=subprocess.Popen(['taskset','-c','0-3']+sys.argv[2:],stdout=subprocess.DEVNULL)
# index load = rchar reaches idx size
sz=os.path.getsize('/home/user/S/idx/ic.idx'); load=None
while p.poll() is None:
    try:
        r=int([l for l in open(f'/proc/{p.pid}/io') if l.startswith('rchar')][0].split()[1])
        if load is None and r>=sz: load=time.time()-t; f=open(f'/proc/{p.pid}/stat').read().rsplit(')',1)[1].split(); lc=(int(f[11])+int(f[12]))/os.sysconf('SC_CLK_TCK')
    except Exception: pass
    time.sleep(0.05)
wall=time.time()-t; ru=resource.getrusage(resource.RUSAGE_CHILDREN)
print(f"TIME {L} wall {wall:.1f} load {load:.1f} loadcpu {lc:.1f} cpu {ru.ru_utime+ru.ru_stime:.1f} rc {p.returncode}",file=sys.stderr)
