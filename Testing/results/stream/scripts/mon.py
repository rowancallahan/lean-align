import time,os,sys
T='/home/user/scratch/wg/trace.log'; R='/home/user/scratch/wg/result_ours.json'
pos=0; n=0; last=time.time(); t0=time.time(); nxt=t0+600; slow=[]
while True:
    time.sleep(5)
    with open(T) as f:
        f.seek(pos); d=f.read(); pos=f.tell()
    new=0
    for l in d.splitlines():
        p=l.split()
        if p[0]=='J' and len(p)==6:
            n+=1; new+=1; dur=(int(p[3])-int(p[2]))/1e9
            if dur>5: print(f"SLOW job#{n} dur {dur:.1f}s start_ns {p[2]}",flush=True)
    if new: last=time.time()
    elif time.time()-last>60 and not os.path.exists(R): print(f"STALL: no job finished for {time.time()-last:.0f}s (jobs done {n})",flush=True); last=time.time()
    if time.time()>nxt:
        print(f"PROGRESS {int((time.time()-t0)/60)} min: {n} jobs done = {n*16000/1e6:.1f} M pairs, {n*16000/(time.time()-t0):.0f} pairs/s",flush=True); nxt+=600
    if os.path.exists(R): print("RESULT",open(R).read(),flush=True); break
