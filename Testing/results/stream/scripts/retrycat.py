# retrycat.py URL : write the file at URL to stdout, resuming with Range after any connection drop
import sys,time,urllib.request,urllib.error
url=sys.argv[1]; pos=0; tries=0
out=sys.stdout.buffer
while True:
    try:
        req=urllib.request.Request(url,headers={'Range':f'bytes={pos}-'} if pos else {})
        with urllib.request.urlopen(req,timeout=60) as r:
            total=int(r.headers.get('Content-Range','/%d'%(pos+int(r.headers['Content-Length']))).split('/')[-1]) if pos else int(r.headers['Content-Length'])
            while True:
                b=r.read(1<<20)
                if not b: break
                out.write(b); pos+=len(b)
        if pos>=total: break
        sys.stderr.write(f'retrycat: short read at {pos}/{total}, resuming\n')
    except (OSError,urllib.error.URLError) as e:
        if isinstance(e,BrokenPipeError): sys.exit(0)
        tries+=1; sys.stderr.write(f'retrycat: {e!r} at {pos}, retry {tries}\n'); time.sleep(2)
        if tries>50: sys.exit(1)
