# usage: xb.py SAM  -> stats for mapped pairs with XU:Z:unknown
import sys, collections
def tags(f): return {t[:2]: t[5:] for t in f[11:]}
def bound(m): return -16 if m>=125 else -12 if m>=100 else -8 if m>=75 else -4 if m>=50 else 0
tot=0; unk=0; cat=collections.Counter(); tier=collections.defaultdict(collections.Counter); ge=0; lt=0; ex=[]; xus=collections.Counter()
prev=None
for l in open(sys.argv[1]):
    if l[0]=='@': continue
    f=l.rstrip('\n').split('\t')
    if prev is None: prev=f; continue
    a,b=prev,f; prev=None; assert a[0]==b[0]
    tot+=1
    ta,tb=tags(a),tags(b)
    xus[ta.get('XU')]+=1
    if int(a[1])&4 or int(b[1])&4 or ta.get('XU')!='unknown': continue
    unk+=1
    xb=int(ta['XB']); s=int(ta['AS'])+int(tb['AS']); d=xb-s
    c='eq' if d==0 else 'lt1-8' if 1<=d<=8 else 'lt>8' if d>8 else 'gt'
    cat[c]+=1; tier[c][ta.get('XT')]+=1
    bd=bound(min(len(a[9]),len(b[9])))
    if xb>=bd:
        ge+=1
        if len(ex)<5: ex.append(a[0])
    else: lt+=1
print(f"pairs {tot}; XU values {dict(xus)}; mapped+unknown {unk} ({unk/tot:.4%})")
print("AS1+AS2 vs XB:", dict(cat))
for c in tier: print("  tiers",c,dict(tier[c]))
print(f"XB>=bound {ge} ({ge/tot:.4%} of all pairs), XB<bound {lt} ({lt/tot:.4%}); examples {ex}")
