import re,sys,collections
src=open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)),'size.py')).read().split("if __"+"name__")[0]; exec(src)
T=lambda s: proxy(s)[0]
CM=re.compile(r'/-.*?-/|--[^\n]*',re.S)
def strip_comments(s): return CM.sub('',s)
def docs_only(s): return sum(T(m) for m in re.findall(r'/--.*?-/',s,re.S))
BP={'set_option':r'^\s*set_option\b[^\n]*(?<!\bin)$','print/check/eval':r'^\s*#(print|check|eval|guard|reduce|synth)\b[^\n]*',
    'import':r'^import\b[^\n]*','open':r'^\s*open\b[^\n]*','ns/section/end':r'^\s*(namespace|section|end)\b[^\n]*',
    'variable/omit/include':r'^\s*(variable|omit|include)\b[^\n]*','attribute':r'^\s*attribute\b[^\n]*',
    '... in prefix':r'^\s*(set_option|open|omit|include)\b[^\n]*\bin$'}
ID=re.compile(r"(?<![\w.'])[A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)+")
def qual(s):
    s=strip_comments(s); save=0; pre=collections.Counter()
    for m in ID.finditer(s):
        parts=m.group().split('.'); k=0
        while k<len(parts)-1 and parts[k][:1].isupper(): k+=1
        if k==0: continue
        p='.'.join(parts[:k]); pre[p]+=1; save+=T(p)
    cost=sum(1+T(p) for p in pre)  # one `open P` per prefix per file
    return save,cost,pre
def dup_lines(s):
    ls=[l.strip() for l in strip_comments(s).split('\n') if len(l.strip())>12]
    c=collections.Counter(ls)
    return sum(T(l)*(n-1) for l,n in c.items() if n>=2)
def shows(s):
    s=strip_comments(s)
    return sum(T(m) for m in re.findall(r'\bshow\b[^\n]*',s))
def analyze(fs):
    R=collections.Counter()
    for f in fs:
        s=open(f).read(); t=T(s); R['total']+=t
        R['comments']+=t-T(strip_comments(s)); R['docstrings']+=docs_only(s)
        for k,p in BP.items(): R['bp:'+k]+=sum(T(x.group()) for x in re.finditer(p,s,re.M))
        sv,c,_=qual(s); R['qual_prefix']+=sv; R['qual_open_cost']+=c
        R['dup_lines']+=dup_lines(s); R['show_lines']+=shows(s)
        if '/wfa' in f: R['wfa']+=t
    return R
if __name__=='__main__':
    fs=sys.argv[1:] or files(['Aligner','Proofs','Testing'])
    R=analyze(fs); tot=R['total']
    for k,v in R.items(): print(f"{k:24s}{v:9d} {100*v/tot:5.1f}%")
