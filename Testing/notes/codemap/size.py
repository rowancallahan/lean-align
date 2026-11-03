import re,os,sys,glob,math,collections
os.chdir('/home/user/lean-align')
def files(scope):
    fs=[]
    for d in scope:
        for root,_,names in os.walk(d):
            if '.lake' in root: continue
            fs+=[os.path.join(root,n) for n in names if n.endswith('.lean')]
    return sorted(fs)
# dictionary: prose words in comments and .md notes
words=collections.Counter()
for f in glob.glob('**/*.md',recursive=True)+files(['Aligner','Proofs','Spec','Testing']):
    if '.lake' in f: continue
    s=open(f,errors='ignore').read()
    if f.endswith('.lean'): s=' '.join(re.findall(r'--[^\n]*|/-.*?-/',s,re.S))
    words.update(w for w in re.findall(r'(?<![A-Za-z_`.])[a-z]{3,}(?![A-Za-z_`(])',s))
D={w for w,c in words.items() if c>=3}
def pieces(ident):
    out=[]
    for part in re.split(r'[_.\'!?]',ident):
        out+=re.findall(r'[A-Z]+(?=[A-Z][a-z])|[A-Z]?[a-z]+|[A-Z]+|\d+',part)
    return out
def proxy(text):
    t=0; idw=0; idf=0
    for tok in re.findall(r"[A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*|\d+|[^\sA-Za-z0-9_]+",text):
        if tok[0].isalpha() or tok[0]=='_':
            for p in pieces(tok):
                if p.isdigit(): t+=math.ceil(len(p)/3); continue
                if p.lower() in D: t+=1; idw+=1
                else: t+=math.ceil(len(p)/2); idf+=1
        elif tok.isdigit(): t+=math.ceil(len(tok)/3)
        else: t+=1
    return t,idw,idf
def measure(fs):
    L=C=T=W=F=0
    for f in fs:
        s=open(f).read(); L+=s.count('\n'); C+=len(s); t,w,fr=proxy(s); T+=t; W+=w; F+=fr
    return dict(files=len(fs),lines=L,chars=C,tokens=T,word_pieces=W,fragment_pieces=F)
if __name__=='__main__':
    scope=sys.argv[1:] or ['Aligner','Proofs','Testing']
    print(measure(files(scope)), "dict size",len(D))
