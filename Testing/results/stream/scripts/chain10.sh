# series for one data set: S = n (NovaSeq) or h (HiSeq)
S=$1; PY=wgrun3.py; [ $S = h ] && PY=wgrun3h.py
cd /home/user/scratch/wg
OLD=/home/user/scratch/fast2/.lake/build/bin/lean-align
NEW=/home/user/scratch/all/.lake/build/bin/lean-align
run() { # tool label LA tag
  for try in 1 2 3; do
    tag=$4; [ $try -gt 1 ] && tag=${4}_try$try
    LA=$3 LABEL=$2 python3 -I ../$PY $1 10000000 $tag > run10_${S}_$1$tag.log 2>&1
    d=${S}10000000_$1$tag; [ $S = n ] && d=n10000000_$1$tag
    if python3 -I -c "import json,sys;r=json.load(open('$d/result.json'));sys.exit(0 if r['pairs_R1']==10000000 and r['pairs_R2']==10000000 else 1)"; then echo "OK $S $1 $2 $tag" >> chain10_$S.status; return; fi
    echo "SHORT $S $1 $2 $tag" >> chain10_$S.status
  done; }
run ours f465a57 $OLD _s_ref1
for i in 1 2 3; do run ours cc26db2 $NEW _s_new$i; run minibwa c07de5c "" _s_mb$i; done
run ours f465a57 $OLD _s_ref2
echo CHAINDONE >> chain10_$S.status
