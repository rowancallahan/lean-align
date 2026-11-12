cd /home/user/scratch/wg
OLD=/home/user/scratch/fast2/.lake/build/bin/lean-align
NEW=/home/user/scratch/all/.lake/build/bin/lean-align
run() { # label LA tag
  for try in 1 2 3; do
    tag=$3; [ $try -gt 1 ] && tag=${3}_try$try
    LA=$2 LABEL=$1 python3 -I ../wgrun3h.py ours 10000000 $tag > run11_$1$tag.log 2>&1
    d=h10000000_ours$tag
    if python3 -I -c "import json,sys;r=json.load(open('$d/result.json'));sys.exit(0 if r['pairs_R1']==10000000 and r['pairs_R2']==10000000 else 1)"; then echo "OK $1 $tag" >> chain11.status; return; fi
    echo "SHORT $1 $tag" >> chain11.status
  done; }
run cc26db2 $NEW _ab_warm
for i in 1 2 3 4 5 6; do run cc26db2 $NEW _ab_new$i; run f465a57 $OLD _ab_old$i; done
echo CHAINDONE >> chain11.status
