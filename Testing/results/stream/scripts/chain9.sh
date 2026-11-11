cd /home/user/scratch/wg
run() { t=$1; i=$2
  for try in 1 2 3; do
    tag=_rep$i; [ $try -gt 1 ] && tag=_rep${i}_try$try
    python3 -I ../wgrun3h.py $t 10000000 $tag > run3h_${t}$tag.log 2>&1
    if python3 -I -c "import json,sys;r=json.load(open('h10000000_$t$tag/result.json'));sys.exit(0 if r['pairs_R1']==10000000 and r['pairs_R2']==10000000 else 1)"; then echo "OK $t $tag" >> chain9.status; return; fi
    echo "SHORT $t $tag" >> chain9.status
  done; }
run minibwa 2; run ours 3; run minibwa 3
echo CHAINDONE >> chain9.status
