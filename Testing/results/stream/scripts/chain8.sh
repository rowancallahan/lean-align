cd /home/user/scratch/wg
while ! grep -q CHAINDONE chain7.status; do sleep 10; done
for i in 1 2 3; do
  for t in ours minibwa; do
    for try in 1 2 3; do
      tag=_rep$i; [ $try -gt 1 ] && tag=_rep${i}_try$try
      python3 -I ../wgrun3h.py $t 10000000 $tag > run3h_${t}$tag.log 2>&1
      if python3 -I -c "import json,sys;r=json.load(open('h10000000_$t$tag/result.json'));sys.exit(0 if r['pairs_R1']==10000000 and r['pairs_R2']==10000000 else 1)"; then echo "OK $t $tag" >> chain8.status; break; fi
      echo "SHORT $t $tag" >> chain8.status
    done
  done
done
echo CHAINDONE >> chain8.status
