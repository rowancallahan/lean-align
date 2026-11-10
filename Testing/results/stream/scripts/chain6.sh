cd /home/user/scratch/wg
export FETCH=1
for N in 20000000 40000000; do
  for i in 1 2 3; do
    t=_rf$i
    TAG=$t python3 -I ../wgrun2.py minibwa $N > run_mb_${N}$t.log 2>&1
    d=n${N}_minibwa$t
    if python3 -I -c "import json,sys;r=json.load(open('$d/result.json'));sys.exit(0 if r['pairs_R1']==$N and r['pairs_R2']==$N else 1)"; then echo "OK $d" >> chain6.status; break; fi
    echo "SHORT $d" >> chain6.status
  done
done
echo CHAINDONE >> chain6.status
