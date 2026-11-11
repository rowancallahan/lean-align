cd /home/user/scratch/wg
export PATH=/opt/lean435/lean-4.35.0-linux/bin:$PATH
while pgrep -f "wgrun2.py ours 10000000" >/dev/null; do sleep 5; done
(cd /home/user/scratch/fast && lake build lean-align > /home/user/scratch/fast.build.log 2>&1)
FAST=/home/user/scratch/fast/.lake/build/bin/lean-align
run() { # tool N tag [LA]   -- reruns (new tag suffix) up to 3 times until both mates delivered N pairs
  for i in 1 2 3; do
    t=$3; [ $i -gt 1 ] && t=$3_try$i
    LA=$4 TAG=$t python3 -I ../wgrun2.py $1 $2 > run_$1_$2$t.log 2>&1
    d=n$2_$1$t
    if python3 -I -c "import json,sys;r=json.load(open('$d/result.json'));sys.exit(0 if r['pairs_R1']==$2 and r['pairs_R2']==$2 else 1)"; then echo "OK $d" >> chain4.status; return; fi
    echo "SHORT $d" >> chain4.status
  done; }
export MD5=1
run ours 10000000 _fast $FAST
run ours 20000000 _fast $FAST
run ours 40000000 _fast $FAST
unset MD5
run minibwa 20000000 "" ""
run minibwa 40000000 "" ""
echo CHAINDONE >> chain4.status
