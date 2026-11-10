cd /home/user/scratch/wg
export PATH=/opt/lean435/lean-4.35.0-linux/bin:$PATH
while pgrep -f "wgrun2.py ours 10000000" >/dev/null; do sleep 5; done
echo "OK n10000000_ours_fast (6164113) done" >> chain5.status
(cd /home/user/scratch/fast2 && lake build lean-align > /home/user/scratch/fast2.build.log 2>&1)
F2=/home/user/scratch/fast2/.lake/build/bin/lean-align
# slow pairs on f465a57: together and singly, SAM compared with 4ced426's
cd /home/user/scratch/sp && mkdir -p f2 && ( time $F2 map ../idx/ic.idx all_R1.fq all_R2.fq f2/all.sam 100 1000 2> f2/all.err ) 2> f2/all.time
for n in 01 02 03 04 05 06 07 08 09 10; do /usr/bin/env bash -c "s=\$(date +%s.%N); $F2 map ../idx/ic.idx slow${n}_R1.fq slow${n}_R2.fq f2/s$n.sam 100 1000 2>/dev/null; e=\$(date +%s.%N); echo slow$n \$(echo \"\$e-\$s\"|bc)" >> f2/single.times; done
cd /home/user/scratch/wg
run() {
  for i in 1 2 3; do
    t=$3; [ $i -gt 1 ] && t=$3_try$i
    LA=$4 TAG=$t python3 -I ../wgrun2.py $1 $2 > run_$1_$2$t.log 2>&1
    d=n$2_$1$t
    if python3 -I -c "import json,sys;r=json.load(open('$d/result.json'));sys.exit(0 if r['pairs_R1']==$2 and r['pairs_R2']==$2 else 1)"; then echo "OK $d" >> chain5.status; return; fi
    echo "SHORT $d" >> chain5.status
  done; }
export MD5=1
run ours 10000000 _f465 $F2
run ours 20000000 _f465 $F2
run ours 40000000 _f465 $F2
unset MD5
run minibwa 20000000 "" ""
run minibwa 40000000 "" ""
echo CHAINDONE >> chain5.status
