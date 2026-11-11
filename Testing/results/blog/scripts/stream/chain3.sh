cd /home/user/scratch/wg
export PATH=/opt/lean435/lean-4.35.0-linux/bin:$PATH
(cd /home/user/scratch/hol2 && lake build lean-align > /home/user/scratch/hol2.build.log 2>&1)
(cd /home/user/scratch/fix && lake build lean-align > /home/user/scratch/fix.build.log 2>&1)
export MD5=1
LA=/home/user/scratch/hol2/.lake/build/bin/lean-align TAG=_4ced python3 -I ../wgrun2.py ours 10000000 > run_ours10_4ced.log 2>&1
LA=/home/user/scratch/fix/.lake/build/bin/lean-align TAG=_fix python3 -I ../wgrun2.py ours 10000000 > run_ours10_fix.log 2>&1
LA=/home/user/scratch/fix/.lake/build/bin/lean-align TAG=_fix python3 -I ../wgrun2.py ours 20000000 > run_ours20_fix.log 2>&1
LA=/home/user/scratch/fix/.lake/build/bin/lean-align TAG=_fix python3 -I ../wgrun2.py ours 40000000 > run_ours40_fix.log 2>&1
TAG=_rerun python3 -I ../wgrun2.py minibwa 20000000 > run_mb20_rerun.log 2>&1
unset MD5
python3 -I ../wgrun2.py minibwa 40000000 > run_mb40.log 2>&1
echo CHAINDONE > chain3.done
