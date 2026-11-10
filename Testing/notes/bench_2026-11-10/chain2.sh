# wait for base run, build 64ae73f, md5 check, time
while pgrep -f 'bench/run.sh /root/bench/log_base' >/dev/null; do sleep 10; done
export PATH=$HOME/.elan/bin:$PATH
cd /root/wt-mapfiles && git fetch -q origin spec/mapfiles && git checkout -q 64ae73f && lake build lean-align 2>&1 | tail -1 && cp .lake/build/bin/lean-align /root/bin/mapfiles_64ae73f
cd /root && bash bench/run.sh /root/bench/log_mapfiles.txt "mf:/root/bin/mapfiles_64ae73f"
echo FINISHED
