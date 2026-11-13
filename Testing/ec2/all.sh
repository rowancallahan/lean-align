#!/bin/bash
# Whole benchmark unattended: setup, timing + agreement, optional verify, pack the results, power off.
#   nohup bash Testing/ec2/all.sh full ~/bench > ~/all.out 2>&1 &
# Options (environment): VERIFY=1 also runs Testing/verify.sh and `lake check --paranoid` (an hour or more);
#                        NO_SHUTDOWN=1 leaves the machine on (use it for `tiny` on a laptop).
#                        MAX_MIN=720 powers off after that many minutes whatever happens.
# Result: WORKDIR/results.tgz (all.log, timing.tsv, compare.txt, verify output). The machine powers off even if a
# step fails, so a broken run does not keep costing money; all.log ends with the exit code of each step.
set -uo pipefail
MODE=$1; mkdir -p "$2"; W=$(cd "$2" && pwd); cd "$(dirname "$0")/../.."
# a `full` run needs about 60 GB in WORKDIR; refuse to start (and do not power off) if the disk is too small
if [ "$MODE" = full ]; then
  FREE_GB=$(df --output=avail -BG "$W" | tail -1 | tr -dc '0-9')
  [ "$FREE_GB" -ge 80 ] || { echo "only $FREE_GB GB free in $W; a full run needs 80. Enlarge the disk first."; exit 1; }
fi
# safety net: power off after MAX_MIN minutes (default 12 h) even if something hangs
[ "${NO_SHUTDOWN:-0}" = 1 ] || sudo shutdown -h +"${MAX_MIN:-720}"
# for diagnosis: every 10 s, the 40 threads with the most CPU time so far (cumulative, so two samples give the rate)
( while true; do date +%s; ps -eLo pid,tid,comm,time,pcpu --sort=-time | head -41; sleep 10; done > "$W/threads.log" ) &
SAMPLER=$!
{
  date; git rev-parse HEAD; nproc; free -g | head -2; lscpu
  bash Testing/ec2/setup.sh "$MODE" "$W"; echo "SETUP EXIT $?"
  bash Testing/ec2/run.sh "$MODE" "$W";   echo "RUN EXIT $?"
  if [ "${VERIFY:-0}" = 1 ]; then
    sudo DEBIAN_FRONTEND=noninteractive NEEDRESTART_MODE=a apt-get install -y samtools
    mkdir -p "$W/sets"
    for r in 1 2; do gzip -dc "$W/cmp_R$r.fq.gz" | head -n 800000 > "$W/sets/nova200k_R$r.fq"; done
    P=$W/sets SETS=nova200k INDEX=$W/ours.idx MBINDEX=$W/mb MINIBWA=$W/minibwa/minibwa SAMTOOLS=samtools \
      GENOME=$W/genome.fa THREADS=$(nproc) bash Testing/verify.sh "$W/verify"; echo "VERIFY EXIT $?"
    # lake check --paranoid: sandboxed rebuild, export, replay through Lean's kernel and the bundled external
    # checkers (leanchecker-paranoid, lean4lean, nanoda, con-leche, con-ron); fails on any non-standard axiom.
    # The sandbox (bubblewrap) needs unprivileged user namespaces, which Ubuntu 24.04 restricts by default.
    sudo DEBIAN_FRONTEND=noninteractive NEEDRESTART_MODE=a apt-get install -y bubblewrap
    sudo sysctl -w kernel.apparmor_restrict_unprivileged_userns=0
    export PATH=$HOME/.elan/bin:$PATH
    lake check --paranoid > "$W/lake_check.log" 2>&1; echo "LAKE CHECK PARANOID EXIT $?"
    tail -30 "$W/lake_check.log"
  fi
  date
} > "$W/all.log" 2>&1
kill $SAMPLER
cd "$W" && tar czf results.tgz all.log threads.log $(ls timing.tsv compare.txt minibwa.log lake_check.log verify/*.log verify/*.txt 2>/dev/null)
[ "${NO_SHUTDOWN:-0}" = 1 ] || sudo shutdown -h now
