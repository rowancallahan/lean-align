#!/bin/bash
# Whole benchmark unattended: setup, timing + agreement, optional verify, pack the results, power off.
#   nohup bash Testing/ec2/all.sh full ~/bench > ~/all.out 2>&1 &
# Options (environment): VERIFY=1 also runs Testing/verify.sh (about 15 min more);
#                        NO_SHUTDOWN=1 leaves the machine on (use it for `tiny` on a laptop).
# Result: WORKDIR/results.tgz (all.log, timing.tsv, compare.txt, verify output). The machine powers off even if a
# step fails, so a broken run does not keep costing money; all.log ends with the exit code of each step.
set -uo pipefail
MODE=$1; mkdir -p "$2"; W=$(cd "$2" && pwd); cd "$(dirname "$0")/../.."
{
  date; git rev-parse HEAD; nproc; free -g | head -2
  bash Testing/ec2/setup.sh "$MODE" "$W"; echo "SETUP EXIT $?"
  bash Testing/ec2/run.sh "$MODE" "$W";   echo "RUN EXIT $?"
  if [ "${VERIFY:-0}" = 1 ]; then
    sudo apt-get install -y samtools
    mkdir -p "$W/sets"
    for r in 1 2; do gzip -dc "$W/cmp_R$r.fq.gz" | head -n 800000 > "$W/sets/nova200k_R$r.fq"; done
    P=$W/sets SETS=nova200k INDEX=$W/ours.idx MBINDEX=$W/mb MINIBWA=$W/minibwa/minibwa SAMTOOLS=samtools \
      GENOME=$W/genome.fa THREADS=$(nproc) bash Testing/verify.sh "$W/verify"; echo "VERIFY EXIT $?"
  fi
  date
} > "$W/all.log" 2>&1
cd "$W" && tar czf results.tgz all.log $(ls timing.tsv compare.txt minibwa.log verify/*.log verify/*.txt 2>/dev/null)
[ "${NO_SHUTDOWN:-0}" = 1 ] || sudo shutdown -h now
