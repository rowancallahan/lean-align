# EC2-script and verify.sh check on a 4-core box (2026-11-10/11)
Box: Firecracker VM, 4 vCPU Xeon 2.3 GHz (no SMT), 15 GB RAM, 252 GB disk (~40 GB usable). festive worktree 54229dd for Testing/ec2 (code = f465a57 lineage); verify.sh on 79af844. minibwa c07de5c.
ec2 runs: `THREADS=4 REPS=3 bash Testing/ec2/run.sh full WORKDIR` (nova5m/ and hiseq5m/: timing.tsv, compare.txt). Script fixes are on fix/ec2-scripts (ccc7cd9), not used for these two runs.
WORKDIR (made by hand, not setup.sh): ours.idx -> ic.idx built by festive e96862d (5,338,015,764 B) + ours.idx.chromosomes; mb.l2b, mb.mbw -> bench-release minibwa index; minibwa/minibwa -> minibwa c07de5c binary;
venv/ with pysam 0.24.1; reads_R{1,2}.fq.gz -> first 5M pairs of the HG002 NovaSeq 30x (nova5m) or GIAB HG002 2x250 D1_S1_L001 (hiseq5m); cmp_R{1,2}.fq.gz = first 1M pairs of it; reads.bases/cmp.bases with setup.sh's awk.
verify/: `P=$PB SETS=novaseq_200k INDEX=ic.idx MBINDEX=$PB/mb MINIBWA=... GENOME=$PB/genome.fa THREADS=4 REPEAT=3 SAMTOOLS="venv/bin/python Testing/scripts/samtools_pysam.py" bash Testing/verify.sh /root/vfy` (one step at a time).
Steps 1-4 PASS (472 theorems, standard axioms only; HARD A-D = 0 in 9 cells; unique genome identical); step 5 was rerun alone after a container restart (step5_rerun.log; speed.txt is from that rerun).
No SAM files are included. Numbers are in the session reports; method notes in Testing/notes/BENCH_SETUP.md.
