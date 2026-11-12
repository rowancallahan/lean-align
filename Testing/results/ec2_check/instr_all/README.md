# fix/instr-all cc26db2 vs festive head 00c24c5 (f465a57 code) vs minibwa c07de5c, 4-core box, 2026-11-11
timing_*.tsv: per-run rows (columns: tool, build, tool, threads, set, wall_s, cpu_s, peak_GB, Gbp, Gbp/hr, Gbp/core-hr); the duplicated 3rd column is a harness artefact.
Method: Testing/ec2/bench.py (festive c7a828e version; gzip -dc pipes, 64 KiB, same cat sink for all tools, pinned to cores 0-3, cpu = aligner + 2 gzips), 3 reps per build, order H N M / N M H / M H N in one session.
md5_*.txt: full-run SAM md5 (12 hex), new vs head, gz FIFOs. compare_*.txt: compare.py ours (cc26db2) vs minibwa on the first 1M pairs. nova5m compare was rerun after a disk-full failure.
verify_steps1-5_cc26db2.log: Testing/verify.sh steps 1-5 on cc26db2 (472 theorems; HARD A-D 0; unique genome identical; step 5 table).
