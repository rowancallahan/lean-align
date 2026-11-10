# Profile of festive 027ef1e (callgrind, Ir)

Setup: Lean 4.35.0 (GitHub release tarball), `lake build lean-align`; ic.idx built by this code from hg38.upper.fa
(27 min, 5,338,015,764 B, same size as BENCH_SETUP). Reads: first 4000 pairs of the release's novaseq_200k and hg002_200k
(HiSeq 2x250). Mapped 7462/8000 (nova) and 7512/8000 (hg) reads. `valgrind --tool=callgrind la map ic.idx R1 R2 /dev/null 100 1000`.
Total Ir: nova 1.862 G (466 k/pair), hg 2.079 G (520 k/pair). Index load costs ~0 Ir (it is sys time). 4000 pairs = one job (jobPairs 16000),
so the 4 workers are not exercised; inclusive shares are of total Ir. Lists in profile/ (top30_*). Inclusive numbers of recursive/nested functions overlap.
Writing goes to /dev/null: not visible.
