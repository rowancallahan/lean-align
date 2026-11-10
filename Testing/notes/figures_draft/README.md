# Draft of the paper's two short-read figures (not final)

`python3 make_figs.py SAMDIR` (needs matplotlib) reads `ours_{mason,low,high}.sam` and `mb_{mason,low,high}.sam`. Outputs: `roc.png`/`roc.tsv`, `speed_paper.png`, `speed_4threads.png`/`.tsv`.

## roc.png / roc.tsv (paper Fig 2 style)
- Data: our simulator Testing/benches/sim_pairs.py, modes mason/low/high, seed 1, 100k pairs each (200k reads), mapped to hg38.
  Mason v2.0.9 (the paper's `--illumina-read-length 150 --illumina-prob-mismatch-scale 2.5`) is NOT installed here and was not tried to install; sim_pairs.py's "mason" mode only approximates it, and low/high are our own haplotype-variant models. Not the paper's data.
- Per READ (not per pair), supplementary/secondary records dropped. Correct = same chromosome and |mapped interval ∩ true interval| / |∪| >= 10%; mapped interval = POS .. POS + reference span of the CIGAR; true interval = the mate's interval in the read name.
- x = reads with flag 4 unset (and MAPQ >= threshold) / all 200k reads. y = correct among those.
- minibwa c07de5c: one point per MAPQ threshold 60,59,58,57,56,55,50,45,40,35,30,25,20,15,10,5..0, cumulative from high to low.
- lean-align 027ef1e: two points. MAPQ 60 (= XU:Z:unique) and MAPQ>=0 (all mapped reads, MAPQ 0 or 60).
- Pairs we leave unmapped count as unmapped reads (x < 1).

## speed_paper.png (paper Fig 3 style)
Paper numbers as published: WGS HG002 NovaSeq, 32 threads, 2x Xeon Gold 6130, from the paper's perf.tsv (`paper_perf.tsv`). Gbp/hr and peak GB for nine tools.

## speed_4threads.png / .tsv (separate; NOT comparable to the paper bars)
Our box, 4 threads, 1M NovaSeq plain pairs (2x151, 0.302 Gbp), from the orchestrator's numbers: map time 17.2 s (ours) vs 44.3 s (minibwa); Gbp per core-hour (whole run) 16.8 vs 6.2; peak RSS ours 5.9 GB. Gbp/hr in the TSV is derived as 0.302/map-seconds*3600 (63.2 vs 24.5), not measured separately. minibwa peak RSS not measured (n/a). I did not re-measure these.
