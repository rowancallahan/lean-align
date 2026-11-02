# n32: repeats and ties on short reads (branch `speed/n32-repeats`, 2026-11-02)

Base ce7ea1d (festive-fermi final proven head). hg38 release `bench-release`; 4 cores, 15 GB. CI_check passes.

## 1. Where the CPU went (`lake exe tie_prof INDEX R1 R2 [N]`, 1 thread, per tag / RT reason / lookup cost)
- Base, mason 20k: tie pairs 24% of CPU, almost all inside RT's whole-genome mate search (`mateKP`), not in
  `tierUp`/xe (<1%). Tied mates spent ~75% of that in the gapped stage (stage K) after phase 1 already had the
  tie (mates tied at the cap 16: 2,900 anchors each).
- By lookup cost (sum of the `sbound c + 1` rarest buckets per strand, worse mate): pairs over 2k places are
  ~11% of pairs but 66% (mason) / 57% (NovaSeq) of mapping CPU, and most of them are unique T1 pairs.

## 2. Tie cut (proved, output byte-identical) — `Aligner/mapper/TieCut.lean`
When phase 1's best is a tie at `p`, a window scoring `p` changes nothing (`Best.add` keeps the tie), so:
- the gapped stages run at cap `p − 1` from a fresh best (`tieCut`); result = that best if below `p`, else the tie;
  a tie at 0 skips them;
- phase 1 stops on `effP` (`p − 1` for a tie): `sbound (p − 1) + 1` lookups per strand (`ilGT`, compiled `ilGFGNT`).
`mapChromsGBT_inv` = `mapChromsGB_inv`'s statement: the existing `kbFold` runs at cap `p − 1`; phase 1's
same-length windows within `p − 1` cannot exist (`gsOk_cap`). `mateKP` uses it; `mateKP_ok`, `KerOk`, `tierPair_sound`
unchanged. Callgrind 5000 pairs: mason 7.92G → 6.37G Ir (−19.5%), NovaSeq 3.92G → 3.64G (−7.2%); SAM identical on
mason, NovaSeq, low, HiSeq (200k).
Tried and dropped: the same cut for region searches (only the penalty is read there): −1.4% mason, +0.9% NovaSeq.

## 3. Per-mate caps (Rowan's "super-common seeds possibly spoiled") — `Proofs/Aligner.lean`
`RouteCfg.cap1` takes the mate (was its length). `pairCfg`: a mate < 200 letters whose rarest `sbound c + 1` buckets per
strand hold more than `capBudget` places is searched at 15 (one seed fewer), else 11; the gate skips RT when even cap 11
is over `capBudget` (`budOf`; reads ≥ 200 keep cap and `gateBudget` 60000, HiSeq SAM identical). Any `TierCfg` is sound,
so `alignPairs_correct` is unchanged; a lower cap only weakens RT's claims for that mate.

| capBudget | mason Ir (5k) | NovaSeq Ir | mason unique / at truth | low unique / at truth | NovaSeq unique / mapped |
|---|---|---|---|---|---|
| base (gate 60000 at 16) | 7.92G | 3.92G | 88.22 / 93.80% | 94.61 / 96.63% | 81.97 / 92.87% |
| 15000 | 6.23G | 3.65G | 88.20 / 93.82% | 94.75 / 96.65% | 82.07 / 92.89% |
| **10000 (default)** | 5.22G | 3.58G | 88.06 / 93.78% | 94.63 / 96.62% | 81.95 / 92.91% |
| 5000 | 4.43G | 3.12G | 87.63 / 93.64% | 94.21 / 96.50% | 81.51 / 92.97% |
(all with the tie cut; "at truth" = both mates within 20 of the true start, right chromosome and strand; `sam_stats.py`.)
Degenerate pairs at 10000: mason 0.63 → 0.64%, NovaSeq 0.97 → 1.02%. For comparison, the plain gate at 15000 (cap 16):
mason −29% CPU for −4,554 unique pairs; per-mate caps at 5000 give −38% for −2,364.
Left: `capFor` prepares each mate a second time (~7% of NovaSeq Ir); sharing `tierPairBS`'s preparation needs a
router hook.

## 4. Timing (4 threads, median of 3, FASTQ + SAM, load subtracted) — `Testing/scripts/shim_ab.sh`, `ab_med.py`
minibwa c07de5c (default / `-O3 -march=native`), load = its "index loaded" time. Ours: an untimed empty run, then a
timed one (= load), then the set; our builds run as one group (interleaving minibwa evicts our index from the page
cache and makes the empty-run load meaningless).

| set | minibwa default / ours | native / ours | CPU (default / native) | ours CPU base → n32 |
|---|---|---|---|---|
| mason 2×150 | 15.2 s / 9.4 s = 1.62x | 14.6 / 9.4 = 1.55x | 1.72x / 1.68x | 48.5 → 32.6 s (base: 0.96x) |
| NovaSeq 2×151 | 13.3 s / 8.8 s = 1.51x | 13.9 / 8.8 = 1.58x | 1.81x / 1.91x | 29.7 → 27.3 s (base: 1.58x) |
NovaSeq's wall did not move (8.4 → 8.8 s, noise) although its CPU fell: 27 s CPU on 4 cores is 6.8 s, the rest is
outside alignPairs (FASTQ reading / SAM writing in Main.lean, not edited).

## 5. Combined matrix after merging festive-fermi 12d1016 (quality trimming in the shim)
Same box, minibwa c07de5c default, 4 threads, FASTQ + SAM in, load subtracted; ours median of 5 (NovaSeq, mason) or 3,
minibwa median of 3. Our load is measured inside each run (`timed_load.py`); the separate empty-run load of §4 turned out
unreliable once trimming runs were added (2-12 s run to run, impossible values), so §4's numbers are superseded.
a = 12d1016; b = + n32 (capBudget 10000); c = b, capBudget 5000; d = b + chunk 20000; e = chunk 10000;
f = first chunk 10000, then 100000 (d-f: Main.lean literal changed locally only, not committed).

| set | a | b | c | d | e | f |
|---|---|---|---|---|---|---|
| NovaSeq (mb 14.2 s) | 12.5 s 1.13x | 10.5 s 1.35x | 9.9 s 1.43x | 9.4 s **1.50x** | 9.9 s 1.43x | 10.4 s 1.36x |
| CPU ratio | 1.40x | 1.60x | 1.74x | 1.66x | 1.68x | 1.62x |
| mason (mb 14.1 s) | 15.2 s 0.93x | 11.1 s 1.27x | 9.8 s 1.44x | 10.2 s 1.38x | 10.1 s 1.39x | 10.8 s 1.30x |
| CPU ratio | 1.09x | 1.49x | 1.75x | 1.52x | 1.52x | 1.51x |
| low (mb 9.9 s) | 8.8 s 1.13x | 8.3 s 1.19x | 7.6 s 1.30x | 7.2 s 1.38x | 6.7 s 1.47x | 8.5 s 1.17x |
| HiSeq 200k (mb 28.7 s) | 13.4 s 2.14x | 12.1 s 2.37x | 11.7 s 2.46x | 10.1 s 2.86x | 10.1 s 2.84x | 12.5 s 2.31x |

SAM split (real mapped / degenerate / unique; d-f identical to b):
| set | a | b | c |
|---|---|---|---|
| NovaSeq | 95.06 / 2.63 / 82.50% | 95.07 / 2.65 / 82.44% | 95.09 / 2.72 / 81.94% |
| mason (at truth) | 97.00 / 0.92 / 87.21% (93.91%) | 97.00 / 0.94 / 86.99% (93.87%) | 96.98 / 0.99 / 86.51% (93.70%) |
| low (at truth) | 99.70 / 0.15 / 94.68% (96.69%) | 99.70 / 0.15 / 94.68% (96.67%) | 99.70 / 0.16 / 94.23% (96.54%) |
| HiSeq | 92.86 / 1.12 / 82.01% | 92.87 / 1.13 / 81.87% | 92.90 / 1.19 / 81.71% |
HiSeq now changes too: trimmed mates under 200 letters get per-mate caps.

## 6. Headline round on festive-fermi ad6f7df (= f3f7be1 for the shim: capBudget 5000, chunk 20000)
`Testing/scripts/headline.sh`: one tool at a time, the other tool's index dropped from the page cache (posix_fadvise),
own index read before every run, our empty-FASTQ run right before each timed run, load measured in the run
(`timed_load.py`); 4 threads, median of 3, FASTQ + SAM in. g = shipped head; g10 = same with capBudget 10000.

| set | minibwa default / ours (g) | native / g | CPU (def) | g10 | user CPU g / mb |
|---|---|---|---|---|---|
| NovaSeq 200k | 14.5 s / 8.3 s = **1.75x** | 1.73x | 1.84x | 1.74x (CPU 1.91x) | 26.0 / 50.9 s |
| mason | 14.2 / 7.2 = 1.97x | 1.97x | 2.12x | 1.54x | 23.0 / 48.8 |
| low | 11.1 / 5.7 = 1.94x | 1.86x | 2.06x | 1.87x | 17.4 / 36.9 |
| HiSeq 200k | 27.3 / 10.0 = 2.72x | 2.71x | 3.19x | 2.79x | 29.6 / 99.5 |
Min wall (ours g): NovaSeq 7.5, mason 7.2, low 5.7, HiSeq 8.3 s. Runs within ~1 s of each other.

SAM split g (real mapped / degenerate / unique / at truth): NovaSeq 95.09 / 2.72 / 81.94; mason 96.98 / 0.99 / 86.51 / 93.70;
low 99.70 / 0.16 / 94.23 / 96.54; HiSeq 92.90 / 1.19 / 81.71. (g10: NovaSeq 95.07 / 2.65 / 82.44; mason 97.00 / 0.94 /
86.99 / 93.87; low 99.70 / 0.15 / 94.68 / 96.67; HiSeq 92.87 / 1.13 / 81.87.)

Degenerate pairs with a mate trimmed short (shorter mate's SEQ length): NovaSeq 5,436 degenerate: < 50 bp 915 (16.8%),
< 75 bp 1,314, < 100 bp 1,721, < 151 (any trimming) 4,578 (84%). HiSeq: 2,385, < 50 bp 613 (25.7%).
Pair score (AS1 + AS2) of real mapped pairs (all-insertion CIGARs excluded), share below −16 / −32 / −50 / −64 / −100:
NovaSeq 9.26 / 5.14 / 3.68 / 3.08 / 2.40%; HiSeq 8.78 / 4.49 / 3.61 / 3.20 / 2.62%.

## 7. Headline round on festive-fermi e384063 (ad6f7df + speed/n32-kernels), 2026-11-02 evening
Commits: ours = festive-fermi e384063 (shim built from that tree: capBudget 5000, chunk 20000); minibwa = lh3/minibwa
c07de5c, `make` default flags. Index: release `bench-release` (shim.idx, mb.*). Box: 4 cores, 15 GB, nothing else running.
Invocation (from the repo root; S = scratchpad holding the two binaries):

    sh Testing/scripts/headline.sh OUT 'k:$S/v.k mbdef:$S/minibwa' 'novaseq:novaseq_200k'
    sh Testing/scripts/headline.sh OUT 'k:$S/v.k mbdef:$S/minibwa' 'mason:hg38_mason low:hg38_low hiseq:hg002_200k'
    python3 -I Testing/scripts/ab_med.py LOG

headline.sh: THREADS=4 (taskset 0-3, `map -t 4` for minibwa), REPEAT=3; per set all our runs, then all minibwa runs; before
a tool's group the other tool's index is dropped from the page cache (posix_fadvise DONTNEED); before every run the
tool's own index is read once (cat > /dev/null); our timed runs are preceded by an empty-FASTQ run (timed, not used) and
timed by timed_load.py, which measures the load inside the run (time and CPU until the process has read
index-file-size bytes). minibwa's load = its own "index loaded" wall and wall × CPU ratio. FASTQ read and SAM write
included. Headline = median of (wall − load); CPU = median of (CPU − load CPU).

| set | minibwa / ours (wall − load) | CPU | end-to-end wall |
|---|---|---|---|
| NovaSeq 200k | 15.7 s / 6.2 s = **2.51x** | 57.0 / 20.9 s = 2.73x | 29.5 / 7.9 s |
| mason | 14.7 / 8.0 = 1.85x | 54.2 / 26.9 = 2.01x | 28.4 / 9.7 |
| low | 9.7 / 5.4 = 1.80x | 34.0 / 17.5 = 1.94x | 19.8 / 9.7 |
| HiSeq 200k | 28.0 / 7.9 = 3.56x | 107.1 / 26.4 = 4.06x | 39.2 / 10.6 |

Noise: our three runs per set agree within ~1 s on wall − load (NovaSeq 6.2 / 6.2 / 6.5 s); minibwa within ~1.5 s. Across
rounds on different days / page-cache histories the same build moved ~10% (mason 7.2 s in §6 vs 8.0 s here, same Ir — below).

Raw lines (ours: TIME with in-run load; minibwa: TIME and MBLOAD = index-loaded wall, CPU ratio):

    TIME novaseq k r1: wall 7.9 s, cpu 22.6 s, user 18.5 s, sys 4.0 s, load 1.75 s, loadcpu 1.73 s, peak 5.43 GB, exit 0
    TIME novaseq k r2: wall 7.9 s, cpu 22.2 s, user 19.0 s, sys 3.1 s, load 1.65 s, loadcpu 1.63 s, peak 5.44 GB, exit 0
    TIME novaseq k r3: wall 8.2 s, cpu 23.9 s, user 20.4 s, sys 3.5 s, load 1.72 s, loadcpu 1.66 s, peak 5.43 GB, exit 0
    TIME novaseq mbdef r1: wall 37.9 s, cpu 79.5 s, user 56.2 s, peak 7.69 GB, exit 0
    MBLOAD novaseq mbdef r1 22.681 0.99
    TIME novaseq mbdef r2: wall 27.7 s, cpu 71.1 s, user 58.8 s, peak 7.69 GB, exit 0
    MBLOAD novaseq mbdef r2 11.075 0.99
    TIME novaseq mbdef r3: wall 29.5 s, cpu 70.7 s, user 55.7 s, peak 7.70 GB, exit 0
    MBLOAD novaseq mbdef r3 13.811 0.99
    TIME mason k r1: wall 13.6 s, cpu 34.1 s, user 27.3 s, sys 6.8 s, load 5.04 s, loadcpu 5.00 s, peak 5.43 GB, exit 0
    TIME mason k r2: wall 9.7 s, cpu 28.3 s, user 25.0 s, sys 3.3 s, load 1.74 s, loadcpu 1.72 s, peak 5.41 GB, exit 0
    TIME mason k r3: wall 9.6 s, cpu 28.7 s, user 24.7 s, sys 4.0 s, load 1.79 s, loadcpu 1.75 s, peak 5.42 GB, exit 0
    TIME mason mbdef r1: wall 33.4 s, cpu 73.0 s, user 51.9 s, peak 7.86 GB, exit 0
    MBLOAD mason mbdef r1 18.895 0.99
    TIME mason mbdef r2: wall 27.7 s, cpu 66.6 s, user 52.6 s, peak 7.87 GB, exit 0
    MBLOAD mason mbdef r2 12.954 0.99
    TIME mason mbdef r3: wall 28.4 s, cpu 67.5 s, user 52.9 s, peak 7.86 GB, exit 0
    MBLOAD mason mbdef r3 13.451 0.99
    TIME low k r1: wall 9.7 s, cpu 22.7 s, user 16.4 s, sys 6.3 s, load 4.07 s, loadcpu 4.03 s, peak 5.43 GB, exit 0
    TIME low k r2: wall 10.3 s, cpu 22.4 s, user 16.3 s, sys 6.1 s, load 4.93 s, loadcpu 4.89 s, peak 5.43 GB, exit 0
    TIME low k r3: wall 7.9 s, cpu 19.5 s, user 16.0 s, sys 3.4 s, load 2.65 s, loadcpu 2.60 s, peak 5.43 GB, exit 0
    TIME low mbdef r1: wall 30.3 s, cpu 56.2 s, user 33.0 s, peak 7.58 GB, exit 0
    MBLOAD low mbdef r1 20.372 0.99
    TIME low mbdef r2: wall 19.8 s, cpu 43.9 s, user 32.9 s, peak 7.58 GB, exit 0
    MBLOAD low mbdef r2 10.113 0.98
    TIME low mbdef r3: wall 16.1 s, cpu 39.5 s, user 32.0 s, peak 7.58 GB, exit 0
    MBLOAD low mbdef r3 6.568 0.99
    TIME hiseq k r1: wall 14.0 s, cpu 34.0 s, user 25.7 s, sys 8.3 s, load 5.08 s, loadcpu 5.02 s, peak 5.48 GB, exit 0
    TIME hiseq k r2: wall 9.5 s, cpu 27.1 s, user 23.1 s, sys 4.1 s, load 1.86 s, loadcpu 1.82 s, peak 5.48 GB, exit 0
    TIME hiseq k r3: wall 10.6 s, cpu 29.1 s, user 24.9 s, sys 4.2 s, load 2.74 s, loadcpu 2.72 s, peak 5.47 GB, exit 0
    TIME hiseq mbdef r1: wall 44.2 s, cpu 123.3 s, user 103.8 s, peak 8.03 GB, exit 0
    MBLOAD hiseq mbdef r1 16.234 1.00
    TIME hiseq mbdef r2: wall 39.2 s, cpu 119.5 s, user 107.8 s, peak 8.02 GB, exit 0
    MBLOAD hiseq mbdef r2 10.365 0.99
    TIME hiseq mbdef r3: wall 38.0 s, cpu 112.5 s, user 100.3 s, peak 8.03 GB, exit 0
    MBLOAD hiseq mbdef r3 10.786 0.99

Mason recheck (callgrind, `lean-align map`, first 2,000 pairs): ad6f7df 1.658G Ir, e384063 1.619G Ir (−2.4%); NovaSeq
1.406G → 1.141G (−18.8%); SAM identical on both. The kernels merge did not slow mason; 7.2 vs 8.0 s is run-to-run noise.
