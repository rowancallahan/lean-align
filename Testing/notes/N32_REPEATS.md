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
