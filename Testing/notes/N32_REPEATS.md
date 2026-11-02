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
