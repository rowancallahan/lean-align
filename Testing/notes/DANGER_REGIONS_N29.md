# Danger regions (n29, `speed/n29-danger`): measurements and proof route

Rowan's idea: mark, at index build, the seeds whose every occurrence lies in an exact duplicated region; a
read whose hitting seeds are all such "danger" seeds is a multimapper, so stop searching early.

## Data caveat

This box could not download chr21 or the read sets (the environment's network policy refuses
ngi-igenomes / giab S3, storage.googleapis.com, UCSC, NCBI; the repo has no release). All numbers below are from a
**synthetic** genome: `Testing/scripts/sim_genome_dup.py <dir> 40 1 21` (sim_genome.py plus ~5% exact and ~3%
near-exact 2–10 kb segmental copies; 40 Mb, one chromosome), with sims `sim_pairs.py … 200000 mason|low 7`.
It is far more repetitive than chr21: **23.1%** of bases lie inside an exact duplicated 150-mer
(`Testing/benches/dup_mask.py`), and **18–20%** of pairs are mate ties (chr21: 6.7%). Treat the percentages as
upper bounds for chr21; repeat on chr21 (and the two real sets) before deciding anything.

## Step 1: where tie pairs spend time (bench RTX, WG_XH=0, 4 cores, CPU s, median of 3)

| set   | pairs | tie pairs | CPU tie / rest | µs per pair tie / rest | tie share of CPU |
|-------|------:|----------:|---------------:|-----------------------:|-----------------:|
| mason | 200k  | 36 937    | 3.09 / 6.31    | 84 / 39                | 33%              |
| low   | 200k  | 40 064    | 4.91 / 4.96    | 123 / 31               | 50%              |

Tie pairs only, by stage (switching stages off on the tie subset; mason / low):
RT ≈ 1.0 / 0.7 s; floors (`mateT`) ≈ 0.5 s; ceilings (`ceilX`) ≈ 0.3 s; the exact pair search `xe`
(`pairGXE`, TierOpt) ≈ 1.3 / 3.3 s. `xe` dominates, and it is what ends in `T1um`.

Final tags of tie pairs (mason): T3 18.5k, T2 9.0k, T1um 5.1k, T1u 4.2k, T2b 71.

## Danger flag (WG_DANGER=<mask>: a seed is danger when all its occurrences lie in the dup150 mask)

Pairs with both mates' hitting seeds all danger:

| set   | flagged | of them ties | ties flagged | CPU of flagged pairs | of total |
|-------|--------:|-------------:|-------------:|---------------------:|---------:|
| mason | 18 450  | 16 449 (89%) | 44%          | 1.05 s               | 11%      |
| low   | 16 299  | 15 768 (97%) | 39%          | 1.28 s               | 13%      |

- Answering flagged pairs at once saves at most 11–13% here, so **≈4% on chr21** at a third of the tie rate
  (estimate). The danger flag catches the cheaper ties: unflagged ties cost 2–4× more per pair.
- An immediate answer changes the output: flagged pairs include RT-unique T1 pairs (527 mason / 439 low) and
  pair-unique T1u (757 / 1098), and lose their floors (bound 0 instead).
- Check cost: per seed **key** (what the numbers above use) needs a lookup per seed: the prototype pays
  ~18 µs per pair and is net slower (mason 9.4 → 12.0 s). One bit per **bucket** (B = 26, `WG_DTAB=1`) is
  cheap but flags only 890 / 841 tie pairs (2%): buckets mix keys, so few are all-duplicate. A useful
  cheap flag needs a bit per index **entry** (index format change), checked only on entries the lookup
  reads anyway.

## Proof route

- **(a) hint only.** Any gate is already sound (`tierPair_sound` holds for any `cfg.gate`; it only
  skips RT). An immediate answer `T3` with zero floors is sound with no new proof (`FloorOk` from
  `mateFloor_zero`, `pf = none`), whatever the danger table says: an unchecked table is harmless as a hint.
  But it changes the SAM (tier, bound), so it could only ship default-off.
- **(b) proved tie by byte compare.** Prototype `WG_TWIN=1`: on a T2 pair where `xe` would run and `t2Opt`
  already proves the ceiling pair (x, y) is a best proper pair, shift (x, y) by the other occurrences of
  mate 1's rarest seed and byte-compare both windows. A distinct proper twin with identical windows scores the
  same, so both are best and `pairSpecUT = none` at every caps ≥ c (`bestPairD` needs a strict winner):
  `PairTieOk`, i.e. `T1um`'s claim. Because `tierXE`'s result is determined by the spec (`pairGXE_sound`:
  seen ↔ a proper pair within c, r = `pairSpecUT`), firing in `xe`'s place gives the **same tag** as `xe`,
  so the output stays identical by construction. Measured: the dumps (tiers, RTX) are byte-identical with
  and without; every fire matched a base `T1um`. But it fires on only 884 mason / 2344 low pairs (2.4% /
  5.9% of ties): ~70% of `T1um` pairs fail `t2Opt` (floors below the ceiling sum), so "best" still needs
  `xe`. CPU unchanged within noise. Not worth the proof work now. Reverse-strand twins are not tried
  (they would need a reversal lemma for the alignment score).
- Note: in M1 `answerOf` reports `T1um` with bound 0 (the `_ => 0` case), weaker than the T2 floors it
  replaces, so `xe` on tie pairs (1.3–3.3 s here) buys a tier label and a weaker bound until M2 reports
  multimappers.

## Recommendation

Do not put danger regions in the proved path now: ≈4% (estimated) on chr21 for an output change, or an
index format change for a cheap per-entry bit. Revisit with M2, when `.multimapper` reaches the SAM: then
route (b) plus a per-entry danger bit at index build (as a hint, so no index check needed).

## Bench switches (whole_genome, mode RTX; all default off; output unchanged when off)

`WG_TWIN=1` twin shortcut (`=2` also marks tags: `w` fired, `n` no twin, `o` no `t2Opt`); `WG_TWBK` bucket
limit for the twin seed (500). `WG_DANGER=<mask>` per-pair dump `danger_<set>.tsv` (hit seeds, danger seeds
per mate). `WG_DSTOP=1` flagged → T3 at once; `=2` after RT (slow: re-implements the RT step outside the
router); `=3` flag only (tag suffix `d`). `WG_DTAB=1` flag from one bit per bucket instead of a lookup.
Scripts: `Testing/scripts/sim_genome_dup.py`, `Testing/benches/dup_mask.py`, `Testing/benches/split_by_dump.py`.
