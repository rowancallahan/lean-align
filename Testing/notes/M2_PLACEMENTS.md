# M2: placements in the SAM (branch m2/placements, box O3, 2026-11-02)

The shim used to print every pair unmapped (M1: `answerOf` had `found := none`). Now `Proofs/Aligner.lean`
`alignOne` answers with `Report.answerOfPair` (`Proofs/Report.lean`), proved by `Report.answerOfPair_correct`;
`alignPairs_correct` / `alignPairs_end_to_end` keep their statements. Spec/ and Main.lean are unchanged.

## What is printed
| router tag | found | uniqueness | how |
|---|---|---|---|
| T1, T1g, T1u | the pair | `unique` | `UniqHits` (T1: per-mate unique bests, `pairSpecT`; T1g/T1u: `pairSpecUT` at every cap ≥ g0) → `unique_of_uniqHits` |
| T2b, T2 | the pair in hand, if proper | `unknown` | real proper pair only |
| T1gm | one tied best pair (`pairGQCtie`) | `unknown` | real proper pair only |
| T1um | the T2 pair in hand, if proper | `unknown` | real proper pair only |
| T3 | none | `unknown` | bounds only (as M1) |

Any failure below prints nothing for the pair (`found := none`, the M1 answer, still correct).

## How a mate is printed (CIGAR by certificate)
1. The router's placement `x` (window + strand, on the packed genome read as ONE sequence) and score.
2. CIGAR proposals, cheapest first (lazy `<|>`; Lean is strict, a list forced the DP for every mate):
   all-match `[(diag, n)]` when the window has the read's length; else the router's checked runs, or the
   unproved banded DP `TierHeur.bandDP` over exactly `x`'s window.
3. The proved checker `chkCand` (`chkCand_sound`): the runs are a monotone walk of the read (on `x`'s strand)
   against the window letters with score `x.2` → `alignment_of_cigar`: a `GenomicAlignment` on the whole
   sequence whose `report` is `⟨placement, encodeCigar steps, x.2⟩`.
4. `chromOf`: the ONE chromosome slice holding the window (none or several → not printed; a runtime check,
   so the proof needs no lemma that the index's slices are disjoint) → `alignment_unshift`: the same path
   and score on the real genome, placement moved to that chromosome.
5. The pair: both mates printed and `properPairU` (slack, fragment range) → `isProper_iff`.

## Results (stage 1–4)
- `Testing/examples/sam_compare` (28 pairs, hg38 `shim.idx`): every pair the router maps lands at minibwa's
  exact position (38/38 mates, `XU:Z:unique`, MAPQ 60). The rest stay unmapped: T3 (no pair in hand: the
  router's 60000-hit lookup gate, bound 0) or T2 without a proper pair in hand, and 3 HG002 pairs.
- chr21 mason subset (2,563 pairs, chr21-only genome): both mates mapped 90.17%, both at truth 88.80%;
  2,212 unique pairs (2,198 T1, 14 T1u), 65 T2 and 34 T1um pairs printed with uniqueness unknown. The 8 mapped
  pairs not at truth are all T2 in chr21's duplicated pericentromeric region (real proper pairs, no claim).
- Cost (callgrind, 2,000 HiSeq pairs): M1 1.67G Ir, M2 2.45G Ir. Left: `chkCand` (checkRepeatGo, pushF),
  `Spec.encodeCigar` over the expanded step list, the banded DP for mates with indels, SAM formatting of
  mapped records. Next cut: print `encodeCigar` from merged runs directly (a proof that merging runs equals
  `encodeCigar ∘ expand`), and check the window letters in place instead of building `Array Char`s.

## Timing
hg38 release (`shim.idx`, minibwa c07de5c index), this box (4 cores, 15 GB), 4 threads (taskset 0-3), 3
interleaved rounds, median. Headline = index load subtracted, FASTQ read + SAM write included: ours = `lean-align
map` wall minus the empty-FASTQ load (warm cache: an untimed empty run right before each timed run; median 1.9 s);
minibwa = wall minus its `index loaded` time, SAM to a file. x = minibwa / ours (> 1: we are faster).

| set | minibwa default / ours | minibwa native / ours | CPU (default / native) | end-to-end wall (default / native) |
|---|---|---|---|---|
| mason 2x150 | 14.4 s / 20.7 s = 0.70x | 15.3 s / 20.7 s = 0.74x | 0.84x / 0.85x | 28.4 s / 22.6 s = 1.26x / 1.54x |
| HiSeq 2x250 | 25.8 s / 11.1 s = 2.33x | 26.6 s / 11.1 s = 2.40x | 3.39x / 3.37x | 42.0 s / 13.0 s = 3.23x / 3.12x |
| NovaSeq 2x151 | 14.5 s / 12.3 s = 1.18x | 15.9 s / 12.3 s = 1.29x | 1.46x / 1.45x | 25.7 s / 14.2 s = 1.81x / 2.39x |

Raw seconds (wall/CPU per round; minibwa's index-loaded wall/CPU in brackets):
- mason: ours 22.6/65.5, 27.3/67.5, 18.6/57.9; minibwa default 28.4/66.7 [14.0/13.3], 28.2/66.7 [14.0/13.7],
  29.5/68.5 [15.0/14.4]; native 37.7/76.3 [22.4/22.2], 34.9/72.7 [19.9/19.5], 30.0/71.2 [14.1/14.0].
- HiSeq: ours 13.0/30.3, 13.0/30.9, 18.1/35.4; default 42.0/113.5 [16.4/15.9], 47.3/119.3 [21.1/20.4],
  41.8/113.7 [16.0/15.5]; native 40.3/113.4 [13.7/13.4], 40.5/110.9 [14.6/14.3], 41.6/112.3 [14.7/14.5].
- NovaSeq: ours 14.2/37.7, 25.8/48.6, 13.9/39.2; default 26.1/65.6 [11.6/11.1], 25.7/67.5 [9.8/9.6],
  25.2/62.4 [11.2/10.8]; native 33.9/68.8 [20.4/20.2], 36.7/76.5 [20.8/20.6], 33.1/70.6 [16.8/16.6].
- ours, empty FASTQ: 1.9/1.9, 1.7/1.7, 13.2/13.1.

Caveat: the shim index (5.3 GB) and minibwa's (8.7 GB) do not both fit in this box's page cache, so load times
(and end-to-end numbers) vary by up to ~10 s run to run; the no-load numbers are steadier.

## Open
- `Spec/Sam.lean` prints T2/T1um pairs (uniqueness unknown) as mapped with MAPQ 0; Rowan may want a flag.
- `.multimapper` needs a second tied best pair named by the router (the tie proofs only say no unique best).
- The shim's `rtxCfg` has the pair guarantee off (`pg := none`): T1g/T1gm never occur in the shim.

## Stage 5 (2026-11-02 later): report the pair in hand; Rowan's `.unknown` clause
Spec (main f57e195): `InsertSettings.junkScore` (default −17; −16 approved, pending on main) and, for `.unknown`,
`found = none → bestPossibleScore < junkScore`. Proved here with `junkScore` as a parameter; Spec/ not edited.
- `Bridge.CorrectU` = the old clause; every router-level theorem proves it. `Proofs/LastResort.lean`
  `finalize` / `finalize_correct` turn it into `Correct`: no pair and bound ≥ junkScore → the degenerate proper
  pair (mate 1 forward on `[0,0)`, mate 2 reverse on `[lo,lo)`, insertions only) on the first chromosome with
  ≥ lo letters; none (or lo > hi) → no proper pair exists (`no_proper`), bound := junkScore − 1.
- Failed index build: `buildIndex` writes a chromosome-lengths record (tag `LENS`, base-255 digits;
  `readLens_record`), read before `loadIndex`, so the clause also holds without an index.
- Before the last resort (settings in `Proofs/Aligner.lean`): `reportTies` (ties print a pair), `fallbackOn`
  (bound ≥ junkScore: router placement, then up to 16 rarest-seed anchors per strand per mate, the other mate
  aligned near it with `nearY`; all re-checked), `mateRescue` (the fallback also on junk answers with a mate in
  hand), `gateBudget` (router lookup budget; default 60000).
- Cost cuts: CIGAR from merged runs (`encodeCigar_expand`), gap-free check as a byte compare (`chkCandD_ok`);
  both SAM byte-identical.

hg38 200k, main's junkScore −17: printed mason 100% (degenerate 1.53%), low 100% (0.19%), NovaSeq 99.97% (4.92%),
HiSeq 99.92% (9.18%); both at truth mason 95.38%, low 96.80%. With −16 the degenerate pairs fall to mason 1,261,
low 329, NovaSeq 1,938, HiSeq 1,112 (the bound −17 pairs become junk). Timing (median of 3, load subtracted,
FASTQ + SAM in): mason minibwa 15.0 s / ours 26.2 s = 0.57x (CPU 0.92x); HiSeq 26.7 s / 17.0 s = 1.57x (CPU 2.84x);
NovaSeq 13.7 s / 11.2 s = 1.22x (CPU 1.51x); our wall is noisy here, CPU steadier.

gateBudget sweep (median of 3, CPU s / unique pairs): mason 60000 60.6 / 176,444; 15000 42.7 / 171,890;
5000 30.1 / 165,474; 2000 26.6 / 160,062. NovaSeq 46.7 / 163,941; 35.4 / 159,029; 29.5 / 153,267; 26.4 / 148,763.
