# Adapter trimming + minimum mate length (`speed/adapter-trim`)

## What
- `Aligner/trimmer/AdapterTrim.lean` (lib Trimmer). Spec predicate `matchesAt adapter minLen maxErr read i`:
  compare `len = min |adapter| (|read| − i)` letters from `i`; needs `i < |read|`, `len ≥ minLen`, mismatches
  `≤ maxErr` if the whole adapter fits, `= 0` if only a prefix fits. `cutPos` = first matching `i`, else `|read|`
  (byte scan, no allocation; the mismatch count stops at the limit).
- Proved (standard axioms only): `fastMatchesAt_eq` (scan test = spec), `cut_le`, `cut_prefix` (kept letters and
  qualities are list prefixes of the input), `cut_matches` (cut ⇒ match there), `cut_first` (no earlier match),
  `cut_none` (no cut ⇒ no match anywhere), `dropShort_size` (after `dropShort n`, empty or ≥ n letters).
- Setting `cutTruSeq` = `AGATCGGAAGAGC`, `minLen` 6, `maxErr` 1.

## Spec/Fastq.lean change (Rowan's file — needs approval; Proofs/Fastq.lean mirrors it)
`import AdapterTrim`; new `def minLength : Nat := 25`; `trimRecord` becomes adapter cut → `ReadTrim.trimRead`
→ `AdapterTrim.dropShort minLength` → record (doc comment updated). Order: adapter first, because adapter letters
are usually high quality, so the quality window would keep them. Spec/FROZEN.sha256 does not list Spec/Fastq, so it
regenerates unchanged. CI_check passes (PATH=$HOME/.elan/bin:$PATH, elan + lean 4.35.0 release linked).

## Data (200k reads per mate file)
| | TruSeq 13-mer | Nextera | cut reads R1 / R2 | bases removed R1 / R2 |
|---|---|---|---|---|
| hg38 mason | 0 | 0 | 27 / 25 | 455 / 542 |
| hg38 low | 0 | 0 | 22 / 26 | 459 / 917 |
| NovaSeq | 1,000 / 1,052 | 0 | 1,487 / 1,545 (0.76%) | 43k / 46k |
| HiSeq | 5,556 / 5,451 | 0 | 6,744 / 6,874 (3.4%) | 295k / 327k |

`minLen` from read-end matches of exactly k adapter letters (no full match), R1 per 200k: mason (no adapter, so all false)
k=5: 156, k=6: 19, k=7: 3; HiSeq k=5: 255, k=6: 166, k=7: 157; NovaSeq k=6: 82, k=7: 61. So 6.

Mates removed by the minimum length (non-empty after cut + quality trim, shorter than n), R1 / R2:
NovaSeq n=25: 156 / 1,177; n=50: 890 / 2,426. HiSeq n=25: 103 / 1,849; n=50: 652 / 3,173. Sims: ≤ 4.

## Shim on hg38, 4 threads (base = e384063; new = adapter + minLength 25; new50 = minLength 50)
| set | mapped | degenerate | unique | mapped < −50 | mapped < −100 |
|---|---|---|---|---|---|
| mason base → new | 96.978 → 96.978% | 1,972 → 1,971 | 173,017 → 173,014 | 1.464 → 1.464% | 0.995 → 0.996% |
| low base → new | 99.696 → 99.695% | 320 → 320 | 188,466 → 188,455 | 0.967 → 0.967% | 0.664 → 0.664% |
| NovaSeq base → new → new50 | 95.087 → 95.294 → 94.585% | 2.718 → 2.337 → 2.144% | 81.939 → 82.419 → 82.406% | 3.681 → 3.646 → 3.482% | 2.402 → 2.377 → 2.249% |
| HiSeq base → new → new50 | 92.903 → 95.215 → 94.371% | 1.192 → 0.798 → 0.747% | 81.713 → 84.550 → 84.526% | 3.612 → 3.524 → 3.364% | 2.622 → 2.552 → 2.413% |

Sims: 52 (mason) / 48 (low) pairs differ; at truth 187,406 → 187,402 and 193,083 → 193,077.
Adapters explain only a small part of the low-scoring pairs (< −50 drops 0.04 pts NovaSeq, 0.09 pts HiSeq); degenerate
pairs drop 14% (NovaSeq) and 33% (HiSeq). minLength 50 cuts low scores further but loses mapped pairs (mates removed).

## CPU
`adapter_bench` (one thread, scan only, best of 5): 0.68–0.75 s per 200k 150-bp reads, 1.19–1.27 s per 200k
250-bp reads (≈ 25 ns per read position), i.e. ≈ 1.4 s (NovaSeq) / 2.5 s (HiSeq) per 200k pairs; it runs inside the
chunk workers. Shim end to end (min CPU of 3 runs): NovaSeq 22.0 → 23.3 s, HiSeq 28.0 → 28.2 s; run-to-run noise on this
box is larger than that (load times 1.7–12.8 s, wall times bimodal), so the end-to-end cost is not resolved.

### Machine-word scan + skip (second round)
The compiled code runs `cutPosF` (`@[csimp] cutPos_eq_cutPosF`, standard axioms): `scanU` / `matchU` / `mmU`, the same
scan with `USize` counters and one-compare byte reads (`ReadTrim.rtGet`), for reads and adapters shorter than 2^30
(else the Nat scan). Skip: when at most 1 mismatch is allowed and ≥ 2 letters are compared, a position whose first two
letters both differ cannot match (`mmLoop_two`), so the mismatch loop is not called (about 56% of positions on random
sequence). The fast section sits before `cutAdapter` so the shim's `cutTruSeq` also compiles to it (a `csimp` lemma
only rewrites code compiled after it).

Scan only, one core, best of 7 per 200k reads (checksums of all cut positions identical):
| | Nat scan | USize | USize + skip |
|---|---|---|---|
| NovaSeq R1 / R2 | 681 / 687 ms | 426 / 413 ms | 373 / 375 ms |
| HiSeq R1 / R2 | 1142 / 1171 ms | 690 / 724 ms | 622 / 632 ms |
callgrind (20k NovaSeq reads, 3.02M positions, scan only): 803M → 358M → 310M Ir (266 → 119 → 103 Ir per position).
So ≈ 0.75 s (NovaSeq) / 1.25 s (HiSeq) of one thread per 200k pairs, down from 1.37 / 2.31 s. ~12 ns per position for ~103 Ir suggests
branch mispredictions on random letters (not measured); a 4-letter skip (3 of the first 4 must match) would cut the mismatch-loop
calls from ~44% to ~19% of positions.
