# Commits since `new-spec-typechecked` (90fab3d)

Branch `claude/festive-fermi-mf9mo6`; `provisional` = 6d0d218 (tag made locally; push it from a clone).
Every commit below passed `CI_check.sh` where it touched Lean code. To roll back, check out the tag or
a commit and rebuild.

## Layout and scripts (no change to what the aligner computes)
| Commit | What it did |
|---|---|
| 5d39394 | Session summary: names the `new-spec-typechecked` tag. |
| a24a2a4 | Reorganized into `Spec/`, `Proofs/` (+ `Proofs/core/`), `Aligner/`, `Bench/`; 7 PNGs removed; README with agent pointers; `fetch.sh`; `AGENT_OVERVIEW.md`. Module names unchanged. |
| 6ac467f | Renamed `Bench/` to `Testing/`. |
| 1d318e7 | `fetch.sh` adds NovaSeq 2x151; shim-vs-bench script; `WholeGenome.lean` fixed for Lean 4.35 (`String.trim`). |
| 1a31c83, dbf7881, 39c3277, c452d81 | `compare.sh`: shim / bench / minibwa (default and native); `SETS`; keeps going when a tool fails; I/O-only step on a tiny genome. |
| d48c05d, 2cdaa96 | `compare.sh`: `MB_ONCE` (minibwa once on chosen sets); bench run with the heuristic off like `alignPairs`. |

## The executable (Spec/ shim and plumbing; Spec/FROZEN.sha256 updated where Shim.lean changed)
| Commit | What it did |
|---|---|
| cc76530 | `Main.lean` is now the shim (= `Spec/Shim.lean`, importing Proofs); `Proofs/Fasta, Fastq, Sam` mirror the Spec files; CI checks the mirrors. Old pairwise tool moved to `Aligner/PairwiseMain.lean` (exe `pairwise`). |
| 1aff8c0 | Shim I/O: byte-level FASTQ reader (`FastqReader`), SAM formatted in 16 parallel parts (`samChunk`), next chunk read and previous written while one aligns. SAM byte-identical. |
| ea9134f | Lower build memory: FASTA parsed as bytes; `saveIndex` into one preallocated buffer; `compare.sh` at 2 and 4 cores with `taskset`. Index and SAM byte-identical. |
| 6989e0b | SAM sequences reversed/complemented as bytes (no `List Char`); `compare.sh` repeats timings 3x. SAM byte-identical. |
| 6d0d218 | FASTA streamed from the file (`Spec.readFasta`), never read whole; `fetch.sh` makes the uppercase `hg38.upper.fa`; notes on letter case. chr21 index byte-identical. |

## alignPairs (Proofs/ only; statements unchanged)
| Commit | What it did |
|---|---|
| dce84d2 | Router helpers moved from the bench into `Aligner/mapper/TierHeur.lean`; `alignPairs` runs with the bench's RTX settings (budget gate, ceiling, heuristic, exact pair search). |
| d9b67f0 | `alignPairs` maps each chunk on all cores (`ParMap.parMap`, proved = `map`; `alignPairs_eq_map`). |
| 606084c | Tier 2 heuristic OFF in `alignPairs` (bounds-only answers never use it; ~2.4x faster on easy reads; 0.4% of SAM bounds change, mostly tighter). Re-enable for M2. |
| 1741ee4, a3bc17d, 1bb47ec (+ merge) | Index views (from `speed/index-views`): `loadIndex` reads `G.w`, `ix.sl`, `ix.offs` in place in the saved bytes; `roundTrips` and its second copy removed; `loadIndex_buildIndex` re-proved. SAM identical. |
| 75d5651 | Notes: the heuristic is off and why. |
