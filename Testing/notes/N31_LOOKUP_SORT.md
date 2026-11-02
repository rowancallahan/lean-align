# n31: index lookup (§1) and sorting (§4) on hg38 — box O2, 2026-11-02

Base 5c309c3; release `bench-release` (shim.idx built at f7ab094); 4 cores, 15 GB RAM. SAM byte-identical to
the base on every run below (4 sets × 3 reps × each version, and 6 callgrind subsets).

## Changes (all proved, `@[csimp]`)
| commit | what | proof |
|---|---|---|
| `diags_eqM` (FastGenAlgo) | `diags` = merge of each lookup's anchor diagonals; an array is sorted only if not already increasing (`ascB`), then balanced pairwise `List.merge` rounds, `dedupAdj` | sorted + permutation ⇒ equal (`List.Perm.eq_of_pairwise`) |
| `scanAWK_eqC` (MzWord) | `scanAWK` = `scanAWK2`: a 6-argument loop `nextK` skips to the next slot whose key bits match; the full check (`okAtW`) only on matches | `scanAWK_skip` (skipped slots add nothing) + `nextK_spec` |

Note: a `@[csimp]` lemma only rewrites calls compiled in modules that import it. The old `diags_eqI` (WgPacked)
therefore never reached the hot callers (FastGenPair, PairHits, …); `diags_eqM` sits next to `diags` and does.

## Callgrind (`lean-align map`, Ir per pair = (6000 − 2000 pairs) / 4000)
| set | base | + diags merge (m1) | + nextK (m2) |
|---|---|---|---|
| NovaSeq | 785k | 717k (−8.7%) | 714k |
| mason | 2.234M | 2.006M (−10.2%) | 1.998M |
| HiSeq | 790k | 750k (−5.0%) | — |
`List.mergeSort` + helpers: 6.3% → 1.2% of Ir (NovaSeq).

## Wall / CPU (4 threads, median of 3, order rotated per rep)
| set | base wall / CPU s | m1 | m2 |
|---|---|---|---|
| HiSeq 200k | 14.1 / 31.5 | 13.7 / 30.2 | 11.0 / 25.2 |
| NovaSeq 200k | 15.5 / 47.1 | 18.1 / 47.1 | 11.7 / 31.9 |
| mason 200k | 26.4 / 82.0 | 26.6 / 81.7 | 16.5 / 52.5 |
| low 200k | 13.9 / 36.1 | 13.7 / 36.3 | 11.7 / 27.3 |
- m1's −9% Ir does not show in wall/CPU (noise ±5–10%).
- m2 cuts CPU by ~30% although its Ir is only −0.4%. The old `scanAWK` loop carried ~20 arguments including
  the index, which is shared by the mapping tasks, so its reference counts are atomic and contended across cores.
  `nextK` touches only the byte array. Callgrind (single-threaded, instruction counts) cannot see this. Look for
  the same pattern in the other hot loops (`stageKSP`, `hitsCK`): likely part of the "40% multithreading overhead".
- `@&` (borrowed) on `scanAWK2`'s `ix`/`G`/`R`: no measurable change; not kept.

## Multiples of minibwa (c07de5c, `map -t 4`), same box
Headline = load subtracted (ours: wall minus a pooled median of 9 empty-FASTQ runs, 2.98 s; minibwa: wall minus
its `index loaded` time). Format: vs default / vs native (`-O3 -march=native`).
| set | base wall | base CPU | m2 wall | m2 CPU | m2 end-to-end wall |
|---|---|---|---|---|---|
| HiSeq | 2.11 / 2.28 | 3.17 / 3.36 | 2.93 / 3.17 | 4.06 / 4.31 | 3.06 / 3.24 |
| NovaSeq | 0.95 / 0.93 | 1.03 / 0.99 | 1.37 / 1.34 | 1.58 / 1.50 | 1.99 / 1.64 |
| mason | 0.57 / 0.54 | 0.61 / 0.58 | 0.99 / 0.94 | 0.97 / 0.93 | 1.27 / 1.34 |
| low | 0.81 / 0.84 | 0.93 / 0.97 | 1.01 / 1.05 | 1.27 / 1.32 | 1.35 / 1.36 |
Caveat: on 15 GB the two indexes (ours 5.3 GB file + 5.3 GB heap; minibwa 7.7 GB file, 8 GB RSS) cannot both stay
cached; load times swing 1.5–13 s (ours) and 4–17 s (minibwa), so load-subtracted multiples carry ±10–15%.

## Why keys-sorted buckets (§1a) are not worth an index rebuild
hg38 index: k = 22, B = 26, sw = 5 → only kf = 8 key bits per slot (the rest of the 18 key bits are checked on the
genome). Per lookup (~10.6 per pair) ~280 slots are scanned and ~26 match the stored key; those are mostly genuine
22-mer occurrences (bucket ≈ 13 slots on average; false 8-bit matches are rare), and completeness needs each one
checked. After m2 the key scan (`nextK`) is 2.1% of Ir; the per-match check (`okAtW`, genome words, ~865 Ir per
match) is ~11%. Sorting keys in a bucket + binary search removes only the 2%. Levers that remain: a cheaper match
check (machine-word path), or context bits in the slot (sw = 6, c = 1: reject without reading the genome; index
+20%, rebuild needed).

## Order of diagonals (does `diags` need sorting at all?)
`Best.add` keeps the FIRST window found at the minimum penalty and only sets `amb` on later ties. `pen`/`amb` look
order-free, but the reported `(chr, st, len)` of a tied pair depends on the visit order (ascending diagonal, then
shape order). Skipping the sort would change SAM on ties; an order-free tie-break would change it as well. With the
merge, the sort costs ~1.2% of Ir, so leaving the order as it is.
