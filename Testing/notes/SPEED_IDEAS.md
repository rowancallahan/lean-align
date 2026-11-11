# Speed ideas below the Spec (reviewer S-I, 2026-11-11, festive 449867a)

Every idea is an exact-equality swap: same SAM bytes, same found pair or none, same XB bound, same class.
Nothing here touches `Spec/` or `Main.lean` except the items under "Needs Rowan".

## How it was measured

callgrind inside `MapFast.job`, 1 thread, on this branch. No hg38 index on the measuring box (15 GB), so the
numbers come from proxy sets; hg38 shares are estimates.

| proxy | what | Ir / pair |
|---|---|---|
| chr | chr21 index (iGenomes chr21, uppercased) + 20k real NovaSeq pairs that map to chr21 | 814k (repeat-heavy) |
| tiny | `Testing/ec2/setup.sh tiny` genome, 50k simulated pairs | 161k (easy path only) |
| disc | chr21 index, 2,000 discordant pairs (mate 1 of pair i + mate 2 of pair i+1000): 98% end unmapped | 1.84M |
| mut | chr21 index, 2,000 pairs with 6 substitutions in mate 2: 75% mapped unknown, 25% unmapped | 581k |
| x200 | chr21 cut into 200 contigs (hg38's index has 195), same reads | |

hg38 for reference (lead): 444k Ir/pair; unmapped pairs 4.7% of pairs but 27% of align time (NovaSeq).

Status: assigned (box), open, bigger rewrite, needs Rowan. Proof size: S (lines, rfl/simp), M (a lemma or two),
L (new invariant or kernel proof).

## Ranked list

### 1. properPairU / fragLen / pairScoreD without `fwdRev`
- Where: `Proofs/core/PairSpecU.lean` (`fwdRev`, `fragLen`, `properPairU`), `Proofs/core/PairSpec.lean` (`properPair`).
- What: `fwdRev` builds a tuple per call; `properPairU` calls it 4 times, `fragLen` 3 times. Add `@[csimp]` versions that branch once on `a.2` and read the fields directly.
- Why equal: unfolding; both branches are the same expressions.
- Proof: S.
- Saving (measured on chr): fwdRev is the top allocation site (1.71M per 20k pairs); properPairU 624 Ir/call (545k calls), pairScoreD 400 Ir/call (648k calls). chr 3.3%, tiny 0.5%; hg38 est. 1-2%.
- Owner: S-P. Status: assigned.

### 2. Fallback walk: drop repeated anchors
- Where: `Proofs/Report.lean` `fallbackOfKP` (`c1 := t.m1.pl.toList ++ anchorsOf …`, same for c2).
- What: remove from the anchor list every x equal (placement and score) to an earlier element, in particular the router's own placement `t.m.pl` coming back from `anchorsOf`.
- Why equal: `walkAt` is a pure function of x (the mate record is fixed per list), and `findSome?` stops at the first success, so a later copy of an x that was already tried returns `none` again.
- Proof: S-M (findSome? over a list with later duplicates removed).
- Saving (measured with an instrumented copy; SAM identical):
  - chr: 1,589 of 19,113 walk steps repeat; 998 rerun `nearAt` (281k Ir each); 1,367 are the router placement, 222 anchor-anchor. About 1.8%.
  - disc: 2,625 of 12,105 steps repeat; 2,444 of 10,280 `nearAt` calls; about 15% of the set.
  - mut: 297 of 2,740 steps; 193 of 2,106 `nearAt` calls; about 6%.
  - hg38 est. 2-4% (walk is a large part of unmapped/unknown time).
- Owner: S-G. Status: assigned.

### 3. alnC: gap-free re-check with the byte/word compare
- Where: `Aligner/mapper/TierRouter.lean` `alnC`, `upA`, `mateT`; `Proofs/Report.lean` `chkCandD`, `chkCandDK`, `chkCandD_ok`.
- What: `alnC` checks gap-free alignments (`runs = [(diag, R.size)]`) with `chkCand` (two `Array Char` + `checkRuns` with an Int accumulator). Use `chkCandDK` with `s.K1/K2` passed through `mateT`.
- Why equal: needs the converse of `chkCandD_ok` for runs `[(diag, n)]`: `checkRuns` gives `some v` iff `X.size = n`, `len = n` and `v = diagPen …` (`walk_diag` is the core).
- Proof: M.
- Saving: 15.5k calls per 20k chr pairs, 42k Ir each: chr 4.0%, tiny 0; hg38 est. 0.5-2%.
- Owner: S-G. Status: assigned.

### 4. voteD (seed-less window vote) without repeated work
- Where: `Aligner/mapper/TierHeur.lean` `voteD`, `vIns`, `vScan`, `vProbe`, `argMaxB`, `nearY`, `winL`/`winLg4`.
- What, three exact parts:
  - a. Track `(best value, first index)` inside `vScan`, where votes are incremented, and drop the separate `argMaxB` pass. Votes only grow, so the invariant "best = max, index = first index of max" is kept by: raise if `c > bv`, or `c = bv` and `t < bt`.
  - b. Build the read's k-mer table (`vIns`, two 1,024-entry tables) once per mate strand and pass it to every anchor's `nearY`; today it is rebuilt per anchor.
  - c. Hash the window from the packed 2-bit genome directly: today `winLg4` decodes the window to ASCII bytes (~36 Ir/letter, byte pushes) and `vScan` re-encodes each byte with `baseCode`. Non-ACGT letters need the same `c = 4` reset (the packed genome's exception runs).
- Why equal: a. invariant over the increments; b. pure function of the same inputs; c. pointwise code equality.
- Proof: a M, b S-M, c M-L.
- Saving (measured on disc, where 10,219 of 10,280 `nearY` calls reach `voteD`, 168k Ir each, 46.7% of the set):
  - argMaxB 22k Ir/call (6.1% of disc);
  - vIns 17.5k Ir/call (4.8% of disc), saved on all but the first anchor per strand;
  - winLg4 36k Ir per nearY (10.8% of disc), plus `baseCode` in vScan.
  - chr: voteD 4.4%, winLg4 1.65%. hg38 est. 1-3%, concentrated in unmapped/unknown pairs.
- Owner: S-G. Status: open.

### 5. Carry each mate's preparation into the later stages
- Where: `Proofs/Aligner.lean` `joinAt`/`rareCost`; `Aligner/mapper/TierOpt.lean` `tierNo`/`rareSel`; `Proofs/LastResort.lean` `splitOf`, `pairsAt`, `splitEmpty`; `Aligner/mapper/PairHitsKP.lean` `hitsAtKP`/`hitsSKV` (and `hitsAtKPN`); `Proofs/Report.lean` `checkMove`/`checkMoveD`/`mateRuns`/`alignAt`.
- What: these recompute `revCompK`, `packRP` (x2), the seed preparations and bucket sizes that `alignOneP`'s `s1`, `s2`, `za…zb` already hold.
  - Measured on disc: 6.6 reverse complements and 10 read packings per mate (rcSetU 26,390 calls, packRPU 41,387 calls per 4,000 mates).
  - `rareSel` (join seed choice) costs 13.8k Ir per call, 5,484 calls.
  - Reporter `revCompK`: 37.7k extra calls per 20k chr pairs.
  - `hitsAtKP` in the exact pair search: 0.55% of chr.
- Why equal: `prepMz_eq`, `seedP_eq`, `revCompK` of the same bytes. For `rareSel`, keep its `qsort` over `(j, size)` (ties must keep qsort's order, since the selected seeds decide what the join proves) and only take the sizes from `za`.
- Proof: S-M per call site.
- Saving: disc ~4-5%, chr ~1.5%, hg38 est. 1-2% (mostly unmapped/unknown pairs).
- Owner: S-G (S-P has the reporter `revCompK` part). Status: partly assigned (reporter, hitsAtKP); join/look parts open.

### 6. Look stage: per-contig work per call
- Where: `Proofs/Aligner.lean` `lookAt` (`cutAll pk.2 offs ns` per call); `Aligner/mapper/PairHitsKP.lean` `hitsSKV` (`layoutOk offs pgs2 n t`, `pgs ++ pgs`, `visOf`, `(List.range n).flatMap` with a `vis[c]!` test); `decB`.
- What:
  - Build `cutAll`'s chromosome views and `layoutOk` once per job (they depend only on the index).
  - Loop over the chromosomes that hold an anchor (from the `visOf` marks) instead of all `n`.
- Why equal: same values (pure, per-job constants); the skipped chromosomes give `[]` already (`hitsSK_eqV`'s argument).
- Proof: S (hoist) to S-M (marked list).
- Saving (measured, disc): 1 contig → 200 contigs raises `lookAt` from 80M to 139M Ir (+73%) and `splitEmpty` from 45M to 97M. `layoutOk` is ~12k Ir per call at 200 contigs. hg38 has 195 contigs, so this applies at full size there. hg38 est. 1-3% (look is the largest block for unmapped NovaSeq pairs).
- Owner: S-G. Status: open.

### 7. splitOf sorts the sizes for every split value
- Where: `Proofs/LastResort.lean` `splitOf`, `pairsAt` (`costP` with `mergeSort` per call).
- What: `splitOf` calls `costP` 2(c+1) times (c ≤ 16); each sorts both strands' sizes again. Sort each strand once (`costZS` on the sorted lists, as `alignOneP` does) and evaluate every split with `sumTake`. `pairsAt` then calls `costP` twice more with fresh `prepMate`s.
- Why equal: `costZ_eqS`, `costZ_eq`, `costPF_eq` already show `costP` = `costZS` of the sorted lists.
- Proof: S-M.
- Saving: splitOf 188k Ir per call (disc) → est. ~15k. disc 0.3%; hg38 est. 0.3-1% (once per pair reaching the look).
- Owner: S-G. Status: open.

### 8. Gapped re-check without Char arrays
- Where: `TierRouter.lean` `rescoreRunsA`, `chkCand`; called from `Report.checkMove`.
- What: one loop over the runs reading `R`/`Rr` bytes and `G.get` directly, instead of building two `Array Char` with `pushF`, then `checkRepeatGo`.
- Why equal: pointwise `xa[i] = Char.ofNat R[i]`, `ya[j] = Char.ofNat (G.get (st + j))`.
- Proof: M.
- Saving: ~42k Ir per 150-letter check, 12k calls per 20k chr pairs (3.1% chr) → est. 50-60% saved: chr ~1.8%, hg38 0.5-1%.
- Owner: S-G. Status: assigned.

### 9. SAM reverse-strand SEQ/QUAL copy
- Where: `Proofs/SamFused.lean` `pushSeqQual`, `pushRevMap`/`revPush`; `Proofs/SamBytes.lean` `complementByte`.
- What: today one `lean_byte_array_push` call and one non-inlined `complementByte` call per byte (~26 Ir/byte). Grow the buffer once (`copySlice`), then fill it in place with `uset`, with the complement inlined (4 compares or a 256-byte table).
- Why equal: pointwise; `revMapU_eq` is the pattern.
- Proof: M.
- Saving: tiny 16.6M pushes and 7.5M complementByte calls per 100k lines; est. ~5k Ir/pair: tiny ~3%, hg38 ~1%. Applies to every mapped pair.
- Owner: S-U. Status: assigned.

### 10. winTrim copies a read it keeps whole
- Where: `Proofs/TrimCore.lean` `winTrim` (and `trimBF`).
- What: when the window is `(0, letters.size)` and `qual.size = letters.size`, return `(letters, qual)` instead of two `extract`s.
- Why equal: `extract 0 size = self`.
- Proof: S.
- Saving: measured on the SAM, 77% of NovaSeq and 31% of HiSeq mate-1 reads are kept whole; each pays 2 extracts (~230 Ir each) + alloc + free. tiny 0.7%; hg38 est. 0.2-0.3%. Less memory traffic per pair. Related: adapter cut then trim copies twice; one extract of `[s, e)` is possible (M).
- Owner: S-U. Status: open.

### 11. One sort for seed sizes and seed order
- Where: `Proofs/Aligner.lean` `alignOneP` (`za.foldr insN []`), `TierRouter.lean` `tierPairBQ` (`ordG` = `insKey` sort of indices).
- What: 8 list insertion sorts per pair over the same keys (2.07M allocations per 50k tiny pairs). Take the sorted sizes as `(ordG z m).map (z[·]!)`, or compute `sumTake` from the order.
- Why equal: both are the sorted permutation of `z` (`List.eq_of_perm_of_sorted`).
- Proof: S-M.
- Saving: tiny ~1.4%, hg38 est. ~0.5%.
- Owner: S-G. Status: open.

### 12. `pgs ++ pgs` built per mate
- Where: `TierRouter.lean` `mateKPPO` (twice), `TieCut.lean` `mapChromsGBFGPOT` (`gbs2`), `PairHitsKP.lean` `hitsAtKP`, `regionPenKPSO` (`#[v] ++ #[v]`).
- What: build `pgs2` once per job in the setup and pass it. Keep it per job, not global: objects shared across threads get atomic reference counts (see the comment on `MapFast.job`).
- Why equal: same value.
- Proof: S.
- Saving: tiny 3 appends + alloc + free per mate (~700 Ir): ~0.9%; hg38 est. ~0.3%.
- Owner: S-G. Status: open.

### 13. tbRun traceback allocates per step
- Where: `TierHeur.lean` `tbRun` (`push`).
- What: carry the current `(step, count)` in the loop and cons only when the step changes.
- Why equal: same runs list. `bandDPg` has no value theorem (its output is re-checked), but the list is identical anyway.
- Proof: S.
- Saving: 549k allocations per 20k chr pairs: chr 0.6%, hg38 est. 0.2-0.3%.
- Owner: S-P. Status: assigned.

### 14. pairGXE: one fold instead of three lists
- Where: `Aligner/mapper/PairExact.lean` `pairGXE`; `PairNear.lean` `properPairsW`; `PairLadderF.lean` `bestOfPairs`; also `LastResort.pairsAt` / `splitEmpty` (same pattern, `.any`).
- What: `properPairsW` builds the full `List PairHit`, `.filter` drops low scores, then `bestOfPairs` runs `topW`, a filter and `find?` with an inner `all` that recomputes `pairScoreD` of `p` for each `p'`. One fold computing `(best, seen)` with scores computed once.
- Why equal: the same set, the same tie rule.
- Proof: M-L (bestOfPairs' tie rule).
- Saving: chr properPairsW 4.0% incl., filter 2.2%, bestOfPairs 0.7% (overlaps #1). After #1: chr 1.5-2.5%, hg38 est. 0.3-0.8%.
- Owner: S-G. Status: assigned.

### 15. bandDPg keeps every DP row
- Where: `TierHeur.lean` `bandDPg`, `bandCellsJ`, `BandCellsJProof.lean`.
- What: H and F are `(n+1)·K` boxed `UInt32` each (8 bytes per element: 41 KB per call at n = 150, w = 8) though only rows i-1 and i are read. Keep two rows (reset to INF per row); `tb` stays full.
- Why equal: the same cells get the same values.
- Proof: M (rolling-row invariant).
- Saving: instructions ~4% of bandDPg. Working set per call ~43 KB → ~3 KB, which matters at 16-32 cores (L1 is 32-48 KB).
- Owner: S-G. Status: assigned.

### 16. Per-pair closures that could be per job
- Where: `Proofs/Aligner.lean` `alignOneP` (generated C).
- What: every pair allocates the `afterRouter` closure (12 fields), used only for leftovers (20 of 20k chr pairs), and `fitNs`/`preOf`/`limOf`/`keepOf` partial applications that depend only on the settings. Build those four per job; pass `afterRouter`'s arguments instead of a closure.
- Why equal: definitional.
- Proof: S.
- Saving: ~600 Ir/pair: tiny 0.4%, hg38 ~0.15%.
- Owner: S-G. Status: open.

### 17. prepPairsB extracts QNAMEs to compare them
- Where: `Proofs/MapFast.lean` `prepPairsB`.
- What: compare the two name prefixes in place instead of `qnameB` (extract) on both; zip once instead of twice.
- Why equal: byte equality of the prefixes.
- Proof: S.
- Saving: tiny ~0.2%.
- Owner: S-U. Status: open.

### 18. seedVote looks the mate's seeds up again per anchor
- Where: `TierHeur.lean` `seedVote` (from `Report.nearOf`).
- What: 6 range-limited lookups per anchor. Look each seed up once per mate and cut per window by binary search.
- Why equal: same hits in the window.
- Proof: M.
- Saving: chr 1.2% total (13k Ir/call), est. half saved; disc 2.5%.
- Owner: S-G. Status: open.

Sum of 1-18: chr ~25%, tiny ~9%, disc ~35%, hg38 est. 10-15%, weighted towards unmapped/unknown pairs (items 2, 4, 5, 6, 7).

## Cache and memory ideas

C1. Many objects are `Array UInt32` / `Array Nat`, stored as 8-byte boxed scalars: bandDPg H/F (2 × 20 KB per call), voteD's `keys`/`offs` (2 × 8 KB per call), DP and vote tables. 4-byte cells in a `ByteArray` halve the footprint, and with #15 the DP fits in L1. Exact; M per kernel (S-G/S-P).

C2. Index lookup chain: bucket `h` → `offs[h]`, `offs[h+1]` (one line) → slots in `sl` (sequential) → genome word only for ambiguous tags (`okAtW`). That is two dependent misses per seed. The bucket headers of all 24 seeds of a pair are already read together (the `za…zb` sizes in `alignOneP`), so those misses overlap. The slot ranges are then read one seed at a time inside the search.
- Pure-Lean option: right after the sizes, touch the first slot line of the rarest k seeds of both mates. This is fragile: the compiler removes unused pure loads, so the value has to feed something it cannot drop.
- Clean option: a trusted `prefetch` FFI call (under Needs Rowan).

C3. Pair batching for memory-level parallelism: inside a job, run the preparation and bucket-size reads for B pairs, then route the B pairs. Any B gives the same output: each pair's answer is a pure function of the pair (map over chunks = map; proof S). So B can be chosen from the cache size, at run time if Main may read it. Without prefetch, the gain comes only from out-of-order overlap of the header loads (24·B independent loads). Measure before adopting. Memory: B prepared mates live at once (a few KB each).

C4. Per-call working sets above L1: bandDPg ~43 KB (#15), voteD ~18 KB plus a ~1 KB window, the window decode (#4c).

C5. Data read together but stored apart: the slot tag (key bits, context letters, flag) already sits next to the position, which avoids most genome reads. Nothing better found without changing the index format.

## Bigger rewrites (structural, new proofs; not designed)

- B1. bandCellsJ kernel: ~128 Ir per cell (boxed array get/set with bounds and exclusivity checks, Nat fuel, ~15 branches). Rows of UInt32 in a ByteArray, USize fuel, two rows: est. ~40-50 Ir/cell, hg38 -3%. L.
- B2. Hit lists as packed `UInt64` arrays (chr, start, len, strand, score) instead of `List (Placement × Int)`: removes most allocation in the hitsCK flatMap/filterMap, properPairs, bestOfPairs and the walk. L.
- B3. Seeds and `PrepM` as flat arrays (no per-seed `MzP` objects): `alignOneP` frees 14 objects per pair (6.1k Ir/pair on tiny, 3.8%); `prepLoop` and `mzLookSP` allocate per seed. L.
- B4. One pass per read: parse + adapter cut + trim + pack + reverse complement + seed preparation into job-level buffers. Today a read is copied up to 5 times (3 extracts in parse, 2 in trim). L.
- B5. Specialise `routeGS`/`passGSF` on the concrete searches instead of closures called through `lean_apply` (~30 closure objects per pair on tiny). M-L.
- B6. Carry seed lookup results (anchor arrays) from the router into walk (`anchorsOf`), join (`noPairJS`) and look (`hitsKPF`), which today look the same buckets up again. Memory trade-off for repeat-rich mates (keep only for leftovers). M-L.

## Needs Rowan

- A trusted `prefetch` FFI call (one `__builtin_prefetch`), for C2/C3. Not allowed in finished work today (`extern`).
- Whether test-only equality (A/B like `bandcells_ab`, no proof) is acceptable inside `bandDPg`, which has no value theorem: it would make B1, #13 and #15 cheaper. The list assumes proofs.
- If the batch size of C3 is to be read from the machine at run time, `Main.lean` would pass it (locked). A compile-time constant needs nothing.

## Checked and dropped

- `R == a` in `pairCfgZ`'s `cap1` closure: `lean_sarray_dec_eq` (memcmp), cheap.
- `Option.getD (lookAt …)` in `afterRouter`: `getD` is `macro_inline`, so `lookAt` is not run eagerly.
- `tieCut` runs the gapped stage once; no double scan.
- `dedupAdj`'s large inclusive cost in callgrind is a recursion artifact (self < 0.9%).
- An exact skip of `voteD` by the seed cover: `junkScore` is -100, so `limOf` reaches ~85-101 and 6 seeds cannot cover that many edits. No exact skip.
