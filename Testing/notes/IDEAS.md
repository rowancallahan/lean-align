# Ideas and parked work (collected 2026-11-12)

Everything that was on side branches when the release was merged, in one place, so the branches can be deleted.
Each code change is saved as a patch in `Testing/notes/ideas/patches/` (they apply to older commits; expect to
redo them by hand). Nothing here is merged into the build.

Contents: 1 parked code changes, 2 speed ideas below the Spec, 3 cache and prefetch, 4 mapping more pairs,
5 trimming, 6 reader loop and many cores, 7 tools and test data, 8 open decisions.

## 1. Parked code changes (one line each; detail in the sections below)

| what | old branch | patch | result | status |
|---|---|---|---|---|
| Prefetch in the minimizer scan, old scan | exp/prefetch | prefetch_old_scan.patch | -6 to -11% user CPU on the old scan | superseded by the new scan |
| Prefetch in the minimizer scan, new scan | exp/prefetch-instr | prefetch_new_scan.patch | no gain outside noise (6 runs per cell); has 2 `sorry` | experimental, needs a trusted C call |
| Record-boundary scan moved into the worker tasks | fix/cut-tasks-2 | cut_tasks.patch | loop-thread CPU -30 to -34%, ceiling 365-450 -> 550-650 Gbp/hr; total CPU no better at 4 cores, HiSeq +2.7% wall | proved, SAM identical; try at 16-32 cores |
| Adapter scan with a letter table | exp/util-prep-table | adapter_letter_table.patch | instructions +0.0001% / +0.0005%, simulated mispredicts -2.9% | proved; held out as a judgement call |
| Walk keeps the best pair for mapped `unknown` (walkK 3, walkStop -8) | exp/unknown-walkbest | unknown_walkbest.patch | recovers about 35-40% of the mapped-pairs gap to minibwa for 5-8% CPU | changes output (still satisfies the Spec); Rowan decides |
| 1 MiB pipes in the benchmark harness | fix/ec2-pipes | ec2_bigger_pipes.patch | no gain for either tool | dropped |
| Per-job / per-pair / per-stage timing trace | exp/hol-trace | hol_trace.patch, `ideas/hol_trace/` | found the slow pairs | never merge; rebuild it for the next slowdown hunt |

Done this round and already in the build (from the speed list in section 2): items 1, 2, 3, 7, 9, 10, 13, the
`layoutOk` part of 6, plus the minimizer scan as one machine-word loop, the wlR / saLoopTS unchecked loops and
pushNat on words. Total: instructions -12.0% NovaSeq, -7.4% HiSeq.

## 2. Speed ideas below the Spec

Source: reviewer S-I, 2026-11-11 (Speed ideas below the Spec (reviewer S-I, 2026-11-11, festive 449867a)). Status lines inside are as written then; see the "done this round" line in section 1.

Every idea is an exact-equality swap: same SAM bytes, same found pair or none, same XB bound, same class.
Nothing here touches `Spec/` or `Main.lean` except the items under "Needs Rowan".

### How it was measured

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

### Ranked list

#### 1. properPairU / fragLen / pairScoreD without `fwdRev`
- Where: `Proofs/core/PairSpecU.lean` (`fwdRev`, `fragLen`, `properPairU`), `Proofs/core/PairSpec.lean` (`properPair`).
- What: `fwdRev` builds a tuple per call; `properPairU` calls it 4 times, `fragLen` 3 times. Add `@[csimp]` versions that branch once on `a.2` and read the fields directly.
- Why equal: unfolding; both branches are the same expressions.
- Proof: S.
- Saving (measured on chr): fwdRev is the top allocation site (1.71M per 20k pairs); properPairU 624 Ir/call (545k calls), pairScoreD 400 Ir/call (648k calls). chr 3.3%, tiny 0.5%; hg38 est. 1-2%.
- Owner: S-P. Status: assigned.

#### 2. Fallback walk: drop repeated anchors
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

#### 3. alnC: gap-free re-check with the byte/word compare
- Where: `Aligner/mapper/TierRouter.lean` `alnC`, `upA`, `mateT`; `Proofs/Report.lean` `chkCandD`, `chkCandDK`, `chkCandD_ok`.
- What: `alnC` checks gap-free alignments (`runs = [(diag, R.size)]`) with `chkCand` (two `Array Char` + `checkRuns` with an Int accumulator). Use `chkCandDK` with `s.K1/K2` passed through `mateT`.
- Why equal: needs the converse of `chkCandD_ok` for runs `[(diag, n)]`: `checkRuns` gives `some v` iff `X.size = n`, `len = n` and `v = diagPen …` (`walk_diag` is the core).
- Proof: M.
- Saving: 15.5k calls per 20k chr pairs, 42k Ir each: chr 4.0%, tiny 0; hg38 est. 0.5-2%.
- Owner: S-G. Status: assigned.

#### 4. voteD (seed-less window vote) without repeated work
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

#### 5. Carry each mate's preparation into the later stages
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

#### 6. Look stage: per-contig work per call
- Where: `Proofs/Aligner.lean` `lookAt` (`cutAll pk.2 offs ns` per call); `Aligner/mapper/PairHitsKP.lean` `hitsSKV` (`layoutOk offs pgs2 n t`, `pgs ++ pgs`, `visOf`, `(List.range n).flatMap` with a `vis[c]!` test); `decB`.
- What:
  - Build `cutAll`'s chromosome views and `layoutOk` once per job (they depend only on the index).
  - Loop over the chromosomes that hold an anchor (from the `visOf` marks) instead of all `n`.
- Why equal: same values (pure, per-job constants); the skipped chromosomes give `[]` already (`hitsSK_eqV`'s argument).
- Proof: S (hoist) to S-M (marked list).
- Saving (measured, disc): 1 contig → 200 contigs raises `lookAt` from 80M to 139M Ir (+73%) and `splitEmpty` from 45M to 97M. `layoutOk` is ~12k Ir per call at 200 contigs. hg38 has 195 contigs, so this applies at full size there. hg38 est. 1-3% (look is the largest block for unmapped NovaSeq pairs).
- Owner: S-G. Status: open.

#### 7. splitOf sorts the sizes for every split value
- Where: `Proofs/LastResort.lean` `splitOf`, `pairsAt` (`costP` with `mergeSort` per call).
- What: `splitOf` calls `costP` 2(c+1) times (c ≤ 16); each sorts both strands' sizes again. Sort each strand once (`costZS` on the sorted lists, as `alignOneP` does) and evaluate every split with `sumTake`. `pairsAt` then calls `costP` twice more with fresh `prepMate`s.
- Why equal: `costZ_eqS`, `costZ_eq`, `costPF_eq` already show `costP` = `costZS` of the sorted lists.
- Proof: S-M.
- Saving: splitOf 188k Ir per call (disc) → est. ~15k. disc 0.3%; hg38 est. 0.3-1% (once per pair reaching the look).
- Owner: S-G. Status: open.

#### 8. Gapped re-check without Char arrays
- Where: `TierRouter.lean` `rescoreRunsA`, `chkCand`; called from `Report.checkMove`.
- What: one loop over the runs reading `R`/`Rr` bytes and `G.get` directly, instead of building two `Array Char` with `pushF`, then `checkRepeatGo`.
- Why equal: pointwise `xa[i] = Char.ofNat R[i]`, `ya[j] = Char.ofNat (G.get (st + j))`.
- Proof: M.
- Saving: ~42k Ir per 150-letter check, 12k calls per 20k chr pairs (3.1% chr) → est. 50-60% saved: chr ~1.8%, hg38 0.5-1%.
- Owner: S-G. Status: assigned.

#### 9. SAM reverse-strand SEQ/QUAL copy
- Where: `Proofs/SamFused.lean` `pushSeqQual`, `pushRevMap`/`revPush`; `Proofs/SamBytes.lean` `complementByte`.
- What: today one `lean_byte_array_push` call and one non-inlined `complementByte` call per byte (~26 Ir/byte). Grow the buffer once (`copySlice`), then fill it in place with `uset`, with the complement inlined (4 compares or a 256-byte table).
- Why equal: pointwise; `revMapU_eq` is the pattern.
- Proof: M.
- Saving: tiny 16.6M pushes and 7.5M complementByte calls per 100k lines; est. ~5k Ir/pair: tiny ~3%, hg38 ~1%. Applies to every mapped pair.
- Owner: S-U. Status: assigned.

#### 10. winTrim copies a read it keeps whole
- Where: `Proofs/TrimCore.lean` `winTrim` (and `trimBF`).
- What: when the window is `(0, letters.size)` and `qual.size = letters.size`, return `(letters, qual)` instead of two `extract`s.
- Why equal: `extract 0 size = self`.
- Proof: S.
- Saving: measured on the SAM, 77% of NovaSeq and 31% of HiSeq mate-1 reads are kept whole; each pays 2 extracts (~230 Ir each) + alloc + free. tiny 0.7%; hg38 est. 0.2-0.3%. Less memory traffic per pair. Related: adapter cut then trim copies twice; one extract of `[s, e)` is possible (M).
- Owner: S-U. Status: open.

#### 11. One sort for seed sizes and seed order
- Where: `Proofs/Aligner.lean` `alignOneP` (`za.foldr insN []`), `TierRouter.lean` `tierPairBQ` (`ordG` = `insKey` sort of indices).
- What: 8 list insertion sorts per pair over the same keys (2.07M allocations per 50k tiny pairs). Take the sorted sizes as `(ordG z m).map (z[·]!)`, or compute `sumTake` from the order.
- Why equal: both are the sorted permutation of `z` (`List.eq_of_perm_of_sorted`).
- Proof: S-M.
- Saving: tiny ~1.4%, hg38 est. ~0.5%.
- Owner: S-G. Status: open.

#### 12. `pgs ++ pgs` built per mate
- Where: `TierRouter.lean` `mateKPPO` (twice), `TieCut.lean` `mapChromsGBFGPOT` (`gbs2`), `PairHitsKP.lean` `hitsAtKP`, `regionPenKPSO` (`#[v] ++ #[v]`).
- What: build `pgs2` once per job in the setup and pass it. Keep it per job, not global: objects shared across threads get atomic reference counts (see the comment on `MapFast.job`).
- Why equal: same value.
- Proof: S.
- Saving: tiny 3 appends + alloc + free per mate (~700 Ir): ~0.9%; hg38 est. ~0.3%.
- Owner: S-G. Status: open.

#### 13. tbRun traceback allocates per step
- Where: `TierHeur.lean` `tbRun` (`push`).
- What: carry the current `(step, count)` in the loop and cons only when the step changes.
- Why equal: same runs list. `bandDPg` has no value theorem (its output is re-checked), but the list is identical anyway.
- Proof: S.
- Saving: 549k allocations per 20k chr pairs: chr 0.6%, hg38 est. 0.2-0.3%.
- Owner: S-P. Status: assigned.

#### 14. pairGXE: one fold instead of three lists
- Where: `Aligner/mapper/PairExact.lean` `pairGXE`; `PairNear.lean` `properPairsW`; `PairLadderF.lean` `bestOfPairs`; also `LastResort.pairsAt` / `splitEmpty` (same pattern, `.any`).
- What: `properPairsW` builds the full `List PairHit`, `.filter` drops low scores, then `bestOfPairs` runs `topW`, a filter and `find?` with an inner `all` that recomputes `pairScoreD` of `p` for each `p'`. One fold computing `(best, seen)` with scores computed once.
- Why equal: the same set, the same tie rule.
- Proof: M-L (bestOfPairs' tie rule).
- Saving: chr properPairsW 4.0% incl., filter 2.2%, bestOfPairs 0.7% (overlaps #1). After #1: chr 1.5-2.5%, hg38 est. 0.3-0.8%.
- Owner: S-G. Status: assigned.

#### 15. bandDPg keeps every DP row
- Where: `TierHeur.lean` `bandDPg`, `bandCellsJ`, `BandCellsJProof.lean`.
- What: H and F are `(n+1)·K` boxed `UInt32` each (8 bytes per element: 41 KB per call at n = 150, w = 8) though only rows i-1 and i are read. Keep two rows (reset to INF per row); `tb` stays full.
- Why equal: the same cells get the same values.
- Proof: M (rolling-row invariant).
- Saving: instructions ~4% of bandDPg. Working set per call ~43 KB → ~3 KB, which matters at 16-32 cores (L1 is 32-48 KB).
- Owner: S-G. Status: assigned.

#### 16. Per-pair closures that could be per job
- Where: `Proofs/Aligner.lean` `alignOneP` (generated C).
- What: every pair allocates the `afterRouter` closure (12 fields), used only for leftovers (20 of 20k chr pairs), and `fitNs`/`preOf`/`limOf`/`keepOf` partial applications that depend only on the settings. Build those four per job; pass `afterRouter`'s arguments instead of a closure.
- Why equal: definitional.
- Proof: S.
- Saving: ~600 Ir/pair: tiny 0.4%, hg38 ~0.15%.
- Owner: S-G. Status: open.

#### 17. prepPairsB extracts QNAMEs to compare them
- Where: `Proofs/MapFast.lean` `prepPairsB`.
- What: compare the two name prefixes in place instead of `qnameB` (extract) on both; zip once instead of twice.
- Why equal: byte equality of the prefixes.
- Proof: S.
- Saving: tiny ~0.2%.
- Owner: S-U. Status: open.

#### 18. seedVote looks the mate's seeds up again per anchor
- Where: `TierHeur.lean` `seedVote` (from `Report.nearOf`).
- What: 6 range-limited lookups per anchor. Look each seed up once per mate and cut per window by binary search.
- Why equal: same hits in the window.
- Proof: M.
- Saving: chr 1.2% total (13k Ir/call), est. half saved; disc 2.5%.
- Owner: S-G. Status: open.

Sum of 1-18: chr ~25%, tiny ~9%, disc ~35%, hg38 est. 10-15%, weighted towards unmapped/unknown pairs (items 2, 4, 5, 6, 7).

### Cache and memory ideas

C1. Many objects are `Array UInt32` / `Array Nat`, stored as 8-byte boxed scalars: bandDPg H/F (2 × 20 KB per call), voteD's `keys`/`offs` (2 × 8 KB per call), DP and vote tables. 4-byte cells in a `ByteArray` halve the footprint, and with #15 the DP fits in L1. Exact; M per kernel (S-G/S-P).

C2. Index lookup chain: bucket `h` → `offs[h]`, `offs[h+1]` (one line) → slots in `sl` (sequential) → genome word only for ambiguous tags (`okAtW`). That is two dependent misses per seed. The bucket headers of all 24 seeds of a pair are already read together (the `za…zb` sizes in `alignOneP`), so those misses overlap. The slot ranges are then read one seed at a time inside the search.
- Pure-Lean option: right after the sizes, touch the first slot line of the rarest k seeds of both mates. This is fragile: the compiler removes unused pure loads, so the value has to feed something it cannot drop.
- Clean option: a trusted `prefetch` FFI call (under Needs Rowan).

C3. Pair batching for memory-level parallelism: inside a job, run the preparation and bucket-size reads for B pairs, then route the B pairs. Any B gives the same output: each pair's answer is a pure function of the pair (map over chunks = map; proof S). So B can be chosen from the cache size, at run time if Main may read it. Without prefetch, the gain comes only from out-of-order overlap of the header loads (24·B independent loads). Measure before adopting. Memory: B prepared mates live at once (a few KB each).

C4. Per-call working sets above L1: bandDPg ~43 KB (#15), voteD ~18 KB plus a ~1 KB window, the window decode (#4c).

C5. Data read together but stored apart: the slot tag (key bits, context letters, flag) already sits next to the position, which avoids most genome reads. Nothing better found without changing the index format.

### Bigger rewrites (structural, new proofs; not designed)

- B1. bandCellsJ kernel: ~128 Ir per cell (boxed array get/set with bounds and exclusivity checks, Nat fuel, ~15 branches). Rows of UInt32 in a ByteArray, USize fuel, two rows: est. ~40-50 Ir/cell, hg38 -3%. L.
- B2. Hit lists as packed `UInt64` arrays (chr, start, len, strand, score) instead of `List (Placement × Int)`: removes most allocation in the hitsCK flatMap/filterMap, properPairs, bestOfPairs and the walk. L.
- B3. Seeds and `PrepM` as flat arrays (no per-seed `MzP` objects): `alignOneP` frees 14 objects per pair (6.1k Ir/pair on tiny, 3.8%); `prepLoop` and `mzLookSP` allocate per seed. L.
- B4. One pass per read: parse + adapter cut + trim + pack + reverse complement + seed preparation into job-level buffers. Today a read is copied up to 5 times (3 extracts in parse, 2 in trim). L.
- B5. Specialise `routeGS`/`passGSF` on the concrete searches instead of closures called through `lean_apply` (~30 closure objects per pair on tiny). M-L.
- B6. Carry seed lookup results (anchor arrays) from the router into walk (`anchorsOf`), join (`noPairJS`) and look (`hitsKPF`), which today look the same buckets up again. Memory trade-off for repeat-rich mates (keep only for leftovers). M-L.

### Needs Rowan

- A trusted `prefetch` FFI call (one `__builtin_prefetch`), for C2/C3. Not allowed in finished work today (`extern`).
- Whether test-only equality (A/B like `bandcells_ab`, no proof) is acceptable inside `bandDPg`, which has no value theorem: it would make B1, #13 and #15 cheaper. The list assumes proofs.
- If the batch size of C3 is to be read from the machine at run time, `Main.lean` would pass it (locked). A compile-time constant needs nothing.

### Checked and dropped

- `R == a` in `pairCfgZ`'s `cap1` closure: `lean_sarray_dec_eq` (memcmp), cheap.
- `Option.getD (lookAt …)` in `afterRouter`: `getD` is `macro_inline`, so `lookAt` is not run eagerly.
- `tieCut` runs the gapped stage once; no double scan.
- `dedupAdj`'s large inclusive cost in callgrind is a recursion artifact (self < 0.9%).
- An exact skip of `voteD` by the seed cover: `junkScore` is -100, so `limOf` reaches ~85-101 and 6 seeds cannot cover that many edits. No exact skip.

## 3. Cache and prefetch

Source: Cache behaviour of the mapper (measurement and reading only; nothing in Aligner/, Proofs/, Spec/ was changed).

Code: festive head code f465a57 (identical to c7a828e), index built by that code (`ic.idx`, 5,338,015,764 B), 200k NovaSeq and hg002 sets,
50k-pair prefixes for the simulations. Scripts: `Testing/scripts/cache_run.py`, `cache_hp.sh`, `cache_cg.sh`, `cg_cost.py`.
**Measured** = real runs on this box. **Simulated** = callgrind / cachegrind, no hardware prefetcher, no out-of-order overlap, no TLB.
**Estimated** = arithmetic on those numbers.

Box: Xeon 2.1 GHz VM, 4 cores, L1d 48 KB, L2 2 MB per core, L3 260 MB shared (so "server-like" already); THP `madvise`, defrag `madvise`.
Not measured: any other CPU (no 32-64 core server, no laptop, no phone).

### 1. Huge pages (measured; SAM md5 identical in all 72 runs)

- Lean's bundled mimalloc 3.4.5 reads `MIMALLOC_*` (`MIMALLOC_VERBOSE=1` lists `allow_large_os_pages`, `reserve_huge_os_pages`, ...).
- The index is **already** on transparent huge pages at baseline: `AnonHugePages` in `/proc/PID/smaps_rollup` = 5.3-5.5 GB of 5.6 GB RSS with `madvise` and no env var (the binary calls `madvise`).
- No further gain: user CPU at 4 cores, NovaSeq, mean [min-max] s: THP=always 12.5 [12.2-12.7], `MIMALLOC_ALLOW_LARGE_OS_PAGES=1` 12.8 [12.1-13.4], both 12.8 [12.4-13.2],
  base (madvise) 13.7 [13.3-14.1]. The base figure is an **order effect** (base ran right after the hugetlb variant): in a control with 5 back-to-back alternating madvise / always pairs the ranges were
  11.0-12.8 and 11.4-12.8 s. hg002 behaves the same.
- Huge pages help the system side, not the per-pair side: THP=never (AnonHugePages 0) has the same user time (13.6-13.7 s) but sys 4.8-5.1 s vs 3.0-3.2 s and wall +12-17 % (NovaSeq 1 core 19.8 s vs 17.7 s; 4 cores 8.4 s vs 7.2 s): fewer page faults while the 5.3 GB index is read in.
- A preallocated hugetlb pool (`nr_hugepages=2800` + `MIMALLOC_ALLOW_LARGE_OS_PAGES=1`) is worse: user 12.0-12.5 s (inside the noise), sys 7.8-8.9 s, wall 11.2-12.4 s at 4 cores vs 7.2 s.
- dTLB: not visible in these timings (4 KB pages cost no extra user time). It is a VM (nested paging), so TLB cost on bare metal could differ; I could not measure that.
- Settings written during the runs (`/sys/kernel/mm/transparent_hugepage/enabled`, `/proc/sys/vm/nr_hugepages`) were restored to `madvise` / 0.

### 2. Where the misses are (simulated)

Three geometries, 50k NovaSeq pairs, 1 core. Estimated cost = 10 cycles per D1 miss + 100 per LL miss (reads and writes, no overlap).
A = callgrind on the host's geometry (D1 48 KB 12-way, LL 276 MB 33-way; callgrind ignores `--D1/--LL` when the CPU reports an L3), collecting only inside `Spec.MapFast.job`.
B = cachegrind D1 48 KB/12, LL 32 MB/16 ("server, 32 MB slice"). C = cachegrind D1 32 KB/8, LL 8 MB/16 ("laptop"). B and C: whole run minus a 500-pair run (includes parsing and SAM output).

| per 50k pairs | A (job only) | B | C |
|---|---|---|---|
| instructions | 22.2 G | 22.1 G | 22.1 G |
| D1 misses rd + wr | 48.4 M + 17.7 M | 53.1 M + 21.6 M | 65.4 M + 24.0 M |
| LL misses rd + wr | 5.8 M + 2.8 M | 14.6 M + 8.4 M | 20.7 M + 10.9 M |
| estimated miss cycles | 1.52 G (6.9 % of Ir) | 3.05 G (13.8 %) | 4.06 G (18.3 %) |
| LL read misses per pair | 115 | 293 | 415 |

Steady state (100k minus 50k pairs, A): 7.2 % of Ir, i.e. the numbers above are not a warm-up effect. An instruction count of 22 G per 50k pairs (443k per pair) against about 3 s of CPU shows most of
this cost is overlapped by the out-of-order core; the percentages are an upper bound on the share of time, not an estimate of it.

By function (A, share of estimated miss cycles; calls per 50k pairs):
- 22 % `flagsOkU`: the genome flag/fetch check, called from `scanAWF` for each candidate slot: 11.6 M calls (233 per pair), 8.7 M D1 and 2.5 M LL misses (50 per pair). The largest source of LL read misses; at 32/8 MB LL it grows to 4.8 M / 5.7 M.
- 7 % `getU32F` (bucket offsets `offs[b]`, `offs[b+1]`): 1.03 M LL misses (21 per pair).
- 5 % `nextK`, 4 % `scanAWF`, 2 % `rdSlot` (the scan of a bucket's slots): LL 0.7 M, 0.5 M, 0.25 M. 325,719 bucket scans (6.5 per pair), 12.0 M slot steps (240 per pair, about 37 per scan).
- 22 % `memcpy` (1.39 M `lean_byte_array_copy_slice` calls = 28 per pair, almost all write misses into fresh objects), 2.8 % `lean_mk_array`, 2.1 % `lean_array_push`, 2.1 % `mi_page_free_list_extend`: allocation and copying of Lean objects.
- 6.5 % `lean_alloc_small_object_core` (9.9 M D1 misses, 0 LL), 2.2 % `lean_del_core_other`, 1.3 % `lean_dec_ref_cold`: allocator and refcount traffic, D1 only. About a quarter of all D1 misses.
- 2.5 % `Spec.parseFromF` (reading the FASTQ, compulsory), 0.8 % `mappedLineF` (SAM line).

Which data (LL read misses per pair, A): packed genome 50, minimizer table 50 (offsets 21 + slots about 29), reads about 7, everything else (hit lists, DP, output) about 8.
Hit lists, reads and the per-pair temporaries are D1-only.

dTLB (estimated, not simulated): about 115 LL read misses per pair at random positions in 5.3 GB = up to about 115 distinct 4 KB pages per pair. At 30-60 cycles per walk with the page tables in L2/L3 that is 3.5-7 k cycles per pair
against about 130 k cycles of compute (3-5 %). The THP=never run (section 1) shows no user-time difference.

Job working set (2b, estimated from file sizes; `jobPairs` = 4000): FASTQ in about 3.0 MB (NovaSeq, 739 B per pair) / 4.4 MB (hg002, 1,112 B per pair); SAM out about 3.3 MB / 4.7 MB (820 / 1,165 B per pair).
So a job's reads + output are 6-9 MB, more than L2 (2 MB) but they stream sequentially through the pair loop; what has to stay in L2 is the current pair's temporaries and the hot code/tables, not the job. The constant was not changed.

### 3. The hot lookup code (read, plus objdump of the built binary)

Chain per seed (`Aligner/index/minimizer/MzWord.lean`: `lookupPWK`, `scanAWK3`, `scanAWF`, `nextK`, `fastOkW`):
1. `offs[b]`, `offs[b+1]` (`getU32`, 4 bytes each, adjacent, usually one line): one random access into the bucket offset table.
2. The bucket's slots `sl[lo..hi)` (`slotW`, `sw` = 4-8 bytes per slot): a sequential run (about 37 slots, a few lines) after a random start, so the hardware prefetcher helps after the first line.
3. For each slot whose key bits match (`nextK`; here about 97 % of the slots, 233 of 240 steps): the genome block of the candidate position: `flagsOkU` reads the flag bytes at 17-byte stride (block = 17 bytes per 64 letters) and `gWU` reads the letter words
   from the same block(s): a random access per candidate, 1-2 lines (a 17-byte block straddles a 64-byte line in 25 % of cases; the 25-letter window crosses a block border in 37 %).
4. Only candidates that pass go on to alignment (hit lists).

Facts from the code and assembly:
- The genome access of slot t does not depend on slot t-1 (only the bucket offsets -> slots -> genome chain is dependent), so a batch of candidates could be fetched in parallel; the compiled loop does not expose that.
  `nextK` costs about 104 instructions per slot step (1.25 G Ir / 12 M calls): boxed-`Nat` tag tests, a once-guard on the `slotWF` closed term, and repeated bound checks (objdump of `lp_lean__align_MapSpec_Fast_nextK`). With about 100 instructions between independent genome probes
  the out-of-order window (512 entries) holds only a few candidates, so the miss overlap is small.
- Entries: a slot is `pos * 2^T + tag` with `sw` in {4,5,6,8}; the tag holds the key bits (`kf`), `c` context letters on each side, and a flag. Key and position are in the same slot, bucket offsets are in a separate table (one extra random line per lookup).
  I did not extract `sw` for hg38 from the index, so whether the slots are wider than needed is not checked.
- False sharing: the index `ByteArray` is shared read-only by all workers and passed as `@&` (borrowed); the aligner setup is made inside each job precisely because shared objects get atomic reference counts (commit 7cfddfb: +6 % CPU). I found no per-thread counters on shared lines.
  Measured scaling is flat: NovaSeq user CPU 12.4-13.8 s at 1 core and 12.1-13.7 s at 4 cores (section 1), so no contention shows up to 4 threads. Not testable here beyond 4 cores.
- A plain early load is **deleted** by clang when its value is provably unused: tested with `clang -O3` on `b = p[i]; return i + (b & 0)`, `i + (b >> 8)`, `i + (b ^ b)` -> all three compile to a bare `ret`. A `volatile` load is kept (`movzbl`), and `__builtin_prefetch` is kept (`prefetcht0`).
  So a Lean-only "touch" pass needs a result clang cannot fold, and any such result changes what the function returns unless it is added to something already observable.

### 4. Ideas, ranked by estimated gain per proof effort (all are exact-equality changes; none was implemented)

1. **Fewer short-lived objects in the pair loop** (28 `ByteArray` slice copies, the arrays and the allocator traffic per pair). Upper bound from the simulation: copies, array growth and allocator about 40 % of the estimated miss cycles in A
   (mostly write misses to fresh lines and D1-only allocator misses), i.e. about 2-3 % of Ir-equivalent. Replace `extract` copies by views / index arithmetic on the same array. Proof effort: moderate (each use needs `extract`-free equations); no new trusted code.
2. **A tight `UInt64`/`USize` slot loop** for `nextK` + `scanAWF` (no boxed `Nat` tests or once-guards per step): 3.0 G + 1.25 G Ir of 22 G = about 19 % of instructions in one loop; halving its per-step cost would give a few percent, and it also lets more slot probes sit in the out-of-order window (which is what helps the genome misses).
   Proof effort: moderate, the equation lemmas already exist for the current forms (`scanAWK_eq2`, `scanAWF_eq`).
3. **Batched genome probes within a bucket** (compute the block offsets of the next B candidates, touch them, then evaluate): output identical by construction (reordered reads only). Target: the 50 LL misses per pair of `flagsOkU` (22 % of estimated miss cycles in A, 19-16 % at 32/8 MB LL).
   In plain Lean this needs a load that clang keeps (see section 3): either the touched value must feed something observable, or a `volatile`/prefetch primitive, i.e. **needs Rowan** (a new trusted piece). Gain not reported. Before the instruction not to do this reached me I had built a prototype on branch `exp/prefetch` (inline-C `extern`, no build change, identity in the logic so no proof changes, SAM md5 identical in the 4 runs I checked) and had a partial timing run going (38 of 80 rows, in the session scratchpad, not analysed); I stopped it. I suggest deleting the branch.
4. **Process lookups in address order / batch seeds of a read**: the bucket-offset table (21 LL misses per pair) and slot starts could be sorted by bucket and read in order; needs a restructure of the seed loop and a proof that the result list order is unchanged. Gain at most the 7 % + 5 % of estimated miss cycles for the table; uncertain, **bigger rewrite** of the loop.
5. **Run-time block size from the cache size**: the job is already far above L2 and the streams are sequential, so the working-set argument (section 2) says little is gained; reading the cache size is IO and would come in through `Main` (**needs Rowan**); the proof obligation would be "output independent of `jobPairs`", which `MapFast` already has for the existing constant (the cut-slices proofs).
6. **Index layout changes** (key and positions with the offsets, flags separate from the letters, narrower slots): change the index file format and its proofs: **bigger rewrite**. Separating the flag bytes would not remove the genome miss because the letters are read right after the flags from the same block.
7. Huge pages: already on (section 1); nothing to do.

Not covered: bare-metal servers or laptops, phones (no hardware here), more than 4 threads, the hg002 set in the simulations (only NovaSeq was simulated).

### 5. Look-ahead prefetch of the genome block (side branches, never merged; measured)

Two experimental branches, left as they are: `exp/prefetch` (base: festive c7a828e, code = f465a57, old `scanAWF` loop) and `exp/prefetch-instr` (base: `fix/instr` 10d42cb, S-G's single-loop `scanAWV`).
Mechanism: in the slot scan, at slot `t` touch the genome block (flag byte + letters, two addresses) that slot `t + B` will read; the first `B` slots are touched before the loop.
`@[extern c inline "(__builtin_prefetch(lean_sarray_cptr(#1) + #2, 0, 3), #2)"] def prefetchAt (a : @& ByteArray) (i : USize) : USize := i`; `touchAt` is the same with an ordinary `volatile` 1-byte read.
`B` and the mode come from the environment (`LA_PF_B`, `LA_PF_MODE`, read once by inline C `getenv`), so one binary serves every row.
Build needs: nothing. The inline C needs no `.c` file, no lakefile / `extern_lib` / link-argument change; `getenv` and `atoi` are declared inside the inline expression because `lean.h` does not include `<stdlib.h>`.
The generated C keeps the call (`__builtin_prefetch(lean_sarray_cptr(w) + off, 0, 3)`; `prefetcht0` in the binary).
Proofs: `exp/prefetch` has none changed (the externs are identities and `pfB` / `pfMode` are 0 in the logic, so `scanAWF_eq` goes through by defeq). `exp/prefetch-instr` has two `sorry`s: `scanAWVQ_eq` (a `partial def` copy of `scanAWV` with the look-ahead) and `mzPrepC_eq`.
Diff size: `exp/prefetch` +43/-2 lines (one file); `exp/prefetch-instr` +97/-2 (`MzWord.lean`, one line in `TierRouter.lean`).
SAM md5 identical in every run (NovaSeq `223ab24ed9237863fe0f78e18cd39a69`).

User CPU in s, [min-max], 200k pairs, interleaved reps with the variant order reversed on every second rep. "Outside range" = the whole range of the prefetch cell lies below the base cell's whole range.
- A. Old scan (`exp/prefetch`, festive base, 3 reps, NovaSeq): 1 thread: base 12.94 [12.69-13.26]; B4 12.16 [11.69-12.53], B8 11.52 [11.50-11.54], B16 12.00 [11.76-12.47], B32 11.99 [11.75-12.17]: all four outside the base range (-6 to -11 %).
  4 threads: base 13.22 [12.34-13.79]; B4 11.94 [11.78-12.06] (-9.7 %, outside); B8 11.65 [10.60-12.67], B16 12.08 [11.77-12.68], B32 11.85 [11.26-12.53]: means -8.6 to -11.9 %, ranges overlap the base's. The 6-rep confirmation on this base was not run (festive now carries the new scan).
- B. New scan (`exp/prefetch-instr`, `fix/instr` base, 6 reps, NovaSeq and hg002, base / look-ahead off / B4 / B8): NovaSeq 1 thread 13.20 [12.01-14.56] / 12.88 / 12.36 [11.75-13.03] / 12.44 [12.05-13.07]; 4 threads 12.84 [12.31-13.51] / 12.71 / 12.42 [11.69-13.41] / 13.03 [12.23-14.33];
  hg002 1 thread 13.47 [12.71-14.44] / 13.82 / 13.64 [12.64-15.00] / 13.18 [12.75-13.76]; 4 threads 13.47 [12.48-14.24] / 13.14 / 13.17 [12.38-14.17] / 13.24 [12.83-13.73].
  Every range overlaps the base's: no gain outside run-to-run noise. The earlier 3-rep matrix on this base (B8 -6.3 % at 1 thread, 10.77-11.25 vs base 11.54-12.04) was not reproduced by the 6-rep rerun. The base alone moves by about +-10 % within a run and between sessions, and the "look-ahead off" build of the same code differs from base by up to +13 % (layout/noise), which is as large as any effect seen.
- C. Volatile touch read (`touch1`, all B, both bases, 3 reps): worse by +8 to +26 % in every cell, outside range (the load has to retire before later instructions, so it cannot overlap). A plain load is deleted by clang (section 3).
- D. Bucket-offset prefetch at seed preparation (`mzPrepC`, `exp/prefetch-instr`): only 2 NovaSeq reps finished before the run was interrupted; offsets prefetch alone +2 to +12 % (the "off" build of the same binary is itself +2 to +13 %), B8 alone -1.8 % / -8.4 % (1 / 4 threads), B8 + offsets -5.0 % / -13.8 %. n = 2: not interpretable. hg002 not run.
- E. Not ported to `fix/instr-all` (cc26db2): the condition was a gain clearly above noise, and the new scan, which that build carries, shows none.

Verdict: no gain outside run-to-run noise on the new scan; -6 to -11 % user CPU only on the old `scanAWF` loop; the touch read is worse; the offsets prefetch is not interpretable at n = 2.

## 4. Mapping more pairs (the gap to minibwa)

Measured on 1M pairs per data set, build cc26db2 vs minibwa c07de5c
(`Testing/results/ec2_check/unmapped_breakdown/`, script `analyze.py`). NovaSeq | HiSeq, % of all pairs.

- Pairs minibwa maps with MAPQ >= 30 and proper pair: 90.83 | 92.28. Of these we call unique 81.53 | 84.58,
  map as `unknown` 6.43 | 4.78, leave unmapped 2.86 | 2.91. So we map 96.9% of the pairs minibwa is confident about.
- Pairs we leave unmapped that minibwa maps with both mates: 5.50 | 5.50. Of these, minibwa MAPQ < 30 for
  42.9% | 43.7% (filtered by most pipelines); not a proper pair 22.1% | 20.5%; mates on different chromosomes
  16.7% | 14.5%; a supplementary alignment 12.3% | 19.3%; >= 10 soft-clipped bases on a mate 42.8% | 56.7%.
- The clean pairs we miss (2.86% | 2.91%), by our reason: best pair scores -17..-40 (below the required bound):
  17,363 | 19,086; bound >= -16 but no pair reported: 6,584 | 2,338; repetitive: 3,286 | 2,157;
  trimmed away: 1,393 | 5,561 (on 2x250 reads our trimming drops mates minibwa maps well).
- The Spec allows reporting any real proper pair scoring -100 or better as `unknown`, so closing this gap is an
  implementation choice. Ideas: the walk-best change above; quality-aware soft clipping (a Spec change: local
  alignment with a clipping cost, see ROADMAP.md); a softer treatment of the 2x250 tails than discarding the mate.
- Cost by outcome (1M pairs, 4 threads): unique pairs 82-84% of pairs, 41-42 us each, 41-49% of align time;
  unmapped 4.7-4.8% of pairs, 271-481 us each, 18-27% of time; mapped `unknown` 9-11%, 182-215 us, 25-27%;
  repetitive 0.7-0.8%, 644-675 us, 6-7%. For NovaSeq unmapped pairs: last-resort search 13.5 s of 22.7 s.
- Testing repeats first (the `witnessFirst` option, off by default) would cut the repetitive class's cost but
  changes output whenever the earlier stages would have found a pair.

### The walk-best experiment in detail

Source: Walk keeps the best candidate pair (exp/unknown-walkbest).

Problem: ~1 pair in 9 is mapped with `XU:Z:unknown` (n1m 11.8%, h1m 9.1%). Most come from the router giving up
(gate budget, bound 0) and the fallback walk (`Report.fallbackOfK`) reporting the FIRST acceptable pair from at most
`walkK` (3) anchors per strand of each mate's rarest seed.

Change (Proofs/Report.lean, Proofs/Aligner.lean): the walk tries candidates in order and keeps the best-scoring pair
(`bestLazy`), stopping once a pair scores >= `walkStop` (-8). Mate 2's anchors are computed only if needed; a candidate
whose gap-free anchor score is below the best pair so far is skipped. Soundness: `bestLazy_mem` + existing
`walkAt_sound`; `lake build lean-align` green; Spec untouched. Default: `walkK = 3`, `walkStop = -8`.
Mapped counts and mapped-unknown counts are unchanged; XB is not tightened. SAM differs only on baseline-unknown pairs.

### Accuracy (200k sim pairs, pairs at the true position +-20 bp; "unk" = base's mapped-unknown pairs: mason 20256, low 10576)
| variant | mason all / unk | low all / unk |
|---|---|---|
| base | 187909 / 14898 | 193308 / 4854 |
| thr -8, k=3 (default) | 188771 / 15760 | 194273 / 5819 |
| thr -8, k=6 | 188975 / 15933 | 194460 / 5994 |
| thr -8, k=12 | 189106 / 16042 | 194643 / 6157 |
| no stop, k=3 | 188813 / n.m. | 194489 / n.m. |
(n.m. = not measured)
| minibwa c07de5c | 196329 / 17357 | 196486 / 7286 |

### CPU cost (user+sys, median of 3 interleaved runs, 4 threads, 1M pairs; base drifts between batches, compare within a row)
| | base | k=3 | k=6 | k=12 |
|---|---|---|---|---|
| n1m | 75.2 s | +6.8% | +8.1% | +14.8% |
| h1m | 77.7 s | +5.5% | +7.9% | +5.8% (noisy) |
Wall +3% to +7%. No 5M FIFO run (no variant meets the +1% goal).

### Tried, did not help
- Steering (try candidates with a nearby partner-mate anchor first): same candidate set under the early stop, +1/+5 pairs vs k=6, more CPU.
- Lazy mate-2 anchors: no CPU change (k=3: 80.8 vs 80.3 s).
- Pruning candidates by gap-free anchor score vs the best pair: identical results to k=6, no CPU saving (anchors are sorted best-first).
- Threshold sweep -4/-8/-12/none: accuracy within ~100 pairs, time differences below the noise (~1 s).

### To get under +1%
The cost is the partner DP (`nearOf`: seed vote over the window + banded DP) of every extra candidate, run on ~12% of pairs
whose first pair scores below -8. It needs a cheaper PROVED check before the DP that rejects a candidate that cannot beat the
best pair so far (e.g. an upper bound on the partner score from seed votes in the window), or a better first candidate.
Not started. The small extra index (format change) was not tried.

## 5. Trimming

Source: What a softer trim threshold would do (measurement only; decision: stays at 25).

Base `fix/fast` f465a57. Only the per-base score constant `Q` of the quality trim was changed (`Phred - Q`, T = Q); `minLength` stays 25.
Scale: 200 000 pairs per set (not 1M). `novaseq_200k` = NovaSeq 2x151; `hg002_200k` = HG002 2x250 (stands in for HiSeq).
`map shim2.idx R1 R2 out.sam 100 1000`, 4 cores (`taskset -c 0-3`), SAM to a real file, warm cache. minibwa `map -t 4`. Script: `Testing/fuzz/trim_threshold.py`.
The 13 slow pairs were not measured for this (stopped on request).

### Proofs: not parametric in 25
The implementation is (`trimReadQ Q`, `ReadTrim.defQ`); the spec side hard-codes 25 in four places:
`Aligner/mapper/ReadTrim.lean` `defQ`, `Spec/Trim.lean:28`, `Proofs/Trim.lean:29` (copy of the spec) and `Proofs/Trim.lean:56` (`baseScoreS`).
Changing `defQ` alone breaks `Proofs.Trim` (`baseScoreS_eq`, omega). Changing all four to T = 20/15/10 builds the whole `lean-align` target (408 jobs, proofs included)
without any proof edit. The binaries were built that way, locally; nothing else was changed and the edits are not on this branch.

### Results (T25 / T20 / T15 / T10)
| | novaseq_200k | hg002_200k |
|---|---|---|
| trimmed length, mean (kept mates) | 148.5 / 150.0 / 150.5 / 150.8 | 231.3 / 239.7 / 246.0 / 248.4 |
| median | 151 / 151 / 151 / 151 | 248 / 249 / 249 / 250 |
| mates < 50 | 0.50 / 0.13 / 0.03 / 0.01 % | 0.47 / 0.06 / 0.00 / 0.00 % |
| mates dropped (< 25) | 0.33 / 0.07 / 0.03 / 0.00 % | 0.49 / 0.03 / 0.00 / 0.00 % |
| pairs mapped | 93.80 / 92.94 / 92.22 / 91.79 % | 93.61 / 91.29 / 86.60 / 84.53 % |
| pairs proper (ours sets 0x2 on every mapped pair) | = mapped | = mapped |
| pairs unique (both XU:Z:unique) | 82.42 / 82.15 / 82.03 / 82.02 % | 84.55 / 81.22 / 75.63 / 73.46 % |
| our unique pairs agreeing with minibwa (same chr, both mates within 300 bp) | 99.99 % each (13-14 elsewhere) | 99.98-99.99 % (36 / 20 / 15 / 15 elsewhere) |
| minibwa: mapped / proper / MAPQ 60 | 99.08 / 97.62 / 85.15 % | 99.57 / 98.06 / 87.57 % |
| wall (warm) / CPU at 4 threads, ours | 6.4, 6.4, 6.1 s / 15.8, 16.4, 14.2 s (T20/15/10; T25 run was cold: 142 s wall, 16.8 s CPU) | 5.8 / 6.9 / 6.9 / 8.3 s; 14.7 / 17.5 / 17.6 / 18.9 s |
| minibwa wall / CPU | 200 s (cold) / 46 s | 27 s / 84 s |

Reading: a softer rule keeps longer reads and drops almost nothing, but it lowers pairs mapped and unique, a lot on 250 bp reads (hg002, T15: -7 points mapped, -9 points unique);
NovaSeq loses little (-0.4 point unique at T15). The placement of pairs that stay unique does not change. No hol-trace P lines (the trace build was not made here).
Per the lead: the threshold stays at 25.

## 6. Reader loop and many cores (nothing above 4 cores is measured)

- Loop thread at 4 threads: 14.9 s CPU on NovaSeq 5M (ceiling about 365 Gbp/hr), 19.8 s on HiSeq (451). Its system
  time (9-12 s) is page faults on freshly allocated 8 MiB chunk buffers, not the number of read calls: forcing
  1 MiB reads cut read calls from 130k to 5k and changed nothing.
- Fixes in order: the cut-tasks patch (ceiling 550-650); reusing chunk buffers or a smaller chunk size in
  `Main.lean` `nextChunks` (Main change, not measured); two reader threads (tried once, no gain at 4 cores).
- gunzip of two files is single-threaded per file: estimated ceiling near 400 Gbp/hr. `rapidgzip` or block-gzip
  input lifts it; that is a change to the pipeline, not the aligner.
- Output order costs 0.3-8.5% of the wall after the slow-pair fixes; out-of-order output would be a Spec change.
- Memory grows without limit if one read file ends early or the files have very different record sizes
  (seen: 13.9 GB, killed). Fix: a cap or backpressure in `nextChunks` (Main), see FINISH_CHECKLIST.md.
- Index build peaks at 13.84 GB (8.9 GB of tables plus the 5.3 GB index being written). Freeing the tables before
  the save, or writing in pieces, would lower it.

## 7. Tools and test data kept with these notes

- `Testing/notes/ideas/slow_pairs/`: 13 one-pair FASTQ files that took 1-60 s before the fixes (3 HiSeq, 10 NovaSeq).
- `Testing/notes/ideas/hol_trace/`: README, `ana.py`, `pmp.sh` for the timing trace.
- `Testing/notes/ideas/scripts/`: cache simulation (`cache_cg.sh`, `cg_cost.py`), huge pages (`cache_hp.sh`),
  `cache_run.py`, `prefetch_bench.sh`, `trim_threshold.py`, streamed minibwa runs (`mb_lane.py`, `rangecat.py`,
  `hiseq_reps.py`).
- Stream and timing scripts: `Testing/results/blog/scripts/`, `Testing/results/stream/scripts/`, `Testing/ec2/`.

## 8. Open decisions (Rowan)

- Prefetch needs a trusted inline C call (`__builtin_prefetch`); identity in the logic, no proof changes.
  On the new scan it showed no gain outside noise.
- A run-time batch size from the cache size would enter through `Main.lean`; the proof obligation is that the
  output does not depend on it. Pair batching inside a job is output-independent for any batch size.
- The adapter letter table (instruction-neutral, fewer mispredicts): merge or not.
- The walk-best change (more mapped `unknown` pairs for 5-8% CPU): merge or not.
- Whether proofs of internals with no theorem of their own (banded alignment) may be replaced by tests: currently no.
- Trim: threshold stays 25; tie rule (longest, then leftmost) and best-window-among->=25 still open.

## 9. Later Spec change: report the whole read, with the trimmed ends soft-clipped (Rowan, 2026-11-13)

Not started. A question for the to-do list.
- Today a SAM record holds only the part of the read kept after adapter cut and trimming (SEQ, QUAL and CIGAR cover
  that part). The idea: SEQ and QUAL hold the whole read as it came in, and the CIGAR is `aS` + the alignment + `bS`,
  where a and b are the letters removed at each end. POS stays the first aligned letter. On the reverse strand the two
  clips swap sides.
- Why: the original reads can be recovered from the SAM; tools that expect whole reads work; comparing with other
  aligners needs no lining-up of a trimmed window against the whole read.
- Spec changes: `Spec/Trim.lean` has to give the window (start, stop) and keep the read (today it returns the cut
  read, so the offsets are lost); `Spec/MapFiles.lean` `prepPairs` carries the read and the window; `Spec/Sam.lean`
  `cigar`, `seq`, `qual` use them. To decide: a read trimmed away (today `*` with `XT:Z:trimmedAwayN`) could keep
  its letters as an unmapped record; the adapter part could be `S` or `H`.
- Proofs to redo: the SAM writer equalities (SamFast, SamFused), the read preparation and job equality in MapFast,
  `process_correct`. The mapping proofs are untouched (they see the same trimmed letters).
- Speed: not a gain. Alignment still runs on the kept part; the output gets longer (whole reads), so slightly more
  bytes to write.
