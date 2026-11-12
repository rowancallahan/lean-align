# Search ideas: exact speedups not yet tried (literature pass, 2026-11-03)

Scope: ideas that keep the answers the same (or provably equal as sets, see each item), beyond what the notes
already cover. Read first: SESSION_SUMMARY (night of 2026-11-03), NEW_FILTER, INDEX_COUNTS, LOOKAT_SLICES,
JOIN_ARRAYS, SMALL_COSTS, INDEX_TRICKS, SECOND_INDEX_PLAN, PROOF_MAP, plus LOOKAT_FAST, FINE_FILTER, N31/N32/N33/N35,
THREADS, SECOND_LOOK, WFA_HG38. No code was run for this note. Gains are estimates from the notes' callgrind
numbers. Each one says whether it is measured or derived.

Cost reference (NovaSeq 2k, callgrind, ~1223M after `speed/join`): router `tierPairBP` ~254M (`mateKPPO` 184M:
bucket scans `scanAWF`/`nextK` ~88M, staging `stageKSPN` ~67M). Second look `lookAt` ~320M on 33 pairs: `hitsCKT`
~207M, with the filter (`lanesAnyR` 49M + `fineEU` 16M), `suppA` 33M, the shape loop 49M (~19.6k kernels,
~2.1k Ir each) and ~3.2k Ir per false diagonal. 27 of the 33 pairs find no pair. Join ~42M. Fallback ~135M. Shim
~418M. SECOND_INDEX_PLAN, 200k NovaSeq: the "too heavy" pairs (a seed with > 500 places among the e+1 rarest of
the searched mate) are 16% of `lookAt` pairs and 59-76% of its time.

## Ranking (gain / effort)

| # | idea | where | identical output? | est. gain (NovaSeq) | proof |
|---|---|---|---|---|---|
| 1 | Split the error budget across the pair (pigeonhole over both mates) | `LastResort.pairsAt`, `noPairJS` | yes: rerun today's path when a pair is found | 5-12% Ir (derived; check offline first) | med |
| 2 | Region lookups (`RgMz`) for the partner in the second look | `hitsKPFN`/`hitsSKNG` | yes (same anchors, same order) | 1-5% Ir (derived) | low-med |
| 3 | Huge pages + memory-level parallelism for index/genome reads | `scanAWF`/`okAtW`, `mzLookSP`, whole process | yes (no semantic change) | 3-10% wall (literature; Ir blind) | none / low |
| 4 | Shape pruning from a piece x shift match map (SHD/Shouji/A*PA-style bound) | `hitsCKT`/`hitsCKN` shape loop; `stageKSPN` | yes (pruned shapes have no hit within cap) | 1.5-3% Ir | med |
| 5 | Memoize kernels across nearby diagonals (same window twice) | `hitsCKT`, `chromKBFGK` | yes (pure memo) | 0-2% Ir (measure first) | low |
| 6 | Variable-length seeds from the 25-mer index (OSS-style partition + extension check) | `hitsSK` seed choice, `exists_clean_seed_amongE` | yes as sets; same trick as #1 for order | 2-6% NovaSeq, more on 2x250 (derived) | med-high |
| 7 | Optimum first, then replay at the final cap | router `chromKB`/`stageKSPN` (Best-capped searches) | yes (Best fields equal; needs a lemma) | 0.5-2% Ir | med |
| 8 | Shorter pieces (5-6 letters, 6 lanes/word) in the fine filter | `fineEU`/`lanesAnyR` | yes (same pigeonhole, `coverLE` for l >= 2) | ~1% Ir | low-med |
| 9 | Ends-free WFA / banded bit-vector lower bound per diagonal | before the 43 shapes | yes | overlaps #4; <= 1% beyond it | high |

Do #1 + #2 together: #1 is what makes #2 pay most.

---

## 1. Split the error budget across the pair

**What.** `pairsAt` keeps pairs with `pairScoreD >= -c`, so `pen1 + pen2 <= c` (dovetail cost >= 0). Penalties
are integers, so for any split `a`: `pen1 <= a` or `pen2 <= c - a - 1`. Today is the case `a = c`: the cheaper
mate X is searched genome-wide at cap `c` (its `sbound c + 1 = 5` rarest seeds per strand for c = 16), then Y only
near X's hits. Instead, choose `a` per pair from the bucket sizes: X genome-wide at cap `a`
(`sbound a + 1` seeds), plus Y genome-wide at cap `c - a - 1` (`sbound (c-a-1) + 1` seeds). Each found hit
gets a near search of the partner at cap `c` (or `c - pen` of the hit). With c = 16 (`sbound x = x/4`) the
options are X/Y seeds = (5,0) today, (4,1), (3,2), (2,3), (1,4). That is always 5 lookups per strand side, but they
can come from the rarest seeds of both mates. This is the optimal-seed-solver idea applied to the pair instead
of one read.

**Why it helps here.** The expensive pairs ("too heavy", 59-76% of `lookAt` time) have a 500+ place seed among the
5 rarest of the mate searched in full. S-F's note: "two ~4.5k-hit seeds among the 5 needed on both mates". With
the split, a pair needs only its 5 rarest seeds across both mates under the per-mate limits. A pair whose mates
each have 2-3 rare seeds then avoids both heavy seeds. The lower caps also make each searched diagonal cheaper:
`gapBound 8 = 1`, so `r = 2` instead of 10, 5 shifts in the piece filter instead of 21, and far fewer shapes.

**Same answers.** Membership is unchanged: `p` in the new list iff it is a proper pair of hits at cap `c` with
score >= -c (case split on `pen1 <= a`; use `hitsKPF_mem` at caps `a` and `c-a-1`, and the near searches at cap
`c`). Keep the two parts disjoint by keeping only `pen1 > a` in the second one. The order can differ, and
`topW` picks among tied top pairs by order. To stay byte-identical: if the new list is empty (27 of 33 calls), it
is empty today too, so `boundsOnly` is the same answer. If it is non-empty, run today's `pairsAt` (rare and cheap
relative to the rest). Proof: `pairsAt_mem` restated, an arithmetic lemma, reuse `hitsKPFN_near`. The same split
applies to the join (`noPairJS`, stage 3).

**Gain (derived).** If it removes half of the too-heavy time, that is ~0.3 x 320M ≈ 100M, ~8% of NovaSeq Ir.
**Check before writing Lean:** extend `Testing/scripts/second_index/evalq.py`. It already has the per-pair
25-mer counts for every k-mer of the bound-only mates. Add a cost per split, `min_a (cost_X(a) + cost_Y(c-a-1))`,
next to today's `cost_X(c)`. This is an afternoon.

Refs: Xin et al., Optimal seed solver, Bioinformatics 2016,
https://doi.org/10.1093/bioinformatics/btv670 (choose the least frequent set of non-overlapping seeds that
still satisfies the pigeonhole). The pigeonhole over a concatenated pattern is the classic partition lemma: Baeza-Yates & Navarro,
"Faster approximate string matching", Algorithmica 1999, https://doi.org/10.1007/PL00009253.

## 2. Region lookups for the partner in the second look

**What.** `hitsKPFN` → `hitsSKNG` looks up the partner's `sbound c + 1` rarest seeds genome-wide (`LookG` on
`PkMz`, full bucket scans plus a genome check per match, ~865 Ir per `okAtW` match). Only then does it keep the
diagonals near the first mate's hits (`keepN`, chromosome gate). The router already has a proved region lookup:
`RgMz`/`mzLookRP` → `lookupPWR` jumps to the first slot at or after the region start (`startSlot`, slots are in
position order) and stops at its end. When the first mate has few hits (`ys` small), look the partner's seeds up only in the
merged `keepN` windows, one region lookup per window.

**Same answers.** The anchors in a window from `lookupPWR` are the genome-wide anchors cut to the window
(`cutAnc` is how `mzLookRP` is already specified). The union over disjoint windows in increasing order is the
same sorted array that `slicesAt` would produce for the kept diagonals. So the `hitsCKN` inputs are equal. The proof
needs window merging, an `extract` of a sorted array, and `keepN` gives the same set. Pick per pair by cost
(region path when `|ys|` x window << sum of bucket sizes). Both branches are equal, so the choice is free.

**Gain (derived).** It is the partner side of `lookAt` when its seeds are heavy. A 4.5k-place seed costs ~4-5M Ir
genome-wide, against ~10-30k per window. With #1 the partner near search runs after every split, so this is
what makes #1 pay. Alone: 1-5% NovaSeq Ir (measure: split `lookAt`'s Ir between `hitsKPF` and `hitsKPFN`).

Refs: mate rescue in BWA-MEM (Li 2013, https://arxiv.org/abs/1303.3997) and minimap2 (Li 2018,
https://doi.org/10.1093/bioinformatics/bty191). Those use SW in the window. Here it is the exact seed lookup cut
to the window.

## 3. Huge pages and memory-level parallelism (wall time; callgrind cannot see it)

**What.** Every lookup touches a random bucket offset (4 x (2^26+1) B table), random slots in a 5.3 GB index, and
then the packed genome at each matching slot (~26 matches per lookup, ~10.6 lookups per pair). That is hundreds of
DRAM and TLB misses per pair with 4 KB pages. N31 already saw CPU fall ~30% for a −0.4% Ir change (atomic
refcounts). Memory effects are similar in kind.
- (a) **Transparent huge pages, no code change.** The Lean runtime allocates through mimalloc
  (`mi_free` appears in profiles). Try `MIMALLOC_ALLOW_LARGE_OS_PAGES=1` (older name
  `MIMALLOC_LARGE_OS_PAGES`). If the big ByteArray goes through glibc instead, try
  `GLIBC_TUNABLES=glibc.malloc.hugetlb=1`. Or set `/sys/kernel/mm/transparent_hugepage/enabled=always` on the bench box.
  Check with `grep AnonHugePages /proc/<pid>/smaps_rollup`. Measure with `perf stat -e dTLB-load-misses,LLC-load-misses`.
- (b) **Batch, then check.** Inside `scanAWF`, first collect the key-matching slot positions in a small
  array (sequential reads), then run the genome checks `okAtW` in a separate tight loop. The independent loads
  can then overlap. Do the same one level up: compute all seeds' bucket bounds (`mzPrep`/`p.b`) for both strands
  before scanning any. No prefetch instruction is needed (Lean has no `extern`), only independent loads close
  together. Proof: `filter (p) ∘ filter (q)` / `List.map` reordering, low.
- (c) Later: chunk-level batching, with all seeds of a chunk sorted by bucket (BWA-MEM2 style). This is high effort.
  It cuts across the per-pair early exits.

**Same answers.** (a) Nothing changes semantically. (b) is an equal function.
**Gain.** BWA-MEM2 reports most of its 2x SMEM gain from batching plus software prefetch. THP typically
gives 5-20% on random-access index workloads. Estimate 3-10% wall here. Measure on the 200k sets with
`perf stat`, since Ir will not move.

Refs: Vasimuddin et al., BWA-MEM2, IPDPS 2019, https://arxiv.org/abs/1907.12931;
glibc tunables, https://sourceware.org/glibc/manual/latest/html_node/Memory-Allocation-Tunables.html;
mimalloc options, https://microsoft.github.io/mimalloc/environment.html.

## 4. Shape pruning from a piece x shift match map

**What.** In `hitsCKT` every diagonal that passes `kfiltVF` runs all shapes of `shapesT lim` at cap `lim`
(43 at 16), about 90k Ir per passing diagonal. For the hit list, the cap is not lowered by the best. The fine
filter already compares each 8-letter piece at the `2r + 1` shifts, but stops after `sb + 1` failures and
keeps only a yes/no. For a passing diagonal, compute the full map instead: for each piece, a mask of the shifts
where it matches (~21 lane steps per read word, ~5k Ir). A window of shape `(s, t)` within penalty `Q` has `G <= gapBound Q`
gap letters. Along its path the offset stays within `[min(s,t) - g', max(s,t) + g']` with
`g' = (G - |t - s|) / 2`. Every clean piece matches at some shift in that range, and at most `sbound Q`
pieces are spoiled. So `#pieces with (mask & range) = 0 > sbound Q` ⇒ skip the shape (one AND/popcount
per piece and shape).

On a true locus most pieces match only at shift 0, so shapes whose range excludes 0 are skipped. Roughly
half of the 43 shapes (e.g. `(5,5)`: range `[3,7]`).

**Same answers.** A skipped shape has no window within `lim`, so `hitsCKT` emits nothing for it either way.
The list is the same, in the same order. Proof: `coverLE` (already proved for pieces) refined from `±r` to the
shape's offset range. The new lemma says a monotone path with `G` gap letters stays in that range. The router's
`stageKSPN` can use the same map with its moving cap.

**Gain.** About half of the 49M shape loop, minus the map cost: ~20-25M, ~2% NovaSeq. More on HiSeq (2x250:
more pieces, so the bound is tighter). This is Shouji's neighbourhood map and SHD's shifted masks, used as a per-shape
lower bound. A*PA's seed heuristic is the same "spoiled seeds bound the cost" bound, applied to a sub-problem.

Refs: Xin et al., SHD, Bioinformatics 2015, https://doi.org/10.1093/bioinformatics/btu856; Alser et al., Shouji,
Bioinformatics 2019, https://doi.org/10.1093/bioinformatics/btz234; Alser et al., SneakySnake, Bioinformatics 2020,
https://doi.org/10.1093/bioinformatics/btaa1015; Groot Koerkamp & Ivanov, A*PA, Bioinformatics 2024,
https://doi.org/10.1093/bioinformatics/btae032.

## 5. Memoize kernels across nearby diagonals

**What.** Shape `(s, t)` on diagonal `D` and shape `(s + 1, t - 1)` on `D + 1` are the same window: start
`D - n - s`, length `n + s + t`. With an indel in the read, the anchors of seeds on both sides give two or three
adjacent distinct diagonals, and each one runs its shapes. Keep a small map from window `(st, len)` to kernel
result per chromosome pass, and look it up before `kerHKG`.

**Same answers.** The emitted list is identical: the memo returns `kerHKG`'s value. Proof: a memo invariant,
low. Is the hit list allowed to contain the same window twice today? Yes, and it still will.
**Gain.** Unknown. Count passing diagonals within `2 * gapBound` of another passing diagonal first, with a debug counter
in the bench. Worth it only if > ~20% of passing diagonals have a neighbour.

## 6. Variable-length seeds from the same 25-mer index

**What.** OSS for one mate. The pigeonhole needs `e + 1` disjoint, error-free seeds, not grid 25-mers. At 150 bp
with e = 4 there are 5 seeds over 150 letters: a 30-letter average and 25 letters of slack. A seed of length
`L >= 25` is looked up by its rarest 25-letter substring (any 25-mer is a valid query of the minimizer index).
Each anchor is then kept only if the other `L - 25` letters also match there: one or two packed genome words,
~100-200 Ir, against ~3.2k Ir for a false diagonal in the filter. Pick the partition by a small DP over the
start offsets, with bucket sizes as costs. At 2x250 (10 grid seeds, 5 needed) the seeds can be 50 letters.

**Same answers.** The candidate diagonals are still a superset of every hit's diagonal: one seed of the partition
is clean, and its exact occurrence is found by its 25-mer lookup and survives the extension check. The later
`kfilt`/kernels are unchanged, so `hitsCKT` gives the same hits. List order follows the anchors, which come from
other seeds. Use the empty/non-empty trick of #1 or show order independence. Proof: `exists_clean_seed_amongE` for
a variable partition (new statement, same argument), plus the plumbing that `SECOND_INDEX_PLAN` says touches
`/ 25` in many files. Med-high.
**Gain (derived).** On the too-heavy class the rarest 25-mer is inside Alu/L1. A 30-50-letter exact match
across diverged copies is far rarer (at ~15% divergence about 0.85^25 ≈ 2% of copies keep a clean 25-mer,
and 0.85^50 ≈ 0.03% a clean 50-mer). Largest on 2x250, smaller at 150 bp. Measure with
`kcount.c` at k = 30/40/50 on the dumped mates before deciding. This is a new angle on SECOND_INDEX_PLAN: it
rejected *shorter* seeds and a second index. This idea uses *longer* seeds from the existing index.

Ref: Xin et al. 2016 (OSS), https://doi.org/10.1093/bioinformatics/btv670; Kiełbasa et al., LAST adaptive seeds,
Genome Res 2011, https://doi.org/10.1101/gr.113985.110.

## 7. Optimum first, then replay at the final cap (Best-capped searches only)

**What.** In the router (`chromKB`, `stageKSPN`, `addK`), the cap `min lim b.pen` shrinks as better windows are
found. The filter (`sbound Q`, `r`) and the kernels get cheaper as the cap shrinks. The visit order (ascending
diagonal, then shape) decides ties, so it cannot be changed (N31 §Order). Run pass 1 in a best-first order
(diagonals by support count, descending) to get only the optimal penalty `Q*`. Then run pass 2 in today's
order with the cap fixed at `Q*` from the start.

**Same answers.** A lemma is needed: the `Best` reached from cap `Q*` equals today's final `Best`. The windows
above `Q*` that today's run passes through are all replaced later, and the first window at `Q*` in visit order is
the same. Check `Best.add`'s `amb` rule. If `amb` is set on a tie and kept across later improvements, the
lemma needs care.
**Gain.** Only pays where the best improves several times along the diagonal order. Small on the shown profiles
(the true diagonal often comes first). 0.5-2%.

Ref: classic branch-and-bound / A* ordering; Ukkonen's cut-off, Inf. Control 1985,
https://doi.org/10.1016/S0019-9958(85)80046-2.

## 8. Shorter pieces in the fine filter

**What.** `fineEU` rejects a false diagonal after `sb + 1 = 5` failed 8-letter pieces. 4 pieces per word (16-bit
lanes), so at least 2 read words, ~44 lane steps. With 5-letter pieces (10-bit lanes, 6 per word) the 5 failures
can come within one word on diverged copies.
**Same answers.** `coverLE` holds for any piece length >= 2. `zt` must be re-proved for 10-bit lanes (same
add-carry argument). Pieces match more often by chance (21 shifts x 4^-5 ≈ 2% per piece). Measure the steps per
false diagonal before committing.
**Gain.** Up to ~1/3 of `lanesAnyR` (49M), ~1%. This overlaps with the unproved fused two-word scan
(`lanesAny2`, −5M).

## 9. One-pass lower bound per diagonal (ends-free WFA or banded Myers)

One ends-free pass over the band `±gapBound` gives, for each end shift, the best penalty over all start shifts
(forward pass), and the reverse pass gives the same per start shift. A shape `(s,t)` with either bound `> lim` is
skipped. A unit-cost banded Myers/Hyyrö pass fits one `UInt64` (band 11 at Q = 16). The affine-to-edit
conversion is weak, though: `pen >= 4*ed - 2*gapBound + 6` when gaps exist. The proved WFA kernels lack an
ends-free variant (MAPPER_DESIGN_NOTES §5 calls it "probably the largest change"). Do #4 first. This adds
little beyond it (NEW_FILTER: ~40 of ~280 filter-passing diagonals have no hit).
Refs: Myers, JACM 1999, https://doi.org/10.1145/316542.316550; Hyyrö & Navarro, CPM 2002,
https://users.dcc.uchile.cl/~gnavarro/abstracts/cpm02.2.html; WFA, Marco-Sola et al. 2021,
https://doi.org/10.1093/bioinformatics/btaa777; BiWFA 2023, https://doi.org/10.1093/bioinformatics/btad074;
Edlib, Šošić & Šikić 2017, https://doi.org/10.1093/bioinformatics/btw753.

---

## Considered and not proposed (already done or rejected in the notes, no new angle)
- Stronger q-gram counting filter per diagonal, 8-mer set probes, replicated pieces: NEW_FILTER (at most ~15% of
  kernels after the filter; same work per diagonal).
- Finer pigeonhole by a second index of shorter seeds or syncmers: SECOND_INDEX_PLAN (~1-2% of the headline, over
  budget). #6 uses *longer* seeds instead.
- Sorted-key buckets and binary search within a bucket: N31 and LOOKAT_SLICES (<= 2%).
- Stored context bits in slots (INDEX_TRICKS 3a): still open. The new angle in #3 is that each rejected match saves a
  DRAM miss, not ~865 Ir. Measure the 22-mer → 25-mer pass rate of `okAtW` first; if most matches pass, it gains little.
- Banded DP / WFA per diagonal instead of the word kernels: NEW_FILTER and WFA_HG38 (< 1%).
- Thread contention and refcounts: THREADS (fixed). Read-pair dedup: N31_O4 (neutral).
- Reusing the join's lookups in the second look, rare-seed completion: S-F (no gain).
- Spaced seeds, strobemers, LSH: INDEX_TRICKS (no deterministic completeness for single patterns).
- SIMD (GateKeeper/SneakySnake hardware forms, mm2-fast AVX-512): no SIMD in proved Lean. Only the
  word-parallel forms (#4, #8) transfer.

## Suggested order
1. Offline: `evalq.py` with the split cost (#1) and with 30/40/50-mer counts (#6). `perf stat` with THP on/off (#3a).
2. #2 (smallest proof, needed by #1). Then #1 with the empty-list fallback.
3. #4. Then #5 only if the neighbour count is high.
