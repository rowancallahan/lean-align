# Cache behaviour of the mapper (measurement and reading only; nothing in Aligner/, Proofs/, Spec/ was changed)

Code: festive head code f465a57 (identical to c7a828e), index built by that code (`ic.idx`, 5,338,015,764 B), 200k NovaSeq and hg002 sets,
50k-pair prefixes for the simulations. Scripts: `Testing/scripts/cache_run.py`, `cache_hp.sh`, `cache_cg.sh`, `cg_cost.py`.
**Measured** = real runs on this box. **Simulated** = callgrind / cachegrind, no hardware prefetcher, no out-of-order overlap, no TLB.
**Estimated** = arithmetic on those numbers.

Box: Xeon 2.1 GHz VM, 4 cores, L1d 48 KB, L2 2 MB per core, L3 260 MB shared (so "server-like" already); THP `madvise`, defrag `madvise`.
Not measured: any other CPU (no 32-64 core server, no laptop, no phone).

## 1. Huge pages (measured; SAM md5 identical in all 72 runs)

- Lean's bundled mimalloc 3.4.5 reads `MIMALLOC_*` (`MIMALLOC_VERBOSE=1` lists `allow_large_os_pages`, `reserve_huge_os_pages`, ...).
- The index is **already** on transparent huge pages at baseline: `AnonHugePages` in `/proc/PID/smaps_rollup` = 5.3-5.5 GB of 5.6 GB RSS with `madvise` and no env var (the binary calls `madvise`).
- No further gain: user CPU at 4 cores, NovaSeq, mean [min-max] s: THP=always 12.5 [12.2-12.7], `MIMALLOC_ALLOW_LARGE_OS_PAGES=1` 12.8 [12.1-13.4], both 12.8 [12.4-13.2],
  base (madvise) 13.7 [13.3-14.1]. The base figure is an **order effect** (base ran right after the hugetlb variant): in a control with 5 back-to-back alternating madvise / always pairs the ranges were
  11.0-12.8 and 11.4-12.8 s. hg002 behaves the same.
- Huge pages help the system side, not the per-pair side: THP=never (AnonHugePages 0) has the same user time (13.6-13.7 s) but sys 4.8-5.1 s vs 3.0-3.2 s and wall +12-17 % (NovaSeq 1 core 19.8 s vs 17.7 s; 4 cores 8.4 s vs 7.2 s): fewer page faults while the 5.3 GB index is read in.
- A preallocated hugetlb pool (`nr_hugepages=2800` + `MIMALLOC_ALLOW_LARGE_OS_PAGES=1`) is worse: user 12.0-12.5 s (inside the noise), sys 7.8-8.9 s, wall 11.2-12.4 s at 4 cores vs 7.2 s.
- dTLB: not visible in these timings (4 KB pages cost no extra user time). It is a VM (nested paging), so TLB cost on bare metal could differ; I could not measure that.
- Settings written during the runs (`/sys/kernel/mm/transparent_hugepage/enabled`, `/proc/sys/vm/nr_hugepages`) were restored to `madvise` / 0.

## 2. Where the misses are (simulated)

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

## 3. The hot lookup code (read, plus objdump of the built binary)

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

## 4. Ideas, ranked by estimated gain per proof effort (all are exact-equality changes; none was implemented)

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

## 5. Look-ahead prefetch of the genome block (side branches, never merged; measured)

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
