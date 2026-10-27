# Loop-shape campaign: plan (prep for the timing runs, 2026-10-27)

Branch `speed/loop-shape` (from `claude/festive-fermi-mf9mo6` @ 3f8ca20). Rowan's rules hold throughout: no
`extern` / `implemented_by` / `unsafe` / `native_decide` / `sorry` / new axioms; no hand-written SIMD; every fast
form is a separate definition + an equality proof + `@[csimp]`, existing theorems untouched; Spec/ and the
frozen files unchanged; `sh scripts/check.sh` passes.

## 1. What is ready

| item | where | status |
|---|---|---|
| `hamW`, `fwdW`, `bwdW` → USize loops | `kernels/k250/MapperK250.lean`: `@[csimp] hamW_eq_hamWF`, `fwdW_eq_fwdWF`, `bwdW_eq_bwdWF` | proved, measured |
| `seedLE` → USize loop | `index/minimizer/MzWord.lean`: `@[csimp] seedLE_eq_seedLEF` | proved, measured |
| `revCompLoop` → USize loop | `kernels/k250/FastGenK250.lean`: `@[csimp] revCompLoop_eq_revCompLoopF` | proved, measured |
| `Mz.miniGo` → USize loop | `index/minimizer/MzIndex.lean`: `@[csimp] miniGo_eq_miniGoF` | proved, measured (in the total) |
| generated-C scan + tierPair profile | `notes/GENERATED_C_SCAN_2026-10-27.txt`, `scripts/cscan.py` | done (synthetic data) |
| synthetic data | `scripts/sim_genome.py`, `scripts/bench_data.sh` | done |
| A/B harness | `scripts/ab_kernel.sh`, `scripts/ab_pair.sh`, `scripts/ab_ir.sh` (+ `AB_PROD=1`) | done |

All csimp theorems: standard axioms only; no theorem statement changed; `sh scripts/check.sh` passes on the final
state; every A/B below compares the RTX and tier dumps of base and new byte for byte (identical).

**Result (base 3f8ca20 → this branch, synthetic 8 Mb genome, 2×150 pairs, 1 task):**

| measure | production settings (`AB_PROD=1`) | bench RTX mode |
|---|---|---|
| callgrind Ir inside `tierPair`, 2000 pairs | 597.5 M → 553.5 M (**−7.4%**) | 1,247.9 M → 1,187.0 M (**−4.9%**) |
| wall, 20k pairs, median of 7 alternated runs | 0.835 → 0.746 s (**−10.6%**) | 1.612 → 1.517 s (**−5.9%**) |
| CPU, same runs | 0.820 → 0.750 s (−8.5%) | 1.600 → 1.500 s (−6.2%) |

### One-line commands

```sh
export PATH=$HOME/.elan/bin:$PATH                       # or the lean-4.33.0 bin dir
lake build && lake build whole_genome k250_bench       # ~35 min from scratch
sh scripts/bench_data.sh out/bench                      # synthetic genome + pairs + checked index (~20 s)
# snapshot binaries per variant, e.g. before and after a change:
mkdir -p out/bin/A && cp .lake/build/bin/{whole_genome,k250_bench} out/bin/A/
sh scripts/ab_kernel.sh out/bin/A/k250_bench out/bin/B/k250_bench 5        # per-window kernel ns, alternated
sh scripts/ab_pair.sh   out/bin/A/whole_genome out/bin/B/whole_genome 5    # whole pair path wall/CPU, dumps compared
sh scripts/ab_ir.sh     out/bin/A/whole_genome out/bin/B/whole_genome      # callgrind Ir inside tierPair (exact)
AB_PROD=1 sh scripts/ab_ir.sh ...      # router settings of the spec's alignPairs (see §2)
python3 scripts/cscan.py tierPair 60   # static loop-shape table from .lake/build/ir
```
On real data: `ab_pair.sh` / `ab_ir.sh` take `<dir>` with `<dir>/g/{ix.*,chr1.fa,chr2.fa,p150_1/_2.reads.txt}`;
for chr21 / hg38 run `whole_genome pmap` directly with `WG_READS=...` (see `bench/WholeGenome.lean` header).
Timing on shared cloud boxes is ±10% (bench/research_notes.txt); use ≥5 alternated runs and the medians, and
`ab_ir.sh` (instruction counts, deterministic) to decide small changes.

## 2. Two things to know before timing

1. **Bench mode ≠ production settings.** `whole_genome pmap` mode RTX runs `tierPair` with the bench's untrusted
   helpers on: budget gate (WG_XBUD 60000), ceilings (`ceilX`), the tier-2 heuristic `heurP` (19% of tierPair's
   instructions here, plus `rescoreRuns`/`chkCand` re-checking its proposals, 15%) and the exact pair search (`xe`).
   The spec's `alignPairs` (`Proofs/Aligner.lean`, `tierCfg`) sets none of these: no gate, no ceilings, no
   heuristic, no exact search, guarantee at 4. `AB_PROD=1` in the scripts sets `WG_PG=4 WG_XBUD=0 WG_XCEIL=0
   WG_XH=0 WG_XEBUD=0` to approximate it (the guarantee's mate order `pref` still comes from the bench). Decide
   which configuration the campaign optimises; the ranking below differs between them.
2. **Synthetic ≠ hg38.** The profile here is on an 8 Mb synthetic genome. On real data repeat-heavy pairs dominate
   (≈2% of mates, ≈84% of time per the 10-25 notes), which weights the bucket scans (`scanAWK`, `scanAWR`,
   `rawScan`) and `stageKSP` far more. Re-run `ab_ir.sh` / callgrind on chr21 first and re-rank.

## 3. Candidates (each: fast definition + equality proof + `@[csimp]`, theorems untouched)

Self-instruction shares inside `tierPair`, 2000 synthetic pairs, `AB_PROD=1` (prod; 597 M Ir) and bench RTX
(1,248 M Ir; RTX adds heurP, rescoreRuns, the gate, ceilings and the exact search):

| function | prod | RTX | what |
|---|---|---|---|
| `seedLE` | 5.8% | 4.0% | seed word of the read per lookup (Nat byte loop, ~1,900 Ir per 25 letters) — **csimp done** |
| `Mz.miniGo` | 5.6% | 3.6% | minimizer of a q-word (Nat `o`, `w`, `bo`) — **csimp proved (scratch), §K7** |
| `packLoopU` | 5.0% | 3.1% | `packRP` twice per mate (both strands) + in pairGQC/hitsAtQ |
| `scanWF` (pscanD) | 4.8% | — | PairGuarQ sliding filter: one `cnt64` per position, closure `f st`, Nat `k`/`st` |
| alloc/free (`lean_dec_ref_cold`, `mi_free`, `mi_malloc_small`, `lean_del_core`) | 10.5% | 13.5% | lists, arrays, closures |
| `fwdMis`/`bwdMis` @gappedPen2Pk, `hamming` @ilG | 9.3% | 6.5% | byte loops on the packed genome via `GRead PGen` (8-letter pre-scans of `fwdLG`/`bwdLG` + gapped fallback) |
| `kerGKG` | 3.2% | 2.2% | window dispatch (240 Nat ops in its body) |
| `revCompLoop` + `lean_byte_array_push` | 4.8% | 3.1% | reverse complement per mate — **csimp done** (push stays) |
| `hamW`/`fwdW`/`bwdW` | 4.7% | 3.0% | word kernels — **csimp done** |
| `scanAWK` / `scanAWR` / `mzLookSP` | 2.2 / 0.6 / 1.6% | 1.8 / 0.6 / 1.1% | bucket scans (grow with repeats) |
| `lanesAny`, `flagsOk`, `costPI` List.map, kpKer `Array.mapM` ×2 | 1.7, 1.0, 1.4, 2.8% | | |

### K1. hamW / fwdW / bwdW on USize — DONE (prototype)
*How.* For each kernel `X` (all `Nat` arguments):
- `XU`: same recursion with `x = 32 j`, `acc`/`k`, `lim`, `stop`/`lo`/`e`, `u0` in `USize`; read word `rwAt rw j`
  (`Array.uget`, falls back to `rw[j.toNat]!`); genome word `gwordU` (offset `17 (u >>> 1) + 1 + 8 (u &&& 1)` in
  USize, one bounds check `b < b + 8 ∧ b + 8 ≤ w.usize`, else `gwordS`); `lowFU`/`highFU`/`combU`/`subU` USize forms of
  `lowF`/`highF`/`comb`/truncated `-`; `cnt64U` (cnt64 before `.toNat`). Termination: `stop < 2^20` carried as a
  proof argument (erased), so no run-time check per iteration.
- `XU_eq`: `XU … = X …` given `toNat` equalities for each USize argument and the bounds (strong induction on the
  measure, ~50 lines each; the helper lemmas `usz_*`, `uget_ok`, `gwordU_eq`, `lowFU_eq`, … are shared).
- `XF`: `if (u0 < 2^28 ∧ args < 2^20 ∧ j < 2^14/2^16) then XU … else XS …` where `XS` is a verbatim copy of `X`
  (`csimp` rewrites `X` everywhere, including in `XF`, so the fallback must be a copy); `XS_eq` by induction.
- `@[csimp] theorem X_eq_XF : @X = @XF`. Bounds hold for reads ≤ 256 on genomes < 2^33 letters (hg38: u0 < 1e8).
*Effect.* `hamW`: 12.88 M → 6.54 M Ir (−49%); the wrapper's `Nat` bound checks are 1.5 M of that. The three
kernels together: tierPair Ir −1.92% (prod) / −1.25% (RTX). `k250_bench` same-length windows (hamA path) 0.58–0.87×
of base time, but that bench is too noisy here (unchanged byte kernels moved 0.92–1.52×).
*Risk.* Low; proofs done; generated C checked (loop bodies: size_t/uint64_t only; Nat only on exits/cold paths).
Possible follow-up: move the bound test from `hamWF` (per call) into `hamA`'s caller (per window) — saves most of
the 1.5 M wrapper cost but means a csimp on `kerGKG` / `ker16KWG`.

### K2. Read words unboxed (ByteArray + uget instead of `Array UInt64`)
*Now.* `rwAt` already uses `Array.uget` (no bounds/panic path, no Nat), but each element is still a boxed `UInt64`
(`lean_array_uget_borrowed` + `lean_unbox_uint64` = two dependent loads per 32 letters).
*How.* `RP` gets a `ByteArray` copy (`b`, 8 bytes per word) built by `packRPU` alongside `w`, invariant
`∀ j < w.size, rd8 b (8 j) = w[j]`; `rwAtB` reads 8 `uget`s (clang merges them into one 64-bit load). The kernels' `XU`
take `b`; `XF` passes `K.b`… but `hamW` receives only `rw : Array UInt64`, so the csimp has to sit one level up
(`hamA`/`fwdA`/`bwdA` or `kerGKG`/`ker16KWG`, which receive `K : RP`), with the invariant as a hypothesis
discharged from `packRP`. Changing `RP`'s fields touches `packLoop`/`packRP` (definitions, not statements).
*Effect.* Small: one cache-resident pointer chase per word; ≤ 10% of the kernels' remaining cost, ≪ 1% overall.
*Risk.* Medium (structure change, more proof plumbing). **Do after re-profiling on hg38, only if K1's loops show
the unbox as hot.**

### K3. gwordF offset arithmetic in USize — DONE inside K1
`gwordU` is used by all three loops. The remaining `Nat` `gword`/`gwordF` calls are once per kernel call (the first
word in `hamA`/`fwdA`/`bwdA`) and in `winOk`/`flagsOk` (`17 * b` per block, 0.7% self). A `flagsOk` USize form is
the same template (`flagsOkU` over block index, `w.uget (17 b)`), ~30 lines of proof. Effect ≤ 0.7%.

### K4. cnt64 → textbook popcount
*How.* Two steps, each a csimp on `Packed.cnt64` (global: every caller benefits).
- (a) `% 255` → `(b * 0x0101010101010101) >>> 56`. Equality: each byte of `b` is ≤ 8 (sum ≤ 32 < 256), so the
  multiply puts the byte sum in the top byte with no carries; `cnt64_eq` already gives `b % 255 = dsum` via
  `dsum_mod`; needs a new `mul_shift = dsum` lemma over the 8-byte expansion (Nat, `rep`/`lowSum` style).
- (b) the full idiom `y - ((y >>> 1) &&& m1)`, `(y &&& m2) + ((y >>> 2) &&& m2)`, `(y + (y >>> 4)) &&& m4`,
  `(· * h01) >>> 56` on `y = fold x` — the exact pattern clang's AggressiveInstCombine turns into `popcnt` (checked
  in the 10-25 test). Equality: `(y >>> 1) &&& m1 = 0` when `y` has only even bits (bitwise, `Nat.testBit` ext +
  `decide` on the constant's bits), and `(a + (a >>> 4)) &&& m4 = (a &&& m4) + ((a >>> 4) &&& m4)` when every nibble
  of `a` ≤ 7 (no carries). No `bv_decide` (it uses `Lean.ofReduceBool`, a non-standard axiom).
*Effect.* `popcnt` only with `-march` ≥ x86-64-v2 (K6); without it (b) is no faster than (a). cnt64 is ~10 of
~40 instructions per word in the kernel loops → ~10–20% of K1's loops, < 0.5% overall here.
*Risk.* Low (pure arithmetic), but the proof is fiddly (~100–150 lines). Do with K6.

### K5. Minimizer bucket scans (scanAWK, scanAW, scanAWR, rawScan/rawScanU, okAtW, lbSlot)
*Now.* 182–210 Nat ops per iteration (the largest loop bodies in the router path), 18 `Nat` parameters threaded
through each call, `ix.slot t` / `ix.posOf` with Nat offsets; self Ir here: scanAWK 1.8%, scanAWR 0.6%,
rawScan < 0.5% — but these are the loops that grow with repeats.
*How.* Same template as K1: `scanAWKU` with `t`, `hi`, and the slot offset `sw * t` in USize, slots read by
`uget` (`slotW` already returns UInt64), the key test on UInt64 (already), positions converted to Nat only when
pushed. The 15 loop-invariant Nat arguments become a structure or USize locals checked once in the wrapper
(`hi < 2^32`, `sw ≤ 8`, `sl.size < 2^40`). Proof per scan ~80 lines (the existing `scanAWK_eq` is the model).
*Effect.* Synthetic: ≤ 2.5%. hg38 (repeat-heavy buckets): likely the largest single item — measure first.
*Risk.* Medium (many arguments; `okAtW` stays Nat unless also converted).

### K6. `moreLeancArgs` / `-march` levels (no proofs involved)
*How.* `lakefile.lean`: `package lean_align where moreLeancArgs := #["-march=x86-64-v2"]` (popcnt, SSE4.2) or
`"-march=x86-64-v3"` (AVX2, BMI2, LZCNT); `weakLeancArgs` to try without rebuild traces; or `LEAN_CC`. Also
`-flto` + LTO link (as lean-zip does): lets clang inline `hamWU`/`gwordU` into `kerGKG` across modules.
*Effect.* 0–5% expected; the K1 loops auto-vectorize poorly anyway (data-dependent exits); popcnt (K4b) and
BMI2 shifts help a little. LTO may matter more than `-march` now that the hot loops are machine-word code.
*Risk.* None for proofs. A v3 binary dies with SIGILL on pre-Haswell CPUs; make it a build option. Full C rebuild.

### Further candidates found while reading / profiling (§B of the scan note)
- **I1. Index re-parsed and copied on every `alignPairs` chunk (from the B5 index work, festive-fermi b2aed4f;
  not in this branch yet).** `loadIndex` (`Proofs/Aligner.lean`) `extract`s `ix.offs` (~256 MB at B = 26), `ix.sl`
  (GBs) and `G.w`/`G.ex` (~0.8 GB) out of the saved `index` ByteArray and rebuilds `pm`, `runs`, `offs`, `ns` once
  per chunk of 100k pairs. `alignPairs` is a pure function of the ByteArray, so it cannot cache across calls; the
  fix is to stop copying: `MzIdx` / `PGen` read their byte fields as views (base ByteArray + offset, reads via
  `uget` at `off + i`) into the saved bytes, so parsing is O(header) and the multi-GB `extract`s go away. That is
  a layout change (definitions of the index readers + their lemmas), or a csimp on `loadIndex` to a view-based
  `LoadedIndex` if the readers are made generic over the byte source (`GRead`-style). Expected: several GB of
  memcpy + allocation per chunk removed, i.e. ~0.5–2 s per 100k-pair chunk single-threaded on hg38, plus peak
  memory (index held twice during a chunk). **Likely the largest whole-genome item; rank first for hg38 runs.**
  The synthetic `whole_genome pmap` bench does not go through `loadIndex`, so measure it with the Spec shim
  (`map INDEX R1 R2 OUT MIN MAX`) on chr21 / hg38.
- **N1. Allocation + refcount (13.5% self) and list building (~6%).** `mi_free` / `lean_dec_ref_cold` /
  `mi_malloc_small` / `lean_del_core`; `List.range` (rescoreRuns 1.7%, shapes, ilGFG), `lean_list_to_array` → 
  `List.toArrayAux` + `lengthTR` (4.3% inclusive, 4,727 calls), `properPairs` filter, `mergeSort` (1.3%).
  How: replace `List.range n |>.toArray |>.map f` by `Array.ofFn`/a USize fill loop; build `Array`s directly
  where a `List` is only converted; csimp per definition. Effect 3–8%. Risk low–medium (many small proofs).
- **N2. `rescoreRuns` (15% inclusive in RTX; check prod).** Converts read and window to `Array Char` through
  `List.range` + `Char.ofNat` on every check, then `checkRuns` on `Array Char` (`checkRepeatFast` 2.4% self, 1.5%
  of `lean_dec_ref_cold`). How: `checkRunsB` on `ByteArray` with USize positions, csimp `rescoreRuns =
  rescoreRunsB` (equality through `Char.ofNat (b.toNat)` injective on bytes). Effect: up to ~10% in RTX mode;
  0 if production never calls `chkCand` (no heuristic, no ceilings). Risk medium.
- **N3. `packRP` per mate** (`packLoopU` 5.0% prod: `packRPU` twice per mate in `tierPairBS` — forward and
  reverse complement — plus `pairGQC`/`hitsAtQ`; 3.3× per mate in RTX). The loop is already USize (`packLoopU`);
  the cost is ~21 Ir/letter (`codeTab.get!`, `push`, a Nat test per letter). How: (a) pack the reverse complement
  from the forward words (complement = `x ^^^ 0xFFFF…`, reverse the 2-bit fields) instead of re-reading bytes,
  proved against `packRP (revCompB R)`; (b) thread one `K` per strand through `tierPairBS` (signature change,
  hypothesis `K = packRP R`). Effect 2–4%. Risk medium.
- **N4. Per-read seeding — DONE for the loops:** `seedLE` (5.8% prod; ~1,900 Ir per 25-letter seed) → `seedLEU`
  (−51%), `revCompLoop` (2.9%) → `revCompLoopU` (−17%; the `push` stays: 1.9%), `Mz.miniGo` (5.6%) → `miniGoU`.
  Remaining: `miniGo` is computed in four `Array.mapM` specialisations of `kpKer` (24,000 calls each per 2,000
  pairs) — check whether the same minimizers are recomputed per pass/strand and share them (needs signature
  changes); `revCompLoop` could fill a preallocated array (`uset`) instead of `push` (equality via `ByteArray.ext`).
- **N5. Byte kernels on the packed genome: `fwdMis`/`bwdMis` @gappedPen2Pk 4.9%, `hamming` @ilG 1.5%.** Generic
  over `[GRead Gt]`; the csimp must be on the generic definition, so the fast form has to be generic too (USize
  index, `GRead.get` stays) or the csimp goes on the specialised caller (`gappedPen2Pk`). Effect 3–5%. Risk medium.
- **N6. Closures in the router (`passGSF`: 15 closure ops, 18 allocations; `tierPairBS` lambdas).** Rowan's
  "data, not closures" idea: an explicit state machine, proved equal. Effect 1–5% (unmeasured). Risk high (big).
- **N7. Bench-only, no proofs needed:** `heurP`'s `bandCells` (6.9%) and `hamD` (`for i in [a:b]` over Nat,
  3.2%) — untrusted helpers, rewrite freely (only matters if RTX keeps the heuristic); `hashRange` at index load
  (72% of the whole run's instructions, ~1 s per pmap run) and read parsing (`hasNL`/`allAcgt`/`codes64`) — load
  time only.
- **N9. Nat literals ≥ 2^32 in compiled code are rebuilt on every evaluation** (`lean_cstr_to_nat` → GMP string
  parsing): found because `revCompLoopF`'s first bound `i < 4294967296` cost ~3.5 M Ir (now `1073741824`). Still
  present per call in `pscanD` (2^62, PairGuarQ) and in `checkRunsFast3Go` / `diagMisFast3` (2^32,
  AlignmentCigarCheckFast). Literals in closed terms (`_init_…`) are fine. Check:
  `grep -n 'lean_cstr_to_nat(' .lake/build/ir/*.c`. Fix: a smaller literal or a hoisted constant (definitions only).
- **N8. Wrapper cost of K1** (`hamWF` 1.5 M of 6.5 M): hoist the bound test to the window level (see K1).

## 4. Ranking of what is left (expected gain on tierPair; re-rank on chr21 / hg38 before starting)

1. **I1 index views instead of per-chunk copies** — production `alignPairs` path only; seconds per 100k-pair chunk
   on hg38 (GB-scale `extract` + rebuild); biggest whole-genome item; medium risk (index readers).
2. **N1 allocation + list building** — 10.5% (prod) / 13.5% (RTX) self in mi_free/dec_ref/malloc, plus ~3–6% in
   list building; expect 3–8%; many small csimps; low–medium risk.
3. **N5 byte kernels on the packed genome** (`fwdMis`/`bwdMis` pre-scans and gapped fallback, `hamming`) — 9.3% prod;
   expect 4–6%; medium risk (generic `GRead`; csimp on `gappedPen2Pk`/`kerGKG` or a USize getter in `GRead`).
4. **K5 minimizer bucket scans + `scanWF` (`pscanD`)** — 2.2% + 4.8% prod here (`scanWF` does one `cnt64` per
   position, a closure call and Nat `k`/`st`), and the scans grow with repeats; expect 3–5% here, more on hg38;
   medium risk. `scanWF` is also where K4 (popcount) pays most.
5. **N3 pack the reverse complement from the forward words** — 5.0% prod in `packLoopU`; expect 2–4%; medium risk.
Then K6 (`-march`/LTO: no proof cost, try first in a separate build tree), K4 (popcount; with K6), N2 (rescoreRuns:
RTX only), N9 (big literals: trivial), N8, N6, K2.

## 5. Measurements (this box, synthetic data, base = 3f8ca20)

callgrind Ir inside `tierPair`, 2000 pairs (`scripts/ab_ir.sh`), cumulative; every row dumps identical to base:

| variant | prod (`AB_PROD=1`) | RTX |
|---|---|---|
| base | 597.5 M | 1,247.9 M |
| + hamW | 591.2 M (−1.05%) | 1,241.5 M (−0.51%) |
| + fwdW, bwdW | 586.0 M (−1.92%) | 1,232.3 M (−1.25%) |
| + seedLE | 569.5 M (−4.68%) | — |
| + revCompLoop (bound literal 2^32: GMP parsing per call) | 570.1 M (−4.57%) | — |
| + miniGo, revCompLoop bound fixed (final) | **553.5 M (−7.37%)** | **1,187.0 M (−4.87%)** |

Per function (prod, base → final): seedLE 34.6 M → seedLEU 17.0 M + seedLEF 1.1 M; revCompLoop 17.3 M → 14.4 M;
miniGo 33.7 M → miniGoF 20.6 M (miniGoU inlined); hamW 12.8 M → 6.5 M (incl. wrapper); bwdW 8.5 M → 5.7 M;
fwdW 6.6 M → 4.3 M. The remaining GMP string parsing (0.25 M) is `pscanD`'s literal (N9).
Wall/CPU (20k pairs, 7 alternated runs, medians; `scripts/ab_pair.sh`): prod 0.835 → 0.746 s wall (−10.6%),
0.820 → 0.750 s CPU (−8.5%); RTX 1.612 → 1.517 s wall (−5.9%), 1.600 → 1.500 s CPU (−6.2%).
Not measured here: chr21 / hg38 (the box has no reference genome), `-march` / LTO, multi-thread runs.
