# Machine-code comparison and hot-loop rewrites (box O4, 2026-11-02)

Branch `speed/n31-dedup-heur` on `claude/festive-fermi-mf9mo6` 2b496d6 (+ the dedup commits). hg38 release, 4 cores
(Firecracker VM, 15.7 GB). Ir = callgrind instructions on the shim (`lean-align map`), 2000 hg38 mason pairs, load
included (an empty-FASTQ run costs 13.8M Ir). CPU time on this box varies ±10–12% run to run (single core too), so
Ir is the A/B measure for code changes; timings are median of 3.

## 1. Compiler flags
Lake compiles our C with Lean's bundled clang at `-O3 -DNDEBUG` (no `-march`). A local build with
`moreLeancArgs := #["-march=native"]` (not committed) uses AVX registers far more (1426 vs 309 `ymm/zmm` uses)
but gives **0–4% user CPU, inside the noise** (table 3), SAM identical on all 5 sets. The Lean runtime
(`libleanrt`, allocator, `lean_nat_*` slow paths) is prebuilt and unaffected.

## 2. Where the instructions go (lean.h lines inlined into our code, % of all Ir)
| lean.h helper | % Ir | meaning |
|---|---|---|
| `lean_unbox` / `lean_box` | 6.0 / 5.7 | boxed `Nat` (and `Nat`-typed fields) moved in and out of registers |
| small-nat overflow / scalar tests in `lean_nat_add/sub/mul/dec_lt/eq` | ~13 | every `Nat` operation checks both operands are scalars and the result fits 63 bits |
| `lean_nat_mul` overflow (`r / n1 == n2`) | 3.5 | `Nat` multiplications (e.g. `sw * t`, `17 * (u / 2)`) |
| `lean_dec` / `lean_dec_ref_cold` | 2.0 / 1.5 | reference counts of boxed values and structures |
In all, **boxed `Nat` arithmetic is ~25–30% of the instructions**; a hand-written C loop would use plain registers.
Byte reads are fine: clang merges the 8 `lean_byte_array_uget` + shift + or of a 64-bit genome word into one
`mov` (2 `movzbl` left in the 10k-instruction `stageKSPN`). The kernels' 32-letter word compares (64-bit lanes) are
the same idea as minibwa's packed compares; minibwa's SSE/AVX2 striped extension (ksw) has no Lean counterpart —
Lean emits no vector intrinsics, and clang auto-vectorizes none of our loops (they are branchy recursions).

Machine code of the hot functions (`objdump`, our binary): calls to `lean_nat_*`/`lean_big_*` slow paths,
`lean_dec_ref_cold`, other calls:
| function (Ir share) | instructions | nat/big calls | dec_ref | other calls |
|---|---|---|---|---|
| `stageKSPN…spec__23` (9.6%) | 10081 | 359 (95 add, 92 usize→nat, 80 mul) | 304 | 32 gwordS, 7 seedBoundE |
| `scanAWK3` (9.5%) | 3643 | 176 | 99 | 22 |
| `kerGKG` (6.3%) | 12574 | 568 | 348 | 101 |
| `ker16KWG` (3.3%) | 4567 | 155 | 121 | 44 |
| `fineE` (2.3%) | 1975 | 101 | 57 | 7 |
| `unlookV` (1.9%) | 1501 | 74 | 35 | 6 |
| `rdSlot` (1.3%) | 970 | 49 | 29 | 0 |
| `svAnyU`, `fwdMisU`, `bwdMisU`, `sweepA` | 340–362 | 2–12 | 3–9 | 0–4 |
The `…U` loops from n28 (`svAnyU`, `fwdMisU`, `bwdMisU`) are already close to C; the rest is `Nat`.

## 3. Implemented (all `@[csimp]` with proofs; SAM byte-identical on 20k NovaSeq + 20k mason and on all 5 full sets)
| commit | change | Ir (2000 mason pairs) |
|---|---|---|
| 8857181 | `lanesAnyV`: `lowF`'s mask computed once (`lowM`, `lowF_eqM`), lane count in `USize` | 3.7675G → 3.7211G (−1.2%) |
| a77217a | `stageKSPN`: `gapBound sc0 (−Q) = (Q − 6)/2` (`gb0`, two `Int` calls per diagonal gone) and `acc.length` once per stage | 3.7211G → 3.6216G (−2.7%) |
| 052080d | `scanAWK3`: a matching entry's slot read once (test + anchor); `rdSlot` calls 883k → 546k | 3.6216G → 3.5827G (−1.1%) |
| total | | **3.7628G → 3.5827G (−4.8%)** |

Before/after C, `lanesAnyU` (per step): `lean_nat_dec_eq(k, 0)`, `lean_nat_sub(k, 1)`, `lean_dec(k)`, and in
`lowF` `lean_nat_dec_lt(c, 32)` + `lean_nat_mul(2, c)` + `lean_uint64_of_nat`; after (`lanesAnyV`): `k == 0`,
`k - 1` on `size_t`, one `&` with the precomputed mask. `stageKSP` per diagonal: two calls of `gapBound`
(`lean_nat_to_int`, `lean_int_neg`, `lean_int_div`, `Int.toNat`, ~105 Ir each) and `List.lengthTR` (72 Ir); after:
`(Q - 6) / 2` on a scalar `Nat`, length passed in.

Tried and dropped: `nextK` (the key scan) on `USize` with unchecked reads (`nextKU`, proved): neutral, because
`nextK` skips few entries on hg38 (546k matches, the key scan is short) and its per-call guard costs what the loop
saves. Kept in the notes only. Found on the way: a `Nat` literal ≥ 2^32 inside a function body is rebuilt from its
decimal digits at every call (`lean_cstr_to_nat` → `__gmpz_init_set_str`); hoist such literals into `@[noinline]`
constants. Present today in `diagMisFast3`, `checkRunsFast3Go` (cigar checks) and `pscanD`.

## 4. Speed vs minibwa (hg38, 4 cores, median of 3; map = wall − index load, FASTQ read + SAM write included)
ours: current branch (default flags) and the same code with `-march=native`; ours' load = pooled median of the
empty-FASTQ runs (2.7 s); minibwa's = its `index loaded` time per run.
| set | ours default map / wall / CPU s | ours native | minibwa default | minibwa native |
|---|---|---|---|---|
| HiSeq 200k | 6.8 / 9.5 / 21.3 | 11.3 / 14.0 / 25.6 | 30.3 / 57.5 / 136.3 | 28.7 / 48.6 / 124.0 |
| NovaSeq 200k | 12.8 / 15.5 / 34.8 | 9.5 / 12.2 / 30.5 | 15.7 / 31.7 / 70.1 | 15.8 / 37.8 / 78.3 |
| sim mason 200k | 18.0 / 20.7 / 53.6 | 14.4 / 17.1 / 47.6 | 16.7 / 28.3 / 70.4 | 16.8 / 35.8 / 75.6 |
| sim low 200k | 11.5 / 14.2 / 28.0 | 11.0 / 13.7 / 29.2 | 10.8 / 22.4 / 49.6 | 11.5 / 21.9 / 49.2 |
| HiSeq 1M | 40.6 / 43.3 / 104.8 | 39.0 / 41.7 / 97.8 | 129.6 / 155.5 / 525.7 | 129.3 / 161.3 / 531.1 |
User CPU, ours default vs native: 15.8/15.8, 24.9/23.8, 43.1/42.1, 18.6/18.6, 79.7/80.2 s — native is noise-level.
- HiSeq 200k: minibwa 30.3 s / ours 6.8 s = **4.44x** (native builds: 28.7 / 11.3 = 2.53x; ours' native wall is an outlier, its user CPU is identical)
- NovaSeq: minibwa 15.7 s / ours 12.8 s = **1.23x** (native: 15.8 / 9.5 = 1.66x)
- sim mason: minibwa 16.7 s / ours 18.0 s = **0.93x** (native: 16.8 / 14.4 = 1.17x)
- sim low: minibwa 10.8 s / ours 11.5 s = **0.94x** (native: 11.5 / 11.0 = 1.04x)
- HiSeq 1M: minibwa 129.6 s / ours 40.6 s = **3.19x** (native: 129.3 / 39.0 = 3.32x)
CPU: ours uses 1.3–5x less CPU than minibwa on every set (e.g. mason 53.6 vs 70.4 s, HiSeq 1M 104.8 vs 525.7 s).
(Head's per-task setup, `parMapS`, roughly halved the shim's CPU since the 11-02 morning table: HiSeq 1M user 130 → 80 s.)

## 5. Ranked next fixes (estimated from the profile; all as proved csimp rewrites)
1. **`scanAWK3` / `okAtWE` on machine words** (9.5% self + `rdSlot` 1.7% + `nextK` 1%): per matching entry ~630 Ir
   of `Nat` field math (`posOf`, `tagOf`, `befF`/`aftF`, `pos − o`, `gW`, `winOk`). One guard per lookup (64-bit
   platform, every field < 2^62 — a `@[noinline]` constant, see §3), then `UInt64` slot fields and a `USize` genome
   offset. Est. **−6 to −8% Ir**. `nextKU`/`slotWU` (proved, kept aside) give the unchecked slot read.
2. **`stageKSPN` window math on `USize`** (9.6%): `wordWin`, `a = P.o + (D − n − r)`, `a % 32`, `a / 32`, `loadG`'s
   bounds, `unlookV`/`fineE` arguments are boxed `Nat` per diagonal (95 adds, 80 muls, 92 usize→nat boxings in
   the machine code). Est. **−4 to −5%**.
3. **`kerGKG` / `ker16KWG` dispatch** (6.3% + 3.3%): `st`, `len`, `lim`, `P.o + st`, `lim / 4` in `Nat`; 568 slow-path
   call sites. Est. **−3 to −4%**.
4. **`fineE`, `unlookV`, `sweepA`** (2.3 + 1.9 + 2.2%): `Nat` counters and accumulators (`lc F` sums) → `USize`.
   Est. **−2 to −3%**.
5. **`GW` word window**: `GW.getU` is a 16-way branch tree on struct fields (~5 compares per read, two reads per
   lane step). A `ByteArray` window read with merged 8-byte loads is one load. Est. **−1 to −2%**.
6. **`cnt64U`'s `% 255`** → multiply-shift (`(b * 0x0101010101010101) >>> 56`). Est. < 0.5%.
7. **Per-call decimal literals** (§3) in `diagMisFast3`, `checkRunsFast3Go`, `pscanD`: hoist. Small unless those run hot.
8. **Reference counting** (`lean_dec_ref_cold` 1.5%, 99–348 `dec_ref` sites in the hot functions): borrowed `@&`
   parameters on read-only arrays in the recursive helpers.
Items 1–4 together: est. −15 to −20% Ir. Whether Ir turns into CPU here is uncertain: on hg38 the bucket scans and
genome reads miss cache, and the GMP fix's −20% Ir (11-02) did not show beyond the CPU noise on this box.

## 6. Port onto 88bde0a (branch `speed/n31-asm`, merged into `speed/n31-dedup-heur`)
`speed/n31-asm` = 88bde0a + 5c49eb4 (`lanesAnyV`) + 7323fd2 (`stageKSPN`). This branch's `scanAWK3` (052080d) is
superseded by S1's `scanAWK3`/`scanAWF`/`fastOkW` on head (machine-word test, slot read once, one guard per lookup:
item 1 of §5) and is not ported. The dedup (`alignPairsD`, ebd4a47 + 12325f5) does not fit head's new
`alignOneC (setup)` signature and is off the `alignPairs` path after the merge (kept in history).
callgrind on 2000 pairs vs 88bde0a, SAM byte-identical, CI_check passes:
| set | 88bde0a | + lanesAnyV + stageKSPN | change |
|---|---|---|---|
| hg38 mason | 3.7821G | 3.6415G | −3.7% |
| HiSeq HG002 | 2.0318G | 2.0113G | −1.0% |

## 7. Item 2: the per-diagonal window load on machine words (`loadGU`, csimp `loadG_eqU`)
`loadG` built the 16 genome words of each diagonal's window with a boxed `i < k` test and `gword`'s
`17·(u/2) + 1 + 8·(u%2)` in `Nat` per word. `loadGU` checks once that `u0 + 16 < 2^28` and `k < 2^28`, then reads
each word with the existing proved `gwordU` (`USize` offsets, one bounds check per word); otherwise `loadG`.
`ldwU_eq` + `gwordU_eq` prove it equal. SAM byte-identical (2000 mason + 2000 HiSeq vs 88bde0a); CI_check passes.
| set | 88bde0a | + lanesAnyV + stageKSPN | + loadGU | total vs 88bde0a |
|---|---|---|---|---|
| hg38 mason | 3.7821G | 3.6415G | 3.4696G | −8.3% |
| HiSeq HG002 | 2.0318G | 2.0113G | 1.9737G | −2.9% |
The rest of the per-diagonal `Nat` math (`wordWin`, `a = P.o + (D − n − r)`, `% 32`, `/ 32`) is a few operations per
diagonal and was left as is.
