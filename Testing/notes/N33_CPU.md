# n33: NovaSeq CPU (branch `speed/n33-cpu`, 2026-11-02)

Base: `claude/festive-fermi-mf9mo6` e384063 (n32 kernels merged). hg38 release (`bench-release`), 4 cores, 15.7 GB.
Ir = callgrind instructions of the shim (`lean-align map shim.idx R1 R2 out.sam 100 1000`) on the first 2000
pairs, index load included (base NovaSeq 1142.2M = N32 §5's 8bed788 figure). Every change: SAM byte-identical to
base on the 2000-pair subsets of NovaSeq, mason, low, HiSeq (hg002) and on all four full 200k sets;
`CI_check.sh` passes; no Spec/, Main.lean or Spec/Shim.lean edits; no new axioms, no sorry / native_decide /
implemented_by / extern / unsafe / partial.

## 1. Changes (NovaSeq Ir, 2000 pairs)
| commit | change | NovaSeq Ir | step |
|---|---|---|---|
| e384063 | base | 1142.2M | |
| cdf36f5 | `winL` (`winL_eq_winLF`, `@[csimp]`): letters read by `rawU` at a hoisted `USize` offset, no `i < G.n` test per letter (`winLgU_eq`) | | |
| cdf36f5 | `TierHeur.hamP` (`hamP_eq`: `= hamming`): the k250 word kernel `hamA` (32 letters per step) when the read packs and the window's blocks are all flagged, else the letter loop; used by `hamD` and `Report.diagPenH` (`chkCandD`) | 1103.1M | −3.4% |
| cdf36f5 | `bandDP` runs `bandCellsJ`: each row starts at its first live diagonal (`rowStart`) and ends at the first cell after which `bandCells` skips the rest of the row | 1091.6M | −1.0% |
| 9ecc2ad | `zerosB` (`zerosB_eq`: `= ⟨Array.replicate n 0⟩`, by doubling `memcpy`) for `bandDP`'s traceback bytes and `voteD`'s votes | 1084.1M | −0.7% |
Total NovaSeq −5.1% (1142.2M → 1084.1M); mason 1618.9M → 1585.5M (−2.1%).

Per function (inclusive Ir, base → head): `hammingU` self 55.6M → 4.3M (`chkCandD` 32.2M → 12.3M, `hamD` 20.8M →
8.8M; what is left of both is mostly `packRPU`, the read packing per call); `winL` 33.0M → 25.9M (`push` per letter
remains); `bandCells` 75.0M → 63.4M.

`bandCellsJ` is not proved equal to `bandCells`. Argument: cells are visited in the same order and the
skipped ones write nothing; a skip for `col < 0` or `k + 1 < pa` can only happen before `rowStart` (the column grows
with `k`), and after a skip for `col > m` or (`k ≥ pb`, `hl`, `e ≥ lim`) every later cell of the row is skipped too
(`hl`, `e` become `INF = 2^24 > lim ≤ 2^23`). `bandCells`' fuel `n (K + 1)` is exactly rows `1 … n`, which
`bandCellsJ` stops after by `i == n`. Checked: `Testing/benches/BandCellsAB.lean` (`lake build bandcells_ab`)
compares `bandDPg true` and `bandDPg false` (the full result: start, length, penalty, runs) on 1,000,000 random
cases (reads 0–179 letters with 1% N, windows with substitutions / insertions / deletions and random flanks, `w`
0–19, `lim` from 0 to 9·10^6): all equal. Then SAM identical on all sets.

## 2. Tried and dropped
- `bandCells` split into a row loop and a cell loop with the row constants (read letter, `(i − 1) K`, column base,
  row end) hoisted: no gain (63.7M vs 63.4M). Both loops cost ~150–190 Ir per computed cell (19 live loop
  arguments: spills, `Array UInt32` exclusivity / bounds checks); little is pruned, because the fallback's
  `nearY` calls run with `lim` = the gapless penalty (often hundreds).
- `getU32F` (`CsrIndex.lean`) fast path for indices ≥ 2^29 (the hg38 index takes `getU32S`, 1.9% self): inside
  `getU32F` it grew the inlined body and changed specialization of its callers (+2.4% Ir: new closures in
  `mzLookSP`, `rawLook`, `lookupPPR`); out of line (`@[noinline] getU32B`) it saves only 1.1M (−0.1%: `get!` on a
  scalar `Nat` is a bounds check, not much slower). Reverted.

## 3. What is left (NovaSeq, head, inclusive Ir of 1084.1M)
- **SAM text 14.2%** (`mappedLine`: `samSequence` 8.8% = two `reverseMapBytes` + UTF-8 checks, `samName` 2.6%),
  **FASTQ reading 5.3%** (`FastqReader.line` 3.0%, `String.fromUTF8!` 2.1%): frozen; proposal in §4.
- **Report's fallback `fallbackOf` 16.7%** for 315 of 2000 pairs (`tryAt` 427×, each `nearOf` → `nearY`: `bandDP`
  6.2%, `winL` 2.4%, `voteD` 2.6%). Its search order is the result, so it stays; the DP's per-cell cost is the
  lever (above).
- **`capFor` 8.4%** (Proofs/Aligner.lean): a full `prepMate` per mate (seed kernels 30M, `costPK` 28M, packing 15M,
  reverse complement 7M) only to pick the cap. The router does not reuse it. The read packing (`packRPU`, 36.6M
  over 20k calls) and reverse complement (`rcSetU`, 21.3M over 12.7k calls) run ~3× per mate (capFor, `tierPairBS`,
  `checkMoveD` / `hamP`); sharing them means threading a prepared read through `pairCfg`, `tierPair` and
  `answerOfPair` (proved interfaces) — not done.
- `Report.chromGoU` 1.7%: a linear scan of 195 chromosomes per `moveTo` (4097 calls); a binary search needs a
  checked "offsets sorted and disjoint" fact to keep "none when several hold it".
- `ReadTrim.wlU` 3.2% (trimmer, ~57 Ir per letter), refcount/free of the `PrepM` arrays and boxed
  `Array UInt32` (bandDP's `H`/`F` frees walk every element): spread out, no single site above 1%.

## 4. Proposed shim diff for Rowan (frozen: NOT applied)
Measured locally on `Proofs/Sam.lean` / `Proofs/Fastq.lean` (the files `Main.lean` runs), then reverted:
NovaSeq 2000 pairs **1084.1M → 1008.8M (−6.9%)**, SAM byte-identical.
- `reverseMapBytes` `@[specialize]`: `f` (`complementByte` / `id`) was a closure called per byte
  (`lean_apply_1` 25.7M, loop 34.3M) → 30.2M. A `USize` / `uget` loop would cut it further.
- `samName` / `mateName`: `name.takeWhile (· != ' ')` instead of `(name.splitOn " ").headD _` (same string: the
  part before the first space; `splitOn` with a non-empty separator always has a first piece) → −25.7M net.
  `takeWhile` still walks characters (`skipWhile` 23.4M); a byte scan of `name.toUTF8` would be cheaper.
- `findNewline`: `USize` loop with `uget` (22.3M → 7.8M). The rewrite below is not proved equal to the `while`
  loop; it needs a lemma if the file must stay proof-equal.
- Not prototyped: keeping `FastqRecord.quality` (and SEQ / QUAL in SAM lines) as bytes would skip UTF-8
  validation and length counting (`validate_utf8` 42.3M + `utf8_strlen` 18.7M from `fromUTF8!` ≈ 5.6%); that is a
  type change in Spec.
```diff
--- a/Proofs/Fastq.lean
+++ b/Proofs/Fastq.lean
 -- the first newline byte at or after `i` (or `bytes.size` when there is none)
-def findNewline (bytes : ByteArray) (i : Nat) : Nat := Id.run do
+theorem usize_le' (a : ByteArray) : a.usize.toNat ≤ a.size := by
+  show a.size.toUSize.toNat ≤ a.size
+  rw [Nat.toUSize_eq, USize.toNat_ofNat']; exact Nat.mod_le _ _
+
+def findNewlineU (bytes : @& ByteArray) (j : USize) : USize :=
+  if h : j < bytes.usize then
+    if bytes.uget j (Nat.lt_of_lt_of_le h (usize_le' bytes)) != 10 then findNewlineU bytes (j + 1) else j
+  else j
+termination_by bytes.usize.toNat - j.toNat
+decreasing_by
+  have h' : j.toNat < bytes.usize.toNat := h
+  have := USize.toNat_lt_size bytes.usize
+  have hs : USize.size = 2 ^ System.Platform.numBits := rfl
+  rw [USize.toNat_add, USize.toNat_one, Nat.mod_eq_of_lt (by omega)]; omega
+
+def findNewline (bytes : ByteArray) (i : Nat) : Nat :=
+  if i < bytes.size ∧ bytes.size < 4294967295 then (findNewlineU bytes i.toUSize).toNat else Id.run do
   let mut j := i
   while j < bytes.size && bytes[j]! != 10 do
     j := j + 1
@@ def mateName (name : String) : String :=
-  let base := (name.splitOn " ").headD ""
+  let base := (name.takeWhile (· != ' ')).toString
--- a/Proofs/Sam.lean
+++ b/Proofs/Sam.lean
@@ def samName (name : String) : String :=
-  let name := (name.splitOn " ").headD name
+  let name := (name.takeWhile (· != ' ')).toString
@@
-def reverseMapBytes (f : UInt8 → UInt8) (bytes : ByteArray) : ByteArray := Id.run do
+@[specialize] def reverseMapBytes (f : UInt8 → UInt8) (bytes : ByteArray) : ByteArray := Id.run do
```
(The same edits apply to `Spec/Fastq.lean` / `Spec/Sam.lean` if those must stay identical copies.)

## 5. Timing (NovaSeq 200k, CPU of the map part)
4 threads (`taskset -c 0-3`), per binary: one warm-up empty-FASTQ run, then 6 × (empty run, full run); CPU =
(user + sys)(full) − (user + sys)(empty right before). Binaries timed one after the other, nothing else on the box.
| binary | map CPU s, runs 1–6 | median |
|---|---|---|
| base e384063 | 21.0, 22.7, 22.0, 19.7, 21.8, 21.3 | 21.55 |
| head 9ecc2ad | 23.8, 21.1, 20.3, 18.7, 25.2, 24.4 | 22.45 |
The −5.1% Ir is inside this box's run-to-run spread (head 18.7–25.2 s; N32 §5 saw ±20%), so the CPU medians do not
resolve it; Ir is the measure for these changes.

**minibwa was not re-timed here**: building minibwa c07de5c from github.com/lh3/minibwa was refused by this
session's permission policy (external code). With N32 §5's minibwa figure from the same box type and method
(55.5 s, not this session): **minibwa 55.5 s / ours 22.45 s = 2.47x** (base: 55.5 / 21.55 = 2.58x). The 2x goal
holds either way; a same-session minibwa run is still owed.
