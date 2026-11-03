# n35: CPU outside fallbackOf (branch `speed/n35`, 2026-11-02)

Base f2596ba (n34 merged). Same box, measurement and checks as N33_CPU.md / N34_PREP.md: Ir = callgrind of the
shim on the first 2000 pairs (index load included); SAM byte-identical to base on the 2000-pair subsets of
NovaSeq, mason, low, HiSeq and on the four full 200k sets; `CI_check.sh` passes; no Spec/, Main.lean, Shim or
`fallbackOf` edits; no sorry / native_decide / implemented_by / extern / unsafe / partial.

## 1. Profile at f2596ba
NovaSeq 988.8M, HiSeq (hg002, 2×250) 1695.8M. Main path of NovaSeq (inclusive): router `tierPairBP` 29.7% (seed
search kernels behind closures, `routeGS` 25%), reporter 23.5% (of which `fallbackOf` 18.3%, the reported mates'
checks 5.0%), `tierUp` 2.8%, seed preparation 2.5%, `capForZ` 1.1%; trimming `wlU` 3.5%; SAM / FASTQ (frozen)
~20%. HiSeq's top self costs are the k250 kernels (`kerGKG` 5.4%, `ker16KWG` 3.4%, `bwdMisU` / `fwdMisU` 4.9%),
`bandCellsJ` 5.2%, and the letter `hamming` 3.5%, from `twoGapCABG`'s exact-match checks inside `ker16KWG`.

## 2. Changes
| commit | change | NovaSeq Ir | step |
|---|---|---|---|
| f2596ba | base | 988.8M | |
| 25d32d5 | each strand's bucket sizes sorted once (`alignOneP`): `capForS` (`capForS_eq`) tries its caps on the sorted lists (`costZS`, `costZ_eqS`), and the router gets its two pass-1 costs (`tierPairBP.tierPairBQ`; `pairCfgZ_cap`: the router's caps are the ones given, equal reads included) | 979.5M | −0.9% |
| d20b9ca | `exFind` (the packed genome's N-run binary search, 10k calls from `winLgU` on windows touching non-ACGT blocks) on machine words: `exFindU`, `u32W`, `@[csimp] exFind_eq_exFindF`. The guard is `i < 2^32 − 1`: with `2^32` the literal was rebuilt by GMP at every call (+2.4M) | 971.8M | −0.8% |
| ae7a555 | the chromosome lookup of the reported mates stops at the first chromosome that starts after the placement: `Report.monoOk` (offsets non-decreasing) is computed once per chunk (`Aligner.withMono`, the setup now `Setup × Bool`), `chromGoE_eq` (= `chromGo` when the offsets are non-decreasing), `chromOfM_eq`, `moveToM_eq`; `chromGoU` 18.4M → 3.2M (what is left is `fallbackOf`'s) | 959.0M | −1.3% |
Total NovaSeq −3.0% (988.8M → 959.0M); HiSeq 1695.8M → 1681.3M (−0.9%).

`alignPairs_eqC` (csimp) still reaches everything through `alignOneP_eq` (now stated for `setup.map withMono`)
and `alignOneC_eq`; `alignPairs` and its theorems are unchanged.

## 3. Passing the prepared mates into `fallbackOf` (for after S-B's rewrite)
Today `fallbackOf` prepares both mates again (`prepMate` by the generic compiled path: 630 per 2000 NovaSeq pairs)
and its helpers redo what the main path already has. Measured at ae7a555 (NovaSeq, 2000 pairs):
| what | Ir |
|---|---|
| `prepMate` ×2 inside `fallbackOf` (packing 2.2M, seed kernels 4.3M, reverse complement 1.0M, frees ~1.5M) | ~9.2M |
| `anchorsOf` → `hamD` → `hamP`: packing the read per anchor | 5.7M |
| `tryAt` → `mateOf` → `checkMoveD` / `checkMove`: `revCompK` per call | 1.1M |
| `moveTo` → `chromOf` linear scan (`chromGoU`) | 3.2M |
| total | ~19M (≈ 2.0%) |
What it needs (every step an equality theorem, like n34):
1. `fallbackOfP … (ok : Bool) (s1 s2 : PrepM MzP)`: the body with `prepMate pk R1` / `prepMate pk R2` replaced by
   `s1` / `s2`; `fallbackOfP … (monoOk offs ns) (prepMz pk R1) (prepMz pk R2) = fallbackOf …` from `prepMz_eq`.
2. Inside it, `tryAt` → `mateOfK pgs offs ns ok R s.Rr s.K1 s.K2` in place of `mateOf` (`mateOfK_eq` exists), and
   `anchorsOf`'s `hamD R s.Rr pgs b D n` → `hamPK` with `s.K1` / `s.K2` (`hamPK_eq`; `hamD`'s `Rx` is `R` for
   strand 0 and `s.Rr` for strand 1, so `K` is `s.K1` / `s.K2`). `nearOf` already takes `s'`.
3. `answerOfPairP` calls `fallbackOfP … ok s1 s2`; `answerOfPairP_eq` gets one more `rw`.
If S-B's rewrite keeps `prepMate` calls or `mateOf` / `hamD` uses, the same three steps apply to the new code. If it
proves facts about `fallbackOf` itself, those stay as they are (the compiled path changes only through `_eq`).

## 4. Left (not done)
- HiSeq's letter `hamming` from `twoGapCABG` (3.5%): its exact-match checks on read ranges `[A + 1, B − 1)` run
  letter by letter; the word kernels only cover prefixes `[0, stop)`. A range version (count `[0, stop)` minus
  `[0, i)` by `hamA`, or a masked first word) needs the packed read and the `PGen` inside the generic `ker16KWG`.
- `alignAt`'s banded DP (2.3% NovaSeq, 66 calls): the router's gapped placements; ~150–190 Ir per cell (N33).
- `wlU` (3.5% on both): already a `USize` loop (~57 Ir per letter).
- The k250 kernels on HiSeq (`kerGKG` gapped path, `fwdMisU` / `bwdMisU`): the n32 note's `USize` rewrite of
  `gappedLG` / `fwdLG` / `bwdLG`.

## 5. Timing
Not re-timed here (S-B does the same-box minibwa headline).
