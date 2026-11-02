# n34: each mate prepared once (branch `speed/n34-prep`, 2026-11-02)

Base: 83ea523 (n33 merged into festive-fermi). Same box, measurement and checks as N33_CPU.md: Ir = callgrind of
the shim on the first 2000 pairs (index load included); SAM byte-identical to base on the 2000-pair subsets of
NovaSeq, mason, low, HiSeq and on the four full 200k sets; `CI_check.sh` passes; no Spec/, Main.lean, Shim edits;
no sorry / native_decide / implemented_by / extern / unsafe / partial. `fallbackOf` is not touched (S-B is
rewriting it).

## 1. What was done twice or three times per mate
- `capFor` (Proofs/Aligner.lean `pairCfg`, 8.4% of NovaSeq Ir) ran a full `prepMate` per mate (generic code:
  packing, reverse complement, seed kernels) and then its own bucket-size sort, only to pick the cap.
- The router (`tierPairBS`) prepared both mates again (`prepMz`, proved `= prepMate`) and read the bucket sizes.
- The reporter (`answerOfPair` → `mateOf` → `checkMoveD` / `alignAt` / `checkMove`) built `revCompK R` again per
  mate, and `chkCandD`'s word Hamming (`hamP`) packed the read again.

## 2. Changes (NovaSeq Ir, 2000 pairs)
| commit | change | NovaSeq Ir | step |
|---|---|---|---|
| 83ea523 | base | 1084.0M | |
| d99c98d | `alignOneP` (`alignOneP_eq`: `= alignOneC`; `alignPairsC` runs it): each mate prepared once by `prepMz`, its bucket sizes read once; `capForZ` (`capForZ_eq`: `= capFor`, by `costZ_eq`) picks the cap from those sizes; `tierPairBP` (`tierPairB_eqP`: `tierPairB` = `tierPairBP` at `prepMz` and the sizes) is the router taking them | 1003.3M | −7.4% |
| 0e2673b | `Report.answerOfPairP` (`answerOfPairP_eq`: `= answerOfPair` at `prepMz`): the reported mates' checks (`chkCandDK`, `checkMoveDK`, `mateOfK`, `foundOfK`) use the preparation's `Rr`, `K1`, `K2`; `TierHeur.hamPK` (`hamPK_eq`) is `hamP` with the packed read given | 988.6M | −1.5% |
Total NovaSeq −8.8% (1084.0M → 988.6M); mason 1585.7M → 1488.5M (−6.1%).

Every new function is tied to the old one by an equality theorem, and the compiled path reaches them through the
existing `@[csimp] alignPairs_eqC` (its proof now rewrites with `alignOneP_eq` then `alignOneC_eq`), so
`alignPairs` and every statement about it are unchanged.

After this, per mate on the main path: one reverse complement and one packing (in `alignOneP`). The rest of
`rcSetU` / `packRPU` / `prepMate` calls are inside `fallbackOf` (630 `prepMate`s per 2000 pairs, `anchorsOf`'s
`hamD`, `tryAt`'s `mateOf`); the preparation could be passed to it the same way once S-B's rewrite lands
(`fallbackOf` gets `s1 s2` instead of calling `prepMate`).

## 3. Timing
Not re-timed here: S-B has the built minibwa and does the same-box headline. The −8.8% Ir is about the size of
this box's run-to-run CPU spread (N33_CPU.md §5).
