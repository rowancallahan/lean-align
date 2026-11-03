# HiSeq profile and the unlooked-seed scan (festive 71796ac, new-format index), 2026-11-03

Callgrind, first 2000 pairs, whole run: HiSeq 1412.0M, NovaSeq 1211.0M.

HiSeq by stage (inclusive): router `tierPairBP` 481M (`routeGS` 438M, 31%); SAM `samLines` 200M; FASTQ `readChunk`
197M (`trimRecord` 145M: `ReadTrim.wlU` 56M + `AdapterTrim.saLoopU` 44M self); `answerOfPairP` 139M; `prepLoop` 36M;
`orElse` 73M (`lookAt` 52M).
Top self: wlU 56M, reverseMapBytes 52M (SAM), bandCellsJ 49M, saLoopU 44M, scanAWF 37M, prepLoop 34M, findNewline 33M,
UTF-8 validate + strlen ~96M (SAM), svAnyU 32M, ker16KWG 29M, stageKSPN 29M, hamWU 26M, kerGKG 23M, nextK 19M,
unlookV 18M.

SEARCH_IDEAS #6 (longer seeds) targets the last resort's too-heavy repeats; `lookAt` is 52M (3.7%) on HiSeq now, so
its ceiling is small. Not pursued.

The unlooked-seed scan (`unlookV` → `svAny`, in the router's `stageKSPN` filter and the second look): 50M incl. on
HiSeq (about 5 unlooked 25-mer seeds per 2x250 read, each at 2r+1 shifts).
- h1: `fineE` before `unlookV` (exact, `&&` commutes): WORSE (HiSeq +8.5M, NovaSeq +1.2M). Dropped.
- h2, UNPROVED prototype (`hiseq/h2_svAnyR_UNPROVED.patch`, csimp proof is `sorry`): `svAny` on the rolling 2-bit
  window of `lanesAnyR` with a masked 25-field compare. `unlookV` incl. 50.1M → 33.1M; whole run HiSeq 1412.0M →
  1394.6M (−1.2%), NovaSeq 1211.0M → 1206.8M (−0.35%); SAM identical on both 2k subsets. Proof plan: reuse
  `roll_eq` / `RInv` (move them above `svAny_eq_svAnyF`, which must precede `unlookV`).
- Next candidate: `unlookV` recomputes each seed's word `gAt K.w (j * Ls)` per diagonal; hoisting it per read,
  est. −5..8M more on HiSeq.
