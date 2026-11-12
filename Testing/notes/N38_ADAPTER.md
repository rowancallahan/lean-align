# n38: bit-parallel adapter cut (branch `speed/n38`, 2026-11-03)

Base 562a2f5 (adapter trimming merged): HiSeq (hg002 2×250) 1359.0M, NovaSeq 985.5M (callgrind Ir of the shim,
first 2000 pairs, index load included). There the adapter cut (`AdapterTrim.scanU` + `mmU`, already `USize` loops)
was the largest non-frozen item: HiSeq 103.5M (7.6%), NovaSeq 62.1M (6.3%), ~100 Ir per read position (a two-letter
skip test, then the mismatch loop on ~44% of positions).

Checks: SAM byte-identical to base on the 2000-pair subsets of NovaSeq, mason, low, HiSeq and on the four full 200k
sets; `CI_check.sh` passes; no Spec/, Main.lean, Shim or `fallbackOf` edits; no sorry / native_decide /
implemented_by / extern / unsafe / partial. `cutPos` and every `cut_*` theorem are unchanged; only `cutPosF` (what
`@[csimp] cutPos_eq_cutPosF` compiles `cutPos` to) gained a path.

## 1. The scan
Shift-and with at most one substitution, over the adapter's `m` letters (`m ≤ 63`, here TruSeq's 13):
- `st0 p` / `st1 p`: bit `t` set iff the `t + 1` read letters ending at letter `p − 1` are the adapter's first `t + 1`
  letters with no mismatch / at most one (`st0_bit`, `st1_bit`); one step per read letter from the letter's mask
  (`bmask`: bits `j` with `adapter[j] = c`).
- A start `s` with the whole adapter before the read's end matches iff bit `m − 1` is set after `s + m` letters
  (`st0` for `maxErr = 0`, `st1` for `maxErr = 1`); a start nearer the end (a prefix of the adapter, no mismatch)
  iff bit `n − s − 1` of the final exact state is (`saT`, `fastMatchesAt_saT`).
- `saLoop` keeps both states and tests start `p + 1 − m` as soon as its state is known; the starts near the end are
  tested on the final state (`saLoop_eq`; `cutPos_eq_sa`: `cutPos = saLoop …`).
- `saLoopU`: the same on `UInt64` states with the read index in `USize` and the letter mask from four masks (`bOf`;
  any other byte has mask 0 because the adapter is checked to be all `A C G T`, `acgtAll`) (`saLoopU_eq`,
  `saCutU_eq`). `cutPosF` takes it for an `A C G T` adapter of 1–63 letters, `maxErr ≤ 1`, reads below `2^30`; else
  the previous `USize` scan (`cutPosW`, `cutPosW_eq`).

## 2. Measurements
| step | HiSeq | NovaSeq |
|---|---|---|
| base 562a2f5 | 1359.0M | 985.5M |
| shift-and, masks by `Nat` `2^j` | 1384.9M (+1.9%) | 1035.4M |
| masks by `UInt64` shifts (`bmaskU_eq`, `pow_sub_one_u64`) | 1327.9M (−2.3%) | 978.9M (−0.7%) |
| `cutAdapter` / `cutPosF` / `saCutU` `@[inline]`: `cutTruSeq`'s masks become closed terms, computed once | **1309.4M (−3.6%)** | **960.5M (−2.5%)** |
The adapter scan: 103.5M → 44.4M on HiSeq (`saLoopU`, ~44 instructions per letter, against ~100 per position before).
Pitfall: `Nat` `2^j` goes through GMP (`__gmpz_n_pow_ui`, malloc / free) at every call, even for small `j`.

## 3. Left (HiSeq self Ir at the head)
`bandCellsJ` 4.7% (fallback / `alignAt`), `wlU` 4.3% (tight), `saLoopU` 3.4%, the frozen shim (`reverseMapBytes`,
`findNewline`, UTF-8: ~15%, see `shim_speed.patch`), router kernels (`svAnyU`, `scanAWF`, `stageKSPN`, `ker16KWG`,
`hamWU` ~2% each), seed preparation `prepLoop` 2.6%.
