# n36: HiSeq CPU, what each listed item is worth (branch `speed/n36`, 2026-11-02)

Base 34832e7 (n35 merged). HiSeq = hg002 2×250, first 2000 pairs; Ir = callgrind of the shim, index load
included: **1681.4M** (NovaSeq 958.6M). Goal: HiSeq 4x vs minibwa (3.56x now), i.e. ~11% less HiSeq CPU.
No code change is kept on this branch: each listed item was measured or prototyped first and is worth ≤ 1.5%.

## 1. The items, measured
| item | HiSeq share | finding | expected gain |
|---|---|---|---|
| `twoGapCABG`'s letter `hamming` in `ker16KWG` | 3.5% (136k calls, ~440 Ir each) | the letter loop stops at the first mismatch (~8 letters on average); a word version must start mid-read (`[A + 1, B − 1)`, masked first word) and read one letter left of the window `wordOk` flagged (`st − 1`), and `ker16KWG` has no `Rep gbs[c] pvs[c]` (that hypothesis lives in `ker16KW_eq`), so it needs the change in both `ker16KW` and `ker16KWG` plus a range lemma for `hamW` | ~1.5% |
| `ReadTrim.wlU` | 3.4% | already tight: 57 instructions per letter, no calls (instruction profile) | ~0 |
| `alignAt`'s DP (`bandCellsJ`, main path) | 3.1% (97 calls, ~530k Ir each; plus 5.1% from the fallback's `nearY`) | prototype `bandCellsJX` (machine-word `uget` / `uset`, the row's read letter carried; differential test equal, SAM identical): `bandCellsJ` 88.8M → 84.6M, total −0.25%. The ~150–190 Ir per cell is the compiled loop itself (19 live arguments), not the accesses; `bandCellsJ` is now proved (`BandCellsJProof.lean`), so a variant needs its own `_eq` | ≤ 0.3% (not kept) |
| `kerGKG`'s gapped path (k250) | 12.9% inclusive; self 91.6M = 5.4% | per gapped call ~300 Ir of `Nat` glue around two 8-letter prescans (`pre = 8`; `fwdMisF` / `bwdMisF` re-check their guards and `GRead.ok` each time) and ~700 Ir of setup on the 37k word-path calls (`lean_nat_shiftr` / `lean_nat_mod`, `flagsOkU`). Hoisting the guards: ~1%; the full `USize` rewrite of `gappedLG` / `fwdLG` / `bwdLG`: maybe ~3% | 1–3% |
Together these are at most ~5% of HiSeq, for two large proofs (the range word kernel and the gapped-path rewrite).

## 2. The larger levers for HiSeq (outside this round's scope)
- **The frozen shim** (SAM / FASTQ text): the n33 proposal (N33_CPU.md §4: `reverseMapBytes` `@[specialize]`,
  `takeWhile` names, `USize` `findNewline`) measured on HiSeq here, applied locally and reverted:
  **1681.4M → 1591.1M (−5.4%)**, SAM identical. Keeping quality / SEQ / QUAL as bytes (no UTF-8 validation:
  `validate_utf8` + `utf8_strlen` ≈ 95M on HiSeq) would add about another 5%. That alone is about the 11%.
- **`fallbackOf`** 9.2% of HiSeq (S-B's rewrite; N35_CPU.md §3 lists ~2% of shared preparation to pass in).

## 3. Recommendation
For 4x on HiSeq, apply the shim changes (Rowan's files) first: −5.4% measured, ~−10% with byte quality strings.
After that, the k250 gapped-path rewrite (1–3%) is the best non-frozen item; the `twoGapCABG` range kernel (~1.5%)
next. `wlU` and the DP's per-cell cost are not worth more work.
