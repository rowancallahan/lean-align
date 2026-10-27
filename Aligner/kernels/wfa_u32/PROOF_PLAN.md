# Proof plan for the fast UInt32 kernel (`wfau`)

**Latest status, 2026-09-11: third-stage block layout DONE.** `wfau3` now has
the complete level, loop, run and public-kernel proofs. `uLevel3_some`
preserves `BWF` and identifies the three extracted fronts exactly;
`uRun3_some` gives the reference optimum; `wfaAlignU3_score`, `_sound`,
`_isSome` and `_score_fun_eq` are universal with standard axioms only.
`sh alignment/checks/check_all.sh` passes, including the 80-theorem U32
certificate and 5766 executable cases with zero U3 certificate rejections.
See [README.md](README.md) for the current proof chain. Status entries below
are historical; the block layout is no longer pending.

Placeholder prose; Rowan rewrites. Status markers: DONE / PARTIAL / TODO.

**Status 2026-09-11 (later): items 1–15 DONE and the second stage DONE except the block layout** — kernel `wfau2` (`wfaAlignU2`, AlignmentWfaU32Kernel2.lean): hot loop (uget/uset, UInt32 counters, inline compares, USize LCP), level lattice by gcd, single-source path with the ×2 unrolled one-read-per-cell loop; standard axioms. The first-stage status line follows.

**Status 2026-09-11: items 1–15 DONE.** `wfaAlignU` elaborates with standard axioms only
(`lake build CodecWfaU32`; certificate `Certificate.lean` regenerated; `wfau` registered in the
harness and the cross-codec check). The second stage (the probe-combo features) is TODO.

## Target statements

For the assembled kernel `wfaAlignU sc xa ya : Option (Array (Step × Nat) × Int)`:

* `wfaAlignU_score`: `(wfaAlignU sc xa ya).map Prod.snd = (getBestAlignment sc xa.toList ya.toList).map Prod.snd`
* `wfaAlignU_sound`: a returned run-length walk expands to a valid monotone walk whose exact
  score is the returned score
* `wfaAlignU_isSome`: always returns
* `wfaAlignU_score_fun_eq`: the score function equals `wfaAlign`'s as a function
  (as `wfaAlignK_score_fun_eq` does today)

Same shape as `wfaAlignK` (alignment/codecs/wfa_runs): shortcut `compactSmall` first, then the
fast path, then the proven fallback. Every theorem is universal because of the fallback; the
fast path is only taken under the gate `wfaGateB sc ∧ m + n + 2 < 2^30`.

## Architecture: what has to be proven and what is checked at runtime

The fast path returns `some (runs, s)` only if the proven run checker (`checkRunsFast3`,
proven equal to `checkRuns`) accepts the traceback with exact score `s` and
`2 s + L = matchScore·(m + n)` holds for the corner level `L`. Soundness and the exact score are
therefore runtime-certified by an existing theorem (`checkRuns_sound`). The ONLY new proof
obligation is optimality of `L`:

    (uRun … ).map Prod.fst = wfaRunO sc xs ys            (the offsets-only proven loop)

because `offsets_certify_score` (AlignmentWfaCertified.lean) already turns
`wfaRunO sc xs ys = some L` plus the identity into "s is the optimum". Everything reduces to a
refinement of the executed UInt32 run to the proven offsets model, level by level.

## Refinement chain (per level)

    uLevel  ──denotes──▶  nextLevelR  ══(nextLevelP_eq / rdenL_nextLevelR)══▶  nextLevelO  ══▶  model

1. DONE  UInt32 cell arithmetic = Nat code arithmetic below 2^30 (`upushX_toNat`, `upushY_toNat`,
   `upushD_toNat`, `uext_toNat`, `ubetter_toNat`) with SATURATING subtraction `usub`, so no
   geometric invariant on stored codes is needed (AlignmentWfaU32Level.lean).
2. DONE  Padded fronts: `ugetA margin lo f t = f.getD (t + margin - lo) 0`; denotation
   `toRF margin lv sel : RFront` (band start `lo`, the `w` stored codes);
   `rget_toRF : rget (toRF …) t = (uget …).toNat` under well-formedness `WFA`
   (zero padding both sides, exact size when non-empty, codes ≤ m + 1).
3. DONE  The fill loop appends exactly the cell values (`uFillGo_spec`), and
   `uLevel_fronts` exposes the three fronts of a built level as padded fill arrays.
4. DONE  Band facts: the new band contains every non-empty source band expanded by one
   (`uBand_src`); a diagonal outside it reads 0 on every source at t−1, t, t+1 (`src_out`,
   `ugetA_out`), so `pointX`/`pointY`/`pointM` are 0 there (`pointX_zero`, …).
5. DONE  X and Y fronts: `uget_uLevel_xf`, `uget_uLevel_yf` — the built value on every
   diagonal t < len equals `pointX`/`pointY` of the source denotations (AlignmentWfaPoint's
   pointwise characterisation of `nextLevelR`); `wf_uLevel` — well-formedness is preserved.
6. DONE  M front: `uget_uLevel_mf`; same case split as X/Y, uses `cellM_toNat` with the built
   X/Y cells (`pointM` unfolded before rewriting the inner `rget`).
7. DONE  `rdenF_ext`: two `RFront`s with the same `rget` on every t < len have the same
   full-width denotation `rdenF len` (via `bget_den`, `decodeR_rget`, `List.ext_getElem?`).
8. DONE  `rdenL_toRLevel_uLevel`: with hypotheses
   `frontAtR hist' pe (·.xf) = toRF margin xe (·.xf)` (and the other four sources),
   `rdenL len (toRLevel margin (uLevel …)) = rdenL len (nextLevelR … hist')`.
   Proof: `rw [← nextLevelP_eq]`, `congr 1`, each front by `rdenF_ext` and 5.–6. plus
   `packPointX_eq`/`pointX_eq` (and Y, M).
9. DONE  Corner: `cornerU margin m n lv = cornerR m n (toRLevel margin lv)` (via `rget_toRF`,
   UInt32 injectivity, `(m.toUInt32 + 1).toNat = m + 1`), then `cornerR_eq` to `cornerO`.

## Loop and run

10. DONE  `uLoop` mirrors `wfaLoopR` exactly (list window of the last `max pe po px` levels +
    trace array): `(uLoop … fuel hist p trace).map Prod.fst = wfaLoopO … fuel (hist.map (udenL …)) p`
    with `udenL len margin := rdenL len ∘ toRLevel margin`; induction on fuel as in `wfaLoopR_eq`,
    invariant `∀ lv ∈ hist, WF m margin lv` (from `wf_uLevel`), `frontAtR_map_toRLevel` for the
    source hypotheses of 8.
11. DONE  Seed: `rdenL len (toRLevel margin seedU) = seedO m len xs ys` (via `rdenL_seedR` and
    `rdenF_ext`; the seed's X/Y fronts are all-zero arrays, denoting the empty front).
12. DONE  `uRun_eq : (uRun sc xa ya).map Prod.fst = wfaRunO sc xa.toList ya.toList`.

## Kernel

13. DONE  `certifiedRunsU` = `uRun` + traceback (any, unproven) + `checkRunsFast3` + identity;
    `certifiedRunsU_spec` copies `certifiedRuns_spec` with `offsets_certify_score` fed by 12.
14. DONE  `wfaAlignU` = `compactSmall` → `certifiedRunsU` → `wfaAlignK`; the three theorems copy
    `wfaAlignK`'s; `wfaAlignU_score_fun_eq` copies AlignmentWfaRunsVsWfa.
15. DONE  Certificate: KERNEL_THEOREMS entry `wfau`, gen_certificates FOLDER/SUPPORTING, runner
    and SimpleRunner dispatch, check_all.

## Second stage: the speed features of the probes (probe-combo, alignment/probes/ProbeCombo.lean)

probe-combo (unproven) combines ideas 1–4 and is 2.0–3.5× faster than probe-u32 on every cell
(1.2–2.8× BiWFA at 1 %, 1.9–5.2× at 5 %). Plan to prove it, by feature; the target statement is
unchanged (`uRun_eq`-style: the executed run returns `wfaRunO`'s corner level), so items 13–15
are reused verbatim with the new run.

* Single-source path (pe = po = px): store X and Y anyway (3 pushes) so the denotation stays
  per level; needs the per-level invariant `xf ≤ mf ∧ yf ≤ mf` (holds by construction of every
  `nextLevelR` output: `mf = extR (betterR (betterR d xf) yf) ≥ xf, yf`) and monotonicity of
  `pushXR`/`pushYR` in the code, so that `betterR (pushX xf_src) (pushX mf_src) = pushX mf_src`.
* Level lattice by gcd (idea 2): the executed loop steps only over levels ≡ 0 mod g; the
  proof relates it to `wfaLoopO` by showing levels not ≡ 0 mod g are empty (all sources empty),
  i.e. a stuttering refinement: each executed step corresponds to g model steps of which g−1
  build the empty level.
* USize LCP (idea 1): `lcpU1_toNat` already relates it to `lcp`; use it inside `uext_toNat`.
* Hot loop with `uget`/`uset` and one replicate per level (idea 4): only the fill lemma
  (`uFillGo_spec`) and `WFA` change; the pointwise lemmas are stated on `ugetA` and survive.
* Inline compares before the LCP: the lemma `lcpArr xa ya i j = c + [c]·lcpArr (i+1) (j+1)`
  (unfold `lcpArrGo` once).

* Block layout `M|X|Y` in one array per level (combo): the denotation `toRF` takes the block
  offset; `ugetA_eq`/`rget_toRF` restate with `f.getD (blk + t + margin − lo) 0`. The runtime
  per-level layout check (35 conjuncts, `none` ⇒ fallback) becomes a hypothesis `WF` that the
  proof never has to discharge for the hot loop: the theorem is stated under it, and the kernel
  only uses the fast path when the check returned true.

## Second stage: what was done and how (2026-09-11)

* Hot loop (AlignmentWfaU32Fill.lean, FillSpec, Ext, Level2): the new builder `uLevel2` returns
  `none` when a once-per-level index check fails (fallback), otherwise `uLevel2_some`: the level IS
  `uLevel …` array for array (`uFillGo2_spec` gives the written values, `read_X/Y/D` the index
  identities, `uext2_eq` the extension). Nothing downstream of `uLevel` had to change.
* Lattice (AlignmentWfaU32Lattice.lean): `wfaRunO_lattice`, a stuttering refinement of `wfaLoopO`
  with a phase-indexed history relation (`HRel`); the kernel runs with penalties divided by
  `gcdU` (proven = `Nat.gcd`) and multiplies the corner level back.
* Single-source path (AlignmentWfaU32Single, FillS, FillSSpec, LevelS, Kernel2): with divided
  penalties (1,1,1) the level reads only the previous M front. Proof through the R layer:
  `pointX_single`/`pointY_single` (X ≤ M ⇒ the X point is `pushXR` of the M front alone),
  `nextLevelR_xf_le_mf` (every built level satisfies the invariant), `uLevelS_some` (the built M
  front denotes `nextLevelR`'s from any `R` with the same M reads), `uLoopS_some` with the
  M-read relation as loop invariant, `uRunS_some`, dispatch `uRunD_some`.
* NOT done: the block layout (one array `M|X|Y` per level) of the combo probe — the general
  (affine) path allocates three arrays per level and is ~1.2–1.5× slower than probe-combo there;
  doing it means an offset parameter in `toRF`/`WFA` throughout AlignmentWfaU32Step.lean.

## Effort estimate

Items 1–15: done (three sessions). Second stage: done in one session except the block layout. Order: (a) gcd lattice
(pure re-indexing of `wfaLoopO`, no new arithmetic), (b) single-source path (one invariant),
(c) block layout + uget/uset loop (restate `uFillGo_spec`), (d) USize LCP and inline compares
(lemmas exist: `lcpUC_toNat`, `lcpArr_eq`).
