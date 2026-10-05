import FastGenProof

/-!
# Every hit of a read within a cap (`hitsC`, one chromosome, one strand)

The searches give the best hit only.  For pair-level uniqueness (`pairSpecUT`) the
ladder needs every hit of a mate within a cap `lim ≤ 16`:

* look up any `sbound lim + 1` of the read's seeds (anchors `acc`; which ones is a
  choice, e.g. the rarest);
* each anchor diagonal once (`diags`: sorted, deduplicated);
* the diagonal filter `kfilt` at `lim` (seeds not looked up, then 8-letter pieces);
* every shape `(a, b)` allowed within `lim` (`shapesAt lim`) through the kernel
  `kerH` (the exact penalty when `≤ lim`).

A window within penalty `lim` keeps a clean copy of one looked-up seed (`coverLE`), so
its diagonal is an anchor diagonal; the filter passes there (the same counting as
`chromKBS_cover`); its shape is allowed.  So:

    (w, k) ∈ hitsC … ↔ w.chr = c ∧ cwT lim read g w = k ∧ k ≤ lim      (hitsC_sound, hitsC_complete)
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-- Windows of chromosome `c` within penalty `lim` from the anchor arrays `acc` (`us`:
the seeds not looked up; `Ls`: seed spacing), with their penalties. -/
def hitsC (R : ByteArray) (gbs : Array ByteArray) (c lim : Nat) (acc : List (Array Nat)) (us : List Nat)
    (Ls : Nat) : List (Window × Nat) :=
  (diags acc).flatMap fun D =>
    if kfilt R gbs[c]! acc us Ls lim (initP lim) D then
      (shapesAt lim).filterMap fun sh =>
        if 0 ≤ dst R.size D sh ∧ 0 ≤ wlen R.size sh then
          let k := kerH R gbs c (dst R.size D sh).toNat (wlen R.size sh).toNat lim
          if k ≤ lim then some (⟨c, (dst R.size D sh).toNat, (wlen R.size sh).toNat⟩, k) else none
        else none
    else []

section hits
variable (read : List Char) (g : Genome) (gbs : Array ByteArray) (R : ByteArray)
  (hg : GenomeBytes gbs g) (hr : Encodes R read) (c lim : Nat) (hc : c < gbs.size) (hl16 : lim ≤ 16)

include hg hr hc hl16 in
/-- **Sound.** -/
theorem hitsC_sound (acc : List (Array Nat)) (us : List Nat) (Ls : Nat) (w : Window) (k : Nat)
    (h : (w, k) ∈ hitsC R gbs c lim acc us Ls) : w.chr = c ∧ k ≤ lim ∧ cwT lim read g w = k := by
  unfold hitsC at h
  rw [List.mem_flatMap] at h
  obtain ⟨D, -, hD⟩ := h
  split at hD
  · rw [List.mem_filterMap] at hD
    obtain ⟨sh, -, hsh⟩ := hD
    split at hsh
    · simp only [] at hsh
      split at hsh
      · next hk =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hsh
        obtain ⟨rfl, rfl⟩ := hsh
        have := cwT_kerH lim read g gbs R hg hr c (dst R.size D sh).toNat (wlen R.size sh).toNat lim hc
          (Nat.le_refl _) hl16
        refine ⟨rfl, hk, ?_⟩
        omega
      · cases hsh
    · cases hsh
  · cases hD

include hg hr hc hl16 in
set_option maxHeartbeats 2000000 in
/-- **Complete.**  From the anchor arrays of the looked-up seeds `pre` (more than
`sbound lim` of them; sorted, holding every exact seed place), every window of
chromosome `c` within penalty `lim` is listed with its penalty. -/
theorem hitsC_complete (hm : 0 < R.size / 25) (arr : Nat → Array Nat)
    (hArr : ∀ j, j < R.size / 25 → (arr j).toList.Pairwise (· < ·) ∧
      ∀ p, MatchAt gbs[c]! p R (j * (R.size / (R.size / 25))) →
        (p + (R.size - j * (R.size / (R.size / 25)))) * 16 + 0 ∈ (arr j).toList)
    (pre : List Nat) (hpnd : pre.Nodup) (hpm : ∀ j ∈ pre, j < R.size / 25) (hpl : sbound lim < pre.length)
    (w : Window) (hwc : w.chr = c) (hcw : cwT lim read g w ≤ lim) :
    (w, cwT lim read g w) ∈
      hitsC R gbs c lim (pre.map arr) (unseen (R.size / 25) pre) (R.size / (R.size / 25)) := by
  have hn := hr.1
  have hl0 : 0 < q := by decide
  have hlL : q ≤ R.size / (R.size / 25) := le_div_seeds _ hm
  have hm8 : 0 < R.size / pl := by
    have h25 : 25 ≤ R.size := by
      rcases Nat.lt_or_ge R.size 25 with h | h
      · rw [Nat.div_eq_of_lt h] at hm; omega
      · exact h
    exact Nat.div_pos (by unfold pl; omega) (by decide)
  have hlL8 : pl ≤ R.size / (R.size / pl) := le_div_pieces _ _ hm8
  generalize hacc0 : pre.map arr = acc
  have hacc : acc = pre.map arr := hacc0.symm
  generalize hmm : R.size / 25 = m at *
  have hm0 : 0 < m := hm
  generalize hLs : R.size / m = Ls at *
  have hmL : m * Ls ≤ R.size := by
    rw [← hLs]; exact Nat.div_mul_le_self _ _ |> fun h => by rw [Nat.mul_comm]; exact h
  generalize hus : unseen m pre = us
  have husm : ∀ j ∈ us, j < m ∧ j ∉ pre := by
    intro j hj
    rw [← hus] at hj
    unfold unseen at hj
    rw [List.mem_filter, List.mem_range] at hj
    refine ⟨hj.1, fun hp => ?_⟩
    have h3 : ¬ pre.contains j = true := by simpa using hj.2
    exact h3 (by simpa using hp)
  have husnd : us.Nodup := by rw [← hus]; unfold unseen; exact List.nodup_range.filter _
  generalize hx : cwT lim read g w = x at hcw ⊢
  -- the window scores `−x`
  have hws : windowScore sc0 read g w = some (-(x : Int)) := by
    have := (cwT_iff lim read g w (-(cwT lim read g w : Int))).2 ⟨by omega, rfl⟩
    rw [hx] at this; exact this.1
  have hJl : sbound x < pre.length := by
    have := sbound_mono x lim hcw; omega
  have hkq : q ≤ read.length / (m - 1 + 1) := by rw [← hn, show m - 1 + 1 = m by omega, hLs]; exact hlL
  obtain ⟨j, hj, p, a, bb, hcg, hmatch, hshape, ha1, ha2, hst, hwl⟩ :=
    coverLE g read gbs R hg hr (-(x : Int)) q hl0 (m - 1) hkq (by have h2 : 2 ≤ q := (by decide); omega)
      pre hpnd (fun j hj => by have := hpm j hj; omega) (by rw [sbound_def] at hJl; omega) w (-(x : Int)) hws
      (Int.le_refl _)
  rw [← hn, show m - 1 + 1 = m by omega, hLs] at hmatch ha1 hst
  rw [← hn] at hwl
  rw [hwc] at hmatch
  have hjm := hpm j hj
  have hjL : j * Ls + Ls ≤ R.size := by
    have : j * Ls + Ls ≤ m * Ls := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
    omega
  -- the anchor
  have harr : arr j ∈ acc := by rw [hacc]; exact List.mem_map_of_mem hj
  have he : (p + (R.size - j * Ls)) * 16 + 0 ∈ (arr j).toList := (hArr j hjm).2 p hmatch
  generalize he' : (p + (R.size - j * Ls)) * 16 + 0 = e at he
  have he16 : e / 16 = p + (R.size - j * Ls) := by rw [← he']; omega
  have hwin : w = ⟨c, ((p : Int) - (j * Ls : Nat) - a).toNat, ((R.size : Int) + a + bb).toNat⟩ := by
    cases w; simp only at hwc hst hwl; rw [hwc, hst, hwl, hn]
  have hcnt : ∀ (l : List Nat) (f : Nat → Bool),
      (l.filter f).length + (l.filter (fun x => !f x)).length = l.length := by
    intro l f; induction l with
    | nil => rfl
    | cons y l ih => by_cases hy : f y = true <;> simp [hy] <;> omega
  have hal : acc.length = pre.length := by rw [hacc]; simp
  -- more than `sbound x` seeds cannot all fail a test passed by the seeds matched near `e / 16`
  have hfew : ∀ (L : List Nat) (t : Nat → Bool), L.Nodup → (∀ j ∈ L, j < m) →
      (∀ j' ∈ L, ∀ p', MatchAtL gbs[c]! p' R (j' * Ls) q →
        e / 16 ≤ p' + (R.size - j' * Ls) + 2 * gapBound sc0 (-(x : Int)) →
        p' + (R.size - j' * Ls) ≤ e / 16 + 2 * gapBound sc0 (-(x : Int)) → t j' = true) →
      (L.filter fun j => !t j).length ≤ sbound x := by
    intro L t hLn hLm ht
    apply Classical.byContradiction; intro hlt'
    have hsub := List.filter_sublist (p := fun j => !t j) (l := L)
    obtain ⟨j', hj', p', a', bb', -, hmatch', hshape', ha1', -, hst', -⟩ :=
      coverLE g read gbs R hg hr (-(x : Int)) q hl0 (m - 1) hkq (by have h2 : 2 ≤ q := (by decide); omega)
        _ (hsub.nodup hLn)
        (fun j hj => by have := hLm j (hsub.subset hj); omega)
        (by rw [sbound_def] at hlt'; omega) w (-(x : Int)) hws (Int.le_refl _)
    rw [← hn, show m - 1 + 1 = m by omega, hLs] at hmatch' ha1' hst'
    rw [hwc] at hmatch'
    have hj'm := hLm j' (hsub.subset hj')
    have hj'L : j' * Ls + Ls ≤ R.size := by
      have : j' * Ls + Ls ≤ m * Ls := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
      omega
    have hsa := hshape.1
    have hsa' := hshape'.1
    have htj := ht j' (hsub.subset hj') p' hmatch' (by rw [he16]; omega) (by rw [he16]; omega)
    have := (List.mem_filter.1 hj').2
    rw [htj] at this; cases this
  -- the filter passes at `e / 16`
  have hfilt : kfilt R gbs[c]! acc us Ls lim (initP lim) (e / 16) = true := by
    have hQ : min lim (initP lim).pen = lim := Nat.min_eq_left (by simp [initP])
    have hgQ := gapBound_mono x lim hcw
    have hsQ := sbound_mono x lim hcw
    unfold kfilt
    simp only [hQ, Bool.and_eq_true, decide_eq_true_eq]
    generalize hrq : 2 * gapBound sc0 (-((lim : Nat) : Int)) = rq
    have hrx : 2 * gapBound sc0 (-(x : Int)) ≤ rq := by omega
    have hboth := hfew (pre.filter ((fun arr => !anyNear arr (e / 16 - rq) (e / 16 + rq)) ∘ arr) ++
        us.filter (fun j => !seedNear R gbs[c]! Ls rq (e / 16) j))
      (fun j => if j ∈ pre then anyNear (arr j) (e / 16 - rq) (e / 16 + rq) else seedNear R gbs[c]! Ls rq (e / 16) j)
      (by
        refine List.nodup_append.2 ⟨List.Pairwise.filter _ hpnd, List.Pairwise.filter _ husnd, ?_⟩
        intro y hy1 z hy2 hyz
        subst hyz
        exact (husm y (List.mem_filter.1 hy2).1).2 (List.mem_filter.1 hy1).1)
      (by
        intro y hy
        rcases List.mem_append.1 hy with hy | hy
        · exact hpm y (List.mem_filter.1 hy).1
        · exact (husm y (List.mem_filter.1 hy).1).1)
      (by
        intro j' hj' p' hm' h1 h2
        rcases List.mem_append.1 hj' with hy | hy
        · have hj'p := (List.mem_filter.1 hy).1
          have hj'm := hpm j' hj'p
          have hsort : (arr j').toList.Pairwise (· < ·) := (hArr j' hj'm).1
          have he2 : (p' + (R.size - j' * Ls)) * 16 + 0 ∈ (arr j').toList := (hArr j' hj'm).2 p' hm'
          rw [if_pos hj'p]
          rw [anyNear_spec _ hsort]
          refine ⟨_, he2, ?_⟩
          have e1 : ((p' + (R.size - j' * Ls)) * 16 + 0) / 16 = p' + (R.size - j' * Ls) := by omega
          rw [e1]
          omega
        · have hu := husm j' (List.mem_filter.1 hy).1
          rw [if_neg hu.2]
          have hj'L : j' * Ls + Ls ≤ R.size := by
            have : j' * Ls + Ls ≤ m * Ls := by
              rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
            omega
          exact seedNear_of R gbs[c]! Ls rq (e / 16) j' p' (by omega) hm' (by omega) (by omega))
    have e1 : ((pre.filter ((fun arr => !anyNear arr (e / 16 - rq) (e / 16 + rq)) ∘ arr) ++
        us.filter (fun j => !seedNear R gbs[c]! Ls rq (e / 16) j)).filter
        (fun j => !(if j ∈ pre then anyNear (arr j) (e / 16 - rq) (e / 16 + rq)
          else seedNear R gbs[c]! Ls rq (e / 16) j))) =
        pre.filter ((fun arr => !anyNear arr (e / 16 - rq) (e / 16 + rq)) ∘ arr) ++
        us.filter (fun j => !seedNear R gbs[c]! Ls rq (e / 16) j) := by
      rw [List.filter_eq_self]
      intro y hy
      rcases List.mem_append.1 hy with hy | hy
      · have := List.mem_filter.1 hy
        rw [if_pos this.1]
        simpa using this.2
      · have := List.mem_filter.1 hy
        rw [if_neg (husm y this.1).2]
        exact this.2
    rw [e1, List.length_append] at hboth
    have hsupp : suppA acc (e / 16) rq = (pre.filter ((fun arr => anyNear arr (e / 16 - rq) (e / 16 + rq)) ∘ arr)).length := by
      unfold suppA; rw [hacc, List.filter_map, List.length_map]
    have hc2 : (pre.filter ((fun arr => anyNear arr (e / 16 - rq) (e / 16 + rq)) ∘ arr)).length +
        (pre.filter ((fun arr => !anyNear arr (e / 16 - rq) (e / 16 + rq)) ∘ arr)).length = pre.length :=
      hcnt pre _
    have hfJ : acc.length - suppA acc (e / 16) rq =
        (pre.filter ((fun arr => !anyNear arr (e / 16 - rq) (e / 16 + rq)) ∘ arr)).length := by
      rw [hsupp, hal]
      omega
    refine ⟨⟨by omega, ?_⟩, ?_⟩
    · apply unlook_of
      rw [hfJ]
      omega
    -- the pieces
    generalize hm8e : R.size / pl = m8 at hm8 hlL8 ⊢
    generalize hL8 : R.size / m8 = L8 at hlL8 ⊢
    have hmL8 : m8 * L8 ≤ R.size := by rw [← hL8, Nat.mul_comm]; exact Nat.div_mul_le_self _ _
    apply fineOk_of
    rw [Nat.zero_add]
    refine Nat.le_trans ?_ hsQ
    apply Classical.byContradiction; intro hlt'
    have hkq8 : pl ≤ read.length / (m8 - 1 + 1) := by
      rw [← hn, show m8 - 1 + 1 = m8 by omega, hL8]; exact hlL8
    have hsub := List.filter_sublist (p := fun j => !pieceNear R gbs[c]! pl L8 rq (e / 16) j)
      (l := List.range' 0 m8)
    obtain ⟨j', hj', p', a', bb', -, hmatch', hshape', ha1', -, hst', -⟩ :=
      coverLE g read gbs R hg hr (-(x : Int)) pl (by decide) (m8 - 1) hkq8
        (by have : 2 ≤ pl := by decide
            omega)
        _ (hsub.nodup List.nodup_range')
        (fun j hj => by have := List.mem_range'_1.1 (hsub.subset hj); omega)
        (by rw [sbound_def] at hlt'; omega) w (-(x : Int)) hws (Int.le_refl _)
    rw [← hn, show m8 - 1 + 1 = m8 by omega, hL8] at hmatch' ha1' hst'
    rw [hwc] at hmatch'
    have hj'm := (List.mem_range'_1.1 (hsub.subset hj')).2
    have hj'L : j' * L8 + L8 ≤ R.size := by
      have : j' * L8 + L8 ≤ m8 * L8 := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
      omega
    have hsa := hshape.1
    have hsa' := hshape'.1
    have htj := pieceNear_of R gbs[c]! pl L8 rq (e / 16) j' p' (by omega) hmatch'
      (by rw [he16]; omega) (by rw [he16]; omega)
    have := (List.mem_filter.1 hj').2
    rw [htj] at this; cases this
  -- the window is listed at diagonal `e / 16`, shape `(a, bb)`
  have hd : dst R.size (e / 16) (a, bb) = (p : Int) - (j * Ls : Nat) - a := by
    unfold dst; rw [he16]; push_cast; omega
  have hwl' : wlen R.size (a, bb) = (R.size : Int) + a + bb := rfl
  have hker := cwT_kerH lim read g gbs R hg hr c (dst R.size (e / 16) (a, bb)).toNat
    (wlen R.size (a, bb)).toNat lim hc (Nat.le_refl _) hl16
  have hwin' : w = ⟨c, (dst R.size (e / 16) (a, bb)).toNat, (wlen R.size (a, bb)).toNat⟩ := by
    rw [hd, hwl']; exact hwin
  rw [← hwin', hx] at hker
  unfold hitsC
  rw [List.mem_flatMap]
  refine ⟨e / 16, ?_, ?_⟩
  · unfold diags
    rw [mem_dedupAdj, List.mem_mergeSort, List.mem_flatMap]
    exact ⟨_, harr, List.mem_map.2 ⟨e, he, rfl⟩⟩
  · rw [if_pos hfilt, List.mem_filterMap]
    refine ⟨(a, bb), shapesAt_mem x lim hcw a bb hshape, ?_⟩
    rw [if_pos ⟨by rw [hd]; omega, by rw [hwl']; omega⟩]
    simp only []
    rw [← hker, if_pos (by omega)]
    rw [← hwin']
    congr 2
    omega

end hits

end MapSpec.Fast

#print axioms MapSpec.Fast.hitsC_sound
#print axioms MapSpec.Fast.hitsC_complete
