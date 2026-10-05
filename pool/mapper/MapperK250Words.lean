import MapperK250Loops
import MapperK250Spec

/-!
# Word kernels = byte kernels

Under `Rep P G` (the packed genome spells `G`), a packed read that passed its check
(`(packRP R).ok`), and a window inside flagged (pure ACGT) blocks, each word scan
equals the byte loop it replaces: `hamA_eq` (`hamming`), `fwdA_eq` / `fwdK_eq`
(`fwdMis`), `bwdA_eq` / `bwdK_eq` / `bwdL_eq` (`bwdMis`), `gappedL_eq` (`gappedPen3`),
and the kernel `kerGK_eq` (`kerG3`, with no hypothesis but `Rep`).
-/

namespace MapSpec.Fast

open MapSpec MapSpec.Packed

theorem flagsOk_get (w : ByteArray) : ∀ d b stop, stop - b = d → flagsOk w b stop = true →
    ∀ b', b ≤ b' → b' < stop → w.get! (17 * b') = 1 := by
  intro d
  induction d with
  | zero => intro b stop hd _ b' h1 h2; omega
  | succ d ih =>
    intro b stop hd h b' h1 h2
    unfold flagsOk at h
    rw [if_pos (by omega)] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    by_cases hb : b' = b
    · subst hb; exact h.1
    · exact ih (b + 1) stop (by omega) h.2 b' (by omega) h2

/-- Unpacking `wordOk`: every letter of the window `[st, st + len)` is flagged. -/
theorem wordOk_unpack (R : ByteArray) (P : PGen) (st len : Nat)
    (hw : wordOk R (packRP R) P st len = true) :
    (packRP R).ok = true ∧ 0 < R.size ∧ 0 < len ∧ R.size ≤ st + len ∧ st + len ≤ P.n ∧
      ∀ y, st ≤ y → y < st + len → P.w.get! (17 * ((P.o + y) / 64)) = 1 := by
  unfold wordOk winOk at hw
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
  obtain ⟨⟨⟨⟨hok, h0⟩, hl⟩, hs⟩, hn, hf⟩ := hw
  refine ⟨hok, h0, hl, hs, hn, fun y h1 h2 => ?_⟩
  exact flagsOk_get P.w _ _ _ rfl hf _ (Nat.div_le_div_right (by omega)) (by
    have := Nat.div_le_div_right (c := 64) (show P.o + y ≤ P.o + st + len - 1 by omega)
    omega)

/-- The byte pre-scan alone, when it finds the `k`-th mismatch. -/
theorem fwd_pre (R G : ByteArray) (st stop k : Nat) (hk : 1 ≤ k)
    (hf : fwdMis R G st (min stop pre) 0 k < min stop pre) :
    fwdMis R G st (min stop pre) 0 k = fwdMis R G st stop 0 k := by
  generalize hp : min stop pre = p at hf
  have hps : p ≤ stop := by rw [← hp]; exact Nat.min_le_left _ _
  obtain ⟨a1, a2, a3⟩ := fwdMis_spec R G st p (p - 0) 0 k rfl (Nat.zero_le _) hk
  have h1 := fwdMis_spec R G st stop (stop - 0) 0 k rfl (Nat.zero_le _) hk
  refine FSpec_unique _ 0 stop k _ _ ⟨a1, by omega, fun i h1 h2 => ?_⟩ h1
  by_cases hi : i ≤ p
  · exact a3 i h1 hi
  · have := mt (a3 p (Nat.zero_le _) (Nat.le_refl _)).1 (by omega)
    have := cntP_mono (fun x => R.get! x != G.get! (st + x)) 0 (i - 0) 0 (p - 0) (Nat.le_refl _) (by omega)
    omega

theorem bwd_pre (R G : ByteArray) (st len lo k : Nat) (hk : 1 ≤ k)
    (hb : max lo (R.size - pre) < bwdMis R G st len (max lo (R.size - pre)) R.size k) :
    bwdMis R G st len (max lo (R.size - pre)) R.size k = bwdMis R G st len lo R.size k := by
  generalize hq : max lo (R.size - pre) = q at hb
  have hlq : lo ≤ q := by rw [← hq]; exact Nat.le_max_left _ _
  by_cases hqe : q ≤ R.size
  · obtain ⟨a1, a2, a3⟩ := bwdMis_spec R G st len q (R.size - q) R.size k rfl hqe hk
    have h1 := bwdMis_spec R G st len lo (R.size - lo) R.size k rfl (by omega) hk
    refine BSpec_unique _ lo R.size k _ _ ⟨by omega, a2, fun i h1 h2 => ?_⟩ h1
    by_cases hi : q ≤ i
    · exact a3 i hi h2
    · have := mt (a3 q (Nat.le_refl _) hqe).1 (by omega)
      have := cntP_mono (fun x => R.get! x != G.get! (st + len + x - R.size)) i (R.size - i) q
        (R.size - q) (by omega) (by omega)
      omega
  · rw [bwdMis, if_neg (by omega)] at hb
    omega

theorem winOk_flags (P : PGen) (st len : Nat) (h : winOk P st len = true) :
    st + len ≤ P.n ∧ ∀ y, st ≤ y → y < st + len → P.w.get! (17 * ((P.o + y) / 64)) = 1 := by
  unfold winOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1, fun y h1 h2 => ?_⟩
  exact flagsOk_get P.w _ _ _ rfl h.2 _ (Nat.div_le_div_right (by omega)) (by
    have := Nat.div_le_div_right (c := 64) (show P.o + y ≤ P.o + st + len - 1 by omega)
    omega)

theorem fwdL_eq (R G : ByteArray) (P : PGen) (hP : Rep P G) (st stop k : Nat) (hk : 1 ≤ k) :
    fwdL R G (packRP R) P st stop k = fwdMis R G st stop 0 k := by
  unfold fwdL
  simp only []
  split
  · exact fwd_pre R G st stop k hk ‹_›
  split
  · next hc =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hok, hs⟩, hw⟩ := hc
    obtain ⟨hn, hf⟩ := winOk_flags P st stop hw
    have hW : WOk R G P st stop := ⟨hP, hok, hs, hn, fun x hx => by
      rw [show P.o + st + x = P.o + (st + x) by omega]; exact hf _ (by omega) (by omega)⟩
    rw [← fwdK_eq R G P st stop hW k hk]
    unfold fwdK
    simp only []
    rw [if_neg ‹_›]
  · rfl

theorem bwdL_eq (R G : ByteArray) (P : PGen) (hP : Rep P G) (st len lo k : Nat) (hk : 1 ≤ k) :
    bwdL R G (packRP R) P st len lo k = bwdMis R G st len lo R.size k := by
  unfold bwdL
  simp only []
  split
  · exact bwd_pre R G st len lo k hk ‹_›
  split
  · next hc =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hok, hs⟩, hlo⟩, hw⟩ := hc
    obtain ⟨hn, hf⟩ := winOk_flags P _ _ hw
    have hWB : WOkB R G P (st + len - R.size) lo := ⟨hP, hok, by omega, fun x h1 h2 => by
      rw [show P.o + (st + len - R.size) + x = P.o + (st + len - R.size + x) by omega]
      exact hf _ (by omega) (by omega)⟩
    rw [← bwdK_eq R G P st len lo hs hWB k hk]
    unfold bwdK
    simp only []
    rw [if_neg ‹_›]
  · rfl

theorem gappedL_eq (R G : ByteArray) (P : PGen) (hP : Rep P G) (st len lim : Nat) :
    gappedL R G (packRP R) P st len lim = gappedPen3 R G st len lim := by
  unfold gappedL gappedPen3
  simp only [fwdL_eq R G P hP st _ _ (show 1 ≤ 1 by omega), fwdL_eq R G P hP st _ _ (show 1 ≤ 2 by omega),
    fwdL_eq R G P hP st _ _ (show 1 ≤ 3 by omega), bwdL_eq R G P hP st len _ _ (show 1 ≤ 1 by omega),
    bwdL_eq R G P hP st len _ _ (show 1 ≤ 2 by omega), bwdL_eq R G P hP st len _ _ (show 1 ≤ 3 by omega)]

/-- **The word kernel is `kerG3`.** -/
theorem kerGK_eq (R G : ByteArray) (P : PGen) (hP : Rep P G) (st len lim : Nat) :
    kerGK R (packRP R) G P st len lim = kerG3 R G st len lim := by
  unfold kerGK
  by_cases hlen : len = R.size
  · rw [if_pos hlen]
    by_cases hpre : lim / 4 < hamming R G st (lim / 4) 0 (min R.size pre) 0
    · rw [if_pos hpre]
      unfold kerG3
      split
      · try rw [if_pos hlen]
        dsimp only
        rw [hamming_spec R G st (lim / 4) _ _ 0 0 rfl (Nat.zero_le _)] at hpre
        rw [hamming_spec R G st (lim / 4) _ _ 0 0 rfl (Nat.zero_le _)]
        have := cntP_mono (fun k => R.get! k != G.get! (st + k)) 0 (R.size - 0) 0
          (min R.size pre - 0) (Nat.le_refl _) (by omega)
        rw [if_neg (by omega)]
      · rfl
    · rw [if_neg hpre]
      split
      · next hw =>
        obtain ⟨hok, h0, hl, hs, hn, hf⟩ := wordOk_unpack R P st len hw
        have hW : WOk R G P st R.size :=
          ⟨hP, hok, Nat.le_refl _, by omega, fun x hx => by
            rw [show P.o + st + x = P.o + (st + x) by omega]; exact hf _ (by omega) (by omega)⟩
        dsimp only
        rw [hamA_eq R G P st R.size hW]
        unfold kerG3
        rw [if_pos (show st + len ≤ G.size by rw [← hP.1]; omega), if_pos hlen]
      · rfl
  · rw [if_neg hlen]
    unfold kerG3
    rw [hP.1]
    split
    · exact gappedL_eq R G P hP st len lim
    · rfl

/-- **The word kernel is `kerG`** (`lim ≤ 15`). -/
theorem kerGK_kerG (R G : ByteArray) (P : PGen) (hP : Rep P G) (st len lim : Nat) (hlim : lim ≤ 15) :
    kerGK R (packRP R) G P st len lim = kerG R G st len lim := by
  rw [kerGK_eq R G P hP, kerG3_kerG R G st len lim hlim]

end MapSpec.Fast

#print axioms MapSpec.Fast.kerGK_eq
#print axioms MapSpec.Fast.kerGK_kerG
