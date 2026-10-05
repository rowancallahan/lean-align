import MapperK250Loops
import MapperK250Spec

/-!
# Word kernels = byte kernels

Under `Rep P G` (the packed genome spells `G`), a packed read that passed its check
(`(packRP R).ok`), and a window inside flagged (pure ACGT) blocks, each word scan
equals the byte loop it replaces: `hamA_eq` (`hamming`), `fwdA_eq` / `fwdK_eq`
(`fwdMis`), `bwdA_eq` / `bwdK_eq` (`bwdMis`), `gappedW_eq` (`gappedPen3`),
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

theorem gappedW_eq (R G : ByteArray) (P : PGen) (hP : Rep P G) (st len lim : Nat)
    (hw : wordOk R (packRP R) P st len = true) :
    gappedW R G (packRP R).w P.w P.o st len lim = gappedPen3 R G st len lim := by
  obtain ⟨hok, h0, hl, hs, hn, hf⟩ := wordOk_unpack R P st len hw
  unfold gappedW gappedPen3
  dsimp only
  rw [show P.o + st + len - R.size = P.o + (st + len - R.size) by omega]
  generalize hL : (if len > R.size then len - R.size else R.size - len) = L
  generalize hsk : (if len < R.size then L else 0) = skip
  have hskv : skip ≤ R.size ∧ (len < R.size → skip = R.size - len) ∧ (¬ len < R.size → skip = 0) := by
    subst hL hsk; split <;> (try split) <;> omega
  have hW : WOk R G P st (R.size - skip) :=
    ⟨hP, hok, by omega, by omega, fun x hx => by
      rw [show P.o + st + x = P.o + (st + x) by omega]; exact hf _ (by omega) (by omega)⟩
  have hWB : WOkB R G P (st + len - R.size) skip :=
    ⟨hP, hok, by omega, fun x h1 h2 => by
      rw [show P.o + (st + len - R.size) + x = P.o + (st + len - R.size + x) by omega]
      exact hf _ (by by_cases h : len < R.size <;> omega) (by omega)⟩
  rw [fwdK_eq R G P st _ hW 1 (by omega), fwdK_eq R G P st _ hW 2 (by omega),
    fwdK_eq R G P st _ hW 3 (by omega), bwdK_eq R G P st len skip hs hWB 1 (by omega),
    bwdK_eq R G P st len skip hs hWB 2 (by omega), bwdK_eq R G P st len skip hs hWB 3 (by omega)]

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
    split
    · next hw =>
      obtain ⟨hok, h0, hl, hs, hn, hf⟩ := wordOk_unpack R P st len hw
      rw [gappedW_eq R G P hP st len lim hw]
      unfold kerG3
      rw [if_pos (show st + len ≤ G.size by rw [← hP.1]; omega), if_neg hlen]
    · rfl

/-- **The word kernel is `kerG`** (`lim ≤ 15`). -/
theorem kerGK_kerG (R G : ByteArray) (P : PGen) (hP : Rep P G) (st len lim : Nat) (hlim : lim ≤ 15) :
    kerGK R (packRP R) G P st len lim = kerG R G st len lim := by
  rw [kerGK_eq R G P hP, kerG3_kerG R G st len lim hlim]

end MapSpec.Fast

#print axioms MapSpec.Fast.kerGK_eq
#print axioms MapSpec.Fast.kerGK_kerG
