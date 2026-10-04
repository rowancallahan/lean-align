import FastMapper
import EarlyStopMapper

/-!
# Coverage for the general fast path

`cover`: cut the read into `k + 1` seeds of `L = n / (k + 1) ≥ 25` letters.  For
a window scoring at least `S`, any `seedBound sc0 S + 1` distinct seeds contain
one, `j`, whose first 25 letters occur in the window's chromosome at a place `p`
with the window `(p − jL − a, n + a + b)` for a shape `(a, b)` allowed at `S`
(`shapeOk (gapBound sc0 S) (gapBound2 sc0 S)`).  This is `mem_seedCands_among`
(through the scanning lookup) restated over the byte genome.
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

theorem scanLookup_sound (g : Genome) (l0 : Nat) (word : List Char) (c p : Nat)
    (h : (c, p) ∈ scanLookup g l0 word) :
    ∃ ch, g[c]? = some ch ∧ (ch.seq.drop p).take l0 = word := by
  unfold scanLookup at h
  simp only [List.mem_flatMap, List.mem_range] at h
  obtain ⟨c', -, hm⟩ := h
  split at hm
  · next ch hch =>
    simp only [List.mem_map, List.mem_filter, List.mem_range, beq_iff_eq, Prod.mk.injEq] at hm
    obtain ⟨p', ⟨-, he⟩, rfl, rfl⟩ := hm
    exact ⟨ch, hch, he⟩
  · simp at hm

theorem shapes_ok (d d2 : Nat) (st : Int × Int) (h : st ∈ shapes d d2) : shapeOk d d2 st.1 st.2 := by
  unfold shapes at h
  rw [List.mem_filter] at h
  exact of_decide_eq_true h.2

/-- **Coverage.** -/
theorem cover (g : Genome) (read : List Char) (gbs : Array ByteArray) (R : ByteArray)
    (hg : GenomeBytes gbs g) (hr : Encodes R read) (S : Int)
    (k : Nat) (hk : q ≤ read.length / (k + 1))
    (J : List Nat) (hJn : J.Nodup) (hJk : ∀ j ∈ J, j ≤ k) (hJl : seedBound sc0 S < J.length)
    (w : Window) (s : Int) (hs : windowScore sc0 read g w = some s) (hS : S ≤ s) :
    ∃ j ∈ J, ∃ (p : Nat) (a b : Int), w.chr < gbs.size ∧
      MatchAt gbs[w.chr]! p R (j * (read.length / (k + 1))) ∧
      shapeOk (gapBound sc0 S) (gapBound2 sc0 S) a b ∧
      ((j * (read.length / (k + 1)) : Nat) : Int) + a ≤ p ∧ 0 ≤ (read.length : Int) + a + b ∧
      w.start = ((p : Int) - (j * (read.length / (k + 1)) : Nat) - a).toNat ∧
      w.len = ((read.length : Int) + a + b).toNat := by
  have hm := mem_seedCands_among (fun _ _ => true) (scanLookup g q) q sc0 valid_sc0 S g
    (scanLookup_complete g q) (keepAll_complete g) read k (gapBound sc0 S) (gapBound2 sc0 S)
    ⟨by decide, hk⟩ (Nat.le_refl _) (Nat.le_refl _) J hJn hJk hJl w s hs hS
  rw [List.mem_flatMap] at hm
  obtain ⟨j, hj, hw⟩ := hm
  unfold seedCands at hw
  simp only [List.mem_filter, List.mem_flatMap, List.mem_filterMap, Option.ite_none_right_eq_some,
    Option.some.injEq] at hw
  obtain ⟨⟨c, p⟩, ⟨hplace, -⟩, st, hst, ⟨h1, h2⟩, rfl⟩ := hw
  obtain ⟨ch, hch, hword⟩ := scanLookup_sound g q _ c p hplace
  clear hs hplace
  dsimp only at h1 ⊢
  generalize hL : read.length / (k + 1) = L at hk hword h1 ⊢
  have hjk := hJk j hj
  have hjL : j * L + L ≤ read.length := by
    have := Nat.div_mul_le_self read.length (k + 1)
    rw [hL] at this
    have : j * L + L ≤ (k + 1) * L := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
    have h3 : (k + 1) * L = L * (k + 1) := Nat.mul_comm _ _
    omega
  have hc : c < g.length := by
    rcases Nat.lt_or_ge c g.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hch; cases hch
  have hch' : g[c] = ch := by rw [List.getElem?_eq_getElem hc] at hch; cases hch; rfl
  have hcg : c < gbs.size := by rw [hg.1]; exact hc
  have henc := hg.2 c hcg hc
  rw [hch'] at henc
  have hlen : ((read.drop (j * L)).take L).take q = (read.drop (j * L)).take q := by
    rw [List.take_take, Nat.min_eq_left (by omega)]
  rw [hlen] at hword
  have hwl : ((ch.seq.drop p).take q).length = q := by
    rw [hword, List.length_take, List.length_drop]; omega
  have hfit : p + q ≤ ch.seq.length := by
    have hq : q = 25 := rfl
    rw [List.length_take, List.length_drop] at hwl; omega
  refine ⟨j, hj, p, st.1, st.2, hcg, ⟨?_, fun i hi => ?_⟩, shapes_ok _ _ st hst, h1, h2, rfl, rfl⟩
  · rw [getElem!_pos gbs c hcg, henc.1]; exact hfit
  · rw [getElem!_pos gbs c hcg]
    have e1 : ((ch.seq.drop p).take q)[i]'(by rw [hwl]; exact hi) = ch.seq[p + i]'(by omega) := by simp
    have e2 : ((read.drop (j * L)).take q)[i]'(by simp; omega) = read[j * L + i]'(by omega) := by simp
    have he : ch.seq[p + i]'(by omega) = read[j * L + i]'(by omega) := by
      rw [← e1, ← e2]; congr 1
    apply UInt8.toNat_inj.mp
    rw [henc.2 (p + i) (by omega), hr.2 (j * L + i) (by omega), he]

end MapSpec.Fast

#print axioms MapSpec.Fast.cover
