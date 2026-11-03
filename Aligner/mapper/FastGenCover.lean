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

end MapSpec.Fast

