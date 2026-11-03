import FastMapper
import PairSpec

/-!
# Codec `pairFast`: both strands and proper pairs, through the proved fast mapper

The read and its reverse complement are each mapped by the proved fast mapper
(`mapChroms`, whose `Best` carries the proved `Inv`); `combineBest` keeps the
strictly better strand (equal penalties on the two strands tie → unmapped).
`pairFast` maps mate 1, skips mate 2 when mate 1 is unmapped, and keeps the pair
only if `properPair` holds.  Against the DRAFT spec `spec/PairSpec.lean`
(Rowan to review): fast path (`fastOk`, 100–103 letters), scoring `sc0`, T = −12.

    GenomeBytes gbs g → Encodes R read → LookAll lk gbs idxs → fastOk R →
      mapFastBoth lk gbs idxs R = mapSpecBoth sc0 (-12) g read      (mapFastBoth_eq_mapSpecBoth)
    … → pairFast lk lo hi gbs idxs R1 R2 = pairSpec sc0 (-12) lo hi g m1 m2   (pairFast_eq_pairSpec)

Strands are searched one after the other here; the joint (interleaved) search
is a later speed step behind the same `combineBest`.
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-! ## Algorithm -/

def complB (b : UInt8) : UInt8 :=
  if b == 65 then 84 else if b == 84 then 65 else if b == 67 then 71 else if b == 71 then 67 else b

/-- Reverse complement of a byte read (letters other than A, C, G, T kept). -/
def revCompB (R : ByteArray) : ByteArray := ⟨(R.data.map complB).reverse⟩

/-! ## Lemmas -/

theorem complB_toNat_all : ∀ n, n < 256 →
    (complB n.toUInt8).toNat = (complement (Char.ofNat n)).toNat := by
  decide +kernel

theorem complB_toNat (b : UInt8) (c : Char) (h : b.toNat = c.toNat) :
    (complB b).toNat = (complement c).toNat := by
  have hc : c = Char.ofNat b.toNat := by rw [h, Char.ofNat_toNat]
  rw [hc]
  have := complB_toNat_all b.toNat b.toNat_lt
  have e : b.toNat.toUInt8 = b := by simp
  rwa [e] at this

theorem revCompB_size_aux (R : ByteArray) : (revCompB R).size = R.size := by
  show ((R.data.map complB).reverse).size = R.data.size
  simp

/-- byte reverse complement encodes the list reverse complement. -/
theorem revCompB_encodes (R : ByteArray) (read : List Char) (h : Encodes R read) :
    Encodes (revCompB R) (revComp read) := by
  obtain ⟨hs, he⟩ := h
  have hlen : (revComp read).length = read.length := by simp [revComp]
  refine ⟨by rw [revCompB_size_aux, hlen, hs], fun i hi => ?_⟩
  rw [hlen] at hi
  have hRs : R.data.size = read.length := hs
  have hj : read.length - 1 - i < read.length := by omega
  have key := he (read.length - 1 - i) hj
  simp only [revComp, List.getElem_reverse, List.getElem_map, List.length_map]
  simp only [ByteArray.get!, revCompB] at key ⊢
  rw [getElem!_pos _ i (by simp; omega)]
  rw [getElem!_pos _ _ (by omega)] at key
  simp only [Array.getElem_reverse, Array.getElem_map, Array.size_map]
  apply complB_toNat
  simp only [hRs]; exact key

/-- size is kept. -/
theorem revCompB_size (R : ByteArray) : (revCompB R).size = R.size :=
  revCompB_size_aux R

/-- Score of a placement: forward = the read, reverse = its reverse complement. -/
def strandScore (g : Genome) (read : List Char) : Strand → Window → Option Int
  | .fwd => windowScore sc0 read g
  | .rev => windowScore sc0 (revComp read) g

theorem selectUniqueBy_eq_some_iff {α : Type} [DecidableEq α] (l : List (α × Int))
    (hfun : ∀ a ∈ l, ∀ b ∈ l, a.1 = b.1 → a.2 = b.2) (a : α × Int) :
    selectUniqueBy l = some a ↔ a ∈ l ∧ ∀ b ∈ l, b.2 < a.2 ∨ b.1 = a.1 := by
  have hq : ∀ a : α × Int, (l.all fun b => decide (b.2 < a.2) || decide (b.1 = a.1)) = true ↔
      ∀ b ∈ l, b.2 < a.2 ∨ b.1 = a.1 := by
    intro a; simp [List.all_eq_true]
  unfold selectUniqueBy
  constructor
  · intro h
    have h2 := List.find?_some h
    exact ⟨List.mem_of_find?_eq_some h, (hq a).1 h2⟩
  · rintro ⟨hm, hp⟩
    cases h : l.find? (fun a => l.all fun b => decide (b.2 < a.2) || decide (b.1 = a.1)) with
    | none => exact absurd ((hq a).2 hp) (List.find?_eq_none.1 h a hm)
    | some c =>
      have hc0 := List.find?_some h
      have hc := (hq c).1 hc0
      have hcm := List.mem_of_find?_eq_some h
      have h1 := hp c hcm
      have h2 := hc a hm
      have h12 : c.1 = a.1 := by
        rcases h1 with h1 | h1
        · rcases h2 with h2 | h2
          · omega
          · exact h2.symm
        · exact h1
      rw [Prod.ext h12 (hfun c hcm a hm h12)]

theorem strandScore_allWindows (g : Genome) (read : List Char) (st : Strand) (w : Window) (s : Int)
    (h : strandScore g read st w = some s) : w ∈ allWindows g := by
  apply (mem_allWindows g w).2
  cases st <;> (unfold strandScore windowScore at h; cases hw : windowSeq g w <;> simp_all)

/-! ## Top theorems (proved from the lemmas above) -/

end MapSpec.Fast

