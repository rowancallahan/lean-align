import AlignmentWfaOffR

namespace AlignmentSpec

/-- Four-character unrolling, with the existing scalar loop for the last block. -/
def lcpChunk (xa ya : Array Char) (fuel i j acc : Nat) : Nat :=
  if h : 4 ≤ fuel ∧ i + 3 < xa.size ∧ j + 3 < ya.size then
    if xa[i]'(by omega) = ya[j]'(by omega) ∧
        xa[i+1]'(by omega) = ya[j+1]'(by omega) ∧
        xa[i+2]'(by omega) = ya[j+2]'(by omega) ∧
        xa[i+3]'(by omega) = ya[j+3]'(by omega) then
      lcpChunk xa ya (fuel - 4) (i + 4) (j + 4) (acc + 4)
    else lcpArrGo xa ya fuel i j acc
  else lcpArrGo xa ya fuel i j acc
termination_by fuel

theorem lcpChunk_eq (xa ya : Array Char) (fuel : Nat) :
    ∀ i j acc, lcpChunk xa ya fuel i j acc = lcpArrGo xa ya fuel i j acc := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro i j acc
    rw [lcpChunk]
    split
    · rename_i hbounds
      split
      · rename_i heq
        rw [ih (fuel - 4) (by omega)]
        obtain ⟨h0, h1, h2, h3⟩ := heq
        obtain ⟨f, hf⟩ : ∃ f, fuel = f + 4 := ⟨fuel - 4, by omega⟩
        subst fuel
        simp only [Nat.add_sub_cancel]
        have hb0 : i < xa.size ∧ j < ya.size := by omega
        have hb1 : i+1 < xa.size ∧ j+1 < ya.size := by omega
        have hb2 : i+2 < xa.size ∧ j+2 < ya.size := by omega
        have hb3 : i+3 < xa.size ∧ j+3 < ya.size := by omega
        simp only [lcpArrGo, hb0, hb1, hb2, hb3, h0, h1, h2, h3, if_pos,
          Nat.add_assoc, Nat.reduceAdd]
        simp
      · rfl
    · rfl

@[inline] def extChunkR (m : Nat) (xa ya : Array Char) (t a : Nat) : Nat :=
  if a = 0 then 0 else
    let off := a - 1
    off + lcpChunk xa ya (xa.size - off) off (joffOf m t off) 0 + 1

theorem extChunkR_eq (m : Nat) (xa ya : Array Char) (t a : Nat) :
    extChunkR m xa ya t a = extR m xa ya t a := by
  simp only [extChunkR, extR, lcpArr, lcpChunk_eq]

end AlignmentSpec
#print axioms AlignmentSpec.extChunkR_eq
