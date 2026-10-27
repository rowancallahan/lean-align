import FastMapperMz

/-!
# Codec `checkAllMzPar`: the minimizer-index checker on several cores

* `Mz.check3 ix G P`: `Mz.check2` with the per-entry pass (`checkSound`) cut
  into `P` bucket ranges, each in its own `Task` (`check3_eq`: `= check`).
* `checkAllMzPar P idxs gbs`: one task per chromosome running `check3 … P`
  (`checkAllMzPar_eq`: `= checkAllMz`), so every theorem about `checkAllMz`
  (`mapFastMz_eq_mapSpec`, …) holds for it.

In Lean's logic `(Task.spawn fn).get = fn ()`; the proofs only cut and
re-join the conjunctions.
-/

namespace MapSpec.Mz

theorem checkSound_add (ix : MzIdx) (G : ByteArray) :
    ∀ a b s, checkSound ix G (a + b) s = (checkSound ix G a s && checkSound ix G b (s + a)) := by
  intro a
  induction a with
  | zero => intro b s; simp [checkSound]
  | succ a ih =>
    intro b s
    rw [show a + 1 + b = (a + b) + 1 by omega, checkSound, checkSound, ih, Bool.and_assoc,
      show s + 1 + a = s + (a + 1) by omega]

/-- Buckets `[j·ch, min((j+1)·ch, N))`. -/
@[inline] def soundChunk (ix : MzIdx) (G : ByteArray) (ch N j : Nat) : Bool :=
  checkSound ix G (min ((j + 1) * ch) N - j * ch) (j * ch)

theorem soundChunks (ix : MzIdx) (G : ByteArray) (ch N : Nat) :
    ∀ P, (List.range P).all (soundChunk ix G ch N) = checkSound ix G (min (P * ch) N) 0 := by
  intro P
  induction P with
  | zero => simp [checkSound]
  | succ P ih =>
    rw [List.range_succ, List.all_append, ih, List.all_cons, List.all_nil, Bool.and_true]
    unfold soundChunk
    by_cases h : P * ch < N
    · rw [Nat.min_eq_left (Nat.le_of_lt h)]
      conv => rhs; rw [show min ((P + 1) * ch) N = P * ch + (min ((P + 1) * ch) N - P * ch) by
        rw [Nat.succ_mul]; omega]
      rw [checkSound_add, Nat.zero_add]
    · rw [Nat.min_eq_right (by omega), show min ((P + 1) * ch) N = N by
        rw [Nat.min_eq_right]; rw [Nat.succ_mul]; omega, show N - P * ch = 0 by omega]
      simp [checkSound]

/-- `checkSound` over all `2^B` buckets with `P` tasks. -/
def checkSoundPar (ix : MzIdx) (G : ByteArray) (P : Nat) : Bool :=
  let N := 2 ^ ix.B
  let P := max P 1
  let ch := (N + P - 1) / P
  let tasks := (List.range P).map fun j =>
    Task.spawn (prio := .dedicated) fun _ => soundChunk ix G ch N j
  tasks.all (·.get)

theorem checkSoundPar_eq (ix : MzIdx) (G : ByteArray) (P : Nat) :
    checkSoundPar ix G P = checkSound ix G (2 ^ ix.B) 0 := by
  unfold checkSoundPar
  dsimp only
  rw [List.all_map]
  show (List.range (max P 1)).all (soundChunk ix G ((2 ^ ix.B + max P 1 - 1) / max P 1) (2 ^ ix.B)) = _
  rw [soundChunks]
  congr 1
  apply Nat.min_eq_right
  have hp : 0 < max P 1 := by omega
  have := Nat.div_mul_le_self (2 ^ ix.B + max P 1 - 1) (max P 1)
  have h2 := Nat.lt_mul_div_succ (2 ^ ix.B + max P 1 - 1) hp
  rw [Nat.mul_add, Nat.mul_one] at h2
  omega

/-- `check2` with the per-entry pass on `P` tasks. -/
def check3 (ix : MzIdx) (G : ByteArray) (P : Nat) : Bool :=
  checkParams ix && checkSoundPar ix G P &&
    (let s := rollTo G (q - 1); compR ix G ix.offs 0 (G.size + 1 - q) 0 s.1 s.2) &&
    checkRuns ix G ix.nr 0 && checkCover ix G 0 G.size 0

theorem check3_eq (ix : MzIdx) (G : ByteArray) (P : Nat) : check3 ix G P = check ix G := by
  rw [← check2_eq]
  unfold check3 check2
  rw [checkSoundPar_eq]

end MapSpec.Mz

namespace MapSpec.Fast

/-- One task per chromosome, each checking with `P` tasks for its entries. -/
def checkAllMzPar (P : Nat) (idxs : Array Mz.MzIdx) (gbs : Array ByteArray) : Bool :=
  let tasks := (List.range gbs.size).map fun c =>
    Task.spawn (prio := .dedicated) fun _ => Mz.check3 idxs[c]! gbs[c]! P
  tasks.all (·.get)

theorem checkAllMzPar_eq (P : Nat) (idxs : Array Mz.MzIdx) (gbs : Array ByteArray) :
    checkAllMzPar P idxs gbs = checkAllMz idxs gbs := by
  unfold checkAllMzPar checkAllMz
  rw [List.all_map]
  simp only [Function.comp_def, Mz.check3_eq, Mz.check2_eq]
  rfl

end MapSpec.Fast

#print axioms MapSpec.Mz.check3_eq
#print axioms MapSpec.Fast.checkAllMzPar_eq
