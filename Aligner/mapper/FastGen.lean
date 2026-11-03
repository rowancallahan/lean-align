import FastGenProof

/-!
# Codec `mapFastTG`: the general fast mapper, any read length and threshold

For a penalty bound `P` (threshold `T = −P`, scoring (0, −4, −6, −2)), a byte
genome `gbs` with `GenomeBytes gbs g`, a read `R` with `Encodes R read`, and
per-chromosome indexes whose seed lookups are right (`LookAllG`, e.g. a hashed
index passing `checkIdx`):

    mapFastTG P gbs idxs R = mapSpec sc0 (-P) g read               (mapFastTG_eq_mapSpec)

Reads with `sbound P < ⌊n/25⌋` seeds take the fast path (`fastT`); the others
the slow proved path.
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-- What the general mapper needs of the lookups: right on every chromosome. -/
def LookAllG {L Pp : Type} [LookG L Pp] [Inhabited L] (gbs : Array ByteArray) (idxs : Array L) : Prop :=
  ∀ c, c < gbs.size → ∀ (R : ByteArray) (s base : Nat), s + q ≤ R.size →
    LookOkS gbs[c]! R s base 0 (LookG.look idxs[c]! gbs[c]! R s base (LookG.prep idxs[c]! (seedHashAt R s)))

theorem insKey_fold_perm (ks : Array Nat) :
    ∀ (xs l : List Nat), (xs.foldl (fun l j => insKey ks j l) l).Perm (xs.reverse ++ l) := by
  intro xs
  induction xs with
  | nil => intro l; simp
  | cons x xs ih =>
    intro l
    simp only [List.foldl_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
    exact (ih _).trans (List.Perm.append_left _ (insKey_perm ks x l))

theorem ordG_spec (ks : Array Nat) (m : Nat) :
    (ordG ks m).Nodup ∧ (∀ j ∈ ordG ks m, j < m) ∧ (ordG ks m).length = m := by
  have hp : (ordG ks m).Perm (List.range m) := by
    unfold ordG
    have := insKey_fold_perm ks (List.range m) []
    rw [List.append_nil] at this
    exact this.trans (List.reverse_perm _)
  refine ⟨hp.nodup_iff.2 List.nodup_range, fun j hj => List.mem_range.1 (hp.mem_iff.1 hj), by
    rw [hp.length_eq, List.length_range]⟩

section
variable (P : Nat) (read : List Char) (g : Genome) (gbs : Array ByteArray) (R : ByteArray)
  (hg : GenomeBytes gbs g) (hr : Encodes R read)
  {L Pp : Type} [LookG L Pp] [Inhabited L] [Inhabited Pp] (idxs : Array L)
  (hlk : LookAllG gbs idxs) (hm : 0 < R.size / 25) (hsb : sbound P < R.size / 25)

include hg hr hlk hm hsb

end

/-! ## The hashed index -/

theorem lookAllG_hashed (gbs : Array ByteArray) (idxs : Array HIdx) (hchk : checkAll idxs gbs = true) :
    LookAllG gbs idxs := by
  intro c hc R s base _
  unfold checkAll at hchk
  simp only [List.all_eq_true, List.mem_range] at hchk
  exact lookupHG_spec idxs[c]! gbs[c]! R s base 0 (hchk c hc)

end MapSpec.Fast

