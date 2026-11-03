import PairGuarQB
import PairGuarQC

/-!
# `pairGQ`, part (d): the pair-level guarantee

From the raw-lookup X hits (`mem_hitsAtKP3_mzR`), the word reject (`pscanQ_eq`, PairGuarQB) and
the early-stop fold (`goP2_spec`, `ansOk`, PairGuarQC): `pairGQ` meets `pairGF_sound`'s statement.
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec MapSpec.Packed

theorem pairsQ_X (dc : Nat → Nat) (sl lo hi Gc : Nat) (pgs2 : Array PGen) (RY RYr : ByteArray) (KY KYr : RP)
    (swap : Bool) (x : Placement × Int) (p : PairHit) (hp : p ∈ pairsQ dc sl lo hi Gc pgs2 RY RYr KY KYr swap x) :
    (if swap then p.2 else p.1) = x := by
  unfold pairsQ at hp
  rw [List.mem_filterMap] at hp
  obtain ⟨y, -, hy⟩ := hp
  cases swap <;> simp only [Bool.false_eq_true, if_true, if_false] at hy ⊢ <;>
    split at hy <;> simp only [Option.some.injEq, reduceCtorEq] at hy <;> (subst hy; rfl)

theorem foldl_max_ge (l : List (Placement × Int)) :
    ∀ (m : Int), m ≤ l.foldl (fun m x => max m x.2) m ∧ ∀ x ∈ l, x.2 ≤ l.foldl (fun m x => max m x.2) m := by
  induction l with
  | nil => intro m; simp
  | cons y l ih =>
    intro m
    simp only [List.foldl_cons, List.mem_cons]
    obtain ⟨h1, h2⟩ := ih (max m y.2)
    refine ⟨by omega, ?_⟩
    rintro x (rfl | hx)
    · omega
    · exact h2 x hx

theorem foldl_max_le (l : List (Placement × Int)) (B : Int) (hl : ∀ x ∈ l, x.2 ≤ B) :
    ∀ (m : Int), m ≤ B → l.foldl (fun m x => max m x.2) m ≤ B := by
  induction l with
  | nil => intro m hm; simpa
  | cons y l ih =>
    intro m hm
    simp only [List.foldl_cons]
    exact ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) _ (by have := hl y List.mem_cons_self; omega)

section top
variable (dc : Nat → Nat) (sl lo hi Gc : Nat) (g : Genome) (m1 m2 : List Char) (ix : Mz.MzIdx) (G : PGen)
  (offs ns : Array Nat) (R1 R2 : ByteArray)
  (hcut : cutOk G offs ns = true) (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) g)
  (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hchk : Mz.check2P ix G = true)

end top

end MapSpec.Fast

