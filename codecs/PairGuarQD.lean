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

include hcut hg h1 h2 hchk in
/-- (d) **The early-stop fast guarantee is the specification** (`pairGF_sound`'s statement). -/
theorem pairGQ_sound (hG : Gc ≤ 7) (swap : Bool) (P1 P2 : Nat) (hP1 : Gc ≤ P1) (hP2 : Gc ≤ P2)
    (r : Option PairHit) (seen : Bool) (lX : List (Placement × Int))
    (h : pairGQ dc sl lo hi Gc swap (PkMzR.mk ix G) offs (cutAll G offs ns) R1 R2 = some (r, seen, lX)) :
    (∀ x, x ∈ lX ↔ x ∈ hitsBoth sc0 (-(Gc : Int)) g (if swap then m2 else m1)) ∧
    (seen = true ↔ ∃ w ∈ properPairs sl lo hi (hitsBoth sc0 (-(P1 : Int)) g m1) (hitsBoth sc0 (-(P2 : Int)) g m2),
      -(Gc : Int) ≤ pairScoreD dc w) ∧
    (seen = true → r = pairSpecUT sc0 dc sl lo hi (-(P1 : Int)) (-(P2 : Int)) g m1 m2) ∧
    (seen = true → r = none → PairTieOk dc sl lo hi (-(P1 : Int)) (-(P2 : Int)) g m1 m2) := by
  cases hl : hitsAtKP3 Gc (PkMzR.mk ix G) ByteArray.empty offs (cutAll G offs ns) (if swap then R2 else R1) with
  | none => simp only [pairGQ, hl, reduceCtorEq] at h
  | some lX' =>
    simp only [pairGQ, hl, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hrX : Encodes (if swap then R2 else R1) (if swap then m2 else m1) := by cases swap <;> simpa
    have hrY : Encodes (if swap then R1 else R2) (if swap then m1 else m2) := by cases swap <;> simpa
    have hX := mem_hitsAtKP3_mzR Gc (by omega) g _ ix G offs ns _ hcut hg hrX hchk lX' hl
    generalize hRY : (if swap then R1 else R2) = RY at hrY ⊢
    generalize hpg : cutAll G offs ns = pgs at hg ⊢
    have HP := mem_pairsGF g pgs hg dc sl lo hi Gc hG m1 m2 swap RY hrY lX' hX P1 P2 hP1 hP2
    generalize hf : pairsQ dc sl lo hi Gc (pgs ++ pgs) RY (revCompK RY) (packRP RY) (packRP (revCompK RY)) swap = f
    have hAll : pairsGF dc sl lo hi Gc (pgs ++ pgs) RY (revCompK RY) (packRP RY) (packRP (revCompK RY)) swap lX' =
        lX'.flatMap f := by
      rw [← hf]
      unfold pairsGF pairsQ
      congr 1
      funext x
      rw [pscanQ_eq _ _ _ _ _ _ (by omega)]
    rw [hAll] at HP
    generalize hh1 : hitsBoth sc0 (-(P1 : Int)) g m1 = H1 at HP
    generalize hh2 : hitsBoth sc0 (-(P2 : Int)) g m2 = H2 at HP
    have hn1 : ∀ x ∈ H1, x.2 ≤ 0 := by rw [← hh1]; exact hitsBoth_nonpos _ _ _
    have hn2 : ∀ x ∈ H2, x.2 ≤ 0 := by rw [← hh2]; exact hitsBoth_nonpos _ _ _
    -- a pair of `x` scores at most `x.2`
    have hsc : ∀ x ∈ lX', ∀ p ∈ f x, pairScoreD dc p ≤ x.2 := by
      intro x hx p hp
      have hpa := (HP p).1 (List.mem_flatMap.2 ⟨x, hx, hp⟩)
      have hX' : (if swap then p.2 else p.1) = x := by rw [← hf] at hp; exact pairsQ_X _ _ _ _ _ _ _ _ _ _ _ _ _ hp
      rw [mem_properPairs] at hpa
      have e1 := hn1 _ hpa.1.1
      have e2 := hn2 _ hpa.1.2.1
      have hd : (0 : Int) ≤ (dc (fragLen p.1.1 p.2.1) : Int) := Int.natCast_nonneg _
      unfold pairScoreD
      cases swap
      · simp only [Bool.false_eq_true, if_false] at hX'; subst hX'; omega
      · simp only [if_true] at hX'; subst hX'; omega
    have hxn : ∀ x ∈ lX', x.2 ≤ 0 := fun x hx => by
      have := (hX x).1 hx; exact hitsBoth_nonpos _ _ _ x this
    generalize hl0 : lX'.filter (fun x => decide (x.2 = 0)) = l0
    generalize hl1 : lX'.filter (fun x => !decide (x.2 = 0)) = l1
    have hm0 : ∀ x ∈ l0, x ∈ lX' ∧ x.2 = 0 := fun x hx => by
      rw [← hl0, List.mem_filter] at hx; exact ⟨hx.1, by simpa using hx.2⟩
    have hm1 : ∀ x ∈ l1, x ∈ lX' := fun x hx => by
      rw [← hl1, List.mem_filter] at hx; exact hx.1
    have hcov : ∀ x ∈ lX', x ∈ l0 ++ l1 := fun x hx => by
      rw [List.mem_append, ← hl0, ← hl1, List.mem_filter, List.mem_filter]
      by_cases h0 : x.2 = 0
      · exact Or.inl ⟨hx, by simp [h0]⟩
      · exact Or.inr ⟨hx, by simp [h0]⟩
    generalize hU : l1.foldl (fun m x => max m x.2) (-(Gc : Int)) = U1
    have hU0 : U1 ≤ 0 := by
      rw [← hU]; exact foldl_max_le l1 0 (fun x hx => hxn x (hm1 x hx)) _ (by omega)
    have hU1 : ∀ x ∈ l1, x.2 ≤ U1 := by rw [← hU]; exact (foldl_max_ge l1 _).2
    obtain ⟨D, hI, hD, hrest⟩ := goP2_spec dc f U1 hU0 l0 l1
      (fun x hx p hp => by have := hsc x (hm0 x hx).1 p hp; have := (hm0 x hx).2; omega)
      (fun x hx p hp => by have := hsc x (hm1 x hx) p hp; have := hU1 x hx; omega)
    generalize hs : goP dc f U1 l1 (goP dc f 0 l0 (none, false)) = s at hI hrest
    have hA := ansOk dc sl lo hi H1 H2 (by rw [← hh1]; exact hitsBoth_scoreFun _ _ _ _)
      (by rw [← hh2]; exact hitsBoth_scoreFun _ _ _ _) (-(Gc : Int)) (lX'.flatMap f) HP D s hI
      (fun p hp => by
        obtain ⟨x, hx, hpx⟩ := hD p hp
        rw [List.mem_append] at hx
        exact List.mem_flatMap.2 ⟨x, by rcases hx with hx | hx; exact (hm0 x hx).1; exact hm1 x hx, hpx⟩)
      (fun p hp => by
        obtain ⟨x, hx, hpx⟩ := List.mem_flatMap.1 hp
        exact hrest x (hcov x hx) p hpx)
    unfold pairSpecUT PairTieOk pairSpecUT
    rw [hh1, hh2]
    refine ⟨hX, hA.1, hA.2, fun hsn hr => ⟨by rw [← hA.2 hsn]; exact hr, ?_⟩⟩
    obtain ⟨w, hw, -⟩ := hA.1.1 hsn
    exact ⟨w, hw⟩

theorem pairGQ_some (dc : Nat → Nat) (sl lo hi Gc : Nat) (swap : Bool) (ix : PkMzR) (offs : Array Nat)
    (pgs : Array PGen) (R1 R2 : ByteArray) (h : fastT Gc (if swap then R2 else R1) = true) :
    ∃ v, pairGQ dc sl lo hi Gc swap ix offs pgs R1 R2 = some v := by
  obtain ⟨l, hl⟩ := hitsAtKP3_some Gc ix ByteArray.empty offs pgs _ h
  unfold pairGQ
  simp only [hl]
  exact ⟨_, rfl⟩

end top

end MapSpec.Fast

#print axioms MapSpec.Fast.pairGQ_sound
#print axioms MapSpec.Fast.pairGQ_some
