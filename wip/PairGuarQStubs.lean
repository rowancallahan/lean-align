import PairGuarQ

/-!
# Open lemmas of `pairGQ` (work split; outside codecs/ and the lakefile roots: check.sh scans codecs/*.lean)

Statements are fixed; bodies `sorry` until proved, then they move into `codecs/PairGuarQ.lean`.
(b) word reject; (c1) the fold / `goP` invariant; (c2) the two phases; (c3) answer = best pair;
(d) the final theorem.
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec MapSpec.Packed

/-! ## (b) The word reject -/

/-- (b1) A rejected start: the kernel answers `lim + 1`. -/
theorem rejW_ker (R : ByteArray) (pgs2 : Array PGen) (c st lim : Nat) (hl : lim ≤ 15)
    (h : rejW R (packRP R) pgs2[c]! st lim = true) :
    kerHKG R (packRP R) pgs2 pgs2 c st R.size lim = lim + 1 := by
  sorry

/-- (b2) The scan with the reject lists what `partnerK` lists. -/
theorem pscanQ_eq (pgs2 : Array PGen) (RY : ByteArray) (sl lo hi lim : Nat) (hl : lim ≤ 15) (x : Placement) :
    pscanQ pgs2 RY (revCompK RY) (packRP RY) (packRP (revCompK RY)) sl lo hi lim x =
      partnerK pgs2 RY (revCompK RY) (packRP RY) (packRP (revCompK RY)) sl lo hi lim x := by
  sorry

/-! ## (c1) The fold -/

theorem stepP_inv (dc : Nat → Nat) (D : List PairHit) (s : Option PairHit × Bool) (p : PairHit)
    (h : InvQ dc D s) : InvQ dc (D ++ [p]) (stepP dc s p) := by
  sorry

theorem foldP_inv (dc : Nat → Nat) (l : List PairHit) :
    ∀ (D : List PairHit) (s : Option PairHit × Bool), InvQ dc D s → InvQ dc (D ++ l) (l.foldl (stepP dc) s) := by
  sorry

/-- (c1) `goP`: the pairs folded (`D'`) are pairs of `xs`; every pair of `xs` is folded unless the
result stops at `U`. -/
theorem goP_spec (dc : Nat → Nat) (f : Placement × Int → List PairHit) (U : Int) :
    ∀ (xs : List (Placement × Int)) (D : List PairHit) (s : Option PairHit × Bool), InvQ dc D s →
      ∃ D', InvQ dc (D ++ D') (goP dc f U xs s) ∧ (∀ p ∈ D', ∃ x ∈ xs, p ∈ f x) ∧
        ∀ x ∈ xs, ∀ p ∈ f x, p ∈ D' ∨ stopP dc U (goP dc f U xs s) = true := by
  sorry

/-! ## (c2) The two phases -/

/-- (c2) Phase 0 (bound 0) then phase 1 (bound `U1 ≤ 0`): every pair is folded, or lies below a
bound at which the result stops. -/
theorem goP2_spec (dc : Nat → Nat) (f : Placement × Int → List PairHit) (U1 : Int) (hU : U1 ≤ 0)
    (l0 l1 : List (Placement × Int))
    (h0 : ∀ x ∈ l0, ∀ p ∈ f x, pairScoreD dc p ≤ 0) (h1 : ∀ x ∈ l1, ∀ p ∈ f x, pairScoreD dc p ≤ U1) :
    ∃ D, InvQ dc D (goP dc f U1 l1 (goP dc f 0 l0 (none, false))) ∧
      (∀ p ∈ D, ∃ x ∈ l0 ++ l1, p ∈ f x) ∧
      ∀ x ∈ l0 ++ l1, ∀ p ∈ f x, p ∈ D ∨
        ∃ U, pairScoreD dc p ≤ U ∧ stopP dc U (goP dc f U1 l1 (goP dc f 0 l0 (none, false))) = true := by
  sorry

/-! ## (c3) The answer -/

/-- (c3) The pairs at score `≥ W` are `All`; those folded (`D`) are among them, the others lie below a
bound where the fold stopped.  Then a pair was found iff one exists, and the answer
(`none` on a tie) is `bestPairD`. -/
theorem ansOk (dc : Nat → Nat) (sl lo hi : Nat) (h1 h2 : List (Placement × Int)) (f1 : ScoreFun h1)
    (f2 : ScoreFun h2) (W : Int) (All : List PairHit)
    (hA : ∀ p, p ∈ All ↔ p ∈ properPairs sl lo hi h1 h2 ∧ W ≤ pairScoreD dc p)
    (D : List PairHit) (s : Option PairHit × Bool) (hI : InvQ dc D s) (hD : ∀ p ∈ D, p ∈ All)
    (hrest : ∀ p ∈ All, p ∈ D ∨ ∃ U, pairScoreD dc p ≤ U ∧ stopP dc U s = true) :
    (s.1.isSome = true ↔ ∃ w ∈ properPairs sl lo hi h1 h2, W ≤ pairScoreD dc w) ∧
      (s.1.isSome = true → (if s.2 then none else s.1) = bestPairD dc sl lo hi h1 h2) := by
  sorry

/-! ## (d) The theorem -/

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
  sorry

theorem pairGQ_some (dc : Nat → Nat) (sl lo hi Gc : Nat) (swap : Bool) (ix : PkMzR) (offs : Array Nat)
    (pgs : Array PGen) (R1 R2 : ByteArray) (h : fastT Gc (if swap then R2 else R1) = true) :
    ∃ v, pairGQ dc sl lo hi Gc swap ix offs pgs R1 R2 = some v := by
  sorry

end top

end MapSpec.Fast
