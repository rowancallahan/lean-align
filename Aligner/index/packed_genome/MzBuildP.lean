import WgPacked
import MzBuildOk

/-!
# The packed-genome and view builders pass the packed checker

* `buildWP_eq`: `Mz.buildWP P` (the builder reading a `PGen`) is `Mz.buildW` on the bytes `P` spells
  (as `buildWV_eq` for the view);
* `check3P_buildWP`: its index passes `check3P` on `P` itself, for at most `2^32 + 23` letters;
* `check3P_buildWV`: so does the view builder's, when the view spells what `P` spells.
-/

set_option linter.deprecated false

namespace MapSpec.Mz

open MapSpec.Fast (PGen Rep GV RepV)

section
variable {P : PGen} {G : ByteArray} (h : Rep P G)
include h

theorem allAP_eq (stop : Nat) : ∀ d i, stop - i = d → allAP P i stop = allA G i stop := by
  intro d
  induction d with
  | zero => intro i hd; unfold allAP allA; rw [if_neg (by omega), if_neg (by omega)]
  | succ d ih =>
    intro i hd
    unfold allAP allA
    simp only [show i < stop from by omega, if_true, h.2, ih (i + 1) (by omega)]

theorem wcGoP_eq (stop : Nat) : ∀ d i x, stop - i = d → wcGoP P i stop x = wcGo G i stop x := by
  intro d
  induction d with
  | zero => intro i x hd; unfold wcGoP wcGo; rw [if_neg (by omega), if_neg (by omega)]
  | succ d ih =>
    intro i x hd
    unfold wcGoP wcGo
    have ih' := fun x => ih (i + 1) x (by omega)
    simp only [show i < stop from by omega, if_true, h.2, ih']

theorem slotAtP_eq (ix : MzIdx) (pm hh : Nat) : slotAtP ix P pm hh = slotAt ix G pm hh := by
  simp only [slotAtP, slotAt, h.1, fun i stop => allAP_eq h stop _ i rfl, fun i stop x => wcGoP_eq h stop _ i x rfl]

theorem foldMinsP_eq {α : Type} (ix0 : MzIdx) (f : α → Nat → Nat → α) :
    ∀ d p x good last acc, G.size - p = d →
      foldMinsP ix0 P f p x good last acc = foldMinsGo ix0 G f p x good last acc := by
  intro d
  induction d with
  | zero =>
    intro p x good last acc hd
    unfold foldMinsP foldMinsGo; rw [h.1, if_neg (by omega), if_neg (by omega)]
  | succ d ih =>
    intro p x good last acc hd
    unfold foldMinsP foldMinsGo
    have ih' := fun x good last acc => ih (p + 1) x good last acc (by omega)
    simp only [h.1, show p < G.size from by omega, if_true, h.2, ih']

/-- **The builder over a packed genome is `buildW` on the bytes it spells.** -/
theorem buildWP_eq' (k B c sw t : Nat) : buildWP P k B c sw t = buildW G k B c sw t := by
  have e : ∀ {α : Type} (ix0 : MzIdx) (init : α) (f : α → Nat → Nat → α),
      foldMinsP ix0 P f 0 0 0 0 init = foldMins ix0 G init f :=
    fun ix0 init f => foldMinsP_eq h ix0 f _ 0 0 0 0 init rfl
  simp only [buildWP, buildW, h.1, h.2, e, slotAtP_eq h, panicWithPosWithDecl, panic, panicCore]

end

theorem buildWP_eq (P : PGen) (k B c sw t : Nat) : buildWP P k B c sw t = buildW (unpack P) k B c sw t :=
  buildWP_eq' (rep_unpack P) k B c sw t

/-- **The packed builder's index passes the packed checker** (`Proofs/Index.lean`'s parameters). -/
theorem check3P_buildWP (P : PGen) (hsz : P.n ≤ 2 ^ 32 + 23) (T : Nat) :
    check3P (buildWP P 22 26 0 5 6) P T = true := by
  rw [check3P_eq, check2P_eq (rep_unpack P), check2_eq, buildWP_eq]
  exact check_buildW _ (by rw [← (rep_unpack P).1]; exact hsz)

/-- The view builder's index passes the packed checker when the view spells what `P` spells. -/
theorem check3P_buildWV (P : PGen) (V : GV) (hV : RepV V (unpack P)) (hsz : P.n ≤ 2 ^ 32 + 23) (T : Nat) :
    check3P (buildWV V 22 26 0 5 6) P T = true := by
  rw [check3P_eq, check2P_eq (rep_unpack P), check2_eq, buildWV_eq V _ hV]
  exact check_buildW _ (by rw [← (rep_unpack P).1]; exact hsz)

end MapSpec.Mz

#print axioms MapSpec.Mz.check3P_buildWP
#print axioms MapSpec.Mz.check3P_buildWV
