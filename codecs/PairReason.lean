import PairRegion

/-!
# Why a pair is not reported: reasons, proved against the specification

`pairSpecT T1 T2 lo hi g m1 m2` (codecs/PairDispatch.lean) is `none` for several
different reasons.  A pass kernel (codecs/PairRouter.lean) reports which one, and each
reason is a statement about the specification alone (`ReasonOk`):

* `noHit m`     — mate `m` has no hit within its cap: `hitsBoth` is empty;
* `tie m`       — mate `m` has hits, but no unique best (`selectUniqueBy` gives `none`);
* `noPartner m` — the other mate maps uniquely to `a`, and no hit of mate `m` within its
                  cap forms a proper pair with `a` (what the region search proves without
                  searching mate `m` over the whole genome);
* `notProper`   — both mates map uniquely, but not as a proper pair;
* `tooShort m` / `trimmedAway m` — mate `m` is outside the mapper's length range at its
                  cap / was removed by the trimmer (stated by the router, not here).

Every search reason implies `pairSpecT … = none` (`reasonOk_none`).

Deeper caps (`T' ≤ T`): a read with a hit at `T` has the same answer at `T'`
(`mapSpecBoth_mono`): new hits are all worse than the old best.  So `tie` and
`notProper` stay at any deeper cap (`reasonOk_tie_mono`, `reasonOk_notProper_mono`);
only `noHit`, `noPartner` (and length reasons) can change, and only they need a deeper
pass.
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-- A mate of a pair. -/
inductive Mate where
  | one
  | two
deriving DecidableEq, Repr, Inhabited

def Mate.other : Mate → Mate
  | .one => .two
  | .two => .one

/-- Why a pair is not reported. -/
inductive Reason where
  | trimmedAway (m : Mate)
  | tooShort (m : Mate)
  | noHit (m : Mate)
  | tie (m : Mate)
  | noPartner (m : Mate)
  | notProper
deriving DecidableEq, Repr, Inhabited

/-- The reasons a search decides (all but the length reasons). -/
def Reason.searched : Reason → Bool
  | .trimmedAway _ => false
  | .tooShort _ => false
  | _ => true

/-- What a search reason says about the specification, with threshold `T m` and read
`rd m` for mate `m`. -/
def ReasonOk (T : Mate → Int) (lo hi : Nat) (g : Genome) (rd : Mate → List Char) : Reason → Prop
  | .noHit m => hitsBoth sc0 (T m) g (rd m) = []
  | .tie m => hitsBoth sc0 (T m) g (rd m) ≠ [] ∧ mapSpecBoth sc0 (T m) g (rd m) = none
  | .noPartner m => ∃ a, mapSpecBoth sc0 (T m.other) g (rd m.other) = some a ∧
      ∀ p ∈ hitsBoth sc0 (T m) g (rd m), properPair lo hi a.1 p.1 = false
  | .notProper => ∃ a b, mapSpecBoth sc0 (T .one) g (rd .one) = some a ∧
      mapSpecBoth sc0 (T .two) g (rd .two) = some b ∧ properPair lo hi a.1 b.1 = false
  | .tooShort _ => False
  | .trimmedAway _ => False

/-- Thresholds / reads of the two mates as functions of `Mate`. -/
@[reducible] def Mate.sel {α : Type} (x1 x2 : α) : Mate → α
  | .one => x1
  | .two => x2

/-! ## Basic facts -/

theorem mapSpecBoth_mem {T : Int} {g : Genome} {r : List Char} {a : Placement × Int}
    (h : mapSpecBoth sc0 T g r = some a) : a ∈ hitsBoth sc0 T g r := by
  unfold mapSpecBoth selectUniqueBy at h
  exact List.mem_of_find?_eq_some h

theorem hitsBoth_nil_none {T : Int} {g : Genome} {r : List Char} (h : hitsBoth sc0 T g r = []) :
    mapSpecBoth sc0 T g r = none := by
  unfold mapSpecBoth; rw [h]; rfl

/-- **Deeper caps.**  A read with a hit at `T` maps the same at any `T' ≤ T`. -/
theorem mapSpecBoth_mono (T T' : Int) (hT : T' ≤ T) (g : Genome) (r : List Char)
    (h : hitsBoth sc0 T g r ≠ []) : mapSpecBoth sc0 T' g r = mapSpecBoth sc0 T g r := by
  obtain ⟨⟨p0, s0⟩, hm0⟩ := List.exists_mem_of_ne_nil _ h
  rw [mem_hitsBoth_T] at hm0
  obtain ⟨-, hs0, hT0⟩ := hm0
  apply Option.ext
  rintro ⟨p, s⟩
  rw [mapSpecBoth_iffT, mapSpecBoth_iffT]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have hs : T ≤ s := by
      rcases h3 p0 s0 hs0 (by omega) with h4 | h4
      · omega
      · subst h4; rw [h1] at hs0; simp only [Option.some.injEq] at hs0; omega
    exact ⟨⟨h1, hs⟩, fun p' s' h4 h5 => h3 p' s' h4 (by omega)⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨h1, by omega⟩, fun p' s' h4 h5 => ?_⟩
    by_cases h6 : T ≤ s'
    · exact h3 p' s' h4 h6
    · left; omega

theorem hitsBoth_ne_of_some {T : Int} {g : Genome} {r : List Char} {a : Placement × Int}
    (h : mapSpecBoth sc0 T g r = some a) : hitsBoth sc0 T g r ≠ [] := by
  intro hn; rw [hitsBoth_nil_none hn] at h; cases h

theorem mapSpecBoth_mono_some (T T' : Int) (hT : T' ≤ T) (g : Genome) (r : List Char) (a : Placement × Int)
    (h : mapSpecBoth sc0 T g r = some a) : mapSpecBoth sc0 T' g r = some a := by
  rw [mapSpecBoth_mono T T' hT g r (hitsBoth_ne_of_some h)]; exact h

/-! ## Every search reason means the pair is not reported -/

theorem reasonOk_none (T : Mate → Int) (lo hi : Nat) (g : Genome) (rd : Mate → List Char) (r : Reason)
    (h : ReasonOk T lo hi g rd r) :
    pairSpecT (T .one) (T .two) lo hi g (rd .one) (rd .two) = none := by
  unfold pairSpecT
  cases r with
  | trimmedAway m => exact h.elim
  | tooShort m => exact h.elim
  | noHit m =>
    have h' := hitsBoth_nil_none h
    cases m
    · rw [h']
    · rw [h']; cases mapSpecBoth sc0 (T .one) g (rd .one) <;> rfl
  | tie m =>
    have h' := h.2
    cases m
    · rw [h']
    · rw [h']; cases mapSpecBoth sc0 (T .one) g (rd .one) <;> rfl
  | noPartner m =>
    obtain ⟨a, ha, hp⟩ := h
    cases m
    · simp only [Mate.other] at ha
      rw [ha]
      cases hb : mapSpecBoth sc0 (T .one) g (rd .one) with
      | none => rfl
      | some b =>
        have := hp b (mapSpecBoth_mem hb)
        rw [properPair_comm] at this
        simp [this]
    · simp only [Mate.other] at ha
      rw [ha]
      cases hb : mapSpecBoth sc0 (T .two) g (rd .two) with
      | none => rfl
      | some b =>
        simp [hp b (mapSpecBoth_mem hb)]
  | notProper =>
    obtain ⟨a, b, ha, hb, hp⟩ := h
    rw [ha, hb]; simp [hp]

/-! ## Which reasons stay at deeper caps -/

section mono
variable (T T' : Mate → Int) (hT : ∀ m, T' m ≤ T m) (lo hi : Nat) (g : Genome) (rd : Mate → List Char)
include hT

/-- A tie stays a tie at deeper caps. -/
theorem reasonOk_tie_mono (m : Mate) (h : ReasonOk T lo hi g rd (.tie m)) : ReasonOk T' lo hi g rd (.tie m) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, by rw [mapSpecBoth_mono (T m) (T' m) (hT m) g (rd m) h1]; exact h2⟩
  intro hn
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ h1
  rw [mem_hitsBoth_T] at hx
  have : x ∈ hitsBoth sc0 (T' m) g (rd m) := by
    rw [mem_hitsBoth_T]; exact ⟨hx.1, hx.2.1, Int.le_trans (hT m) hx.2.2⟩
  rw [hn] at this; cases this

/-- Not a proper pair stays so at deeper caps. -/
theorem reasonOk_notProper_mono (h : ReasonOk T lo hi g rd .notProper) : ReasonOk T' lo hi g rd .notProper := by
  obtain ⟨a, b, ha, hb, hp⟩ := h
  exact ⟨a, b, mapSpecBoth_mono_some _ _ (hT .one) g _ a ha, mapSpecBoth_mono_some _ _ (hT .two) g _ b hb, hp⟩

/-- A pair reported at `T` is reported the same at any deeper `T'`. -/
theorem pairSpecT_mono_some (x : (Placement × Int) × (Placement × Int))
    (h : pairSpecT (T .one) (T .two) lo hi g (rd .one) (rd .two) = some x) :
    pairSpecT (T' .one) (T' .two) lo hi g (rd .one) (rd .two) = some x := by
  unfold pairSpecT at h ⊢
  cases ha : mapSpecBoth sc0 (T .one) g (rd .one) with
  | none => rw [ha] at h; cases h
  | some a =>
    cases hb : mapSpecBoth sc0 (T .two) g (rd .two) with
    | none => rw [ha, hb] at h; cases h
    | some b =>
      rw [ha, hb] at h
      rw [mapSpecBoth_mono_some _ _ (hT .one) g _ a ha, mapSpecBoth_mono_some _ _ (hT .two) g _ b hb]
      exact h

end mono

end MapSpec.Fast

#print axioms MapSpec.Fast.mapSpecBoth_mono
#print axioms MapSpec.Fast.reasonOk_none
#print axioms MapSpec.Fast.reasonOk_tie_mono
#print axioms MapSpec.Fast.reasonOk_notProper_mono
#print axioms MapSpec.Fast.pairSpecT_mono_some
