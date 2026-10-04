import PairMapper

/-!
# Joint strand search — PROOF SKELETON (work in progress; `sorry` lemmas are tasks)

Both strands share ONE `Best`: the reverse strand is searched as extra
"virtual chromosomes" `n + c` (same genome bytes `gbs[c]`, read = reverse
complement).  The proved per-chromosome step `mapChrom2_inv` only uses the
chromosome index as a tag, and its stop test compares against the shared
best, so once one strand has a good hit the other stops after few lookups.
A tie between the strands at the same window is two different virtual
windows, so `Best.amb` makes it unmapped, as `mapSpecBoth` requires.
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-! ## Algorithm -/

/-- Both strands through one shared `Best`: chromosomes `0..n-1` with the read,
then `n..2n-1` with its reverse complement. -/
@[specialize] def mapChromsJ {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P) (R : ByteArray)
    (gbs : Array ByteArray) (idxs : Array L) : Best :=
  let n := gbs.size
  let Rr := revCompB R
  let hs := seedHashes R
  let hr := seedHashes Rr
  let b := (List.range n).foldl (fun b c => mapChrom2 lk R gbs[c]! c idxs[c]! hs b) {}
  (List.range n).foldl (fun b c => mapChrom2 lk Rr gbs[c]! (n + c) idxs[c]! hr b) b

/-- Virtual window → placement. -/
def decodeJ (n : Nat) (b : Best) : Option (Placement × Int) :=
  match result b with
  | some (c, st, len, pen) =>
    some ((if c < n then (⟨c, st, len⟩, Strand.fwd) else (⟨c - n, st, len⟩, Strand.rev)), -(pen : Int))
  | none => none

def mapFastJ {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P) (gbs : Array ByteArray)
    (idxs : Array L) (R : ByteArray) : Option (Placement × Int) :=
  decodeJ gbs.size (mapChromsJ lk R gbs idxs)

def pairFastJ {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P) (lo hi : Nat)
    (gbs : Array ByteArray) (idxs : Array L) (R1 R2 : ByteArray) :
    Option ((Placement × Int) × (Placement × Int)) :=
  match mapFastJ lk gbs idxs R1 with
  | none => none
  | some a =>
    match mapFastJ lk gbs idxs R2 with
    | some b => if properPair lo hi a.1 b.1 then some (a, b) else none
    | none => none

/-! ## Penalties -/

/-- Penalty of a virtual window. -/
def cwJ (R : ByteArray) (gbs : Array ByteArray) (w : Window) : Nat :=
  if w.chr < gbs.size then cwG R gbs w
  else if w.chr < 2 * gbs.size then cwG (revCompB R) gbs ⟨w.chr - gbs.size, w.start, w.len⟩
  else 13

/-- Penalty of a placement. -/
def cwP (R : ByteArray) (gbs : Array ByteArray) : Strand → Window → Nat
  | .fwd => cwG R gbs
  | .rev => cwG (revCompB R) gbs

/-! ## Lemmas (each `sorry` is one task) -/

/-- TASK J1: the joint search keeps the proved invariant over virtual windows
and covers every virtual window of penalty ≤ 12 (two folds of `mapChrom2_inv`,
as in `mapChroms_inv`, MapperFastLazy.lean). -/
theorem mapChromsJ_inv {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P) (R : ByteArray)
    (gbs : Array ByteArray) (idxs : Array L) (hn : 100 ≤ R.size)
    (hlk : ∀ c, c < gbs.size → ∀ R' : ByteArray, ∀ j, j < 4 →
      LookOk gbs[c]! R' j (lk.look idxs[c]! gbs[c]! R' j (lk.prep idxs[c]! (seedHash R' j)))) :
    ∃ S, Inv (cwJ R gbs) S (mapChromsJ lk R gbs idxs) ∧ ∀ w, cwJ R gbs w ≤ 12 → S w := by
  sorry

/-- TASK J2: decoding the shared best gives the unique best placement. -/
theorem decodeJ_spec (R : ByteArray) (gbs : Array ByteArray) (S : Window → Prop) (b : Best)
    (h : Inv (cwJ R gbs) S b) (hall : ∀ w, cwJ R gbs w ≤ 12 → S w) (p : Placement) (s : Int) :
    decodeJ gbs.size b = some (p, s) ↔
      (cwP R gbs p.2 p.1 ≤ 12 ∧ s = -(cwP R gbs p.2 p.1 : Int)) ∧
      ∀ p', cwP R gbs p'.2 p'.1 ≤ 12 → p' ≠ p → cwP R gbs p.2 p.1 < cwP R gbs p'.2 p'.1 := by
  sorry

/-! ## Top theorems (from the lemmas) -/

theorem mapFastJ_eq_mapSpecBoth {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P)
    (g : Genome) (read : List Char) (gbs : Array ByteArray) (idxs : Array L) (R : ByteArray)
    (hg : GenomeBytes gbs g) (hr : Encodes R read) (hlk : LookAll lk gbs idxs) (hok : fastOk R = true) :
    mapFastJ lk gbs idxs R = mapSpecBoth sc0 (-12) g read := by
  have hn : 100 ≤ R.size := by unfold fastOk q at hok; simp at hok; omega
  have hrr := revCompB_encodes R read hr
  obtain ⟨S, hinv, hall⟩ := mapChromsJ_inv lk R gbs idxs hn (fun c hc R' j hj => hlk c hc R' j hj)
  have key : ∀ (st : Strand) w' s', (strandScore g read st w' = some s' ∧ -12 ≤ s') ↔
      (cwP R gbs st w' ≤ 12 ∧ s' = -(cwP R gbs st w' : Int)) := by
    intro st w' s'
    cases st with
    | fwd =>
      show (windowScore sc0 read g w' = some s' ∧ -12 ≤ s') ↔ _
      rw [show cwP R gbs .fwd w' = cwG R gbs w' from rfl, cwG_eq g read gbs R hg hr]
      exact penOf_some _ s' (windowScore_nonpos read g w')
    | rev =>
      show (windowScore sc0 (revComp read) g w' = some s' ∧ -12 ≤ s') ↔ _
      rw [show cwP R gbs .rev w' = cwG (revCompB R) gbs w' from rfl,
        cwG_eq g (revComp read) gbs (revCompB R) hg hrr]
      exact penOf_some _ s' (windowScore_nonpos (revComp read) g w')
  apply Option.ext
  rintro ⟨p, s⟩
  unfold mapFastJ
  rw [mapSpecBoth_iff, decodeJ_spec R gbs S _ hinv hall]
  constructor
  · rintro ⟨⟨h1, rfl⟩, h3⟩
    refine ⟨(key p.2 p.1 _).mpr ⟨h1, rfl⟩, fun p' s' h4 h5 => ?_⟩
    obtain ⟨h6, rfl⟩ := (key p'.2 p'.1 s').mp ⟨h4, h5⟩
    by_cases hp : p' = p
    · right; exact hp
    · left; have := h3 p' h6 hp; omega
  · rintro ⟨h1, h3⟩
    obtain ⟨h1a, rfl⟩ := (key p.2 p.1 s).mp h1
    refine ⟨⟨h1a, rfl⟩, fun p' h4 h5 => ?_⟩
    rcases h3 p' _ ((key p'.2 p'.1 _).mpr ⟨h4, rfl⟩).1 ((key p'.2 p'.1 _).mpr ⟨h4, rfl⟩).2 with h6 | h6
    · omega
    · exact absurd h6 h5

theorem pairFastJ_eq_pairSpec {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P) (lo hi : Nat)
    (g : Genome) (m1 m2 : List Char) (gbs : Array ByteArray) (idxs : Array L) (R1 R2 : ByteArray)
    (hg : GenomeBytes gbs g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hlk : LookAll lk gbs idxs)
    (hok1 : fastOk R1 = true) (hok2 : fastOk R2 = true) :
    pairFastJ lk lo hi gbs idxs R1 R2 = pairSpec sc0 (-12) lo hi g m1 m2 := by
  unfold pairFastJ pairSpec
  rw [mapFastJ_eq_mapSpecBoth lk g m1 gbs idxs R1 hg h1 hlk hok1,
      mapFastJ_eq_mapSpecBoth lk g m2 gbs idxs R2 hg h2 hlk hok2]
  cases mapSpecBoth sc0 (-12) g m1 <;> cases mapSpecBoth sc0 (-12) g m2 <;> rfl

end MapSpec.Fast
