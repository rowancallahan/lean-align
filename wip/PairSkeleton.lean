import FastMapper
import PairSpec

/-!
# Both strands and proper pairs for the fast mapper — PROOF SKELETON (work in progress)

Top theorems are proved here FROM the `sorry` lemmas below; each `sorry` lemma is
an independent task.  When a lemma is proved it moves to `pool/mapper/` and the
`sorry` disappears.  Nothing in this file is counted as proved until no `sorry`
is left (`scripts/check.sh` does not scan `wip/`).

Design: run the proved fast mapper once on the read and once on its reverse
complement (each gives a `Best` with its proved `Inv`), then `combineBest`.
(The joint, interleaved strand search is a later speed step with the same
`combineBest` interface.)
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-! ## Algorithm -/

def complB (b : UInt8) : UInt8 :=
  if b == 65 then 84 else if b == 84 then 65 else if b == 67 then 71 else if b == 71 then 67 else b

/-- Reverse complement of a byte read (letters other than A, C, G, T kept). -/
def revCompB (R : ByteArray) : ByteArray := ⟨(R.data.map complB).reverse⟩

/-- The two strands' bests → the both-strand answer: the strictly better
strand wins if its best is unique; equal penalties on the two strands tie. -/
def combineBest (bf br : Best) : Option (Placement × Int) :=
  if bf.pen < br.pen then
    (if bf.pen ≤ cap && !bf.amb then some ((bf.win, Strand.fwd), -(bf.pen : Int)) else none)
  else if br.pen < bf.pen then
    (if br.pen ≤ cap && !br.amb then some ((br.win, Strand.rev), -(br.pen : Int)) else none)
  else none

/-- Both strands, fast path only (reads with `fastOk`). -/
def mapFastBoth {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P) (gbs : Array ByteArray)
    (idxs : Array L) (R : ByteArray) : Option (Placement × Int) :=
  combineBest (mapChroms lk R gbs idxs) (mapChroms lk (revCompB R) gbs idxs)

/-- Proper-pair mapping; mate 2 is not mapped when mate 1 is unmapped. -/
def pairFast {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P) (lo hi : Nat)
    (gbs : Array ByteArray) (idxs : Array L) (R1 R2 : ByteArray) :
    Option ((Placement × Int) × (Placement × Int)) :=
  match mapFastBoth lk gbs idxs R1 with
  | none => none
  | some a =>
    match mapFastBoth lk gbs idxs R2 with
    | some b => if properPair lo hi a.1 b.1 then some (a, b) else none
    | none => none

/-! ## Lemmas (each `sorry` is one task) -/

/-- TASK L1: byte reverse complement encodes the list reverse complement. -/
theorem revCompB_encodes (R : ByteArray) (read : List Char) (h : Encodes R read) :
    Encodes (revCompB R) (revComp read) := by
  sorry

/-- TASK L2: size is kept. -/
theorem revCompB_size (R : ByteArray) : (revCompB R).size = R.size := by
  sorry

/-- Score of a placement: forward = the read, reverse = its reverse complement. -/
def strandScore (g : Genome) (read : List Char) : Strand → Window → Option Int
  | .fwd => windowScore sc0 read g
  | .rev => windowScore sc0 (revComp read) g

/-- TASK L3: `mapSpecBoth` is the unique best placement over both strands
(the analogue of `mapSpec_iff` in codecs/FastMapper.lean). -/
theorem mapSpecBoth_iff (g : Genome) (read : List Char) (p : Placement) (s : Int) :
    mapSpecBoth sc0 (-12) g read = some (p, s) ↔
      (strandScore g read p.2 p.1 = some s ∧ -12 ≤ s) ∧
      ∀ p' s', strandScore g read p'.2 p'.1 = some s' → -12 ≤ s' → s' < s ∨ p' = p := by
  sorry

/-- TASK L4: `combineBest` of two strands' bests (each with its proved `Inv`
covering every window of penalty ≤ 12) is the unique best placement. -/
theorem combineBest_spec (cwf cwr : Window → Nat) (Sf Sr : Window → Prop) (bf br : Best)
    (hf : Inv cwf Sf bf) (hr : Inv cwr Sr br)
    (hallf : ∀ w, cwf w ≤ 12 → Sf w) (hallr : ∀ w, cwr w ≤ 12 → Sr w)
    (cw : Strand → Window → Nat) (hcwf : cw .fwd = cwf) (hcwr : cw .rev = cwr)
    (p : Placement) (s : Int) :
    combineBest bf br = some (p, s) ↔
      (cw p.2 p.1 ≤ 12 ∧ s = -(cw p.2 p.1 : Int)) ∧
      ∀ p', cw p'.2 p'.1 ≤ 12 → p' ≠ p → cw p.2 p.1 < cw p'.2 p'.1 := by
  sorry

/-! ## Top theorems (proved from the lemmas above) -/

theorem mapFastBoth_eq_mapSpecBoth {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P)
    (g : Genome) (read : List Char) (gbs : Array ByteArray) (idxs : Array L) (R : ByteArray)
    (hg : GenomeBytes gbs g) (hr : Encodes R read) (hlk : LookAll lk gbs idxs) (hok : fastOk R = true) :
    mapFastBoth lk gbs idxs R = mapSpecBoth sc0 (-12) g read := by
  have hn : 100 ≤ R.size := by unfold fastOk q at hok; simp at hok; omega
  have hn' : 100 ≤ (revCompB R).size := by rw [revCompB_size]; exact hn
  have hrr := revCompB_encodes R read hr
  obtain ⟨Sf, hinvf, hallf⟩ := mapChroms_inv lk R gbs idxs hn (fun c hc j hj => hlk c hc R j hj)
  obtain ⟨Sr, hinvr, hallr⟩ := mapChroms_inv lk (revCompB R) gbs idxs hn' (fun c hc j hj => hlk c hc _ j hj)
  let cw : Strand → Window → Nat := fun st => match st with
    | .fwd => cwG R gbs
    | .rev => cwG (revCompB R) gbs
  have key : ∀ (st : Strand) w' s', (strandScore g read st w' = some s' ∧ -12 ≤ s') ↔
      (cw st w' ≤ 12 ∧ s' = -(cw st w' : Int)) := by
    intro st w' s'
    cases st with
    | fwd =>
      show (windowScore sc0 read g w' = some s' ∧ -12 ≤ s') ↔ _
      rw [show cw .fwd w' = cwG R gbs w' from rfl, cwG_eq g read gbs R hg hr]
      exact penOf_some _ s' (windowScore_nonpos read g w')
    | rev =>
      show (windowScore sc0 (revComp read) g w' = some s' ∧ -12 ≤ s') ↔ _
      rw [show cw .rev w' = cwG (revCompB R) gbs w' from rfl, cwG_eq g (revComp read) gbs (revCompB R) hg hrr]
      exact penOf_some _ s' (windowScore_nonpos (revComp read) g w')
  apply Option.ext
  rintro ⟨p, s⟩
  unfold mapFastBoth
  rw [mapSpecBoth_iff, combineBest_spec _ _ Sf Sr _ _ hinvf hinvr hallf hallr cw rfl rfl]
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

theorem pairFast_eq_pairSpec {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P) (lo hi : Nat)
    (g : Genome) (m1 m2 : List Char) (gbs : Array ByteArray) (idxs : Array L) (R1 R2 : ByteArray)
    (hg : GenomeBytes gbs g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hlk : LookAll lk gbs idxs)
    (hok1 : fastOk R1 = true) (hok2 : fastOk R2 = true) :
    pairFast lk lo hi gbs idxs R1 R2 = pairSpec sc0 (-12) lo hi g m1 m2 := by
  unfold pairFast pairSpec
  rw [mapFastBoth_eq_mapSpecBoth lk g m1 gbs idxs R1 hg h1 hlk hok1,
      mapFastBoth_eq_mapSpecBoth lk g m2 gbs idxs R2 hg h2 hlk hok2]
  cases mapSpecBoth sc0 (-12) g m1 <;> cases mapSpecBoth sc0 (-12) g m2 <;> rfl

end MapSpec.Fast
