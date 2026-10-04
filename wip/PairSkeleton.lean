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

theorem complB_toNat_all : ∀ n, n < 256 →
    (complB n.toUInt8).toNat = (complement (Char.ofNat n)).toNat := by
  decide +kernel

theorem complB_toNat (b : UInt8) (c : Char) (h : b.toNat = c.toNat) :
    (complB b).toNat = (complement c).toNat := by
  have hc : c = Char.ofNat b.toNat := by rw [h, Char.ofNat_toNat]
  rw [hc]
  have := complB_toNat_all b.toNat b.toNat_lt
  have e : b.toNat.toUInt8 = b := by simp
  rwa [e] at this

theorem revCompB_size_aux (R : ByteArray) : (revCompB R).size = R.size := by
  show ((R.data.map complB).reverse).size = R.data.size
  simp


/-- TASK L1: byte reverse complement encodes the list reverse complement. -/
theorem revCompB_encodes (R : ByteArray) (read : List Char) (h : Encodes R read) :
    Encodes (revCompB R) (revComp read) := by
  obtain ⟨hs, he⟩ := h
  have hlen : (revComp read).length = read.length := by simp [revComp]
  refine ⟨by rw [revCompB_size_aux, hlen, hs], fun i hi => ?_⟩
  rw [hlen] at hi
  have hRs : R.data.size = read.length := hs
  have hj : read.length - 1 - i < read.length := by omega
  have key := he (read.length - 1 - i) hj
  simp only [revComp, List.getElem_reverse, List.getElem_map, List.length_map]
  simp only [ByteArray.get!, revCompB] at key ⊢
  rw [getElem!_pos _ i (by simp; omega)]
  rw [getElem!_pos _ _ (by omega)] at key
  simp only [Array.getElem_reverse, Array.getElem_map, Array.size_map]
  apply complB_toNat
  simp only [hRs]; exact key


/-- TASK L2: size is kept. -/
theorem revCompB_size (R : ByteArray) : (revCompB R).size = R.size :=
  revCompB_size_aux R

/-- Score of a placement: forward = the read, reverse = its reverse complement. -/
def strandScore (g : Genome) (read : List Char) : Strand → Window → Option Int
  | .fwd => windowScore sc0 read g
  | .rev => windowScore sc0 (revComp read) g

theorem selectUniqueBy_eq_some_iff {α : Type} [DecidableEq α] (l : List (α × Int))
    (hfun : ∀ a ∈ l, ∀ b ∈ l, a.1 = b.1 → a.2 = b.2) (a : α × Int) :
    selectUniqueBy l = some a ↔ a ∈ l ∧ ∀ b ∈ l, b.2 < a.2 ∨ b.1 = a.1 := by
  have hq : ∀ a : α × Int, (l.all fun b => decide (b.2 < a.2) || decide (b.1 = a.1)) = true ↔
      ∀ b ∈ l, b.2 < a.2 ∨ b.1 = a.1 := by
    intro a; simp [List.all_eq_true]
  unfold selectUniqueBy
  constructor
  · intro h
    have h2 := List.find?_some h
    exact ⟨List.mem_of_find?_eq_some h, (hq a).1 h2⟩
  · rintro ⟨hm, hp⟩
    cases h : l.find? (fun a => l.all fun b => decide (b.2 < a.2) || decide (b.1 = a.1)) with
    | none => exact absurd ((hq a).2 hp) (List.find?_eq_none.1 h a hm)
    | some c =>
      have hc0 := List.find?_some h
      have hc := (hq c).1 hc0
      have hcm := List.mem_of_find?_eq_some h
      have h1 := hp c hcm
      have h2 := hc a hm
      have h12 : c.1 = a.1 := by
        rcases h1 with h1 | h1
        · rcases h2 with h2 | h2
          · omega
          · exact h2.symm
        · exact h1
      rw [Prod.ext h12 (hfun c hcm a hm h12)]

theorem mem_hitsBoth_sc0 (g : Genome) (read : List Char) (p : Placement) (s : Int) :
    (p, s) ∈ hitsBoth sc0 (-12) g read ↔
      p.1 ∈ allWindows g ∧ strandScore g read p.2 p.1 = some s ∧ -12 ≤ s := by
  obtain ⟨w, st⟩ := p
  unfold hitsBoth
  rw [List.mem_append, List.mem_map, List.mem_map]
  cases st with
  | fwd =>
    show _ ↔ w ∈ allWindows g ∧ windowScore sc0 read g w = some s ∧ -12 ≤ s
    rw [← mem_hitsOf]
    constructor
    · rintro (⟨⟨w', s'⟩, h, he⟩ | ⟨⟨w', s'⟩, h, he⟩)
      · simp only [Prod.mk.injEq] at he
        obtain ⟨⟨rfl, -⟩, rfl⟩ := he
        exact h
      · simp at he
    · intro h; exact Or.inl ⟨(w, s), h, rfl⟩
  | rev =>
    show _ ↔ w ∈ allWindows g ∧ windowScore sc0 (revComp read) g w = some s ∧ -12 ≤ s
    rw [← mem_hitsOf]
    constructor
    · rintro (⟨⟨w', s'⟩, h, he⟩ | ⟨⟨w', s'⟩, h, he⟩)
      · simp at he
      · simp only [Prod.mk.injEq] at he
        obtain ⟨⟨rfl, -⟩, rfl⟩ := he
        exact h
    · intro h; exact Or.inr ⟨(w, s), h, rfl⟩

theorem strandScore_allWindows (g : Genome) (read : List Char) (st : Strand) (w : Window) (s : Int)
    (h : strandScore g read st w = some s) : w ∈ allWindows g := by
  apply (mem_allWindows g w).2
  cases st <;> (unfold strandScore windowScore at h; cases hw : windowSeq g w <;> simp_all)

/-- TASK L3: `mapSpecBoth` is the unique best placement over both strands
(the analogue of `mapSpec_iff` in codecs/FastMapper.lean). -/
theorem mapSpecBoth_iff (g : Genome) (read : List Char) (p : Placement) (s : Int) :
    mapSpecBoth sc0 (-12) g read = some (p, s) ↔
      (strandScore g read p.2 p.1 = some s ∧ -12 ≤ s) ∧
      ∀ p' s', strandScore g read p'.2 p'.1 = some s' → -12 ≤ s' → s' < s ∨ p' = p := by
  unfold mapSpecBoth
  rw [selectUniqueBy_eq_some_iff _ (by
    rintro ⟨a, sa⟩ ha ⟨b, sb⟩ hb (rfl : a = b)
    rw [mem_hitsBoth_sc0] at ha hb
    have := ha.2.1.symm.trans hb.2.1
    simpa using this)]
  constructor
  · rintro ⟨hm, h3⟩
    rw [mem_hitsBoth_sc0] at hm
    exact ⟨⟨hm.2.1, hm.2.2⟩, fun p' s' h4 h5 =>
      h3 (p', s') ((mem_hitsBoth_sc0 _ _ _ _).2
        ⟨strandScore_allWindows g read p'.2 p'.1 s' h4, h4, h5⟩)⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨(mem_hitsBoth_sc0 _ _ _ _).2
      ⟨strandScore_allWindows g read p.2 p.1 s h1, h1, h2⟩, fun ⟨p', s'⟩ hb => ?_⟩
    rw [mem_hitsBoth_sc0] at hb
    exact h3 p' s' hb.2.1 hb.2.2

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
