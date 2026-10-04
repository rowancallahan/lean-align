import PairMapper

/-!
# Codec `pairFastJ`: joint strand search (one shared `Best`) and proper pairs

Both strands share ONE `Best`: the reverse strand is searched as extra virtual
chromosomes `n + c` (same genome bytes, read = reverse complement).  The proved
per-chromosome step `mapChrom2_inv` uses the chromosome index only as a tag and
its stop test compares against the shared best, so once one strand has a good
hit the other stops after few lookups.  The same window on the two strands is
two different virtual windows, so a tie is ambiguous (unmapped), as
`mapSpecBoth` requires.  Against the DRAFT spec `spec/PairSpec.lean`; fast path
(`fastOk`), sc0, T = −12.

    … → mapFastJ lk gbs idxs R = mapSpecBoth sc0 (-12) g read              (mapFastJ_eq_mapSpecBoth)
    … → pairFastJ lk lo hi gbs idxs R1 R2 = pairSpec sc0 (-12) lo hi g m1 m2 (pairFastJ_eq_pairSpec)
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-! ## Algorithm -/

/-- Both strands through one shared `Best`: chromosomes `0..n-1` with the read
and `n..2n-1` with its reverse complement; `rf`: reverse strand first.  Any order
is exact; searching the likely strand first lets the other stop early. -/
@[specialize] def mapChromsJ {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P) (R : ByteArray)
    (gbs : Array ByteArray) (idxs : Array L) (rf : Bool := false) : Best :=
  let n := gbs.size
  let Rr := revCompB R
  let hs := seedHashes R
  let hr := seedHashes Rr
  let fwd (b : Best) := (List.range n).foldl (fun b c => mapChrom2 lk R gbs[c]! c idxs[c]! hs b) b
  let rev (b : Best) := (List.range n).foldl (fun b c => mapChrom2 lk Rr gbs[c]! (n + c) idxs[c]! hr b) b
  if rf then fwd (rev {}) else rev (fwd {})

/-- Virtual window → placement. -/
def decodeJ (n : Nat) (b : Best) : Option (Placement × Int) :=
  match result b with
  | some (c, st, len, pen) =>
    some ((if c < n then (⟨c, st, len⟩, Strand.fwd) else (⟨c - n, st, len⟩, Strand.rev)), -(pen : Int))
  | none => none

def mapFastJ {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P) (gbs : Array ByteArray)
    (idxs : Array L) (R : ByteArray) (rf : Bool := false) : Option (Placement × Int) :=
  decodeJ gbs.size (mapChromsJ lk R gbs idxs rf)

def pairFastJ {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P) (lo hi : Nat)
    (gbs : Array ByteArray) (idxs : Array L) (R1 R2 : ByteArray) :
    Option ((Placement × Int) × (Placement × Int)) :=
  match mapFastJ lk gbs idxs R1 false with
  | none => none
  | some a =>
    -- mate 2 of a proper pair is on the other strand: search that one first
    match mapFastJ lk gbs idxs R2 (a.1.2 == Strand.fwd) with
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

/-! ## Lemmas -/

theorem cwJ_le (R : ByteArray) (gbs : Array ByteArray) (w : Window) : cwJ R gbs w ≤ 13 := by
  unfold cwJ; split
  · exact cwG_le _ _ _
  · split
    · exact cwG_le _ _ _
    · exact Nat.le_refl _

/-- One fold of `mapChrom2` over a list of chromosomes with read `R'` and tags `t c`. -/
theorem foldJ_inv {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P) (R R' : ByteArray)
    (gbs : Array ByteArray) (idxs : Array L) (t : Nat → Nat) (hn : 100 ≤ R'.size)
    (hcw : ∀ c, c < gbs.size → ∀ st len, cwJ R gbs ⟨t c, st, len⟩ = penB R' gbs[c]! st len)
    (hlk : ∀ c, c < gbs.size → ∀ j, j < 4 →
      LookOk gbs[c]! R' j (lk.look idxs[c]! gbs[c]! R' j (lk.prep idxs[c]! (seedHash R' j)))) :
    ∀ (l : List Nat) S b, (∀ c ∈ l, c < gbs.size) → Inv (cwJ R gbs) S b →
      ∃ S', Inv (cwJ R gbs) S'
          (l.foldl (fun b c => mapChrom2 lk R' gbs[c]! (t c) idxs[c]! (seedHashes R') b) b) ∧
        (∀ w, S w → S' w) ∧ ∀ c ∈ l, ∀ st len, cwJ R gbs ⟨t c, st, len⟩ ≤ 12 → S' ⟨t c, st, len⟩ := by
  intro l
  induction l with
  | nil => intro S b _ h; exact ⟨S, h, fun w hw => hw, fun c hc => by simp at hc⟩
  | cons c l ih =>
    intro S b hl h
    have hc : c < gbs.size := hl c List.mem_cons_self
    obtain ⟨S1, h1, s1, c1⟩ := mapChrom2_inv (cwJ R gbs) (cwJ_le R gbs) R' gbs[c]! (t c)
      (hcw c hc) hn lk idxs[c]! (hlk c hc) S b h
    obtain ⟨S2, h2, s2, c2⟩ := ih S1 _ (fun c' h' => hl c' (List.mem_cons_of_mem _ h')) h1
    refine ⟨S2, h2, fun w hw => s2 w (s1 w hw), fun c' hc' st len hw => ?_⟩
    rcases List.mem_cons.mp hc' with rfl | hc'
    · exact s2 _ (c1 st len hw)
    · exact c2 c' hc' st len hw

/-- the joint search keeps the proved invariant over virtual windows
and covers every virtual window of penalty ≤ 12 (two folds of `mapChrom2_inv`,
as in `mapChroms_inv`, MapperFastLazy.lean). -/
theorem mapChromsJ_inv {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P) (R : ByteArray)
    (gbs : Array ByteArray) (idxs : Array L) (rf : Bool) (hn : 100 ≤ R.size)
    (hlk : ∀ c, c < gbs.size → ∀ R' : ByteArray, ∀ j, j < 4 →
      LookOk gbs[c]! R' j (lk.look idxs[c]! gbs[c]! R' j (lk.prep idxs[c]! (seedHash R' j)))) :
    ∃ S, Inv (cwJ R gbs) S (mapChromsJ lk R gbs idxs rf) ∧ ∀ w, cwJ R gbs w ≤ 12 → S w := by
  have hrn : 100 ≤ (revCompB R).size := by rw [revCompB_size]; exact hn
  have F := foldJ_inv lk R R gbs idxs (fun c => c) hn
    (fun c hc st len => by unfold cwJ cwG; simp [hc]) (fun c hc => hlk c hc R)
    (List.range gbs.size)
  have V := foldJ_inv lk R (revCompB R) gbs idxs (fun c => gbs.size + c) hrn
    (fun c hc st len => by
      unfold cwJ cwG
      simp [hc, show ¬ gbs.size + c < gbs.size by omega, show gbs.size + c < 2 * gbs.size by omega])
    (fun c hc => hlk c hc (revCompB R)) (List.range gbs.size)
  have hl : ∀ c ∈ List.range gbs.size, c < gbs.size := fun c hc => List.mem_range.mp hc
  -- every window of penalty ≤ 12 is a forward or a reverse virtual window
  have cover : ∀ (S : Window → Prop),
      (∀ c ∈ List.range gbs.size, ∀ st len, cwJ R gbs ⟨c, st, len⟩ ≤ 12 → S ⟨c, st, len⟩) →
      (∀ c ∈ List.range gbs.size, ∀ st len,
        cwJ R gbs ⟨gbs.size + c, st, len⟩ ≤ 12 → S ⟨gbs.size + c, st, len⟩) →
      ∀ w, cwJ R gbs w ≤ 12 → S w := by
    intro S cf cr ⟨c, st, len⟩ hw
    by_cases hc : c < gbs.size
    · exact cf c (List.mem_range.mpr hc) st len hw
    · by_cases hc2 : c < 2 * gbs.size
      · have := cr (c - gbs.size) (List.mem_range.mpr (by omega)) st len
          (by rw [show gbs.size + (c - gbs.size) = c by omega]; exact hw)
        rwa [show gbs.size + (c - gbs.size) = c by omega] at this
      · unfold cwJ at hw; simp [hc, hc2] at hw
  cases rf with
  | false =>
    obtain ⟨S1, h1, -, cov1⟩ := F (fun _ => False) {} hl (inv_init _ (cwJ_le R gbs))
    obtain ⟨S2, h2, s2, cov2⟩ := V S1 _ hl h1
    exact ⟨S2, h2, cover S2 (fun c hc st len hw => s2 _ (cov1 c hc st len hw)) cov2⟩
  | true =>
    obtain ⟨S1, h1, -, cov1⟩ := V (fun _ => False) {} hl (inv_init _ (cwJ_le R gbs))
    obtain ⟨S2, h2, s2, cov2⟩ := F S1 _ hl h1
    exact ⟨S2, h2, cover S2 cov2 (fun c hc st len hw => s2 _ (cov1 c hc st len hw))⟩

/-- Placement → virtual window. -/
def encJ (n : Nat) : Placement → Window
  | (w, .fwd) => w
  | (w, .rev) => ⟨n + w.chr, w.start, w.len⟩

/-- Virtual window → placement (as in `decodeJ`). -/
def decJ (n : Nat) (w : Window) : Placement :=
  if w.chr < n then (⟨w.chr, w.start, w.len⟩, Strand.fwd) else (⟨w.chr - n, w.start, w.len⟩, Strand.rev)

theorem cwP_chr_lt (R : ByteArray) (gbs : Array ByteArray) (p : Placement)
    (h : cwP R gbs p.2 p.1 ≤ 12) : p.1.chr < gbs.size := by
  rcases p with ⟨w, st⟩
  cases st <;> simp only [cwP, cwG] at h <;> split at h <;> first | assumption | omega

theorem cwJ_encJ (R : ByteArray) (gbs : Array ByteArray) (p : Placement)
    (h : cwP R gbs p.2 p.1 ≤ 12) : cwJ R gbs (encJ gbs.size p) = cwP R gbs p.2 p.1 := by
  have hc := cwP_chr_lt R gbs p h
  rcases p with ⟨⟨c, st, len⟩, s⟩
  simp only at hc
  cases s
  · simp [encJ, cwJ, cwP, hc]
  · have h1 : ¬ gbs.size + c < gbs.size := by omega
    have h2 : gbs.size + c < 2 * gbs.size := by omega
    simp [encJ, cwJ, cwP, h1, h2]

theorem cwJ_chr_lt (R : ByteArray) (gbs : Array ByteArray) (w : Window)
    (h : cwJ R gbs w ≤ 12) : w.chr < 2 * gbs.size := by
  unfold cwJ at h
  split at h
  · omega
  · split at h
    · assumption
    · omega

theorem cwP_decJ (R : ByteArray) (gbs : Array ByteArray) (w : Window) :
    cwP R gbs (decJ gbs.size w).2 (decJ gbs.size w).1 = cwJ R gbs w := by
  rcases w with ⟨c, st, len⟩
  unfold decJ cwJ
  by_cases hc : c < gbs.size
  · simp [hc, cwP]
  · simp only [hc, if_false, cwP]
    by_cases h2 : c < 2 * gbs.size
    · simp [h2]
    · simp only [h2, if_false, cwG]
      have : ¬ c - gbs.size < gbs.size := by omega
      simp [this]

theorem decJ_encJ (n : Nat) (p : Placement) (h : p.1.chr < n) : decJ n (encJ n p) = p := by
  rcases p with ⟨⟨c, st, len⟩, s⟩
  simp only at h
  cases s
  · simp [encJ, decJ, h]
  · have h1 : ¬ n + c < n := by omega
    simp [encJ, decJ, h1]

theorem encJ_decJ (n : Nat) (w : Window) (h : w.chr < 2 * n) : encJ n (decJ n w) = w := by
  rcases w with ⟨c, st, len⟩
  unfold decJ
  by_cases hc : c < n
  · simp [hc, encJ]
  · simp only [hc, if_false, encJ]
    simp only [Window.mk.injEq, and_true]
    omega

/-- decoding the shared best gives the unique best placement. -/
theorem decodeJ_spec (R : ByteArray) (gbs : Array ByteArray) (S : Window → Prop) (b : Best)
    (h : Inv (cwJ R gbs) S b) (hall : ∀ w, cwJ R gbs w ≤ 12 → S w) (p : Placement) (s : Int) :
    decodeJ gbs.size b = some (p, s) ↔
      (cwP R gbs p.2 p.1 ≤ 12 ∧ s = -(cwP R gbs p.2 p.1 : Int)) ∧
      ∀ p', cwP R gbs p'.2 p'.1 ≤ 12 → p' ≠ p → cwP R gbs p.2 p.1 < cwP R gbs p'.2 p'.1 := by
  have key := result_spec (cwJ R gbs) S b h hall
  constructor
  · intro hd
    unfold decodeJ at hd
    split at hd
    · next c st len pen hr =>
      obtain ⟨e1, e2, e3⟩ := (key ⟨c, st, len⟩ pen).mp hr
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨hp, hs⟩ := hd
      have hpd : p = decJ gbs.size ⟨c, st, len⟩ := by rw [← hp]; rfl
      have hcp : cwP R gbs p.2 p.1 = pen := by rw [hpd, cwP_decJ, e1]
      refine ⟨⟨by omega, by rw [← hs, hcp]⟩, fun p' h1 h2 => ?_⟩
      rw [hcp, ← cwJ_encJ R gbs p' h1]
      apply e3 _ (by rw [cwJ_encJ R gbs p' h1]; exact h1)
      intro he
      apply h2
      rw [hpd, ← he, decJ_encJ _ _ (cwP_chr_lt R gbs p' h1)]
    · exact absurd hd (by simp)
  · rintro ⟨⟨h1, rfl⟩, h3⟩
    have hr : result b = some ((encJ gbs.size p).chr, (encJ gbs.size p).start,
        (encJ gbs.size p).len, cwP R gbs p.2 p.1) := by
      refine (key _ _).mpr ⟨cwJ_encJ R gbs p h1, h1, fun w' h4 h5 => ?_⟩
      have := h3 (decJ gbs.size w') (by rw [cwP_decJ]; exact h4) (by
        intro he; apply h5; rw [← he, encJ_decJ _ _ (cwJ_chr_lt R gbs w' h4)])
      rwa [cwP_decJ] at this
    have hd := decJ_encJ gbs.size p (cwP_chr_lt R gbs p h1)
    unfold decodeJ
    rw [hr]
    simp only [Option.some.injEq, Prod.mk.injEq, and_true]
    exact hd

/-! ## Top theorems (from the lemmas) -/

theorem mapFastJ_eq_mapSpecBoth {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P)
    (g : Genome) (read : List Char) (gbs : Array ByteArray) (idxs : Array L) (R : ByteArray)
    (rf : Bool) (hg : GenomeBytes gbs g) (hr : Encodes R read) (hlk : LookAll lk gbs idxs)
    (hok : fastOk R = true) : mapFastJ lk gbs idxs R rf = mapSpecBoth sc0 (-12) g read := by
  have hn : 100 ≤ R.size := by unfold fastOk q at hok; simp at hok; omega
  have hrr := revCompB_encodes R read hr
  obtain ⟨S, hinv, hall⟩ := mapChromsJ_inv lk R gbs idxs rf hn (fun c hc R' j hj => hlk c hc R' j hj)
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
  rw [mapFastJ_eq_mapSpecBoth lk g m1 gbs idxs R1 false hg h1 hlk hok1]
  cases mapSpecBoth sc0 (-12) g m1 with
  | none => rfl
  | some a =>
    simp only
    rw [mapFastJ_eq_mapSpecBoth lk g m2 gbs idxs R2 _ hg h2 hlk hok2]
    cases mapSpecBoth sc0 (-12) g m2 <;> rfl

end MapSpec.Fast

#print axioms MapSpec.Fast.mapFastJ_eq_mapSpecBoth
#print axioms MapSpec.Fast.pairFastJ_eq_pairSpec
