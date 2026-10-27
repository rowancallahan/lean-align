import PairJoint
import MapperInterleave

/-!
# Codec `pairFastI`: both strands interleaved, one lookup at a time

As `pairFastJ` (codecs/PairJoint.lean: the reverse strand is the virtual
chromosome `n + c`, one shared `Best`), but on each chromosome the two strands'
seed lookups are interleaved (`ilLoop`, pool/mapper/MapperInterleave.lean): the
next lookup goes to the strand with fewer lookups, then the smaller bucket, as
the prototype's `mapStreams` (bench/Proto.lean).  A strand stops once the shared
best is below `4·(its lookups)`, so a good hit on either strand stops the other
early whichever strand is searched first.  Against the DRAFT spec
`spec/PairSpec.lean`; fast path (`fastOk`), sc0, T = −12.

    … → mapFastI lk gbs idxs R = mapSpecBoth sc0 (-12) g read              (mapFastI_eq_mapSpecBoth)
    … → pairFastI lk lo hi gbs idxs R1 R2 = pairSpec sc0 (-12) lo hi g m1 m2 (pairFastI_eq_pairSpec)
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-! ## Algorithm -/

/-- Per chromosome `c`, the read (tag `c`) and its reverse complement (tag `n + c`)
interleaved through one shared `Best`; `rf`: the reverse strand takes ties. -/
@[specialize] def mapChromsI {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P) (R : ByteArray)
    (gbs : Array ByteArray) (idxs : Array L) (rf : Bool := false) : Best :=
  let n := gbs.size
  let Rr := revCompB R
  let hs := seedHashes R
  let hr := seedHashes Rr
  (List.range n).foldl (fun b c =>
    if rf then mapChromI lk gbs[c]! idxs[c]! Rr R (n + c) c hr hs b
    else mapChromI lk gbs[c]! idxs[c]! R Rr c (n + c) hs hr b) {}

def mapFastI {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P) (gbs : Array ByteArray)
    (idxs : Array L) (R : ByteArray) (rf : Bool := false) : Option (Placement × Int) :=
  decodeJ gbs.size (mapChromsI lk R gbs idxs rf)

def pairFastI {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P) (lo hi : Nat)
    (gbs : Array ByteArray) (idxs : Array L) (R1 R2 : ByteArray) :
    Option ((Placement × Int) × (Placement × Int)) :=
  match mapFastI lk gbs idxs R1 false with
  | none => none
  | some a =>
    -- mate 2 of a proper pair is on the other strand: it takes ties
    match mapFastI lk gbs idxs R2 (a.1.2 == Strand.fwd) with
    | some b => if properPair lo hi a.1 b.1 then some (a, b) else none
    | none => none

/-! ## Proofs -/

/-- The interleaved search keeps the invariant over virtual windows and covers
every virtual window of penalty ≤ 12 (`mapChromI_inv` per chromosome). -/
theorem mapChromsI_inv {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P) (R : ByteArray)
    (gbs : Array ByteArray) (idxs : Array L) (rf : Bool) (hn : 100 ≤ R.size)
    (hlk : ∀ c, c < gbs.size → ∀ R' : ByteArray, ∀ j, j < 4 →
      LookOk gbs[c]! R' j (lk.look idxs[c]! gbs[c]! R' j (lk.prep idxs[c]! (seedHash R' j)))) :
    ∃ S, Inv (cwJ R gbs) S (mapChromsI lk R gbs idxs rf) ∧ ∀ w, cwJ R gbs w ≤ 12 → S w := by
  have hrn : 100 ≤ (revCompB R).size := by rw [revCompB_size]; exact hn
  have cf : ∀ c, c < gbs.size → ∀ st len, cwJ R gbs ⟨c, st, len⟩ = penB R gbs[c]! st len :=
    fun c hc st len => by unfold cwJ cwG; simp [hc]
  have cr : ∀ c, c < gbs.size → ∀ st len, cwJ R gbs ⟨gbs.size + c, st, len⟩ = penB (revCompB R) gbs[c]! st len :=
    fun c hc st len => by
      unfold cwJ cwG
      simp [hc, show ¬ gbs.size + c < gbs.size by omega, show gbs.size + c < 2 * gbs.size by omega]
  have step : ∀ (l : List Nat) S b, (∀ c ∈ l, c < gbs.size) → Inv (cwJ R gbs) S b →
      ∃ S', Inv (cwJ R gbs) S' (l.foldl (fun b c =>
          if rf then mapChromI lk gbs[c]! idxs[c]! (revCompB R) R (gbs.size + c) c
            (seedHashes (revCompB R)) (seedHashes R) b
          else mapChromI lk gbs[c]! idxs[c]! R (revCompB R) c (gbs.size + c)
            (seedHashes R) (seedHashes (revCompB R)) b) b) ∧
        (∀ w, S w → S' w) ∧ ∀ c ∈ l, ∀ st len,
          (cwJ R gbs ⟨c, st, len⟩ ≤ 12 → S' ⟨c, st, len⟩) ∧
          (cwJ R gbs ⟨gbs.size + c, st, len⟩ ≤ 12 → S' ⟨gbs.size + c, st, len⟩) := by
    intro l
    induction l with
    | nil => intro S b _ h; exact ⟨S, h, fun w hw => hw, fun c hc => by simp at hc⟩
    | cons c l ih =>
      intro S b hl h
      have hc : c < gbs.size := hl c List.mem_cons_self
      have one : ∃ S1, Inv (cwJ R gbs) S1 (if rf then mapChromI lk gbs[c]! idxs[c]! (revCompB R) R
            (gbs.size + c) c (seedHashes (revCompB R)) (seedHashes R) b
          else mapChromI lk gbs[c]! idxs[c]! R (revCompB R) c (gbs.size + c)
            (seedHashes R) (seedHashes (revCompB R)) b) ∧ (∀ w, S w → S1 w) ∧ ∀ st len,
          (cwJ R gbs ⟨c, st, len⟩ ≤ 12 → S1 ⟨c, st, len⟩) ∧
          (cwJ R gbs ⟨gbs.size + c, st, len⟩ ≤ 12 → S1 ⟨gbs.size + c, st, len⟩) := by
        cases rf with
        | false =>
          obtain ⟨S1, i1, s1, v1, v2⟩ := mapChromI_inv (cwJ R gbs) (cwJ_le R gbs) gbs[c]! lk idxs[c]! R
            (revCompB R) c (gbs.size + c) (cf c hc) hn (hlk c hc R) (cr c hc) hrn (hlk c hc _) S b h
          exact ⟨S1, i1, s1, fun st len => ⟨v1 st len, v2 st len⟩⟩
        | true =>
          obtain ⟨S1, i1, s1, v2, v1⟩ := mapChromI_inv (cwJ R gbs) (cwJ_le R gbs) gbs[c]! lk idxs[c]!
            (revCompB R) R (gbs.size + c) c (cr c hc) hrn (hlk c hc _) (cf c hc) hn (hlk c hc R) S b h
          exact ⟨S1, i1, s1, fun st len => ⟨v1 st len, v2 st len⟩⟩
      obtain ⟨S1, h1, s1, c1⟩ := one
      obtain ⟨S2, h2, s2, c2⟩ := ih S1 _ (fun c' h' => hl c' (List.mem_cons_of_mem _ h')) h1
      refine ⟨S2, h2, fun w hw => s2 w (s1 w hw), fun c' hc' st len => ?_⟩
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact ⟨fun hw => s2 _ ((c1 st len).1 hw), fun hw => s2 _ ((c1 st len).2 hw)⟩
      · exact c2 c' hc' st len
  obtain ⟨S, h, -, cov⟩ := step (List.range gbs.size) (fun _ => False) {}
    (fun c hc => List.mem_range.mp hc) (inv_init _ (cwJ_le R gbs))
  refine ⟨S, h, fun ⟨c, st, len⟩ hw => ?_⟩
  by_cases hc : c < gbs.size
  · exact (cov c (List.mem_range.mpr hc) st len).1 hw
  · by_cases hc2 : c < 2 * gbs.size
    · have := (cov (c - gbs.size) (List.mem_range.mpr (by omega)) st len).2
      rw [show gbs.size + (c - gbs.size) = c by omega] at this
      exact this hw
    · unfold cwJ at hw; simp [hc, hc2] at hw

theorem mapFastI_eq_mapSpecBoth {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P)
    (g : Genome) (read : List Char) (gbs : Array ByteArray) (idxs : Array L) (R : ByteArray)
    (rf : Bool) (hg : GenomeBytes gbs g) (hr : Encodes R read) (hlk : LookAll lk gbs idxs)
    (hok : fastOk R = true) : mapFastI lk gbs idxs R rf = mapSpecBoth sc0 (-12) g read :=
  decodeJ_eq_mapSpecBoth g read gbs R _ hg hr (mapChromsI_inv lk R gbs idxs rf
    (by unfold fastOk q at hok; simp at hok; omega) (fun c hc R' j hj => hlk c hc R' j hj))

theorem pairFastI_eq_pairSpec {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P) (lo hi : Nat)
    (g : Genome) (m1 m2 : List Char) (gbs : Array ByteArray) (idxs : Array L) (R1 R2 : ByteArray)
    (hg : GenomeBytes gbs g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hlk : LookAll lk gbs idxs)
    (hok1 : fastOk R1 = true) (hok2 : fastOk R2 = true) :
    pairFastI lk lo hi gbs idxs R1 R2 = pairSpec sc0 (-12) lo hi g m1 m2 := by
  unfold pairFastI pairSpec
  rw [mapFastI_eq_mapSpecBoth lk g m1 gbs idxs R1 false hg h1 hlk hok1]
  cases mapSpecBoth sc0 (-12) g m1 with
  | none => rfl
  | some a =>
    simp only
    rw [mapFastI_eq_mapSpecBoth lk g m2 gbs idxs R2 _ hg h2 hlk hok2]
    cases mapSpecBoth sc0 (-12) g m2 <;> rfl

/-- The same through minimizer indexes that pass the checker. -/
theorem pairFastI_mz_eq_pairSpec (lo hi : Nat) (g : Genome) (m1 m2 : List Char) (gbs : Array ByteArray)
    (idxs : Array Mz.MzIdx) (R1 R2 : ByteArray) (hg : GenomeBytes gbs g) (h1 : Encodes R1 m1)
    (h2 : Encodes R2 m2) (hchk : checkAllMz idxs gbs = true)
    (hok1 : fastOk R1 = true) (hok2 : fastOk R2 = true) :
    pairFastI mzL lo hi gbs idxs R1 R2 = pairSpec sc0 (-12) lo hi g m1 m2 := by
  apply pairFastI_eq_pairSpec mzL lo hi g m1 m2 gbs idxs R1 R2 hg h1 h2 _ hok1 hok2
  intro c hc R' j hj
  unfold checkAllMz at hchk
  simp only [List.all_eq_true, List.mem_range] at hchk
  exact mzLook_ok _ _ _ _ hj (by rw [← Mz.check2_eq]; exact hchk c hc)

end MapSpec.Fast

#print axioms MapSpec.Fast.mapFastI_eq_mapSpecBoth
#print axioms MapSpec.Fast.pairFastI_eq_pairSpec
#print axioms MapSpec.Fast.pairFastI_mz_eq_pairSpec
