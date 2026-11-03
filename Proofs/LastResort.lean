import Proofs.Report

/-! # The last step: no answer without a pair unless it is junk

Spec's `.unknown` clause: an answer without a pair must have `bestPossibleScore < junkScore`. The router and
the fallback (`Proofs/Report.lean`) find a real proper pair for almost every pair; for the rest (`finalize`):

* some chromosome has at least `lo` letters (and `lo ≤ hi`): the degenerate proper pair — mate 1 forward on
  the empty window `[0, 0)`, mate 2 reverse on `[lo, lo)`, each aligned as insertions only (`degenerate_sound`);
* else no proper pair exists at all (`no_proper`), so any bound holds: `junkScore - 1`.

The chromosome lengths come from the index (`ns`), or from the lengths record `buildIndex` writes when its
check fails (`Proofs/Aligner.lean`). -/

namespace Spec.LastResort

open Bridge

/-! ## The degenerate pair -/

-- insertions only: a path of the read against no letters
def gapPath (q : Read) : Path q [] :=
  ⟨List.replicate q.length .gapY, by simp [List.count_replicate], by simp [List.count_replicate]⟩

-- a mate's line at the empty window `p` (its letters on `p`'s strand all inserted)
def emptyReport (p : Placement) (read : Read) : MateReport :=
  ⟨p, (gapPath (p.strand.orient read)).cigar, (gapPath (p.strand.orient read)).score defaultScoring⟩

-- mate 1 forward on `[0, 0)`, mate 2 reverse on `[lo, lo)`, chromosome `c`
def degeneratePair (c lo : Nat) (m1 m2 : Read) : PairReport :=
  ⟨emptyReport ⟨c, 0, 0, .forward⟩ m1, emptyReport ⟨c, lo, lo, .reverse⟩ m2⟩

theorem empty_fits {genome : Genome} {c s : Nat} {chr : Chromosome} (hc : genome[c]? = some chr)
    (hs : s ≤ chr.seq.length) (st : Strand) :
    (⟨c, s, s, st⟩ : Placement).reference genome = some [] := by
  unfold Placement.reference
  simp [hc, hs]

-- the alignment printed by `emptyReport`
def emptyAlignment {genome : Genome} (read : Read) (p : Placement) (h : p.reference genome = some []) :
    GenomicAlignment genome read :=
  ⟨p, [], h, gapPath (p.strand.orient read)⟩

theorem degenerate_sound {genome : Genome} {m1 m2 : Read} (range : Nat × Nat) (slack c : Nat) (chr : Chromosome)
    (hc : genome[c]? = some chr) (hlo : range.1 ≤ chr.seq.length) (hr : range.1 ≤ range.2) :
    ∃ pair : PairAlignment genome m1 m2,
      pair.report = degeneratePair c range.1 m1 m2 ∧ pair.IsProper range slack := by
  refine ⟨⟨emptyAlignment m1 _ (empty_fits hc (Nat.zero_le _) .forward),
    emptyAlignment m2 _ (empty_fits hc hlo .reverse)⟩, rfl, ?_⟩
  obtain ⟨lo, hi⟩ := range
  simp only at hlo hr
  simp [PairAlignment.IsProper, emptyAlignment]
  omega

/-! ## No proper pair at all -/

theorem stop_le {genome : Genome} {read : Read} (a : GenomicAlignment genome read) :
    ∃ chr, genome[a.placement.chromosome]? = some chr ∧ a.placement.stop ≤ chr.seq.length := by
  have h := a.fits
  unfold Placement.reference at h
  cases hg : genome[a.placement.chromosome]? with
  | none => rw [hg] at h; cases h
  | some chr =>
    refine ⟨chr, rfl, ?_⟩
    rw [hg] at h
    by_cases hc : a.placement.start ≤ a.placement.stop ∧ a.placement.stop ≤ chr.seq.length
    · exact hc.2
    · simp [hc] at h

theorem no_proper {genome : Genome} {m1 m2 : Read} (range : Nat × Nat) (slack : Nat)
    (h : range.2 < range.1 ∨ ∀ (c : Nat) (chr : Chromosome), genome[c]? = some chr → chr.seq.length < range.1)
    (pair : PairAlignment genome m1 m2) : ¬ pair.IsProper range slack := by
  intro hp
  obtain ⟨lo, hi⟩ := range
  obtain ⟨c1, h1, s1⟩ := stop_le pair.first
  obtain ⟨c2, h2, s2⟩ := stop_le pair.second
  unfold PairAlignment.IsProper at hp
  simp only at hp h
  generalize pair.first.placement = p at *
  generalize pair.second.placement = q at *
  obtain ⟨pc, ps, pe, pst⟩ := p
  obtain ⟨qc, qs, qe, qst⟩ := q
  simp only at hp h1 h2 s1 s2
  rcases h with h | h
  · cases pst <;> cases qst <;> simp_all <;> omega
  · have l1 := h _ _ h1
    have l2 := h _ _ h2
    cases pst <;> cases qst <;> simp_all <;> omega

/-! ## The last step -/

-- `fit lo`: a chromosome where the degenerate pair fits (none: no chromosome has `lo` letters); the mates
-- and `fit` are only used (decoded, searched) when the answer has no pair and is not junk
def finalize (insertSettings : InsertSettings) (fit : Nat → Option Nat) (R1 R2 : ByteArray) (a : PairAnswer) :
    PairAnswer :=
  if a.found.isNone && decide (insertSettings.junkScore ≤ a.bestPossibleScore) then
    match (if insertSettings.range.1 ≤ insertSettings.range.2 then fit insertSettings.range.1 else none) with
    | some c => { a with found := some (degeneratePair c insertSettings.range.1 (decodeRead R1) (decodeRead R2)),
                         uniqueness := .unknown }
    | none => { a with bestPossibleScore := insertSettings.junkScore - 1, uniqueness := .unknown }
  else a

theorem finalize_correct {insertSettings : InsertSettings} {genome : Genome} {R1 R2 : ByteArray} {a : PairAnswer}
    (fit : Nat → Option Nat)
    (hfit : ∀ c, fit insertSettings.range.1 = some c → ∃ chr, genome[c]? = some chr ∧ insertSettings.range.1 ≤ chr.seq.length)
    (hnone : fit insertSettings.range.1 = none →
      ∀ (c : Nat) (chr : Chromosome), genome[c]? = some chr → chr.seq.length < insertSettings.range.1)
    (ha : CorrectU insertSettings genome (decodeRead R1) (decodeRead R2) a) :
    (finalize insertSettings fit R1 R2 a).Correct insertSettings genome (decodeRead R1) (decodeRead R2) := by
  obtain ⟨hf, hb, hu⟩ := ha
  unfold finalize
  by_cases hc : (a.found.isNone && decide (insertSettings.junkScore ≤ a.bestPossibleScore)) = true
  · rw [if_pos hc]
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, decide_eq_true_eq] at hc
    split
    · rename_i c hcf
      have hr : insertSettings.range.1 ≤ insertSettings.range.2 := by
        by_cases hn : insertSettings.range.1 ≤ insertSettings.range.2
        · exact hn
        · rw [if_neg hn] at hcf; cases hcf
      rw [if_pos hr] at hcf
      obtain ⟨chr, hg, hl⟩ := hfit c hcf
      obtain ⟨pair, hrep, hprop⟩ := degenerate_sound (m1 := decodeRead R1) (m2 := decodeRead R2) insertSettings.range
        insertSettings.dovetailSlack c chr hg hl hr
      refine ⟨fun rep h => ?_, hb, fun h => by cases h⟩
      cases h
      exact ⟨pair, hrep, hprop⟩
    · rename_i hcf
      have hno : ∀ pair : PairAlignment genome (decodeRead R1) (decodeRead R2), ¬ pair.IsProper insertSettings.range insertSettings.dovetailSlack := by
        apply no_proper
        by_cases hr : insertSettings.range.1 ≤ insertSettings.range.2
        · rw [if_pos hr] at hcf
          exact .inr (hnone hcf)
        · exact .inl (by omega)
      refine ⟨fun rep h => hf rep h, fun pair hp => absurd hp (hno pair), fun _ => by simp only; omega⟩
  · rw [if_neg hc]
    refine ⟨hf, hb, ?_⟩
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, decide_eq_true_eq, not_and] at hc
    cases hq : a.uniqueness with
    | unique => rw [hq] at hu; exact hu
    | multimapper => rw [hq] at hu; exact hu
    | unknown => intro h0; have := hc h0; omega
    | repetitiveUnknown => rw [hq] at hu; exact hu

/-! ## Chromosome lengths, from the index or from the lengths record -/

-- the first chromosome with at least `lo` letters
def fitNs (ns : Array Nat) (lo : Nat) : Option Nat := (List.range ns.size).find? fun c => decide (lo ≤ ns[c]!)

theorem fitNs_ok {genome : Genome} {ns : Array Nat} (lo : Nat) (hlen : genome.length = ns.size)
    (hchr : ∀ c, c < ns.size → ∃ chr : Chromosome, genome[c]? = some chr ∧ chr.seq.length = ns[c]!) :
    (∀ c, fitNs ns lo = some c → ∃ chr, genome[c]? = some chr ∧ lo ≤ chr.seq.length) ∧
    (fitNs ns lo = none → ∀ (c : Nat) (chr : Chromosome), genome[c]? = some chr → chr.seq.length < lo) := by
  refine ⟨fun c h => ?_, fun h c chr hg => ?_⟩
  · have hm := List.mem_of_find?_eq_some h
    have hp := List.find?_some h
    simp only [decide_eq_true_eq] at hp
    obtain ⟨chr, hg, hl⟩ := hchr c (List.mem_range.1 hm)
    exact ⟨chr, hg, by omega⟩
  · have hc : c < ns.size := by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hg).1
    have hn := List.find?_eq_none.1 h c (List.mem_range.2 hc)
    simp only [decide_eq_true_eq] at hn
    obtain ⟨chr', hg', hl⟩ := hchr c hc
    rw [hg] at hg'; cases hg'
    omega

-- a number as base-255 digits (each stored + 1, so never 0), lowest first
def encNat (n : Nat) : List UInt8 :=
  if h : n = 0 then [] else (n % 255 + 1).toUInt8 :: encNat (n / 255)
termination_by n
decreasing_by omega

-- digits up to a 0 byte
def decNat : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: rest => if b = 0 then some (0, rest) else (decNat rest).map fun (n, r) => (b.toNat - 1 + 255 * n, r)

theorem decNat_encNat (n : Nat) (rest : List UInt8) : decNat (encNat n ++ 0 :: rest) = some (n, rest) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    unfold encNat
    by_cases h : n = 0
    · subst h; simp [decNat]
    · rw [dif_neg h]
      have hb : (n % 255 + 1).toUInt8.toNat = n % 255 + 1 := by
        rw [Nat.toUInt8_eq, UInt8.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
      have hne : (n % 255 + 1).toUInt8 ≠ 0 := by
        intro e; have := congrArg UInt8.toNat e; rw [hb] at this; simp at this
      simp only [List.cons_append, decNat, hne, if_false, ih (n / 255) (by omega), Option.map_some, hb]
      congr 2
      omega

-- the lengths record: a 4-byte tag, then each length followed by a 0 byte
def lensTag : List UInt8 := [76, 69, 78, 83]

def encLens (ls : List Nat) : List UInt8 := lensTag ++ ls.flatMap fun n => encNat n ++ [0]

def decLensGo : Nat → List UInt8 → Option (List Nat)
  | _, [] => some []
  | 0, _ :: _ => none
  | f + 1, bs => match decNat bs with
    | some (n, r) => (decLensGo f r).map (n :: ·)
    | none => none

def decLens (bs : List UInt8) : Option (List Nat) :=
  if bs.take 4 = lensTag then decLensGo bs.length (bs.drop 4) else none

theorem decLensGo_enc (ls : List Nat) : ∀ f, (ls.flatMap fun n => encNat n ++ [0]).length ≤ f →
    decLensGo f (ls.flatMap fun n => encNat n ++ [0]) = some ls := by
  induction ls with
  | nil => intro f _; cases f <;> rfl
  | cons n ls ih =>
    intro f hf
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil] at hf
    cases f with
    | zero => omega
    | succ f =>
      have e : (encNat n ++ [0]) ++ ls.flatMap (fun n => encNat n ++ [0]) =
          encNat n ++ 0 :: ls.flatMap (fun n => encNat n ++ [0]) := by simp
      rw [List.flatMap_cons, e]
      cases hq : encNat n ++ 0 :: ls.flatMap (fun n => encNat n ++ [0]) with
      | nil => simp at hq
      | cons b r =>
        show (match decNat (b :: r) with
          | some (n, r) => (decLensGo f r).map (n :: ·) | none => none) = _
        rw [← hq, decNat_encNat]
        show (decLensGo f _).map (n :: ·) = _
        rw [ih f (by omega)]
        rfl

theorem decLens_enc (ls : List Nat) : decLens (encLens ls) = some ls := by
  unfold decLens encLens
  rw [List.take_left' (by rfl : lensTag.length = 4), List.drop_left' (by rfl : lensTag.length = 4), if_pos rfl]
  exact decLensGo_enc ls _ (by simp)

-- as bytes
def lensRecord (ls : List Nat) : ByteArray := ⟨(encLens ls).toArray⟩

-- the tag is tested on the bytes first: a real index is never turned into a list
def readLens (b : ByteArray) : Option (List Nat) :=
  if 4 ≤ b.size && b.get! 0 == 76 && b.get! 1 == 69 && b.get! 2 == 78 && b.get! 3 == 83 then decLens b.toList
  else none

theorem readLens_record (ls : List Nat) : readLens (lensRecord ls) = some ls := by
  unfold readLens
  have h : (4 ≤ (lensRecord ls).size && (lensRecord ls).get! 0 == 76 && (lensRecord ls).get! 1 == 69 &&
      (lensRecord ls).get! 2 == 78 && (lensRecord ls).get! 3 == 83) = true := by
    simp [lensRecord, encLens, lensTag, ByteArray.size, ByteArray.get!]
  rw [if_pos h]
  unfold lensRecord
  rw [Bridge.byteArray_toList]
  exact decLens_enc ls

end Spec.LastResort
