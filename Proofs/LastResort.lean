import Proofs.Report

/-! # The last step: the report floor

Spec's `PairAnswer.Correct` asks two things the router's answers (`CorrectU`) do not:
* every printed pair scores at least `junkScore` (clause 1, any uniqueness);
* an answer without a pair (`.unknown`) has `bestPossibleScore < requiredMapBound`.

`finalize` checks the first on the pair in hand (its printed score is the pair's score, `score_of_report`) and
drops a pair below `junkScore`. A pair that is `.unique` / `.multimapper` is a best proper pair, so its own score
is then a proved bound (`provedBound`). Without a pair, the answer is correct when its bound is
`< requiredMapBound`, or when no proper pair exists at all (`no_proper`: no chromosome has `range.1` letters, or
the range is empty), where any bound holds: `requiredMapBound - 1`.

What is left is the LEFTOVER (`Leftover`): no pair `≥ junkScore` in hand and no proved bound
`< requiredMapBound`. Spec has no answer for it yet. `finalize_correct` proves: the answer is `Correct`, or it is
a leftover and still `CorrectU` (its pair-free bound is true). The degenerate all-insertion pair is never printed.

The chromosome lengths come from the index (`ns`), or from the lengths record `buildIndex` writes when its
check fails (`Proofs/Aligner.lean`). -/

namespace Spec.LastResort

open Bridge

/-! ## A printed pair's score -/

-- the pair's score as printed (`score_of_report`)
def repScore (rep : PairReport) : Int := rep.mate1.score + rep.mate2.score

theorem score_of_report {genome : Genome} {m1 m2 : Read} {pair : PairAlignment genome m1 m2} {rep : PairReport}
    (h : pair.report = rep) : pair.score = repScore rep := by
  subst h; rfl

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

-- no proper pair exists at all: the range is empty, or no chromosome has `range.1` letters (`fit` finds none)
def noPair (insertSettings : InsertSettings) (fit : Nat → Option Nat) : Bool :=
  !(decide (insertSettings.range.1 ≤ insertSettings.range.2) && (fit insertSettings.range.1).isSome)

-- a bound the answer proves: its own, or (a best proper pair in hand) the pair's score if lower
def provedBound (a : PairAnswer) : Int :=
  match a.found, a.uniqueness with
  | some rep, .unique => min a.bestPossibleScore (repScore rep)
  | some rep, .multimapper => min a.bestPossibleScore (repScore rep)
  | _, _ => a.bestPossibleScore

-- no pair, bound `b`: below `requiredMapBound`, or `requiredMapBound - 1` when no proper pair exists;
-- otherwise the bound stays `b` (a leftover)
def boundOnly (insertSettings : InsertSettings) (fit : Nat → Option Nat) (b : Int) (a : PairAnswer) : PairAnswer :=
  { a with found := none, uniqueness := .unknown,
           bestPossibleScore :=
             if b < insertSettings.requiredMapBound then b
             else if noPair insertSettings fit then insertSettings.requiredMapBound - 1 else b }

-- `fit lo`: a chromosome with at least `lo` letters (none: no chromosome has `lo` letters)
def finalize (insertSettings : InsertSettings) (fit : Nat → Option Nat) (a : PairAnswer) : PairAnswer :=
  match a.found with
  | some rep =>
    if insertSettings.junkScore ≤ repScore rep then a
    else boundOnly insertSettings fit (provedBound a) a
  | none => boundOnly insertSettings fit a.bestPossibleScore a

-- THE LEFTOVER: no pair and no proved bound below `requiredMapBound`. Spec has no correct answer for it yet.
def Leftover (insertSettings : InsertSettings) (a : PairAnswer) : Prop :=
  a.found = none ∧ insertSettings.requiredMapBound ≤ a.bestPossibleScore

instance (insertSettings : InsertSettings) (a : PairAnswer) : Decidable (Leftover insertSettings a) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem provedBound_ok {insertSettings : InsertSettings} {genome : Genome} {m1 m2 : Read} {a : PairAnswer}
    (ha : CorrectU insertSettings genome m1 m2 a) (pair : PairAlignment genome m1 m2)
    (hp : pair.IsProper insertSettings.range insertSettings.dovetailSlack) : pair.score ≤ provedBound a := by
  obtain ⟨-, hb, hu⟩ := ha
  have h0 := hb pair hp
  unfold provedBound
  cases hf : a.found with
  | none => exact h0
  | some rep =>
    cases hq : a.uniqueness with
    | unknown => exact h0
    | unique =>
      rw [hq] at hu
      obtain ⟨rep', hr', best, hbr, hbest⟩ := hu
      rw [hf] at hr'; cases hr'
      have := hbest.1.2 pair hp
      rw [score_of_report hbr] at this
      simp only; omega
    | multimapper =>
      rw [hq] at hu
      obtain ⟨rep', hr', best, -, hbr, hbest, -⟩ := hu
      rw [hf] at hr'; cases hr'
      have := hbest.2 pair hp
      rw [score_of_report hbr] at this
      simp only; omega

theorem boundOnly_correct {insertSettings : InsertSettings} {genome : Genome} {m1 m2 : Read}
    (fit : Nat → Option Nat)
    (hnone : fit insertSettings.range.1 = none →
      ∀ (c : Nat) (chr : Chromosome), genome[c]? = some chr → chr.seq.length < insertSettings.range.1)
    (a : PairAnswer) (b : Int)
    (hb : ∀ pair : PairAlignment genome m1 m2,
      pair.IsProper insertSettings.range insertSettings.dovetailSlack → pair.score ≤ b) :
    (boundOnly insertSettings fit b a).Correct insertSettings genome m1 m2 ∨
      (Leftover insertSettings (boundOnly insertSettings fit b a) ∧
        CorrectU insertSettings genome m1 m2 (boundOnly insertSettings fit b a)) := by
  have hno : noPair insertSettings fit = true →
      ∀ pair : PairAlignment genome m1 m2, ¬ pair.IsProper insertSettings.range insertSettings.dovetailSlack := by
    intro h
    apply no_proper
    simp only [noPair, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
      Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
    rcases h with h | h
    · exact .inl (by omega)
    · exact .inr (hnone h)
  unfold boundOnly
  by_cases h1 : b < insertSettings.requiredMapBound
  · left
    rw [if_pos h1]
    exact ⟨fun _ h => by simp at h, hb, fun _ => h1⟩
  · rw [if_neg h1]
    by_cases h2 : noPair insertSettings fit = true
    · left
      rw [if_pos h2]
      exact ⟨fun _ h => by simp at h, fun pair hp => absurd hp (hno h2 pair),
        fun _ => show insertSettings.requiredMapBound - 1 < insertSettings.requiredMapBound by omega⟩
    · right
      rw [if_neg h2]
      exact ⟨⟨rfl, show insertSettings.requiredMapBound ≤ b by omega⟩, fun _ h => by simp at h, hb, trivial⟩

-- the answer is correct, or it is a leftover whose pair-free bound is still true
theorem finalize_correct {insertSettings : InsertSettings} {genome : Genome} {m1 m2 : Read} {a : PairAnswer}
    (fit : Nat → Option Nat)
    (hnone : fit insertSettings.range.1 = none →
      ∀ (c : Nat) (chr : Chromosome), genome[c]? = some chr → chr.seq.length < insertSettings.range.1)
    (ha : CorrectU insertSettings genome m1 m2 a) :
    (finalize insertSettings fit a).Correct insertSettings genome m1 m2 ∨
      (Leftover insertSettings (finalize insertSettings fit a) ∧
        CorrectU insertSettings genome m1 m2 (finalize insertSettings fit a)) := by
  unfold finalize
  cases hf : a.found with
  | none => exact boundOnly_correct fit hnone a _ ha.2.1
  | some rep =>
    simp only
    by_cases hj : insertSettings.junkScore ≤ repScore rep
    · rw [if_pos hj]
      left
      obtain ⟨h1, h2, h3⟩ := ha
      refine ⟨fun rep' h => ?_, h2, ?_⟩
      · obtain ⟨pair, hr, hp⟩ := h1 rep' h
        rw [hf] at h; cases h
        exact ⟨pair, hr, hp, by rw [score_of_report hr]; exact hj⟩
      · cases hq : a.uniqueness with
        | unique => rw [hq] at h3; exact h3
        | multimapper => rw [hq] at h3; exact h3
        | unknown => intro h; rw [hf] at h; cases h
    · rw [if_neg hj]
      exact boundOnly_correct fit hnone a _ (provedBound_ok ha)

/-! ## A second look at a leftover: the exact pair search at 16

`pairGXE` at `Gc = 16` (`pairGXE_sound`) lists every proper pair of the mates' hits within 16 and keeps those
scoring `≥ -16`. Every mate of a pair `≥ -16` scores `≥ -16`, so its seeds (the pigeonhole of `hitsKPF`) put it in
the list: nothing seen proves every proper pair `< -16` (a T3 with pair floor `pf = 16`, bound `-17`); a pair seen
is the unique best (T1u) or a proved tie (T1um, one tied pair in hand: `tie16`) at every caps `≥ 16`. -/

-- a pair of the tie (unproved: the printed pair is re-checked, `Report.foundOf`): the top proper pair of the
-- mates' hits within 16, as `pairGXE` lists them
open MapSpec MapSpec.Fast in
def tie16 (usl lo hi : Nat) (pk : PkMz) (offs : Array Nat) (pgs : Array PGen) (a b : ByteArray) : Option PairHit :=
  let lX := hitsKPF pk ByteArray.empty offs pgs a 16
  topW dcost0 (properPairsF usl lo hi lX (hitsKPFN usl hi pk ByteArray.empty offs pgs b 16 lX))

open MapSpec MapSpec.Fast in
def search16 (usl lo hi : Nat) (pk : PkMz) (offs : Array Nat) (pgs : Array PGen) (a b : ByteArray)
    (t : TierOut) : TierOut :=
  match pairGXE dcost0 usl lo hi 16 false pk offs pgs a b with
  | some (some (x, y), true) =>
    { t with tag := .t1u, g0 := 16,
             m1 := { st := "P", cap := t.m1.cap, pen := (-x.2).toNat, pl := some x },
             m2 := { st := "P", cap := t.m2.cap, pen := (-y.2).toNat, pl := some y } }
  | some (none, true) =>
    let tp := tie16 usl lo hi pk offs pgs a b
    { t with tag := .t1um, g0 := 16,
             m1 := { st := "P", cap := t.m1.cap, pl := tp.map (·.1) },
             m2 := { st := "P", cap := t.m2.cap, pl := tp.map (·.2) } }
  | some (_, false) => { tag := .t3, pf := some 16 }
  | none => t

open MapSpec MapSpec.Fast in
theorem search16_ok {usl lo hi : Nat} {g : MapSpec.Genome} {m1 m2 : List Char} {ix : Mz.MzIdx} {G : PGen}
    {offs ns : Array Nat} (hcut : cutOk G offs ns = true) (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) g)
    (hchk : Mz.check2P ix G = true) {a b : ByteArray} (ha : Encodes a m1) (hb : Encodes b m2) {t : TierOut}
    (hT : TierOk usl lo hi g m1 m2 (some a) (some b) t) :
    TierOk usl lo hi g m1 m2 (some a) (some b) (search16 usl lo hi ((ix, G) : PkMz) offs (cutAll G offs ns) a b t) := by
  have S := fun r seen P1 P2 (h1 : 16 ≤ P1) (h2 : 16 ≤ P2) h =>
    pairGXE_sound dcost0 usl lo hi 16 g m1 m2 ix G offs ns a b hcut hg ha hb hchk (Nat.le_refl _) false
      P1 P2 h1 h2 r seen h
  have floor : ∀ r, pairGXE dcost0 usl lo hi 16 false ((ix, G) : PkMz) offs (cutAll G offs ns) a b = some (r, false) →
      TierOk usl lo hi g m1 m2 (some a) (some b) ({ tag := .t3, pf := some 16 } : TierOut) := by
    intro r hq
    show FloorOk usl lo hi g m1 m2 _
    refine ⟨mateFloor_zero _ _, mateFloor_zero _ _, fun G0 hG0 P1 P2 h1 h2 w hw => ?_⟩
    cases hG0
    rcases Int.lt_or_le (pairScoreD dcost0 w) (-((16 : Nat) : Int)) with h | h
    · exact h
    · exact absurd ((S r false P1 P2 h1 h2 hq).1.mpr ⟨w, hw, h⟩) Bool.false_ne_true
  unfold search16
  rcases hq : pairGXE dcost0 usl lo hi 16 false ((ix, G) : PkMz) offs (cutAll G offs ns) a b with
    _ | ⟨_ | ⟨x, y⟩, _ | _⟩
  · exact hT
  · exact floor _ hq
  · exact ⟨Nat.le_refl _, fun P1 P2 h1 h2 => (S _ _ P1 P2 h1 h2 hq).2.2 rfl rfl⟩
  · exact floor _ hq
  · exact ⟨Nat.le_refl _, fun P1 P2 h1 h2 => ⟨x, y, rfl, rfl, ((S _ _ P1 P2 h1 h2 hq).2.1 rfl).symm⟩⟩

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
