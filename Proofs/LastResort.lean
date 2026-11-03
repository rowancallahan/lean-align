import Proofs.Report
import AlignmentWavefront

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
`< requiredMapBound` (closed by the second look below, `look_not_leftover`). `finalize_correct` proves: the answer is `Correct`, or it is
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
def boundOnly (insertSettings : InsertSettings) (fit : Nat → Option Nat) (req b : Int) (a : PairAnswer) : PairAnswer :=
  { a with found := none, uniqueness := .unknown,
           bestPossibleScore :=
             if b < req then b
             else if noPair insertSettings fit then req - 1 else b }

-- `fit lo`: a chromosome with at least `lo` letters (none: no chromosome has `lo` letters);
-- `req`: the mates' `requiredMapBound`
def finalize (insertSettings : InsertSettings) (fit : Nat → Option Nat) (req : Int) (a : PairAnswer) : PairAnswer :=
  match a.found with
  | some rep =>
    if insertSettings.junkScore ≤ repScore rep then a
    else boundOnly insertSettings fit req (provedBound a) a
  | none => boundOnly insertSettings fit req a.bestPossibleScore a

-- THE LEFTOVER: no pair and no proved bound below `req` (no correct answer in hand).
def Leftover (req : Int) (a : PairAnswer) : Prop :=
  a.found = none ∧ req ≤ a.bestPossibleScore

instance (req : Int) (a : PairAnswer) : Decidable (Leftover req a) :=
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
    | repetitiveUnknown => exact h0
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
    (boundOnly insertSettings fit (requiredMapBound m1 m2) b a).Correct insertSettings genome m1 m2 ∨
      (Leftover (requiredMapBound m1 m2) (boundOnly insertSettings fit (requiredMapBound m1 m2) b a) ∧
        CorrectU insertSettings genome m1 m2 (boundOnly insertSettings fit (requiredMapBound m1 m2) b a)) := by
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
  by_cases h1 : b < requiredMapBound m1 m2
  · left
    rw [if_pos h1]
    exact ⟨fun _ h => by simp at h, hb, fun _ => h1⟩
  · rw [if_neg h1]
    by_cases h2 : noPair insertSettings fit = true
    · left
      rw [if_pos h2]
      exact ⟨fun _ h => by simp at h, fun pair hp => absurd hp (hno h2 pair),
        fun _ => show requiredMapBound m1 m2 - 1 < requiredMapBound m1 m2 by omega⟩
    · right
      rw [if_neg h2]
      exact ⟨⟨rfl, show requiredMapBound m1 m2 ≤ b by omega⟩, fun _ h => by simp at h, hb, trivial⟩

-- the answer is correct, or it is a leftover whose pair-free bound is still true
theorem finalize_correct {insertSettings : InsertSettings} {genome : Genome} {m1 m2 : Read} {a : PairAnswer}
    (fit : Nat → Option Nat)
    (hnone : fit insertSettings.range.1 = none →
      ∀ (c : Nat) (chr : Chromosome), genome[c]? = some chr → chr.seq.length < insertSettings.range.1)
    (ha : CorrectU insertSettings genome m1 m2 a) :
    (finalize insertSettings fit (requiredMapBound m1 m2) a).Correct insertSettings genome m1 m2 ∨
      (Leftover (requiredMapBound m1 m2) (finalize insertSettings fit (requiredMapBound m1 m2) a) ∧
        CorrectU insertSettings genome m1 m2 (finalize insertSettings fit (requiredMapBound m1 m2) a)) := by
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
        | repetitiveUnknown => rw [hq] at h3; rw [hf] at h3; cases h3
    · rw [if_neg hj]
      exact boundOnly_correct fit hnone a _ (provedBound_ok ha)

/-! ## Two genomes with the same letters (names aside) have the same answers -/

theorem reference_congr {g g' : Genome} (h : g.map (·.seq) = g'.map (·.seq)) (p : Placement) :
    p.reference g = p.reference g' := by
  have hc : (g[p.chromosome]?).map (·.seq) = (g'[p.chromosome]?).map (·.seq) := by
    rw [← List.getElem?_map, ← List.getElem?_map, h]
  unfold Placement.reference
  cases h1 : g[p.chromosome]? <;> cases h2 : g'[p.chromosome]? <;> rw [h1, h2] at hc <;> simp_all

def transferG {g g' : Genome} (h : g.map (·.seq) = g'.map (·.seq)) {r : Read}
    (a : GenomicAlignment g r) : GenomicAlignment g' r :=
  ⟨a.placement, a.reference, (reference_congr h _).symm.trans a.fits, a.path⟩

def transferP {g g' : Genome} (h : g.map (·.seq) = g'.map (·.seq)) {m1 m2 : Read}
    (p : PairAlignment g m1 m2) : PairAlignment g' m1 m2 :=
  ⟨transferG h p.first, transferG h p.second⟩

theorem correct_transfer {insertSettings : InsertSettings} {g g' : Genome} (h : g.map (·.seq) = g'.map (·.seq))
    {m1 m2 : Read} {a : PairAnswer} (hu : a.uniqueness = .unknown)
    (ha : a.Correct insertSettings g m1 m2) : a.Correct insertSettings g' m1 m2 := by
  obtain ⟨h1, h2, h3⟩ := ha
  refine ⟨fun rep hr => ?_, fun pair hp => ?_, ?_⟩
  · obtain ⟨pair, hrep, hp, hs⟩ := h1 rep hr
    exact ⟨transferP h pair, hrep, hp, hs⟩
  · exact h2 (transferP h.symm pair) hp
  · rw [hu] at h3 ⊢; exact h3

theorem finalize_unknown {insertSettings : InsertSettings} {fit : Nat → Option Nat} {req : Int} {a : PairAnswer}
    (hu : a.uniqueness = .unknown) : (finalize insertSettings fit req a).uniqueness = .unknown := by
  unfold finalize
  split
  · split
    · exact hu
    · rfl
  · rfl

/-! ## A second look at a leftover: every proper pair within the cap, printed without a re-check

`pairsAt` lists every proper pair of the mates' hits within the cap `c ≤ 16` (`pairsAt_mem`: the seed pigeonhole
`hitsKPF_mem` and the near-partner list `hitsKPFN`, as in `pairGXE_sound`) scoring `≥ -c`. `lookAnswer`: none
listed proves every proper pair `< -c` (bound `-(c + 1)`); else the top one is a best proper pair (bound: its
score), printed at its placements with the CIGAR of the proved optimal aligner (`bandDoublingAlign` =
`getBestAlignment`), which is a real alignment by construction (`cigarOk_of_hit`): nothing is re-checked. -/

section look
open MapSpec MapSpec.Fast AlignmentSpec

-- the CIGAR (unit runs) of the optimal alignment of `xs` against `ys`
def runsOf (xs ys : List Char) : List (AlignmentSpec.Step × Nat) :=
  match bandDoublingAlign sc0 xs ys with
  | some (path, _) => path.map fun st => (st, 1)
  | none => []

theorem expand_units : ∀ path : List AlignmentSpec.Step, expandCigar (path.map fun st => (st, 1)).toArray = path
  | [] => rfl
  | a :: rest => by
    have := expand_units rest
    simp only [expandCigar, List.map_cons, List.toList_toArray, List.flatMap_cons, List.replicate_one,
      List.singleton_append] at this ⊢
    rw [this]

-- a hit's window, aligned optimally, is a real alignment with the hit's score
theorem cigarOk_of_hit {g : MapSpec.Genome} {m : List Char} {T : Int} {x : MapSpec.Placement × Int}
    (hx : x ∈ hitsBoth sc0 T g m) {ys : List Char} (hys : windowSeq g x.1.1 = some ys) :
    CigarOk g m x (runsOf (strandRead m x.1.2) ys) := by
  obtain ⟨⟨w, st⟩, sx⟩ := x
  rw [mem_hitsBoth_T] at hx
  obtain ⟨-, hsc, -⟩ := hx
  have hws : windowScore sc0 (strandRead m st) g w = some sx := by
    cases st <;> exact hsc
  simp only at hys ⊢
  unfold windowScore at hws
  rw [hys] at hws
  simp only at hws
  obtain ⟨⟨path, bs⟩, hb⟩ := getBestAlignment_returns_some sc0 (strandRead m st) ys
  rw [hb] at hws
  simp only [Option.some.injEq] at hws
  subst hws
  obtain ⟨hw, hs⟩ := getBestAlignment_returns_a_valid_walk sc0 _ _ path _ hb
  have hr : runsOf (strandRead m st) ys = path.map fun st => (st, 1) := by
    unfold runsOf; rw [bandDoublingAlign_equals_getBestAlignment, hb]
  refine ⟨ys, hys, ?_, ?_⟩ <;> rw [hr, expand_units] <;> assumption

-- the pair printed for `w`
def pairOfHit (runs1 runs2 : MapSpec.Placement × Int → List (AlignmentSpec.Step × Nat)) (w : PairHit) : PairReport :=
  ⟨Report.mateReportOf w.1 (runs1 w.1), Report.mateReportOf w.2 (runs2 w.2)⟩

theorem old_new (x : MapSpec.Placement) : oldPlacement (newPlacement x) = x := by
  obtain ⟨⟨c, st, len⟩, sd⟩ := x
  cases sd <;> simp [oldPlacement, newPlacement, oldStrand, newStrand]

theorem pairOfHit_sound {genome : Genome} {m1 m2 : Read} {sl lo hi : Nat} {T1 T2 : Int}
    {runs1 runs2 : MapSpec.Placement × Int → List (AlignmentSpec.Step × Nat)}
    (hr1 : ∀ x ∈ hitsBoth sc0 T1 (oldGenome genome) m1, CigarOk (oldGenome genome) m1 x (runs1 x))
    (hr2 : ∀ x ∈ hitsBoth sc0 T2 (oldGenome genome) m2, CigarOk (oldGenome genome) m2 x (runs2 x))
    {w : PairHit} (hw : w ∈ properPairs sl lo hi (hitsBoth sc0 T1 (oldGenome genome) m1)
      (hitsBoth sc0 T2 (oldGenome genome) m2)) :
    ∃ pair : PairAlignment genome m1 m2, pair.report = pairOfHit runs1 runs2 w ∧
      pair.IsProper (lo, hi) sl ∧ pair.score = pairScoreD dcost0 w := by
  rw [mem_properPairs] at hw
  obtain ⟨h1, h2, hp⟩ := hw
  obtain ⟨a, ha⟩ := Report.alignment_of_cigar (hr1 _ h1)
  obtain ⟨b, hb⟩ := Report.alignment_of_cigar (hr2 _ h2)
  refine ⟨⟨a, b⟩, by simp only [PairAlignment.report, pairOfHit, ha, hb], ?_, ?_⟩
  · rw [isProper_iff]
    have pa : a.placement = newPlacement w.1.1 := by
      have := congrArg MateReport.placement ha; exact this
    have pb : b.placement = newPlacement w.2.1 := by
      have := congrArg MateReport.placement hb; exact this
    simp only [pa, pb, old_new]
    exact hp
  · have sa : a.score = w.1.2 := congrArg MateReport.score ha
    have sb : b.score = w.2.2 := congrArg MateReport.score hb
    simp only [PairAlignment.score, sa, sb, pairScoreD, dcost0]
    omega

-- the answer from the list of every proper pair scoring `≥ -c`
def lookAnswer (c : Nat) (runs1 runs2 : MapSpec.Placement × Int → List (AlignmentSpec.Step × Nat)) (ps : List PairHit) :
    PairAnswer :=
  match topW dcost0 ps with
  | none => { found := none, bestPossibleScore := -((c : Int) + 1), uniqueness := .unknown, tier := .boundsOnly }
  | some w => { found := some (pairOfHit runs1 runs2 w), bestPossibleScore := pairScoreD dcost0 w,
                uniqueness := .unknown, tier := .bestUnchecked }

theorem hit_at {g : MapSpec.Genome} {m : List Char} {T T' : Int} {x : MapSpec.Placement × Int}
    (hx : x ∈ hitsBoth sc0 T g m) (h : T' ≤ x.2) : x ∈ hitsBoth sc0 T' g m := by
  obtain ⟨p, sx⟩ := x
  rw [mem_hitsBoth_T] at hx ⊢
  exact ⟨hx.1, hx.2.1, h⟩

theorem lookAnswer_correct (insertSettings : InsertSettings) (genome : Genome) (m1 m2 : Read) (c : Nat)
    (runs1 runs2 : MapSpec.Placement × Int → List (AlignmentSpec.Step × Nat)) (ps : List PairHit)
    (HP : ∀ p, p ∈ ps ↔ p ∈ properPairs insertSettings.dovetailSlack insertSettings.range.1 insertSettings.range.2
        (hitsBoth sc0 (-(c : Int)) (oldGenome genome) m1) (hitsBoth sc0 (-(c : Int)) (oldGenome genome) m2) ∧
      -(c : Int) ≤ pairScoreD dcost0 p)
    (hr1 : ∀ x ∈ hitsBoth sc0 (-(c : Int)) (oldGenome genome) m1, CigarOk (oldGenome genome) m1 x (runs1 x))
    (hr2 : ∀ x ∈ hitsBoth sc0 (-(c : Int)) (oldGenome genome) m2, CigarOk (oldGenome genome) m2 x (runs2 x)) :
    CorrectU insertSettings genome m1 m2 (lookAnswer c runs1 runs2 ps) := by
  -- a proper pair of hits at any thresholds scoring `≥ -c` is listed
  have listed : ∀ T1 T2 : Int, ∀ w ∈ properPairs insertSettings.dovetailSlack insertSettings.range.1
      insertSettings.range.2 (hitsBoth sc0 T1 (oldGenome genome) m1) (hitsBoth sc0 T2 (oldGenome genome) m2),
      -(c : Int) ≤ pairScoreD dcost0 w → w ∈ ps := by
    intro T1 T2 w hw hs
    rw [mem_properPairs] at hw
    obtain ⟨h1, h2, hp⟩ := hw
    have n1 := hitsBoth_nonpos _ _ _ _ h1
    have n2 := hitsBoth_nonpos _ _ _ _ h2
    simp only [pairScoreD, dcost0] at hs
    exact (HP w).2 ⟨mem_properPairs.2 ⟨hit_at h1 (by omega), hit_at h2 (by omega), hp⟩, by
      simp only [pairScoreD, dcost0]; omega⟩
  unfold lookAnswer
  cases ht : topW dcost0 ps with
  | none =>
    have hps : ps = [] := (topW_none_iff dcost0 ps).1 ht
    let t : TierOut := { tag := .t3, pf := some c }
    have hok : TierOk insertSettings.dovetailSlack insertSettings.range.1 insertSettings.range.2
        (oldGenome genome) m1 m2 (some ByteArray.empty) (some ByteArray.empty) t := by
      show FloorOk _ _ _ _ _ _ _
      refine ⟨mateFloor_zero _ _, mateFloor_zero _ _, fun G0 hG0 P1 P2 _ _ w hw => ?_⟩
      cases hG0
      rcases Int.lt_or_le (pairScoreD dcost0 w) (-((c : Nat) : Int)) with h | h
      · exact h
      · have := listed _ _ w hw h; rw [hps] at this; cases this
    have A := answerOf_correct insertSettings genome m1 m2 _ _ t hok
    refine ⟨fun _ h => by simp at h, fun pair hp => ?_, trivial⟩
    have := A.2.1 pair hp
    simp only [answerOf, boundOf, t] at this
    show pair.score ≤ -((c : Int) + 1)
    omega
  | some w =>
    have hw := topW_mem dcost0 ps w ht
    have hmax := topW_max dcost0 ps w ht
    obtain ⟨hwp, hws⟩ := (HP w).1 hw
    have hwp' := hwp
    rw [mem_properPairs] at hwp'
    obtain ⟨h1, h2, hp⟩ := hwp'
    let t : TierOut := { tag := .t2b, m1 := { pl := some w.1 }, m2 := { pl := some w.2 } }
    have hok : TierOk insertSettings.dovetailSlack insertSettings.range.1 insertSettings.range.2
        (oldGenome genome) m1 m2 (some ByteArray.empty) (some ByteArray.empty) t := by
      refine ⟨w.1, w.2, rfl, rfl, mem_properPairs.2 ⟨hit_at h1 (Int.le_refl _), hit_at h2 (Int.le_refl _), hp⟩,
        fun T1 T2 w' hw' => ?_⟩
      rcases Int.lt_or_le (pairScoreD dcost0 w') (-(c : Int)) with h | h
      · exact Int.le_of_lt (Int.lt_of_lt_of_le h hws)
      · exact hmax w' (listed T1 T2 w' hw' h)
    have A := answerOf_correct insertSettings genome m1 m2 _ _ t hok
    refine ⟨fun rep h => ?_, fun pair hpp => ?_, trivial⟩
    · cases h
      obtain ⟨pair, hr, hpr, -⟩ := pairOfHit_sound hr1 hr2 hwp
      exact ⟨pair, hr, hpr⟩
    · have := A.2.1 pair hpp
      simp only [answerOf, boundOf, t] at this
      simp only [pairScoreD, dcost0]
      omega

-- what keeps `finalize` from a leftover: a pair `≥ junkScore` in hand, or a proved bound `< requiredMapBound`
theorem finalize_not_leftover {insertSettings : InsertSettings} {fit : Nat → Option Nat} {req : Int} {a : PairAnswer}
    (h : (∃ rep, a.found = some rep ∧ insertSettings.junkScore ≤ repScore rep) ∨
      provedBound a < req) :
    ¬ Leftover req (finalize insertSettings fit req a) := by
  have hbo : ∀ b, b < req → ¬ Leftover req (boundOnly insertSettings fit req b a) := by
    intro b hb hl
    have := hl.2
    simp only [boundOnly, if_pos hb] at this
    omega
  unfold finalize
  cases hf : a.found with
  | none =>
    simp only
    have hp : provedBound a = a.bestPossibleScore := by unfold provedBound; rw [hf]
    rcases h with ⟨rep, hr, -⟩ | h
    · rw [hf] at hr; cases hr
    · exact hbo _ (hp ▸ h)
  | some rep =>
    simp only
    by_cases hj : insertSettings.junkScore ≤ repScore rep
    · rw [if_pos hj]; intro hl; rw [hl.1] at hf; cases hf
    · rw [if_neg hj]
      rcases h with ⟨rep', hr, hj'⟩ | h
      · rw [hf] at hr; cases hr; exact absurd hj' hj
      · exact hbo _ h

-- the second look leaves no leftover when its cap reaches `requiredMapBound` and `junkScore ≤ requiredMapBound`
theorem look_not_leftover {insertSettings : InsertSettings} {fit : Nat → Option Nat} {req : Int} {c : Nat}
    {runs1 runs2 : MapSpec.Placement × Int → List (AlignmentSpec.Step × Nat)} {ps : List PairHit}
    (hc : -((c : Int) + 1) < req)
    (hj : insertSettings.junkScore ≤ req) :
    ¬ Leftover req (finalize insertSettings fit req (lookAnswer c runs1 runs2 ps)) := by
  apply finalize_not_leftover
  unfold lookAnswer
  cases topW dcost0 ps with
  | none => exact .inr (by simp only [provedBound]; exact hc)
  | some w =>
    simp only
    have hs : repScore (pairOfHit runs1 runs2 w) = pairScoreD dcost0 w := by
      simp only [repScore, pairOfHit, Report.mateReportOf, pairScoreD, dcost0]; omega
    by_cases h : insertSettings.junkScore ≤ pairScoreD dcost0 w
    · exact .inl ⟨_, rfl, hs ▸ h⟩
    · exact .inr (by simp only [provedBound]; omega)

/-! ### On the index: the hits from the seeds, the windows from the packed chromosomes -/

-- the read's letters on a strand, and a window's letters (as `chkCand` reads them)
def readChars (R : ByteArray) (st : MapSpec.Strand) : List Char :=
  let X := if st = .fwd then R else revCompK R
  ((List.range X.size).toArray.map fun i => Char.ofNat (X.get! i).toNat).toList

def winChars (pgs : Array PGen) (w : Window) : List Char :=
  ((List.range w.len).toArray.map fun i => Char.ofNat (pgs[w.chr]!.get (w.start + i)).toNat).toList

def runsIx (pgs : Array PGen) (R : ByteArray) (x : MapSpec.Placement × Int) : List (AlignmentSpec.Step × Nat) :=
  runsOf (readChars R x.1.2) (winChars pgs x.1.1)

theorem runsIx_ok {pgs : Array PGen} {g : MapSpec.Genome} (hg : GenomeBytes (pgs.map Mz.unpack) g)
    {R : ByteArray} {m : List Char} (hr : Encodes R m) {T : Int} {x : MapSpec.Placement × Int}
    (hx : x ∈ hitsBoth sc0 T g m) : CigarOk g m x (runsIx pgs R x) := by
  have hrc : readChars R x.1.2 = strandRead m x.1.2 := by
    unfold readChars
    cases hs : x.1.2
    · exact chars_of_encodes R m hr
    · exact chars_of_encodes _ _ (revCompK_encodes R m hr)
  have hwin : windowSeq g x.1.1 = some (winChars pgs x.1.1) := by
    obtain ⟨⟨w, st⟩, sx⟩ := x
    have hx' := hx
    rw [mem_hitsBoth_T] at hx'
    have hws : windowScore sc0 (strandRead m st) g w = some sx := by cases st <;> exact hx'.2.1
    obtain ⟨hc, hl⟩ := windowScore_fits g _ hg _ w sx hws
    simp only [Array.size_map] at hc
    have e : (pgs.map Mz.unpack)[w.chr]! = Mz.unpack pgs[w.chr]! := by
      rw [getElem!_pos (pgs.map Mz.unpack) w.chr (by simpa using hc), getElem!_pos pgs w.chr hc]; simp
    have hl' : w.start + w.len ≤ pgs[w.chr]!.n := by rw [e, unpack_size] at hl; exact hl
    exact chars_of_genome pgs g hg w.chr w.start w.len hc hl'
  unfold runsIx
  rw [hrc]
  exact cigarOk_of_hit hx hwin

-- every proper pair of the mates' hits within `c` scoring `≥ -c` (as `pairGXE` lists them). The mate whose
-- rarest seeds cost less (`costP`) is searched in full first, the other only near its hits (`keepN`); either
-- order lists the same pairs (`pairsAt_mem`), possibly in another order
def pairsAt (sl lo hi c : Nat) (pk : PkMz) (offs : Array Nat) (pgs : Array PGen) (R1 R2 : ByteArray) :
    List PairHit :=
  if costP pk c (prepMate pk R2) < costP pk c (prepMate pk R1) then
    let lY := hitsKPF pk ByteArray.empty offs pgs R2 c
    (properPairsF sl lo hi (hitsKPFN sl hi pk ByteArray.empty offs pgs R1 c lY) lY).filter
      fun p => decide (-(c : Int) ≤ pairScoreD dcost0 p)
  else
  let lX := hitsKPF pk ByteArray.empty offs pgs R1 c
  (properPairsF sl lo hi lX (hitsKPFN sl hi pk ByteArray.empty offs pgs R2 c lX)).filter
    fun p => decide (-(c : Int) ≤ pairScoreD dcost0 p)

theorem pairsAt_mem {sl lo hi c : Nat} (hc : c ≤ 16) {g : MapSpec.Genome} {m1 m2 : List Char} {ix : Mz.MzIdx}
    {G : PGen} {offs ns : Array Nat} (hcut : cutOk G offs ns = true)
    (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) g) (hchk : Mz.check2P ix G = true)
    {R1 R2 : ByteArray} (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (p : PairHit) :
    p ∈ pairsAt sl lo hi c ((ix, G) : PkMz) offs (cutAll G offs ns) R1 R2 ↔
      p ∈ properPairs sl lo hi (hitsBoth sc0 (-(c : Int)) g m1) (hitsBoth sc0 (-(c : Int)) g m2) ∧
        -(c : Int) ≤ pairScoreD dcost0 p := by
  have K1 := hitsKPF_mem g ix G offs ns hcut hg hchk R1 m1 h1 c hc
  have K2 := hitsKPF_mem g ix G offs ns hcut hg hchk R2 m2 h2 c hc
  unfold pairsAt
  split
  · rw [List.mem_filter, properPairsF_eq, pp_near_left (hitsKPFN_near sl lo hi _ _ _ _ _ c _) p,
      decide_eq_true_eq, mem_properPairs, mem_properPairs, K1, K2]
  · rw [List.mem_filter, properPairsF_eq, pp_near_right (hitsKPFN_near sl lo hi _ _ _ _ _ c _) p,
      decide_eq_true_eq, mem_properPairs, mem_properPairs, K1, K2]

/-! ### The budget split (SEARCH_IDEAS #1): settle "no pair" with cheaper full searches

A pair within `c` (`pen1 + pen2 ≤ c`) has mate 1 within `a` or mate 2 within `c - a - 1`. So searching mate 1 in
full at cap `a` and mate 2 in full at cap `c - a - 1`, each with a near search of the partner at cap `c`, finds a
pair whenever one exists (`splitEmpty_none`). The split `a` is chosen per pair from the bucket sizes (`costP`).
When the split finds nothing, the answer is `[]`. Otherwise `pairsAt` runs, so the list, and hence the answer,
is today's (`pairsAtS_mem`). -/

-- no pair found with mate 1 within `a` or mate 2 within `c - a - 1`
def splitEmpty (sl lo hi c : Nat) (pk : PkMz) (offs : Array Nat) (pgs : Array PGen) (R1 R2 : ByteArray) (a : Nat) :
    Bool :=
  let l1 := hitsKPF pk ByteArray.empty offs pgs R1 a
  let p1 := (properPairsF sl lo hi l1 (hitsKPFN sl hi pk ByteArray.empty offs pgs R2 c l1)).any
    fun p => decide (-(c : Int) ≤ pairScoreD dcost0 p)
  if p1 then false else
  let l2 := hitsKPF pk ByteArray.empty offs pgs R2 (c - a - 1)
  !((properPairsF sl lo hi (hitsKPFN sl hi pk ByteArray.empty offs pgs R1 c l2) l2).any
    fun p => decide (-(c : Int) ≤ pairScoreD dcost0 p))

-- the split `a < c` with the smallest summed rarest-bucket cost, or `c` (no split: `pairsAt` directly)
def splitOf (c : Nat) (pk : PkMz) (R1 R2 : ByteArray) : Nat :=
  let s1 := prepMate pk R1
  let s2 := prepMate pk R2
  let today := min (costP pk c s1) (costP pk c s2)
  ((List.range c).foldl (fun (acc : Nat × Nat) a =>
    let k := costP pk a s1 + costP pk (c - a - 1) s2
    if k < acc.1 then (k, a) else acc) (today, c)).2

-- the pairs of both parts of the split scoring `≥ -c` (the same members as `pairsAt`: `splitPairs_mem`)
def splitPairs (sl lo hi c : Nat) (pk : PkMz) (offs : Array Nat) (pgs : Array PGen) (R1 R2 : ByteArray) (a : Nat) :
    List PairHit :=
  let l1 := hitsKPF pk ByteArray.empty offs pgs R1 a
  let l2 := hitsKPF pk ByteArray.empty offs pgs R2 (c - a - 1)
  (properPairsF sl lo hi l1 (hitsKPFN sl hi pk ByteArray.empty offs pgs R2 c l1) ++
    properPairsF sl lo hi (hitsKPFN sl hi pk ByteArray.empty offs pgs R1 c l2) l2).filter
    fun p => decide (-(c : Int) ≤ pairScoreD dcost0 p)

-- one pair (as a value) has the top score, so `topW` picks it whatever the order (or the list is empty)
def uniqueTop (S : List PairHit) : Bool :=
  match topW dcost0 S with
  | none => true
  | some w => S.all fun p => decide (pairScoreD dcost0 p < pairScoreD dcost0 w) || p == w

-- the split's pairs, unless the top score is tied (then `pairsAt`, whose order decides the tie as today)
def pairsAtS (sl lo hi c : Nat) (pk : PkMz) (offs : Array Nat) (pgs : Array PGen) (R1 R2 : ByteArray) :
    List PairHit :=
  let a := splitOf c pk R1 R2
  if a < c then
    let S := splitPairs sl lo hi c pk offs pgs R1 R2 a
    if uniqueTop S then S else pairsAt sl lo hi c pk offs pgs R1 R2
  else pairsAt sl lo hi c pk offs pgs R1 R2

theorem splitEmpty_none {sl lo hi c : Nat} (hc : c ≤ 16) {g : MapSpec.Genome} {m1 m2 : List Char} {ix : Mz.MzIdx}
    {G : PGen} {offs ns : Array Nat} (hcut : cutOk G offs ns = true)
    (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) g) (hchk : Mz.check2P ix G = true)
    {R1 R2 : ByteArray} (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (a : Nat) (ha : a < c)
    (hs : splitEmpty sl lo hi c ((ix, G) : PkMz) offs (cutAll G offs ns) R1 R2 a = true) (p : PairHit)
    (hp : p ∈ properPairs sl lo hi (hitsBoth sc0 (-(c : Int)) g m1) (hitsBoth sc0 (-(c : Int)) g m2))
    (hsc : -(c : Int) ≤ pairScoreD dcost0 p) : False := by
  obtain ⟨⟨w1, s1⟩, ⟨w2, s2⟩⟩ := p
  rw [mem_properPairs] at hp
  obtain ⟨hx1, hx2, hpr⟩ := hp
  simp only [pairScoreD, dcost0] at hsc
  have K2c := hitsKPF_mem g ix G offs ns hcut hg hchk R2 m2 h2 c hc
  have K1c := hitsKPF_mem g ix G offs ns hcut hg hchk R1 m1 h1 c hc
  unfold splitEmpty at hs
  simp only [] at hs
  by_cases hA : -(a : Int) ≤ s1
  · -- mate 1 within `a`: the first part finds the pair
    have hx1a : (w1, s1) ∈ hitsBoth sc0 (-(a : Int)) g m1 := by
      rw [mem_hitsBoth_T] at hx1 ⊢; exact ⟨hx1.1, hx1.2.1, hA⟩
    have K1a := (hitsKPF_mem g ix G offs ns hcut hg hchk R1 m1 h1 a (by omega) _).mpr hx1a
    have hin : ((w1, s1), (w2, s2)) ∈ properPairsF sl lo hi (hitsKPF ((ix, G) : PkMz) ByteArray.empty offs
        (cutAll G offs ns) R1 a) (hitsKPFN sl hi ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) R2 c
          (hitsKPF ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) R1 a)) := by
      rw [properPairsF_eq, pp_near_right (hitsKPFN_near sl lo hi _ _ _ _ _ c _), mem_properPairs]
      exact ⟨K1a, (K2c _).mpr hx2, hpr⟩
    split at hs
    · cases hs
    · rename_i hno
      exact hno (List.any_eq_true.mpr ⟨_, hin, by simp [pairScoreD, dcost0]; omega⟩)
  · -- mate 2 within `c - a - 1`: the second part finds it
    have hB : -((c - a - 1 : Nat) : Int) ≤ s2 := by omega
    have hx2b : (w2, s2) ∈ hitsBoth sc0 (-((c - a - 1 : Nat) : Int)) g m2 := by
      rw [mem_hitsBoth_T] at hx2 ⊢; exact ⟨hx2.1, hx2.2.1, hB⟩
    have K2b := (hitsKPF_mem g ix G offs ns hcut hg hchk R2 m2 h2 (c - a - 1) (by omega) _).mpr hx2b
    have hin : ((w1, s1), (w2, s2)) ∈ properPairsF sl lo hi (hitsKPFN sl hi ((ix, G) : PkMz) ByteArray.empty offs
        (cutAll G offs ns) R1 c (hitsKPF ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) R2 (c - a - 1)))
        (hitsKPF ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) R2 (c - a - 1)) := by
      rw [properPairsF_eq, pp_near_left (hitsKPFN_near sl lo hi _ _ _ _ _ c _), mem_properPairs]
      exact ⟨(K1c _).mpr hx1, K2b, hpr⟩
    split at hs
    · cases hs
    · simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false] at hs
      exact hs _ hin (by simp [pairScoreD, dcost0]; omega)

theorem splitPairs_mem {sl lo hi c : Nat} (hc : c ≤ 16) {g : MapSpec.Genome} {m1 m2 : List Char} {ix : Mz.MzIdx}
    {G : PGen} {offs ns : Array Nat} (hcut : cutOk G offs ns = true)
    (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) g) (hchk : Mz.check2P ix G = true)
    {R1 R2 : ByteArray} (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (a : Nat) (ha : a < c) (p : PairHit) :
    p ∈ splitPairs sl lo hi c ((ix, G) : PkMz) offs (cutAll G offs ns) R1 R2 a ↔
      p ∈ properPairs sl lo hi (hitsBoth sc0 (-(c : Int)) g m1) (hitsBoth sc0 (-(c : Int)) g m2) ∧
        -(c : Int) ≤ pairScoreD dcost0 p := by
  have K1c := hitsKPF_mem g ix G offs ns hcut hg hchk R1 m1 h1 c hc
  have K2c := hitsKPF_mem g ix G offs ns hcut hg hchk R2 m2 h2 c hc
  have K1a := hitsKPF_mem g ix G offs ns hcut hg hchk R1 m1 h1 a (by omega)
  have K2b := hitsKPF_mem g ix G offs ns hcut hg hchk R2 m2 h2 (c - a - 1) (by omega)
  unfold splitPairs
  simp only []
  rw [List.mem_filter, List.mem_append, properPairsF_eq, properPairsF_eq,
    pp_near_right (hitsKPFN_near sl lo hi _ _ _ _ _ c _) p, pp_near_left (hitsKPFN_near sl lo hi _ _ _ _ _ c _) p,
    mem_properPairs, mem_properPairs, mem_properPairs, K1c, K2c, K1a, K2b, decide_eq_true_eq]
  obtain ⟨⟨w1, s1⟩, ⟨w2, s2⟩⟩ := p
  simp only [mem_hitsBoth_T, pairScoreD, dcost0]
  constructor
  · rintro ⟨h | h, hs⟩
    · exact ⟨⟨⟨h.1.1, h.1.2.1, by omega⟩, h.2.1, h.2.2⟩, hs⟩
    · exact ⟨⟨h.1, ⟨h.2.1.1, h.2.1.2.1, by omega⟩, h.2.2⟩, hs⟩
  · rintro ⟨⟨hx1, hx2, hpr⟩, hs⟩
    refine ⟨?_, hs⟩
    by_cases hA : -(a : Int) ≤ s1
    · exact .inl ⟨⟨hx1.1, hx1.2.1, hA⟩, hx2, hpr⟩
    · exact .inr ⟨hx1, ⟨hx2.1, hx2.2.1, by omega⟩, hpr⟩

/-- **The split lists today's pairs**: `pairsAtS` has the members `pairsAt_mem` states. -/
theorem pairsAtS_mem {sl lo hi c : Nat} (hc : c ≤ 16) {g : MapSpec.Genome} {m1 m2 : List Char} {ix : Mz.MzIdx}
    {G : PGen} {offs ns : Array Nat} (hcut : cutOk G offs ns = true)
    (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) g) (hchk : Mz.check2P ix G = true)
    {R1 R2 : ByteArray} (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (p : PairHit) :
    p ∈ pairsAtS sl lo hi c ((ix, G) : PkMz) offs (cutAll G offs ns) R1 R2 ↔
      p ∈ properPairs sl lo hi (hitsBoth sc0 (-(c : Int)) g m1) (hitsBoth sc0 (-(c : Int)) g m2) ∧
        -(c : Int) ≤ pairScoreD dcost0 p := by
  unfold pairsAtS
  simp only []
  split
  · rename_i ha
    split
    · exact splitPairs_mem hc hcut hg hchk h1 h2 _ ha p
    · exact pairsAt_mem hc hcut hg hchk h1 h2 p
  · exact pairsAt_mem hc hcut hg hchk h1 h2 p

/-! ### The length-scaled cap (for Rowan's coming `requiredMapBound`)

`errorsChecked n = min 4 (n / 25 - 1)`; cap `c = 4 * errorsChecked (shorter mate)`. Every mate of at least 25
letters has the seeds for it (`fastT_capOfLens`: `n / 25` seeds, more than the `c / 4` events within `c`), so the
second look runs and `pairsAt_mem` (any `c ≤ 16`) decides "no proper pair `≥ -c`". -/

def errorsChecked (n : Nat) : Nat := min 4 (n / 25 - 1)

def capOfLens (n1 n2 : Nat) : Nat := 4 * errorsChecked (min n1 n2)

theorem capOfLens_le (n1 n2 : Nat) : capOfLens n1 n2 ≤ 16 := by
  unfold capOfLens errorsChecked; omega

theorem fastT_capOfLens (R1 R2 : ByteArray) (h1 : 25 ≤ R1.size) (h2 : 25 ≤ R2.size) :
    fastT (capOfLens R1.size R2.size) R1 = true ∧ fastT (capOfLens R1.size R2.size) R2 = true := by
  unfold fastT capOfLens errorsChecked
  simp only [sbound_eq, Bool.and_eq_true, decide_eq_true_eq]
  have a1 : 1 ≤ R1.size / 25 := (Nat.le_div_iff_mul_le (by decide)).2 (by omega)
  have a2 : 1 ≤ R2.size / 25 := (Nat.le_div_iff_mul_le (by decide)).2 (by omega)
  have m1 : min R1.size R2.size / 25 ≤ R1.size / 25 := Nat.div_le_div_right (Nat.min_le_left _ _)
  have m2 : min R1.size R2.size / 25 ≤ R2.size / 25 := Nat.div_le_div_right (Nat.min_le_right _ _)
  have e : 4 * min 4 (min R1.size R2.size / 25 - 1) / 4 = min 4 (min R1.size R2.size / 25 - 1) := by omega
  rw [e]
  omega

/-! ### Without an index: the hits of the whole genome, window by window (total; slow) -/

-- `windowScore` with the proved banded aligner (`bandDoublingAlign` = `getBestAlignment`)
def windowScoreF (read : List Char) (g : MapSpec.Genome) (w : Window) : Option Int :=
  match windowSeq g w with
  | some ys => (bandDoublingAlign sc0 read ys).map (·.2)
  | none => none

theorem windowScoreF_eq (read : List Char) (g : MapSpec.Genome) : windowScoreF read g = windowScore sc0 read g := by
  funext w
  unfold windowScoreF windowScore
  cases windowSeq g w with
  | none => rfl
  | some ys =>
    simp only
    rw [bandDoublingAlign_equals_getBestAlignment]
    cases getBestAlignment sc0 read ys <;> rfl

-- `hitsBoth`, computed with `windowScoreF`
def hitsF (T : Int) (g : MapSpec.Genome) (read : List Char) : List (MapSpec.Placement × Int) :=
  (hitsOf (windowScoreF read g) T (allWindows g)).map (fun h => ((h.1, MapSpec.Strand.fwd), h.2)) ++
  (hitsOf (windowScoreF (revComp read) g) T (allWindows g)).map (fun h => ((h.1, MapSpec.Strand.rev), h.2))

theorem hitsF_eq (T : Int) (g : MapSpec.Genome) (read : List Char) : hitsF T g read = hitsBoth sc0 T g read := by
  unfold hitsF hitsBoth; rw [windowScoreF_eq, windowScoreF_eq]

def pairsSpec (sl lo hi c : Nat) (g : MapSpec.Genome) (m1 m2 : List Char) : List PairHit :=
  (properPairs sl lo hi (hitsF (-(c : Int)) g m1) (hitsF (-(c : Int)) g m2)).filter
    fun p => decide (-(c : Int) ≤ pairScoreD dcost0 p)

theorem pairsSpec_mem (sl lo hi c : Nat) (g : MapSpec.Genome) (m1 m2 : List Char) (p : PairHit) :
    p ∈ pairsSpec sl lo hi c g m1 m2 ↔
      p ∈ properPairs sl lo hi (hitsBoth sc0 (-(c : Int)) g m1) (hitsBoth sc0 (-(c : Int)) g m2) ∧
        -(c : Int) ≤ pairScoreD dcost0 p := by
  unfold pairsSpec; rw [List.mem_filter, hitsF_eq, hitsF_eq, decide_eq_true_eq]

def runsSp (g : MapSpec.Genome) (m : List Char) (x : MapSpec.Placement × Int) : List (AlignmentSpec.Step × Nat) :=
  runsOf (strandRead m x.1.2) ((windowSeq g x.1.1).getD [])

theorem runsSp_ok {g : MapSpec.Genome} {m : List Char} {T : Int} {x : MapSpec.Placement × Int}
    (hx : x ∈ hitsBoth sc0 T g m) : CigarOk g m x (runsSp g m x) := by
  have hws : ∃ ys, windowSeq g x.1.1 = some ys := by
    obtain ⟨⟨w, st⟩, sx⟩ := x
    have hx' := hx
    rw [mem_hitsBoth_T] at hx'
    have h : windowScore sc0 (strandRead m st) g w = some sx := by cases st <;> exact hx'.2.1
    unfold windowScore at h
    cases hw : windowSeq g w with
    | none => rw [hw] at h; cases h
    | some ys => exact ⟨ys, rfl⟩
  obtain ⟨ys, hys⟩ := hws
  unfold runsSp
  rw [hys]
  exact cigarOk_of_hit hx hys

end look

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

#print axioms Spec.LastResort.pairsAtS_mem
