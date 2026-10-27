import PairLadder

/-!
# `pairUKPF`: the proper-pair mode with linear pairing

`pairUKPR` (codecs/PairLadder.lean) with the pairing done fast, same answers:

* `bestOfPairs`: `bestPairD`'s unique best in linear time.  The best `w` of the list
  (`topW`) is found first; only a pair at `w`'s placements can beat every pair at other
  placements (`bestOfPairs_eq`).
* `properPairsF`: the second mate's hits are grouped by chromosome and strand once; each
  first-mate hit is paired within its group only (`properPairsF_eq`: a proper pair is on
  one chromosome, opposite strands).
* `ladderUF`: the ladder with the proper pairs of a rung built once (`ladderUF_eq`).

    pairUKPRF … = pairUKPR …                                        (pairUKPRF_eq)
    pairUKPF … = pairSpecUT sc0 dc sl lo hi (−P1) (−P2) g m1 m2     (pairUKPF_mz_eq)
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-! ## The unique best of a list of pairs, linear -/

/-- Same placements. -/
@[inline] def samePl (p q : PairHit) : Bool := decide (p.1.1 = q.1.1 ∧ p.2.1 = q.2.1)

/-- The pair beating every pair at other placements: only a pair at the best's placements can. -/
def bestOfPairs (dc : Nat → Nat) (ps : List PairHit) : Option PairHit :=
  match topW dc ps with
  | none => none
  | some w =>
    let rest := ps.filter fun p' => !samePl p' w
    ps.find? fun p => samePl p w && rest.all fun p' => decide (pairScoreD dc p' < pairScoreD dc p)

theorem foldl_top_ge (dc : Nat → Nat) : ∀ (ps : List PairHit) (a : PairHit),
    pairScoreD dc a ≤ pairScoreD dc (ps.foldl (topStep dc) a) ∧
      ∀ p ∈ ps, pairScoreD dc p ≤ pairScoreD dc (ps.foldl (topStep dc) a)
  | [], _ => ⟨Int.le_refl _, fun _ h => by cases h⟩
  | b :: ps, a => by
    have ih := foldl_top_ge dc ps (topStep dc a b)
    have ha : pairScoreD dc a ≤ pairScoreD dc (topStep dc a b) := by
      unfold topStep; split <;> omega
    have hb : pairScoreD dc b ≤ pairScoreD dc (topStep dc a b) := by
      unfold topStep; split <;> omega
    simp only [List.foldl_cons]
    refine ⟨Int.le_trans ha ih.1, fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with h | h
    · subst h; exact Int.le_trans hb ih.1
    · exact ih.2 p h

theorem topW_max (dc : Nat → Nat) (ps : List PairHit) (w : PairHit) (h : topW dc ps = some w) :
    ∀ p ∈ ps, pairScoreD dc p ≤ pairScoreD dc w := by
  cases ps with
  | nil => cases h
  | cons a ps =>
    simp only [topW, Option.some.injEq] at h
    subst h
    intro p hp
    rcases List.mem_cons.mp hp with e | e
    · subst e; exact (foldl_top_ge dc ps p).1
    · exact (foldl_top_ge dc ps a).2 p e

theorem find?_congr_mem {α : Type} {p q : α → Bool} : ∀ (l : List α), (∀ x ∈ l, p x = q x) →
    l.find? p = l.find? q
  | [], _ => rfl
  | x :: l, h => by
    rw [List.find?_cons, List.find?_cons, h x List.mem_cons_self,
      find?_congr_mem l (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem bestOfPairs_eq (dc : Nat → Nat) (ps : List PairHit) :
    bestOfPairs dc ps = ps.find? fun p => ps.all fun p' =>
      decide (pairScoreD dc p' < pairScoreD dc p) || decide (p'.1.1 = p.1.1 ∧ p'.2.1 = p.2.1) := by
  unfold bestOfPairs
  split
  · next h =>
    cases ps with
    | nil => rfl
    | cons _ _ => simp [topW] at h
  · next w hw =>
    apply find?_congr_mem
    intro p hp
    apply Bool.eq_iff_iff.mpr
    have hmax := topW_max dc ps w hw p hp
    have hwm := topW_mem dc ps w hw
    simp only [samePl, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_filter,
      Bool.not_eq_true', decide_eq_false_iff_not, Bool.or_eq_true]
    constructor
    · rintro ⟨⟨e1, e2⟩, hr⟩ p' hp'
      by_cases hs : p'.1.1 = w.1.1 ∧ p'.2.1 = w.2.1
      · exact Or.inr ⟨hs.1.trans e1.symm, hs.2.trans e2.symm⟩
      · exact Or.inl (hr p' ⟨hp', hs⟩)
    · intro ha
      rcases ha w hwm with hw' | hw'
      · exact absurd hmax (Int.not_le.mpr hw')
      · refine ⟨⟨hw'.1.symm, hw'.2.symm⟩, fun p' ⟨hp', hs⟩ => ?_⟩
        rcases ha p' hp' with h | h
        · exact h
        · exact absurd ⟨h.1.trans hw'.1.symm, h.2.trans hw'.2.symm⟩ hs

theorem bestOfPairs_pp (dc : Nat → Nat) (sl lo hi : Nat) (h1 h2 : List (Placement × Int)) :
    bestOfPairs dc (properPairs sl lo hi h1 h2) = bestPairD dc sl lo hi h1 h2 := by
  rw [bestOfPairs_eq]; rfl

/-! ## Proper pairs, grouped by chromosome and strand -/

/-- Group key of a second-mate hit, and the key its proper partners of the first mate look up. -/
@[inline] def keyB (b : Placement) : Nat := 2 * b.1.chr + (if b.2 = Strand.fwd then 0 else 1)
@[inline] def keyA (a : Placement) : Nat := 2 * a.1.chr + (if a.2 = Strand.fwd then 1 else 0)

theorem properPairU_key (sl lo hi : Nat) (a b : Placement) (h : properPairU sl lo hi a b = true) :
    keyB b = keyA a := by
  rcases a with ⟨wa, sa⟩
  rcases b with ⟨wb, sb⟩
  cases sa <;> cases sb <;> simp_all [properPairU, properPair, fwdRev, keyA, keyB]

/-- Insert `x` under key `k` (in front of the key's list). -/
def insG {α : Type} (k : Nat) (x : α) : List (Nat × List α) → List (Nat × List α)
  | [] => [(k, [x])]
  | (k', l) :: r => if k' = k then (k', x :: l) :: r else (k', l) :: insG k x r

def getG {α : Type} (k : Nat) : List (Nat × List α) → List α
  | [] => []
  | (k', l) :: r => if k' = k then l else getG k r

/-- Hits grouped by `keyB`, list order kept within a group. -/
def grpB (l : List (Placement × Int)) : List (Nat × List (Placement × Int)) :=
  l.foldr (fun x g => insG (keyB x.1) x g) []

theorem getG_insG {α : Type} (k k' : Nat) (x : α) : ∀ g : List (Nat × List α),
    getG k (insG k' x g) = if k' = k then x :: getG k g else getG k g
  | [] => by
    by_cases h : k' = k <;> simp [insG, getG, h]
  | (k'', l) :: r => by
    have ih := getG_insG k k' x r
    by_cases a : k'' = k' <;> by_cases b : k' = k <;> simp_all [insG, getG]

theorem getG_grpB (k : Nat) : ∀ l : List (Placement × Int),
    getG k (grpB l) = l.filter fun x => keyB x.1 == k
  | [] => rfl
  | x :: l => by
    have ih := getG_grpB k l
    unfold grpB at ih ⊢
    rw [List.foldr_cons, getG_insG, ih, List.filter_cons]
    by_cases h : keyB x.1 = k <;> simp [h]

/-- `properPairs`, each first-mate hit paired within its group of second-mate hits. -/
def properPairsF (sl lo hi : Nat) (h1 h2 : List (Placement × Int)) : List PairHit :=
  let G := grpB h2
  h1.flatMap fun a => ((getG (keyA a.1) G).filter fun b => properPairU sl lo hi a.1 b.1).map fun b => (a, b)

theorem properPairsF_eq (sl lo hi : Nat) (h1 h2 : List (Placement × Int)) :
    properPairsF sl lo hi h1 h2 = properPairs sl lo hi h1 h2 := by
  unfold properPairsF properPairs
  simp only [getG_grpB, List.filter_filter]
  congr 1
  funext a
  congr 1
  apply List.filter_congr
  intro b _
  by_cases h : properPairU sl lo hi a.1 b.1 = true
  · simp [h, properPairU_key sl lo hi a.1 b.1 h]
  · simp [h]

/-- `bestPairD`, fast. -/
def bestPairF (dc : Nat → Nat) (sl lo hi : Nat) (h1 h2 : List (Placement × Int)) : Option PairHit :=
  bestOfPairs dc (properPairsF sl lo hi h1 h2)

theorem bestPairF_eq (dc : Nat → Nat) (sl lo hi : Nat) (h1 h2 : List (Placement × Int)) :
    bestPairF dc sl lo hi h1 h2 = bestPairD dc sl lo hi h1 h2 := by
  rw [bestPairF, properPairsF_eq, bestOfPairs_pp]

/-! ## The ladder, proper pairs built once per rung -/

def ladderUF (dc : Nat → Nat) (sl lo hi P1 P2 : Nat) (hf : Bool → Nat → List (Placement × Int))
    (a1 : Bool) : List Nat → Option PairHit × Bool
  | [] =>
    let ps := properPairsF sl lo hi (hf true P1) (hf false P2)
    (bestOfPairs dc ps, !ps.isEmpty)
  | c :: cs =>
    let c1 := min c P1
    let c2 := min c P2
    let hA := hf a1 (if a1 then c1 else c2)
    if hA.isEmpty then
      if (if a1 then P1 ≤ c1 else P2 ≤ c2) then (none, false) else ladderUF dc sl lo hi P1 P2 hf a1 cs
    else
      let hB := hf (!a1) (if a1 then c2 else c1)
      let l1 := if a1 then hA else hB
      let l2 := if a1 then hB else hA
      let ps := properPairsF sl lo hi l1 l2
      if P1 ≤ c1 ∧ P2 ≤ c2 then (bestOfPairs dc ps, !ps.isEmpty)
      else match topW dc ps with
        | none => ladderUF dc sl lo hi P1 P2 hf a1 cs
        | some w =>
          let e := (-(pairScoreD dc w)).toNat
          if (P1 ≤ c1 ∨ e ≤ c1) ∧ (P2 ≤ c2 ∨ e ≤ c2) then (bestOfPairs dc ps, true)
          else (bestPairF dc sl lo hi (hf true (min P1 e)) (hf false (min P2 e)), true)

theorem ladderUF_eq (dc : Nat → Nat) (sl lo hi P1 P2 : Nat) (hf : Bool → Nat → List (Placement × Int))
    (a1 : Bool) : ∀ cs, ladderUF dc sl lo hi P1 P2 hf a1 cs = ladderUR dc sl lo hi P1 P2 hf a1 cs
  | [] => by simp only [ladderUF, ladderUR, properPairsF_eq, bestOfPairs_pp]
  | c :: cs => by
    have ih := ladderUF_eq dc sl lo hi P1 P2 hf a1 cs
    simp only [ladderUF, ladderUR, properPairsF_eq, bestOfPairs_pp, bestPairF_eq, ih]
    split
    · rfl
    · split
      · rfl
      · cases topW dc _ <;> rfl

/-- `pairUKPR` with the fast pairing. -/
def pairUKPRF {L Pp : Type} [LookG L Pp] [Inhabited Pp] (dc : Nat → Nat) (sl lo hi P1 P2 : Nat) (caps : List Nat)
    (a1 : Bool) (ix : L) (G : ByteArray) (offs : Array Nat) (pgs : Array PGen) (R1 R2 : ByteArray) :
    Option PairHit × Bool :=
  let lad := fun (_ : Unit) =>
    ladderUF dc sl lo hi P1 P2 (fun b c => hitsKPF ix G offs pgs (if b then R1 else R2) c) a1 caps
  match mapFastGBKP P1 ix G offs pgs R1 with
  | some a =>
    match mapFastGBKP P2 ix G offs pgs R2 with
    | some b => if properPairU sl lo hi a.1 b.1 && dc (fragLen a.1 b.1) == 0 then (some (a, b), true) else lad ()
    | none => lad ()
  | none => lad ()

def pairUKPF {L Pp : Type} [LookG L Pp] [Inhabited Pp] (dc : Nat → Nat) (sl lo hi P1 P2 : Nat) (caps : List Nat)
    (a1 : Bool) (ix : L) (G : ByteArray) (offs : Array Nat) (pgs : Array PGen) (R1 R2 : ByteArray) :
    Option PairHit :=
  (pairUKPRF dc sl lo hi P1 P2 caps a1 ix G offs pgs R1 R2).1

theorem pairUKPRF_eq {L Pp : Type} [LookG L Pp] [Inhabited Pp] (dc : Nat → Nat) (sl lo hi P1 P2 : Nat)
    (caps : List Nat) (a1 : Bool) (ix : L) (G : ByteArray) (offs : Array Nat) (pgs : Array PGen)
    (R1 R2 : ByteArray) :
    pairUKPRF dc sl lo hi P1 P2 caps a1 ix G offs pgs R1 R2 = pairUKPR dc sl lo hi P1 P2 caps a1 ix G offs pgs R1 R2 := by
  simp only [pairUKPRF, pairUKPR, ladderUF_eq]
  cases mapFastGBKP P1 ix G offs pgs R1 <;> cases mapFastGBKP P2 ix G offs pgs R2 <;> rfl

section top
variable (dc : Nat → Nat) (sl lo hi P1 P2 : Nat) (caps : List Nat) (a1 : Bool) (g : Genome)
  (m1 m2 : List Char) (ix : Mz.MzIdx) (G : PGen) (offs ns : Array Nat) (R1 R2 : ByteArray)
  (hcut : cutOk G offs ns = true) (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) g)
  (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hchk : Mz.check2P ix G = true)

include hcut hg h1 h2 hchk in
/-- **Proper-pair mode, fast pairing, packed whole genome: the specification.** -/
theorem pairUKPF_mz_eq (hP1 : P1 ≤ 16) (hP2 : P2 ≤ 16) :
    pairUKPF dc sl lo hi P1 P2 caps a1 ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) R1 R2 =
      pairSpecUT sc0 dc sl lo hi (-(P1 : Int)) (-(P2 : Int)) g m1 m2 := by
  unfold pairUKPF
  rw [pairUKPRF_eq]
  exact pairUKP_mz_eq dc sl lo hi P1 P2 caps a1 g m1 m2 ix G offs ns R1 R2 hcut hg h1 h2 hchk hP1 hP2

include hcut hg h1 h2 hchk in
theorem pairUKPRF_tie (hP1 : P1 ≤ 16) (hP2 : P2 ≤ 16)
    (h : pairUKPRF dc sl lo hi P1 P2 caps a1 ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) R1 R2 =
      (none, true)) :
    PairTieOk dc sl lo hi (-(P1 : Int)) (-(P2 : Int)) g m1 m2 := by
  rw [pairUKPRF_eq] at h
  exact pairUKPR_tie dc sl lo hi P1 P2 caps a1 g m1 m2 ix G offs ns R1 R2 hcut hg h1 h2 hchk hP1 hP2 h

end top

end MapSpec.Fast

#print axioms MapSpec.Fast.bestPairF_eq
#print axioms MapSpec.Fast.ladderUF_eq
#print axioms MapSpec.Fast.pairUKPF_mz_eq
#print axioms MapSpec.Fast.pairUKPRF_tie
