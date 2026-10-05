import PairBnB
import PairUnique

/-!
# Box certificates for `bestPairD` (pair-level uniqueness)

The searches give, for a region of placements, only the best hit score in it, the
placement reaching it, and whether another placement in the region ties it
(`RROk`).  A *box* is a region for mate 1 and a region for mate 2.  When the boxes
cover every proper pair (`Cover`), the box results alone often decide `bestPairD`:

* the box bound `U = s1 + s2` bounds every pair in the box (the distance cost is `≥ 0`);
* a box whose two regions are unambiguous and whose best pair is proper gives a
  *witness* pair; let `W` be the best witness score;
* if every box has `U < W`, or `U = W` and both regions unambiguous, then the pairs
  scoring `W` are exactly the witnesses scoring `W`: one placement pair → mapped,
  several → pair tie (not reported).

`certify` returns `none` when the boxes do not decide (refine and try again), and
`some r` with `r = bestPairD …` otherwise (`certify_ok`).
-/

namespace MapSpec

open AlignmentSpec

/-- Result of a region search: best hit (placement, score) and the tie flag. -/
structure RRes where
  best : Option (Placement × Int)
  amb : Bool

/-- `r` is the region search result over the hits of `h` whose placement is in `R`. -/
def RROk (h : List (Placement × Int)) (R : Placement → Bool) (r : RRes) : Prop :=
  match r.best with
  | none => ∀ x ∈ h, R x.1 = false
  | some (p, s) => (p, s) ∈ h ∧ R p = true ∧ (∀ x ∈ h, R x.1 = true → x.2 ≤ s) ∧
      (r.amb = false → ∀ x ∈ h, R x.1 = true → x.2 = s → x.1 = p)

/-- Bound of a box: the summed best scores (`none`: the box holds no pair). -/
def boxU (r : RRes × RRes) : Option Int :=
  match r.1.best, r.2.best with
  | some a, some b => some (a.2 + b.2)
  | _, _ => none

/-- Witness of a box: its best pair, when both regions are unambiguous and it is proper. -/
def boxWit (sl lo hi : Nat) (r : RRes × RRes) : Option PairHit :=
  match r.1.best, r.2.best with
  | some a, some b => if !r.1.amb && !r.2.amb && properPairU sl lo hi a.1 b.1 then some (a, b) else none
  | _, _ => none

/-- Best score of a list of pairs. -/
def maxScore (dc : Nat → Nat) : List PairHit → Option Int
  | [] => none
  | p :: ps => match maxScore dc ps with
    | none => some (pairScoreD dc p)
    | some m => some (max (pairScoreD dc p) m)

/-- A box is settled by the bound `W`. -/
def boxDone (W : Int) (r : RRes × RRes) : Bool :=
  match boxU r with
  | none => true
  | some u => decide (u < W) || (decide (u = W) && !r.1.amb && !r.2.amb)

/-- The decision from box results: `none` = undecided; `some r` = `bestPairD`. -/
def certify (dc : Nat → Nat) (sl lo hi : Nat) (rs : List (RRes × RRes)) : Option (Option PairHit) :=
  if rs.all (fun r => (boxU r).isNone) then some none else
  let ws := rs.filterMap (boxWit sl lo hi)
  match maxScore dc ws with
  | none => none
  | some W =>
    if rs.all (boxDone W) then
      match ws.filter (fun p => decide (pairScoreD dc p = W)) with
      | [] => none
      | p :: rest => if rest.all (fun q => decide (q.1.1 = p.1.1 ∧ q.2.1 = p.2.1)) then some (some p)
          else some none
    else none

/-! ## Proofs -/

theorem maxScore_spec (dc : Nat → Nat) (ws : List PairHit) (W : Int) (h : maxScore dc ws = some W) :
    (∃ p ∈ ws, pairScoreD dc p = W) ∧ ∀ p ∈ ws, pairScoreD dc p ≤ W := by
  induction ws generalizing W with
  | nil => simp [maxScore] at h
  | cons q t ih =>
    simp only [maxScore] at h
    cases hm : maxScore dc t with
    | none =>
      rw [hm] at h
      cases h
      have ht : t = [] := by
        cases t with
        | nil => rfl
        | cons r t' =>
          simp only [maxScore] at hm
          split at hm <;> cases hm
      subst ht
      simp
    | some m =>
      rw [hm] at h
      cases h
      obtain ⟨⟨p, hp, hpe⟩, hall⟩ := ih m hm
      refine ⟨?_, ?_⟩
      · by_cases hle : m ≤ pairScoreD dc q
        · exact ⟨q, List.mem_cons_self, by omega⟩
        · exact ⟨p, List.mem_cons_of_mem _ hp, by omega⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · omega
        · have := hall x hx; omega

/-- Every proper pair lies in some box. -/
def Cover {β : Type} (sl lo hi : Nat) (h1 h2 : List (Placement × Int)) (bs : List β)
    (RA RB : β → Placement → Bool) : Prop :=
  ∀ p ∈ properPairs sl lo hi h1 h2, ∃ b ∈ bs, RA b p.1.1 = true ∧ RB b p.2.1 = true

/-- `bestPairD`, characterized (a placement determines its score). -/
theorem bestPairD_iff (dc : Nat → Nat) (sl lo hi : Nat) (h1 h2 : List (Placement × Int))
    (f1 : ScoreFun h1) (f2 : ScoreFun h2) (p : PairHit) :
    bestPairD dc sl lo hi h1 h2 = some p ↔ p ∈ properPairs sl lo hi h1 h2 ∧
      ∀ x ∈ properPairs sl lo hi h1 h2, pairScoreD dc x < pairScoreD dc p ∨ (x.1.1 = p.1.1 ∧ x.2.1 = p.2.1) := by
  have := Fast.findU_iff (pairScoreD dc) (fun p' p => decide (p'.1.1 = p.1.1 ∧ p'.2.1 = p.2.1))
    (properPairs sl lo hi h1 h2) (by
      rintro ⟨⟨a, sa⟩, ⟨b, sb⟩⟩ hx ⟨⟨a', sa'⟩, ⟨b', sb'⟩⟩ hy he
      simp only [decide_eq_true_eq] at he
      obtain ⟨rfl, rfl⟩ := he
      rw [mem_properPairs] at hx hy
      have ea : sa = sa' := f1 _ hx.1 _ hy.1 rfl
      have eb : sb = sb' := f2 _ hx.2.1 _ hy.2.1 rfl
      rw [ea, eb]) p
  simp only [decide_eq_true_eq] at this
  exact this

section cert
variable {β : Type} (dc : Nat → Nat) (sl lo hi : Nat) (h1 h2 : List (Placement × Int))
  (f1 : ScoreFun h1) (f2 : ScoreFun h2) (bs : List β) (RA RB : β → Placement → Bool)
  (res : β → RRes × RRes)
  (hok : ∀ b ∈ bs, RROk h1 (RA b) (res b).1 ∧ RROk h2 (RB b) (res b).2)
  (hcov : Cover sl lo hi h1 h2 bs RA RB)

include hok in
/-- A pair in a box scores at most the box bound. -/
theorem pair_le_boxU (b : β) (hb : b ∈ bs) (p : PairHit) (hp : p ∈ properPairs sl lo hi h1 h2)
    (ha : RA b p.1.1 = true) (hb2 : RB b p.2.1 = true) :
    ∃ u, boxU (res b) = some u ∧ pairScoreD dc p ≤ u ∧
      (pairScoreD dc p = u → (res b).1.amb = false → (res b).2.amb = false →
        (res b).1.best = some p.1 ∧ (res b).2.best = some p.2 ∧ dc (fragLen p.1.1 p.2.1) = 0) := by
  obtain ⟨hA, hB⟩ := hok b hb
  obtain ⟨hp1, hp2, _⟩ := mem_properPairs.mp hp
  unfold RROk at hA hB
  unfold boxU
  cases e1 : (res b).1.best with
  | none => rw [e1] at hA; have := hA _ hp1; rw [ha] at this; cases this
  | some a =>
    cases e2 : (res b).2.best with
    | none => rw [e2] at hB; have := hB _ hp2; rw [hb2] at this; cases this
    | some c =>
      rw [e1] at hA
      rw [e2] at hB
      obtain ⟨a1, a2⟩ := a
      obtain ⟨c1, c2⟩ := c
      obtain ⟨_, _, hAle, hAu⟩ := hA
      obtain ⟨_, _, hBle, hBu⟩ := hB
      have l1 := hAle _ hp1 ha
      have l2 := hBle _ hp2 hb2
      have hd : (0 : Int) ≤ (dc (fragLen p.1.1 p.2.1) : Int) := Int.natCast_nonneg _
      refine ⟨a2 + c2, rfl, ?_, ?_⟩
      · unfold pairScoreD; omega
      · intro he n1 n2
        unfold pairScoreD at he
        have s1 : p.1.2 = a2 := by omega
        have s2 : p.2.2 = c2 := by omega
        have q1 := hAu n1 _ hp1 ha s1
        have q2 := hBu n2 _ hp2 hb2 s2
        refine ⟨?_, ?_, ?_⟩
        · exact congrArg some (Prod.ext q1.symm s1.symm)
        · exact congrArg some (Prod.ext q2.symm s2.symm)
        · omega

include hok in
/-- A witness is a proper pair of hits. -/
theorem boxWit_mem (b : β) (hb : b ∈ bs) (p : PairHit) (hw : boxWit sl lo hi (res b) = some p) :
    p ∈ properPairs sl lo hi h1 h2 ∧ (res b).1.best = some p.1 ∧ (res b).2.best = some p.2 := by
  obtain ⟨hA, hB⟩ := hok b hb
  unfold boxWit at hw
  unfold RROk at hA hB
  cases e1 : (res b).1.best with
  | none => rw [e1] at hw; cases hw
  | some a =>
    cases e2 : (res b).2.best with
    | none => rw [e1, e2] at hw; cases hw
    | some c =>
      rw [e1, e2] at hw
      rw [e1] at hA
      rw [e2] at hB
      simp only at hw
      split at hw
      · next hc =>
        cases hw
        simp only [Bool.and_eq_true] at hc
        exact ⟨mem_properPairs.mpr ⟨hA.1, hB.1, hc.2⟩, rfl, rfl⟩
      · cases hw

include hok hcov f1 f2 in
/-- **Box certificates are exact.** -/
theorem certify_ok (r : Option PairHit) (hc : certify dc sl lo hi (bs.map res) = some r) :
    r = bestPairD dc sl lo hi h1 h2 := by
  unfold certify at hc
  split at hc
  · -- no box holds a pair: no proper pair at all
    next hn =>
    cases hc
    symm
    cases hbp : bestPairD dc sl lo hi h1 h2 with
    | none => rfl
    | some p =>
      obtain ⟨hp, _⟩ := (bestPairD_iff dc sl lo hi h1 h2 f1 f2 p).mp hbp
      obtain ⟨b, hb, ha, hb2⟩ := hcov p hp
      obtain ⟨u, hu, _⟩ := pair_le_boxU dc sl lo hi h1 h2 bs RA RB res hok b hb p hp ha hb2
      rw [List.all_eq_true] at hn
      have := hn (res b) (List.mem_map_of_mem hb)
      rw [hu] at this
      cases this
  · simp only at hc
    split at hc
    · cases hc
    · next W hW =>
      split at hc
      · next hdone =>
        rw [List.all_eq_true] at hdone
        obtain ⟨⟨w, hwm, hwe⟩, hwle⟩ := maxScore_spec dc _ W hW
        -- a witness: proper pair of hits
        have hwit : ∀ q ∈ (bs.map res).filterMap (boxWit sl lo hi), q ∈ properPairs sl lo hi h1 h2 := by
          intro q hq
          rw [List.mem_filterMap] at hq
          obtain ⟨r', hr', hq'⟩ := hq
          rw [List.mem_map] at hr'
          obtain ⟨b, hb, rfl⟩ := hr'
          exact (boxWit_mem sl lo hi h1 h2 bs RA RB res hok b hb q hq').1
        -- every proper pair scores ≤ W, and one scoring W is a witness scoring W
        have hall : ∀ x ∈ properPairs sl lo hi h1 h2, pairScoreD dc x < W ∨
            (pairScoreD dc x = W ∧ x ∈ ((bs.map res).filterMap (boxWit sl lo hi)).filter
              (fun p => decide (pairScoreD dc p = W))) := by
          intro x hx
          obtain ⟨b, hb, ha, hb2⟩ := hcov x hx
          obtain ⟨u, hu, hle, heq⟩ := pair_le_boxU dc sl lo hi h1 h2 bs RA RB res hok b hb x hx ha hb2
          have hd := hdone (res b) (List.mem_map_of_mem hb)
          unfold boxDone at hd
          rw [hu] at hd
          simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hd
          rcases hd with hd | ⟨⟨hd, n1⟩, n2⟩
          · left; omega
          · by_cases hxW : pairScoreD dc x = W
            · right
              refine ⟨hxW, ?_⟩
              obtain ⟨e1, e2, _⟩ := heq (by omega) n1 n2
              rw [List.mem_filter]
              refine ⟨?_, by simpa using hxW⟩
              rw [List.mem_filterMap]
              refine ⟨res b, List.mem_map_of_mem hb, ?_⟩
              unfold boxWit
              rw [e1, e2]
              obtain ⟨_, _, hpp⟩ := mem_properPairs.mp hx
              simp [n1, n2, hpp]
            · left; omega
        split at hc
        · cases hc
        · next p rest htop =>
          have hpm : p ∈ ((bs.map res).filterMap (boxWit sl lo hi)).filter
              (fun p => decide (pairScoreD dc p = W)) := by rw [htop]; exact List.mem_cons_self
          rw [List.mem_filter] at hpm
          have hpW : pairScoreD dc p = W := by simpa using hpm.2
          have hpp := hwit p hpm.1
          split at hc
          · next hrest =>
            cases hc
            symm
            rw [bestPairD_iff dc sl lo hi h1 h2 f1 f2]
            refine ⟨hpp, ?_⟩
            intro x hx
            rcases hall x hx with h | ⟨_, hxm⟩
            · left; omega
            · right
              rw [htop] at hxm
              rcases List.mem_cons.mp hxm with rfl | hxr
              · exact ⟨rfl, rfl⟩
              · rw [List.all_eq_true] at hrest
                simpa using hrest x hxr
          · next hrest =>
            cases hc
            symm
            cases hbp : bestPairD dc sl lo hi h1 h2 with
            | none => rfl
            | some y =>
              exfalso
              obtain ⟨hy, hyb⟩ := (bestPairD_iff dc sl lo hi h1 h2 f1 f2 y).mp hbp
              rw [List.all_eq_true] at hrest
              simp only [decide_eq_true_eq] at hrest
              have hex : ∃ q ∈ rest, ¬ (q.1.1 = p.1.1 ∧ q.2.1 = p.2.1) := by
                apply Classical.byContradiction
                intro hc
                exact hrest (fun x hx => Classical.byContradiction fun hx' => hc ⟨x, hx, hx'⟩)
              obtain ⟨q, hq, hqne⟩ := hex
              have hqm : q ∈ ((bs.map res).filterMap (boxWit sl lo hi)).filter
                  (fun p => decide (pairScoreD dc p = W)) := by rw [htop]; exact List.mem_cons_of_mem _ hq
              rw [List.mem_filter] at hqm
              have hqW : pairScoreD dc q = W := by simpa using hqm.2
              have hqp := hwit q hqm.1
              have hyW : pairScoreD dc y ≤ W := by
                rcases hall y hy with h | ⟨h, _⟩ <;> omega
              rcases hyb p hpp with h1' | ⟨a1, a2⟩
              · omega
              · rcases hyb q hqp with h2' | ⟨b1, b2⟩
                · omega
                · exact hqne ⟨b1.trans a1.symm, b2.trans a2.symm⟩
      · cases hc

end cert

end MapSpec

#print axioms MapSpec.certify_ok
