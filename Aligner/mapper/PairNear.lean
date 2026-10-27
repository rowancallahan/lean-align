import PairHybrid

/-!
# The ladder with the second mate searched near the first only

At each rung the ladder uses the second-searched mate's hits only through the proper
pairs they make with the first mate's hits.  So the second mate's list may be any list
of its hits that holds every hit with a proper partner in the first mate's list
(`NearOk`); the answers do not change (`ladderUB_eq`: `ladderUB` = `ladderUR`).
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-- `x` has a proper partner in `l` (either mate order). -/
def Partner (sl lo hi : Nat) (l : List (Placement × Int)) (x : Placement × Int) : Prop :=
  ∃ y ∈ l, properPairU sl lo hi y.1 x.1 = true ∨ properPairU sl lo hi x.1 y.1 = true

/-- `l` holds every hit of `H` with a partner in `A`, and only hits of `H`. -/
def NearOk (sl lo hi : Nat) (A H l : List (Placement × Int)) : Prop :=
  (∀ x ∈ l, x ∈ H) ∧ ∀ x ∈ H, Partner sl lo hi A x → x ∈ l

theorem scoreFun_sub {l h : List (Placement × Int)} (s : ∀ x ∈ l, x ∈ h) (f : ScoreFun h) : ScoreFun l :=
  fun x hx y hy he => f x (s x hx) y (s y hy) he

theorem pp_near_right {sl lo hi : Nat} {A H l : List (Placement × Int)} (hn : NearOk sl lo hi A H l) (p : PairHit) :
    p ∈ properPairs sl lo hi A l ↔ p ∈ properPairs sl lo hi A H := by
  rw [mem_properPairs, mem_properPairs]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, hn.1 _ h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, hn.2 _ h2 ⟨p.1, h1, Or.inl h3⟩, h3⟩

theorem pp_near_left {sl lo hi : Nat} {A H l : List (Placement × Int)} (hn : NearOk sl lo hi A H l) (p : PairHit) :
    p ∈ properPairs sl lo hi l A ↔ p ∈ properPairs sl lo hi H A := by
  rw [mem_properPairs, mem_properPairs]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨hn.1 _ h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨hn.2 _ h1 ⟨p.2, h2, Or.inr h3⟩, h2, h3⟩

/-- `bestPairD` depends on the proper pairs only (lists with unique scores). -/
theorem bestPairD_congrPP (dc : Nat → Nat) (sl lo hi : Nat) {l1 l2 h1 h2 : List (Placement × Int)}
    (ep : ∀ p, p ∈ properPairs sl lo hi l1 l2 ↔ p ∈ properPairs sl lo hi h1 h2)
    (f1 : ScoreFun l1) (f2 : ScoreFun l2) (g1 : ScoreFun h1) (g2 : ScoreFun h2) :
    bestPairD dc sl lo hi l1 l2 = bestPairD dc sl lo hi h1 h2 := by
  have key : ∀ p, bestPairD dc sl lo hi l1 l2 = some p ↔ bestPairD dc sl lo hi h1 h2 = some p := by
    intro p
    rw [bestPairD_iff dc sl lo hi l1 l2 f1 f2, bestPairD_iff dc sl lo hi h1 h2 g1 g2]
    simp only [ep]
  cases ha : bestPairD dc sl lo hi l1 l2 with
  | none =>
    cases hb : bestPairD dc sl lo hi h1 h2 with
    | none => rfl
    | some p => have := (key p).2 hb; rw [ha] at this; cases this
  | some p => exact ((key p).1 ha).symm

/-- The penalty bound from the best pair of a list. -/
def topE (dc : Nat → Nat) (ps : List PairHit) : Option Nat :=
  (topW dc ps).map fun w => (-(pairScoreD dc w)).toNat

theorem topW_none_iff (dc : Nat → Nat) (l : List PairHit) : topW dc l = none ↔ l = [] := by
  cases l <;> simp [topW]

theorem topE_congr (dc : Nat → Nat) {l l' : List PairHit} (e : ∀ p, p ∈ l ↔ p ∈ l') :
    topE dc l = topE dc l' := by
  unfold topE
  cases h : topW dc l with
  | none =>
    cases h' : topW dc l' with
    | none => rfl
    | some w =>
      have := (e w).2 (topW_mem dc l' w h')
      rw [(topW_none_iff dc l).1 h] at this; cases this
  | some w =>
    cases h' : topW dc l' with
    | none =>
      have := (e w).1 (topW_mem dc l w h)
      rw [(topW_none_iff dc l').1 h'] at this; cases this
    | some w' =>
      have a := topW_max dc l w h w' ((e w').2 (topW_mem dc l' w' h'))
      have b := topW_max dc l' w' h' w ((e w).1 (topW_mem dc l w h))
      have : pairScoreD dc w = pairScoreD dc w' := by omega
      simp only [Option.map_some, this]

theorem isEmpty_congr {α : Type} {l l' : List α} (e : ∀ p, p ∈ l ↔ p ∈ l') : l.isEmpty = l'.isEmpty := by
  cases l with
  | nil =>
    cases l' with
    | nil => rfl
    | cons y _ => have := (e y).2 List.mem_cons_self; cases this
  | cons y _ =>
    cases l' with
    | nil => have := (e y).1 List.mem_cons_self; cases this
    | cons _ _ => rfl

/-- The ladder, the second mate's hits at each rung from `hn` given the first mate's. -/
def ladderUB (dc : Nat → Nat) (sl lo hi P1 P2 : Nat) (hf : Bool → Nat → List (Placement × Int))
    (hn : Bool → Nat → List (Placement × Int) → List (Placement × Int)) (a1 : Bool) :
    List Nat → Option PairHit × Bool
  | [] =>
    let lA := hf a1 (if a1 then P1 else P2)
    let lB := hn (!a1) (if a1 then P2 else P1) lA
    let ps := properPairsF sl lo hi (if a1 then lA else lB) (if a1 then lB else lA)
    (bestOfPairs dc ps, !ps.isEmpty)
  | c :: cs =>
    let c1 := min c P1
    let c2 := min c P2
    let hA := hf a1 (if a1 then c1 else c2)
    if hA.isEmpty then
      if (if a1 then P1 ≤ c1 else P2 ≤ c2) then (none, false) else ladderUB dc sl lo hi P1 P2 hf hn a1 cs
    else
      let hB := hn (!a1) (if a1 then c2 else c1) hA
      let ps := properPairsF sl lo hi (if a1 then hA else hB) (if a1 then hB else hA)
      if P1 ≤ c1 ∧ P2 ≤ c2 then (bestOfPairs dc ps, !ps.isEmpty)
      else match topE dc ps with
        | none => ladderUB dc sl lo hi P1 P2 hf hn a1 cs
        | some e =>
          if (P1 ≤ c1 ∨ e ≤ c1) ∧ (P2 ≤ c2 ∨ e ≤ c2) then (bestOfPairs dc ps, true)
          else
            let lA := hf a1 (if a1 then min P1 e else min P2 e)
            let lB := hn (!a1) (if a1 then min P2 e else min P1 e) lA
            (bestOfPairs dc (properPairsF sl lo hi (if a1 then lA else lB) (if a1 then lB else lA)), true)

section near
variable (dc : Nat → Nat) (sl lo hi P1 P2 : Nat) (hf : Bool → Nat → List (Placement × Int))
  (hn : Bool → Nat → List (Placement × Int) → List (Placement × Int))
  (hSF : ∀ b c, c ≤ (if b then P1 else P2) → ScoreFun (hf b c))
  (hN : ∀ b c lA, c ≤ (if b then P1 else P2) → NearOk sl lo hi lA (hf b c) (hn b c lA))

include hSF hN in
/-- One rung, mate 1 first: the near list gives the full list's proper pairs. -/
theorem rungB_true (c1 c2 : Nat) (h1 : c1 ≤ P1) (h2 : c2 ≤ P2) :
    (∀ p, p ∈ properPairs sl lo hi (hf true c1) (hn false c2 (hf true c1)) ↔
      p ∈ properPairs sl lo hi (hf true c1) (hf false c2)) ∧
    bestPairD dc sl lo hi (hf true c1) (hn false c2 (hf true c1)) =
      bestPairD dc sl lo hi (hf true c1) (hf false c2) := by
  have E := pp_near_right (hN false c2 (hf true c1) h2)
  exact ⟨E, bestPairD_congrPP dc sl lo hi E (hSF true c1 h1) (scoreFun_sub (hN false c2 _ h2).1 (hSF false c2 h2))
    (hSF true c1 h1) (hSF false c2 h2)⟩

include hSF hN in
theorem rungB_false (c1 c2 : Nat) (h1 : c1 ≤ P1) (h2 : c2 ≤ P2) :
    (∀ p, p ∈ properPairs sl lo hi (hn true c1 (hf false c2)) (hf false c2) ↔
      p ∈ properPairs sl lo hi (hf true c1) (hf false c2)) ∧
    bestPairD dc sl lo hi (hn true c1 (hf false c2)) (hf false c2) =
      bestPairD dc sl lo hi (hf true c1) (hf false c2) := by
  have E := pp_near_left (hN true c1 (hf false c2) h1)
  exact ⟨E, bestPairD_congrPP dc sl lo hi E (scoreFun_sub (hN true c1 _ h1).1 (hSF true c1 h1)) (hSF false c2 h2)
    (hSF true c1 h1) (hSF false c2 h2)⟩

include hSF hN in
/-- **The near ladder is the ladder.** -/
theorem ladderUB_eq (a1 : Bool) : ∀ cs,
    ladderUB dc sl lo hi P1 P2 hf hn a1 cs = ladderUR dc sl lo hi P1 P2 hf a1 cs
  | [] => by
    cases a1
    · have r := rungB_false dc sl lo hi P1 P2 hf hn hSF hN P1 P2 (Nat.le_refl _) (Nat.le_refl _)
      simp only [ladderUB, ladderUR, properPairsF_eq, bestOfPairs_pp, Bool.not_false, Bool.false_eq_true,
        ↓reduceIte, r.2, isEmpty_congr r.1]
    · have r := rungB_true dc sl lo hi P1 P2 hf hn hSF hN P1 P2 (Nat.le_refl _) (Nat.le_refl _)
      simp only [ladderUB, ladderUR, properPairsF_eq, bestOfPairs_pp, Bool.not_true, ↓reduceIte, r.2,
        isEmpty_congr r.1]
  | c :: cs => by
    have ih := ladderUB_eq a1 cs
    cases a1
    · have r := rungB_false dc sl lo hi P1 P2 hf hn hSF hN (min c P1) (min c P2) (Nat.min_le_right _ _) (Nat.min_le_right _ _)
      have re := fun e => rungB_false dc sl lo hi P1 P2 hf hn hSF hN (min P1 e) (min P2 e) (Nat.min_le_left _ _) (Nat.min_le_left _ _)
      simp only [ladderUB, ladderUR, properPairsF_eq, bestOfPairs_pp, Bool.not_false, Bool.false_eq_true,
        ↓reduceIte, r.2, isEmpty_congr r.1, topE_congr dc r.1, ih, (re _).2]
      split
      · rfl
      · split
        · rfl
        · unfold topE
          cases topW dc (properPairs sl lo hi (hf true (min c P1)) (hf false (min c P2))) <;> rfl
    · have r := rungB_true dc sl lo hi P1 P2 hf hn hSF hN (min c P1) (min c P2) (Nat.min_le_right _ _) (Nat.min_le_right _ _)
      have re := fun e => rungB_true dc sl lo hi P1 P2 hf hn hSF hN (min P1 e) (min P2 e) (Nat.min_le_left _ _) (Nat.min_le_left _ _)
      simp only [ladderUB, ladderUR, properPairsF_eq, bestOfPairs_pp, Bool.not_true, ↓reduceIte, r.2,
        isEmpty_congr r.1, topE_congr dc r.1, ih, (re _).2]
      split
      · rfl
      · split
        · rfl
        · unfold topE
          cases topW dc (properPairs sl lo hi (hf true (min c P1)) (hf false (min c P2))) <;> rfl

end near

/-! ## Hits near the first mate's hits -/

/-- `hitsCK` on the diagonals `sel` keeps. -/
def hitsCKN (K : RP) (R : ByteArray) (pgs2 : Array PGen) (c lim : Nat) (acc : List (Array Nat))
    (us : List Nat) (Ls : Nat) (sel : Nat → Bool) : List (Window × Nat) :=
  (diags acc).flatMap fun D =>
    if sel D && kfiltV K R pgs2[c]! acc us Ls lim (initP lim) D then
      (shapesAt lim).filterMap fun sh =>
        if 0 ≤ dst R.size D sh ∧ 0 ≤ wlen R.size sh then
          let k := kerHKG R K pgs2 pgs2 c (dst R.size D sh).toNat (wlen R.size sh).toNat lim
          if k ≤ lim then some (⟨c, (dst R.size D sh).toNat, (wlen R.size sh).toNat⟩, k) else none
        else none
    else []

theorem hitsCKN_sub (K : RP) (R : ByteArray) (pgs2 : Array PGen) (c lim : Nat) (acc : List (Array Nat))
    (us : List Nat) (Ls : Nat) (sel : Nat → Bool) (x : Window × Nat)
    (h : x ∈ hitsCKN K R pgs2 c lim acc us Ls sel) : x ∈ hitsCK K R pgs2 c lim acc us Ls := by
  unfold hitsCKN at h
  unfold hitsCK
  rw [List.mem_flatMap] at h ⊢
  obtain ⟨D, hD, hx⟩ := h
  refine ⟨D, hD, ?_⟩
  split at hx
  · next hk =>
    rw [Bool.and_eq_true] at hk
    rw [if_pos hk.2]; exact hx
  · cases hx

theorem hitsCKN_of (K : RP) (R : ByteArray) (pgs2 : Array PGen) (c lim : Nat) (acc : List (Array Nat))
    (us : List Nat) (Ls : Nat) (sel : Nat → Bool) (x : Window × Nat)
    (h : x ∈ hitsCK K R pgs2 c lim acc us Ls)
    (hs : ∀ D sh, sh ∈ shapesAt lim → 0 ≤ dst R.size D sh →
      x.1 = ⟨c, (dst R.size D sh).toNat, (wlen R.size sh).toNat⟩ → sel D = true) :
    x ∈ hitsCKN K R pgs2 c lim acc us Ls sel := by
  unfold hitsCK at h
  unfold hitsCKN
  rw [List.mem_flatMap] at h ⊢
  obtain ⟨D, hD, hx⟩ := h
  refine ⟨D, hD, ?_⟩
  split at hx
  · next hk =>
    have hx' := hx
    rw [List.mem_filterMap] at hx'
    obtain ⟨sh, hsh, he⟩ := hx'
    split at he
    · next hc =>
      simp only [] at he
      split at he
      · simp only [Option.some.injEq] at he
        have hsel := hs D sh hsh hc.1 (by rw [← he])
        rw [if_pos (by rw [Bool.and_eq_true]; exact ⟨hsel, hk⟩)]
        exact hx
      · cases he
    · cases he
  · cases hx

/-- `hitsSK` with each chromosome's diagonals chosen by `keep` (virtual chromosome, read length). -/
def hitsSKN {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G : ByteArray) (offs : Array Nat)
    (pgs2 : Array PGen) (n t lim : Nat) (Rs : ByteArray) (keep : Nat → Nat → Nat → Bool) : List (Window × Nat) :=
  let m := Rs.size / 25
  let Ls := Rs.size / m
  let K := packRP Rs
  let ps := prepG ix Rs m Ls
  let J := (ordG (ps.map (LookG.size ix)) m).take (sbound lim + 1)
  let lk := J.map fun j => (j, LookG.look ix G Rs (j * Ls) (Rs.size - j * Ls) ps[j]!)
  let us := unseen m J
  (List.range n).flatMap fun c =>
    hitsCKN K Rs pgs2 (t + c) lim (slicesAt lk Rs.size Ls offs[c]! (GRead.size pgs2[t + c]!)) us Ls
      (keep (t + c) Rs.size)

/-- `hitsAtKP` on the diagonals `keep` chooses. -/
def hitsAtKPN {L Pp : Type} [LookG L Pp] [Inhabited Pp] (lim : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (pgs : Array PGen) (R : ByteArray) (keep : Nat → Nat → Nat → Bool) :
    Option (List (Placement × Int)) :=
  if fastT lim R then
    let n := pgs.size
    let pgs2 := pgs ++ pgs
    some ((hitsSKN ix G offs pgs2 n 0 lim R keep ++ hitsSKN ix G offs pgs2 n n lim (revCompK R) keep).map
      fun x => (decB n x.1, -(x.2 : Int)))
  else none

theorem hitsSKN_sub {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G : ByteArray) (offs : Array Nat)
    (pgs2 : Array PGen) (n t lim : Nat) (Rs : ByteArray) (keep : Nat → Nat → Nat → Bool) (x : Window × Nat)
    (h : x ∈ hitsSKN ix G offs pgs2 n t lim Rs keep) : x ∈ hitsSK ix G offs pgs2 n t lim Rs := by
  unfold hitsSKN at h
  unfold hitsSK
  simp only [List.mem_flatMap] at h ⊢
  obtain ⟨c, hc, hx⟩ := h
  exact ⟨c, hc, hitsCKN_sub _ _ _ _ _ _ _ _ _ x hx⟩

theorem hitsSKN_of {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G : ByteArray) (offs : Array Nat)
    (pgs2 : Array PGen) (n t lim : Nat) (Rs : ByteArray) (keep : Nat → Nat → Nat → Bool) (x : Window × Nat)
    (h : x ∈ hitsSK ix G offs pgs2 n t lim Rs)
    (hs : ∀ vc D sh, sh ∈ shapesAt lim → 0 ≤ dst Rs.size D sh →
      x.1 = ⟨vc, (dst Rs.size D sh).toNat, (wlen Rs.size sh).toNat⟩ → keep vc Rs.size D = true) :
    x ∈ hitsSKN ix G offs pgs2 n t lim Rs keep := by
  unfold hitsSK at h
  unfold hitsSKN
  simp only [List.mem_flatMap] at h ⊢
  obtain ⟨c, hc, hx⟩ := h
  exact ⟨c, hc, hitsCKN_of _ _ _ _ _ _ _ _ _ x hx (fun D sh h1 h2 h3 => hs _ D sh h1 h2 h3)⟩

/-- The near hits are hits; a hit whose every possible diagonal is kept is a near hit. -/
theorem hitsAtKPN_mem {L Pp : Type} [LookG L Pp] [Inhabited Pp] (lim : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (pgs : Array PGen) (R : ByteArray) (keep : Nat → Nat → Nat → Bool)
    (l l' : List (Placement × Int)) (hl : hitsAtKP lim ix G offs pgs R = some l)
    (hl' : hitsAtKPN lim ix G offs pgs R keep = some l') (x : Placement × Int) :
    (x ∈ l' → x ∈ l) ∧
    (x ∈ l → (∀ vc nR D sh, sh ∈ shapesAt lim → 0 ≤ dst nR D sh →
      x.1 = decB pgs.size ⟨vc, (dst nR D sh).toNat, (wlen nR sh).toNat⟩ → keep vc nR D = true) → x ∈ l') := by
  unfold hitsAtKP at hl
  unfold hitsAtKPN at hl'
  split at hl
  · next hf =>
    rw [if_pos hf] at hl'
    simp only [Option.some.injEq] at hl hl'
    subst hl hl'
    constructor
    · intro hx
      simp only [List.mem_map, List.mem_append] at hx ⊢
      obtain ⟨y, hy, rfl⟩ := hx
      refine ⟨y, ?_, rfl⟩
      rcases hy with hy | hy
      · exact Or.inl (hitsSKN_sub _ _ _ _ _ _ _ _ _ y hy)
      · exact Or.inr (hitsSKN_sub _ _ _ _ _ _ _ _ _ y hy)
    · intro hx hk
      simp only [List.mem_map, List.mem_append] at hx ⊢
      obtain ⟨y, hy, rfl⟩ := hx
      refine ⟨y, ?_, rfl⟩
      have hs : ∀ (Rs : ByteArray), ∀ vc D sh, sh ∈ shapesAt lim → 0 ≤ dst Rs.size D sh →
          y.1 = ⟨vc, (dst Rs.size D sh).toNat, (wlen Rs.size sh).toNat⟩ → keep vc Rs.size D = true := by
        intro Rs vc D sh h1 h2 h3
        exact hk vc Rs.size D sh h1 h2 (by rw [h3])
      rcases hy with hy | hy
      · exact Or.inl (hitsSKN_of _ _ _ _ _ _ _ _ _ y hy (hs _))
      · exact Or.inr (hitsSKN_of _ _ _ _ _ _ _ _ _ y hy (hs _))
  · cases hl

/-! ## The diagonal choice from the first mate's hits -/

/-- Diagonal `D` of virtual chromosome `vc` (read length `nR`, shift bound `gb`) may hold a
window with a proper partner among the hits `ys`. -/
def keepN (sl hi n gb : Nat) (ys : List (Placement × Int)) (vc nR D : Nat) : Bool :=
  ys.any fun y => y.1.1.chr == (if vc < n then vc else vc - n) &&
    decide (D ≤ y.1.1.start + y.1.1.len + hi + sl + nR + gb) && decide (y.1.1.start + nR ≤ D + hi + sl + gb)

theorem properPairU_near (sl lo hi : Nat) (a b : Placement) (h : properPairU sl lo hi a b = true) :
    a.1.chr = b.1.chr ∧ b.1.start ≤ a.1.start + a.1.len + hi + sl ∧ a.1.start ≤ b.1.start + hi + sl ∧
      a.1.start ≤ b.1.start + b.1.len + hi + sl ∧ b.1.start ≤ a.1.start + hi + sl := by
  rcases a with ⟨⟨ca, sa, la⟩, ta⟩
  rcases b with ⟨⟨cb, sb, lb⟩, tb⟩
  cases ta <;> cases tb <;> simp [properPairU, properPair, fwdRev] at h ⊢ <;> omega

theorem shapesAt_fst (lim : Nat) (sh : Int × Int) (h : sh ∈ shapesAt lim) :
    sh.1.natAbs ≤ gapBound sc0 (-(lim : Int)) := by
  unfold shapesAt at h
  rw [List.mem_mergeSort] at h
  have := (shapes_ok _ _ sh h).1
  omega

/-- The near list of a read at cap `c` given the first mate's hits `ys`. -/
def hitsKPFN {L Pp : Type} [LookG L Pp] [Inhabited Pp] (sl hi : Nat) (ix : L) (G : ByteArray) (offs : Array Nat)
    (pgs : Array PGen) (R : ByteArray) (c : Nat) (ys : List (Placement × Int)) : List (Placement × Int) :=
  match hitsAtKPN c ix G offs pgs R (keepN sl hi pgs.size (gapBound sc0 (-(c : Int))) ys) with
  | some l => l
  | none => hitsKPF ix G offs pgs R c

theorem hitsKPFN_near {L Pp : Type} [LookG L Pp] [Inhabited Pp] (sl lo hi : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (pgs : Array PGen) (R : ByteArray) (c : Nat) (ys : List (Placement × Int)) :
    NearOk sl lo hi ys (hitsKPF ix G offs pgs R c) (hitsKPFN sl hi ix G offs pgs R c ys) := by
  unfold hitsKPFN hitsKPF
  cases hl : hitsAtKP c ix G offs pgs R with
  | none =>
    have hn : hitsAtKPN c ix G offs pgs R (keepN sl hi pgs.size (gapBound sc0 (-(c : Int))) ys) = none := by
      unfold hitsAtKP at hl; unfold hitsAtKPN
      split at hl
      · cases hl
      · next hf => rw [if_neg hf]
    simp only [hn]
    exact ⟨fun x hx => hx, fun x hx _ => hx⟩
  | some l =>
    have hs : ∃ l', hitsAtKPN c ix G offs pgs R (keepN sl hi pgs.size (gapBound sc0 (-(c : Int))) ys) = some l' := by
      unfold hitsAtKP at hl; unfold hitsAtKPN
      split at hl
      · next hf => rw [if_pos hf]; exact ⟨_, rfl⟩
      · cases hl
    obtain ⟨l', hl'⟩ := hs
    simp only [hl']
    refine ⟨fun x hx => (hitsAtKPN_mem c ix G offs pgs R _ l l' hl hl' x).1 hx, fun x hx hp => ?_⟩
    apply (hitsAtKPN_mem c ix G offs pgs R _ l l' hl hl' x).2 hx
    intro vc nR D sh hsh hd hxe
    obtain ⟨y, hy, hpy⟩ := hp
    have hb := shapesAt_fst c sh hsh
    have hxs : x.1.1.start = (dst nR D sh).toNat := by rw [hxe]; unfold decB; split <;> rfl
    have hxc : x.1.1.chr = (if vc < pgs.size then vc else vc - pgs.size) := by
      rw [hxe]; unfold decB; split <;> simp [*]
    have hdd : dst nR D sh = (D : Int) - nR - sh.1 := rfl
    unfold keepN
    rw [List.any_eq_true]
    refine ⟨y, hy, ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    rcases hpy with h | h
    · obtain ⟨e1, e2, e3, e4, e5⟩ := properPairU_near sl lo hi y.1 x.1 h
      refine ⟨⟨e1.trans hxc, ?_⟩, ?_⟩ <;> omega
    · obtain ⟨e1, e2, e3, e4, e5⟩ := properPairU_near sl lo hi x.1 y.1 h
      refine ⟨⟨e1.symm.trans hxc, ?_⟩, ?_⟩ <;> omega

/-! ## Mode HN: mode H with the second mate searched near the first -/

/-- Mode H, the ladder's second-searched mate enumerated only on diagonals near the first
mate's hits at each rung (`keepN`). -/
def pairUKHN {L Pp L2 Pp2 : Type} [LookG L Pp] [Inhabited Pp] [LookG L2 Pp2] [Inhabited Pp2]
    (dc : Nat → Nat) (sl lo hi : Nat) (caps : List Nat) (a1 : Bool) (ix : L) (rl : Nat → Nat → L2)
    (G : ByteArray) (offs : Array Nat) (pgs : Array PGen) (R1 R2 : ByteArray) : Option PairHit × Bool :=
  let lad := fun (_ : Unit) =>
    ladderUB dc sl lo hi (penOf R1) (penOf R2) (fun b c => hitsKPF ix G offs pgs (if b then R1 else R2) c)
      (fun b c ys => hitsKPFN sl hi ix G offs pgs (if b then R1 else R2) c ys) a1 caps
  match pairRegionKP lo hi ix rl G offs pgs R1 R2 with
  | some (a, b) => if properPairU sl lo hi a.1 b.1 && dc (fragLen a.1 b.1) == 0 then (some (a, b), true) else lad ()
  | none => lad ()

section topN
variable (dc : Nat → Nat) (sl lo hi : Nat) (caps : List Nat) (a1 : Bool) (g : Genome)
  (m1 m2 : List Char) (ix : Mz.MzIdx) (G : PGen) (offs ns : Array Nat) (R1 R2 : ByteArray)
  (hcut : cutOk G offs ns = true) (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) g)
  (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hchk : Mz.check2P ix G = true)

include hcut hg h1 h2 hchk in
/-- **Mode HN is mode H.** -/
theorem pairUKHN_eq :
    pairUKHN dc sl lo hi caps a1 ((ix, G) : PkMz) (fun a b => ((((ix, G) : PkMz), a, b) : RgMz)) ByteArray.empty
      offs (cutAll G offs ns) R1 R2 =
    pairUKH dc sl lo hi caps a1 ((ix, G) : PkMz) (fun a b => ((((ix, G) : PkMz), a, b) : RgMz)) ByteArray.empty
      offs (cutAll G offs ns) R1 R2 := by
  have hSF : ∀ (b : Bool) c, c ≤ (if b then penOf R1 else penOf R2) →
      ScoreFun (hitsKPF ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) (if b then R1 else R2) c) := by
    intro b c hc
    cases b
    · exact scoreFun_of_iff (hitsKPF_mem g ix G offs ns hcut hg hchk R2 m2 h2 c
        (Nat.le_trans hc (penOf_le16 R2))) (hitsBoth_scoreFun sc0 _ g m2)
    · exact scoreFun_of_iff (hitsKPF_mem g ix G offs ns hcut hg hchk R1 m1 h1 c
        (Nat.le_trans hc (penOf_le16 R1))) (hitsBoth_scoreFun sc0 _ g m1)
  have e := ladderUB_eq dc sl lo hi (penOf R1) (penOf R2)
    (fun b c => hitsKPF ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) (if b then R1 else R2) c)
    (fun b c ys => hitsKPFN sl hi ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) (if b then R1 else R2) c ys)
    hSF (fun b c lA _ => hitsKPFN_near sl lo hi _ _ _ _ _ c lA) a1 caps
  unfold pairUKHN pairUKH
  simp only [e, ladderUF_eq]
  rfl

include hcut hg h1 h2 hchk in
/-- **Mode HN, packed whole genome: the pair-level specification.** -/
theorem pairUKHN_mz_eq :
    (pairUKHN dc sl lo hi caps a1 ((ix, G) : PkMz) (fun a b => ((((ix, G) : PkMz), a, b) : RgMz)) ByteArray.empty
      offs (cutAll G offs ns) R1 R2).1 =
      pairSpecUT sc0 dc sl lo hi (-(penOf R1 : Int)) (-(penOf R2 : Int)) g m1 m2 := by
  rw [pairUKHN_eq dc sl lo hi caps a1 g m1 m2 ix G offs ns R1 R2 hcut hg h1 h2 hchk]
  exact pairUKH_mz_eq dc sl lo hi caps a1 g m1 m2 ix G offs ns R1 R2 hcut hg h1 h2 hchk

include hcut hg h1 h2 hchk in
/-- **Mode HN: the answer kind `pairTie` is exact.** -/
theorem pairUKHN_tie
    (h : pairUKHN dc sl lo hi caps a1 ((ix, G) : PkMz) (fun a b => ((((ix, G) : PkMz), a, b) : RgMz)) ByteArray.empty
      offs (cutAll G offs ns) R1 R2 = (none, true)) :
    PairTieOk dc sl lo hi (-(penOf R1 : Int)) (-(penOf R2 : Int)) g m1 m2 := by
  rw [pairUKHN_eq dc sl lo hi caps a1 g m1 m2 ix G offs ns R1 R2 hcut hg h1 h2 hchk] at h
  exact pairUKH_tie dc sl lo hi caps a1 g m1 m2 ix G offs ns R1 R2 hcut hg h1 h2 hchk h

end topN

end MapSpec.Fast

#print axioms MapSpec.Fast.ladderUB_eq
#print axioms MapSpec.Fast.hitsKPFN_near
#print axioms MapSpec.Fast.pairUKHN_mz_eq
#print axioms MapSpec.Fast.pairUKHN_tie
