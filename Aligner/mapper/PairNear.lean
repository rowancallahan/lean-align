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

/-- `hitsCKN` with the shapes taken once from the table (`hitsCKN_eqT`). -/
def hitsCKNT (K : RP) (R : ByteArray) (pgs2 : Array PGen) (c lim : Nat) (acc : List (Array Nat))
    (us : List Nat) (Ls : Nat) (sel : Nat → Bool) : List (Window × Nat) :=
  if acc.all fun a => a.isEmpty then [] else
  let shs := shapesT lim
  (diags acc).flatMap fun D =>
    if sel D && kfiltV K R pgs2[c]! acc us Ls lim (initP lim) D then
      shs.filterMap fun sh =>
        if 0 ≤ dst R.size D sh ∧ 0 ≤ wlen R.size sh then
          let k := kerHKG R K pgs2 pgs2 c (dst R.size D sh).toNat (wlen R.size sh).toNat lim
          if k ≤ lim then some (⟨c, (dst R.size D sh).toNat, (wlen R.size sh).toNat⟩, k) else none
        else none
    else []

/-- Compiled code runs `hitsCKNT`. -/
@[csimp] theorem hitsCKN_eqT : @hitsCKN = @hitsCKNT := by
  funext K R pgs2 c lim acc us Ls sel
  unfold hitsCKN hitsCKNT
  split
  · rename_i h; rw [diags_empty acc h]; rfl
  · simp only [shapesT_eq]

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

/-! ### `keepN` by binary search (`keepQ_eq`)
`keepN` scans the first mate's whole hit list for every candidate diagonal of the second mate. `keepTab` sorts the
hits' windows (chromosome, start, end) by chromosome then start and replaces each end by the running maximum of the
ends within its chromosome; `keepQ` then answers `keepN` with one binary search. -/

abbrev Win := Nat × Nat × Nat

-- a hit's window: chromosome, start, end
def winOf (y : Placement × Int) : Nat × Nat × Nat := (y.1.1.chr, y.1.1.start, y.1.1.start + y.1.1.len)

-- (chromosome, start) order
def winLe (a b : Nat × Nat × Nat) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2.1 ≤ b.2.1)

-- the running maximum so far for `x` (`prev`: the previous chromosome and maximum)
def nextMax (prev : Option (Nat × Nat)) (x : Nat × Nat × Nat) : Nat :=
  match prev with
  | some (c, m) => if c == x.1 then max m x.2.2 else x.2.2
  | none => x.2.2

-- each end replaced by the maximum end so far within its chromosome
def runMax : List (Nat × Nat × Nat) → Option (Nat × Nat) → List (Nat × Nat × Nat)
  | [], _ => []
  | x :: xs, prev => (x.1, x.2.1, nextMax prev x) :: runMax xs (some (x.1, nextMax prev x))

def keepTab (ys : List (Placement × Int)) : Array (Nat × Nat × Nat) :=
  (runMax ((ys.map winOf).mergeSort winLe) none).toArray

-- bisection in `[lo, hi)` for the first entry above `(c, a)` in (chromosome, start) order
def keepCountGo (t : Array (Nat × Nat × Nat)) (c a : Nat) : (fuel lo hi : Nat) → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      if winLe t[mid]! (c, a, 0) then keepCountGo t c a fuel (mid + 1) hi else keepCountGo t c a fuel lo mid
    else lo

-- the number of entries `≤ (c, a)` in (chromosome, start) order
def keepCount (t : Array (Nat × Nat × Nat)) (c a : Nat) : Nat := keepCountGo t c a (t.size + 1) 0 t.size

-- the query on a built table (`K = hi + sl + gb`)
def keepQ (K n : Nat) (t : Array (Nat × Nat × Nat)) (vc nR D : Nat) : Bool :=
  let c := if vc < n then vc else vc - n
  if D + K < nR then false else
  let k := keepCount t c (D + K - nR)
  if k == 0 then false else
  let e := t[k - 1]!
  e.1 == c && decide (D ≤ e.2.2 + K + nR)

/-- Diagonal `D` of virtual chromosome `vc` (read length `nR`, shift bound `gb`) may hold a
window with a proper partner among the hits `ys`. -/
def keepN (sl hi n gb : Nat) (ys : List (Placement × Int)) (vc nR D : Nat) : Bool :=
  ys.any fun y => y.1.1.chr == (if vc < n then vc else vc - n) &&
    decide (D ≤ y.1.1.start + y.1.1.len + hi + sl + nR + gb) && decide (y.1.1.start + nR ≤ D + hi + sl + gb)

theorem runMax_length : ∀ (xs : List Win) p, (runMax xs p).length = xs.length
  | [], _ => rfl
  | x :: xs, p => by simp [runMax, runMax_length xs]

theorem runMax_spec : ∀ (xs : List Win) (prev : Option (Nat × Nat)),
    xs.Pairwise (fun a b => a.1 ≤ b.1) → (∀ pc pm, prev = some (pc, pm) → ∀ x ∈ xs, pc ≤ x.1) →
    ∀ i, i < xs.length → ((runMax xs prev)[i]!).1 = xs[i]!.1 ∧ ((runMax xs prev)[i]!).2.1 = xs[i]!.2.1 ∧
      ∀ B, (B ≤ ((runMax xs prev)[i]!).2.2 ↔
        (∃ pm, prev = some (xs[i]!.1, pm) ∧ B ≤ pm) ∨ ∃ j, j ≤ i ∧ xs[j]!.1 = xs[i]!.1 ∧ B ≤ xs[j]!.2.2)
  | [], _, _, _, i, hi => by simp at hi
  | x :: xs, prev, hs, hp, i, hi => by
    rw [List.pairwise_cons] at hs
    have hm : ∀ B, B ≤ nextMax prev x ↔
        (∃ pm, prev = some (x.1, pm) ∧ B ≤ pm) ∨ B ≤ x.2.2 := by
      intro B
      rcases prev with _ | ⟨c, pm⟩
      · simp [nextMax]
      · by_cases h : c = x.1
        · subst h; simp [nextMax]; omega
        · have : (c == x.1) = false := by simpa using h
          simp [nextMax, this, h]
    cases i with
    | zero =>
      refine ⟨by simp [runMax], by simp [runMax], fun B => ?_⟩
      simp only [runMax]
      simp only [List.getElem!_cons_zero]
      rw [hm B]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr ⟨0, Nat.le_refl _, rfl, by simpa using h⟩
      · rintro (h | ⟨j, hj, -, h⟩)
        · exact Or.inl h
        · have : j = 0 := by omega
          subst this
          exact Or.inr (by simpa using h)
    | succ i =>
      have hi' : i < xs.length := by simpa using hi
      have hmem : xs[i]! ∈ xs := by
        rw [getElem!_pos xs i hi']; exact List.getElem_mem hi'
      have hxi : x.1 ≤ xs[i]!.1 := hs.1 _ hmem
      obtain ⟨e1, e2, e3⟩ := runMax_spec xs (some (x.1, nextMax prev x)) hs.2 (by
        intro pc pm h y hy
        simp at h
        obtain ⟨rfl, -⟩ := h
        exact hs.1 y hy) i hi'
      simp only [runMax, List.getElem!_cons_succ]
      refine ⟨e1, e2, fun B => ?_⟩
      rw [e3 B]
      have hz : (x :: xs)[0]! = x := rfl
      constructor
      · rintro (⟨pm, h, hB⟩ | ⟨j, hj, h1, h2⟩)
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨h1, rfl⟩ := h
          rcases (hm B).1 hB with ⟨pm', hp', hB'⟩ | h
          · exact Or.inl ⟨pm', by rw [← h1]; exact hp', hB'⟩
          · exact Or.inr ⟨0, by omega, by rw [hz]; exact h1, by rw [hz]; exact h⟩
        · exact Or.inr ⟨j + 1, by omega, by simpa using h1, by simpa using h2⟩
      · rintro (⟨pm, hp0, hB⟩ | ⟨j, hj, h1, h2⟩)
        · have := hp _ _ hp0 x (by simp)
          have hx : x.1 = xs[i]!.1 := by omega
          exact Or.inl ⟨nextMax prev x, by rw [hx], (hm B).2 (Or.inl ⟨pm, by rw [hx]; exact hp0, hB⟩)⟩
        · cases j with
          | zero =>
            rw [hz] at h1 h2
            exact Or.inl ⟨nextMax prev x, by rw [h1], (hm B).2 (Or.inr h2)⟩
          | succ j => exact Or.inr ⟨j, by omega, by simpa using h1, by simpa using h2⟩

theorem winLe_trans {a b d : Win} (h1 : winLe a b = true) (h2 : winLe b d = true) : winLe a d = true := by
  simp [winLe] at *; omega

theorem winLe_fst {a b : Win} (h : winLe a b = true) : a.1 ≤ b.1 := by
  simp [winLe] at h; omega

theorem keepCountGo_spec (t : Array Win) (c a : Nat)
    (hm : ∀ i j, i ≤ j → j < t.size → winLe t[j]! (c, a, 0) = true → winLe t[i]! (c, a, 0) = true) :
    ∀ fuel lo hi, lo ≤ hi → hi ≤ t.size → hi - lo < fuel →
      (∀ i, i < lo → winLe t[i]! (c, a, 0) = true) → (∀ i, hi ≤ i → i < t.size → winLe t[i]! (c, a, 0) = false) →
      lo ≤ keepCountGo t c a fuel lo hi ∧ keepCountGo t c a fuel lo hi ≤ hi ∧
      (∀ i, i < keepCountGo t c a fuel lo hi → winLe t[i]! (c, a, 0) = true) ∧
      (∀ i, keepCountGo t c a fuel lo hi ≤ i → i < t.size → winLe t[i]! (c, a, 0) = false)
  | 0, lo, hi, h1, h2, h3, _, _ => by omega
  | fuel + 1, lo, hi, h1, h2, h3, hl, hh => by
    unfold keepCountGo
    by_cases hlt : lo < hi
    · simp only [hlt, ite_true]
      cases hp : winLe t[(lo + hi) / 2]! (c, a, 0)
      · simp only [Bool.false_eq_true, ite_false]
        obtain ⟨r1, r2, r3, r4⟩ := keepCountGo_spec t c a hm fuel lo ((lo + hi) / 2) (by omega) (by omega) (by omega) hl
          (fun i hi' hi2 => by
            by_cases hh' : hi ≤ i
            · exact hh i hh' hi2
            · cases hq : winLe t[i]! (c, a, 0)
              · rfl
              · have := hm ((lo + hi) / 2) i (by omega) hi2 hq
                rw [hp] at this; exact absurd this (by simp))
        exact ⟨r1, by omega, r3, r4⟩
      · simp only [ite_true]
        obtain ⟨r1, r2, r3, r4⟩ := keepCountGo_spec t c a hm fuel ((lo + hi) / 2 + 1) hi (by omega) h2 (by omega)
          (fun i hi' => by
            by_cases hh' : i < lo
            · exact hl i hh'
            · exact hm i ((lo + hi) / 2) (by omega) (by omega) hp) hh
        exact ⟨by omega, r2, r3, r4⟩
    · simp only [hlt, ite_false]
      refine ⟨Nat.le_refl _, by omega, hl, fun i hi' hi2 => hh i (by omega) hi2⟩

theorem keepCount_spec (t : Array Win) (c a : Nat)
    (hm : ∀ i j, i ≤ j → j < t.size → winLe t[j]! (c, a, 0) = true → winLe t[i]! (c, a, 0) = true) :
    keepCount t c a ≤ t.size ∧ (∀ i, i < keepCount t c a → winLe t[i]! (c, a, 0) = true) ∧
      (∀ i, keepCount t c a ≤ i → i < t.size → winLe t[i]! (c, a, 0) = false) := by
  obtain ⟨-, r2, r3, r4⟩ := keepCountGo_spec t c a hm (t.size + 1) 0 t.size (by omega) (Nat.le_refl _) (by omega)
    (fun i h => by omega) (fun i h h' => by omega)
  exact ⟨r2, r3, r4⟩

theorem winLe_q (w : Win) (c a : Nat) : winLe w (c, a, 0) = true ↔ w.1 < c ∨ (w.1 = c ∧ w.2.1 ≤ a) := by
  simp [winLe]

theorem keepTab_query (S : List Win) (hS : S.Pairwise (fun a b => winLe a b = true)) (c a B : Nat) :
    let t := (runMax S none).toArray
    (keepCount t c a ≠ 0 ∧ t[keepCount t c a - 1]!.1 = c ∧ B ≤ t[keepCount t c a - 1]!.2.2) ↔
      ∃ w ∈ S, w.1 = c ∧ w.2.1 ≤ a ∧ B ≤ w.2.2 := by
  intro t
  have hn : (runMax S none).length = S.length := runMax_length S none
  have htz : t.size = S.length := by simp [t, hn]
  have hf : S.Pairwise (fun a b => a.1 ≤ b.1) := hS.imp winLe_fst
  have hsp := runMax_spec S none hf (by simp)
  have hT : ∀ i, i < S.length → t[i]! = (runMax S none)[i]! := fun i hi => by
    simp [t]
  have key : ∀ i, i < S.length → winLe t[i]! (c, a, 0) = winLe S[i]! (c, a, 0) := fun i hi => by
    obtain ⟨e1, e2, -⟩ := hsp i hi
    rw [hT i hi]; simp only [winLe, e1, e2]
  have hmono : ∀ i j, i ≤ j → j < S.length → winLe S[j]! (c, a, 0) = true → winLe S[i]! (c, a, 0) = true := by
    intro i j hij hj h
    rcases Nat.lt_or_ge i j with hlt | hge
    · have := List.pairwise_iff_getElem.1 hS i j (by omega) hj hlt
      rw [getElem!_pos S i (by omega)]
      rw [getElem!_pos S j hj] at h
      exact winLe_trans this h
    · have : i = j := by omega
      subst this; exact h
  have hm : ∀ i j, i ≤ j → j < t.size → winLe t[j]! (c, a, 0) = true → winLe t[i]! (c, a, 0) = true := by
    intro i j hij hj h
    rw [htz] at hj
    rw [key j hj] at h; rw [key i (by omega)]; exact hmono i j hij hj h
  obtain ⟨hk1, hk2, hk3⟩ := keepCount_spec t c a hm
  rw [htz] at hk1 hk3
  generalize keepCount t c a = k at *
  have hpair : ∀ i j, i ≤ j → j < S.length → S[i]!.1 ≤ S[j]!.1 := by
    intro i j hij hj
    rcases Nat.lt_or_ge i j with hlt | hge
    · have := List.pairwise_iff_getElem.1 hf i j (by omega) hj hlt
      rwa [getElem!_pos S i (by omega), getElem!_pos S j hj]
    · have : i = j := by omega
      subst this; exact Nat.le_refl _
  constructor
  · rintro ⟨hk0, he1, he2⟩
    have hk' : k - 1 < S.length := by omega
    obtain ⟨e1, -, e3⟩ := hsp (k - 1) hk'
    rw [hT _ hk'] at he1 he2
    rw [e1] at he1
    rcases (e3 B).1 he2 with ⟨pm, hpm, -⟩ | ⟨j, hj, h1, h2⟩
    · cases hpm
    have hjn : j < S.length := by omega
    refine ⟨S[j]!, by rw [getElem!_pos S j hjn]; exact List.getElem_mem hjn, by rw [h1, he1], ?_, h2⟩
    have := hk2 j (by omega)
    rw [key j hjn, winLe_q] at this
    have h1' := h1.trans he1
    omega
  · rintro ⟨w, hw, hw1, hw2, hw3⟩
    obtain ⟨j, hjn, rfl⟩ := List.mem_iff_getElem.1 hw
    have hw' : S[j]! = S[j] := getElem!_pos S j hjn
    rw [← hw'] at hw1 hw2 hw3
    have hpj : winLe S[j]! (c, a, 0) = true := (winLe_q _ _ _).2 (Or.inr ⟨hw1, hw2⟩)
    have hjk : j < k := by
      rcases Nat.lt_or_ge j k with h | h
      · exact h
      · have := hk3 j h hjn
        rw [key j hjn, hpj] at this; exact absurd this (by simp)
    have hk' : k - 1 < S.length := by omega
    have hpk' := hk2 (k - 1) (by omega)
    have hpk := hpk'
    rw [key _ hk'] at hpk
    have hle := winLe_fst hpk
    have hge := hpair j (k - 1) (by omega) hk'
    have hc : S[k - 1]!.1 = c := by
      rw [key _ hk', winLe_q] at hpk'
      omega
    obtain ⟨e1, -, e3⟩ := hsp (k - 1) hk'
    refine ⟨by omega, by rw [hT _ hk', e1, hc], ?_⟩
    rw [hT _ hk']
    exact (e3 B).2 (Or.inr ⟨j, by omega, by rw [hc]; exact hw1, hw3⟩)

theorem keepQ_eq (sl hi n gb : Nat) (ys : List (Placement × Int)) (vc nR D : Nat) :
    keepQ (hi + sl + gb) n (keepTab ys) vc nR D = keepN sl hi n gb ys vc nR D := by
  unfold keepQ keepN
  rw [Bool.eq_iff_iff]
  generalize (if vc < n then vc else vc - n) = c
  by_cases hD : D + (hi + sl + gb) < nR
  · simp only [hD, ite_true, Bool.false_eq_true, false_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, not_exists, not_and]
    intro y _ h1 h2; omega
  · simp only [hD, ite_false]
    have hS : ((ys.map winOf).mergeSort winLe).Pairwise (fun a b => winLe a b = true) :=
      List.pairwise_mergeSort (le := winLe) (fun a b c => winLe_trans) (fun a b => by simp [winLe]; omega) _
    have hq := keepTab_query _ hS c (D + (hi + sl + gb) - nR) (D - (hi + sl + gb) - nR)
    unfold keepTab
    dsimp only at hq
    have h2 : (ys.any fun y => y.1.1.chr == c && decide (D ≤ y.1.1.start + y.1.1.len + hi + sl + nR + gb) &&
        decide (y.1.1.start + nR ≤ D + hi + sl + gb)) = true ↔ ∃ w ∈ (ys.map winOf).mergeSort winLe, w.1 = c ∧
          w.2.1 ≤ D + (hi + sl + gb) - nR ∧ D - (hi + sl + gb) - nR ≤ w.2.2 := by
      rw [List.any_eq_true]
      constructor
      · rintro ⟨y, hy, h⟩
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
        exact ⟨winOf y, List.mem_mergeSort.2 (List.mem_map.2 ⟨y, hy, rfl⟩), h.1.1, by simp only [winOf]; omega,
          by simp only [winOf]; omega⟩
      · rintro ⟨w, hw, h1, h2, h3⟩
        rw [List.mem_mergeSort, List.mem_map] at hw
        obtain ⟨y, hy, rfl⟩ := hw
        simp only [winOf] at h1 h2 h3
        exact ⟨y, hy, by simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]; omega⟩
    rw [h2, ← hq]
    generalize keepCount (runMax ((List.map winOf ys).mergeSort winLe) none).toArray c (D + (hi + sl + gb) - nR) = k
    by_cases hk : k = 0
    · simp [hk]
    · simp only [beq_iff_eq, hk, ite_false, Bool.and_eq_true, decide_eq_true_eq, ne_eq, not_false_eq_true, true_and]
      constructor <;> intro h <;> omega


/-! ### The chromosome gate on the table: does some hit of `ys` lie on chromosome `k` (`keepHas_eq`) -/

-- a start no hit of `ys` exceeds
def maxStart (ys : List (Placement × Int)) : Nat := ys.foldl (fun m y => max m y.1.1.start) 0

theorem le_maxStart_go : ∀ (ys : List (Placement × Int)) (m : Nat),
    m ≤ ys.foldl (fun m y => max m y.1.1.start) m ∧ ∀ y ∈ ys, y.1.1.start ≤ ys.foldl (fun m y => max m y.1.1.start) m
  | [], m => by simp
  | y :: ys, m => by
    obtain ⟨h1, h2⟩ := le_maxStart_go ys (max m y.1.1.start)
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    exact ⟨by omega, by omega, h2⟩

def keepHas (t : Array (Nat × Nat × Nat)) (M k : Nat) : Bool :=
  let i := keepCount t k M
  i != 0 && t[i - 1]!.1 == k

theorem keepHas_eq (ys : List (Placement × Int)) (k : Nat) :
    keepHas (keepTab ys) (maxStart ys) k = ys.any fun y => y.1.1.chr == k := by
  have hS : ((ys.map winOf).mergeSort winLe).Pairwise (fun a b => winLe a b = true) :=
    List.pairwise_mergeSort (le := winLe) (fun a b c => winLe_trans) (fun a b => by simp [winLe]; omega) _
  have hq := keepTab_query _ hS k (maxStart ys) 0
  have hM := (le_maxStart_go ys 0).2
  unfold keepHas keepTab
  dsimp only at hq
  rw [Bool.eq_iff_iff]
  have h2 : (ys.any fun y => y.1.1.chr == k) = true ↔ ∃ w ∈ (ys.map winOf).mergeSort winLe, w.1 = k ∧
      w.2.1 ≤ maxStart ys ∧ 0 ≤ w.2.2 := by
    rw [List.any_eq_true]
    constructor
    · rintro ⟨y, hy, h⟩
      simp only [beq_iff_eq] at h
      exact ⟨winOf y, List.mem_mergeSort.2 (List.mem_map.2 ⟨y, hy, rfl⟩), h, by simp only [winOf]; exact hM y hy,
        Nat.zero_le _⟩
    · rintro ⟨w, hw, h1, -, -⟩
      rw [List.mem_mergeSort, List.mem_map] at hw
      obtain ⟨y, hy, rfl⟩ := hw
      exact ⟨y, hy, by simp only [winOf] at h1; simp [h1]⟩
  rw [h2, ← hq]
  generalize keepCount (runMax ((List.map winOf ys).mergeSort winLe) none).toArray k (maxStart ys) = i
  simp only [bne_iff_ne, ne_eq, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Nat.zero_le, and_true]

theorem properPairU_near (sl lo hi : Nat) (a b : Placement) (h : properPairU sl lo hi a b = true) :
    a.1.chr = b.1.chr ∧ b.1.start ≤ a.1.start + a.1.len + hi + sl ∧ a.1.start ≤ b.1.start + hi + sl ∧
      a.1.start ≤ b.1.start + b.1.len + hi + sl ∧ b.1.start ≤ a.1.start + hi + sl := by
  rcases a with ⟨⟨ca, sa, la⟩, ta⟩
  rcases b with ⟨⟨cb, sb, lb⟩, tb⟩
  cases ta <;> cases tb <;> simp [properPairU, properPair, fwdRev] at h ⊢ <;> omega

/-! ### `properPairsF` on a window of each group (`properPairsF_eqW`)
A first-mate hit `a` pairs only with second-mate hits starting in `[a.start - (hi + sl), a.start + hi + sl]`
(`properPairU_near`). Each group keeps its order; with the running maximum of its starts from the left and the running
minimum from the right (both monotone), two bisections give the slice outside which no hit starts in the window, and
only the slice is filtered: the same list. -/

def pmGo : List Nat → Nat → List Nat
  | [], _ => []
  | x :: xs, m => max m x :: pmGo xs (max m x)

def smGo : List Nat → List Nat
  | [] => []
  | x :: xs =>
    let r := smGo xs
    (match r with
     | [] => x
     | y :: _ => min x y) :: r

-- a group: its hits in order, the running max of their starts, the running min of their starts from the right
structure GrpW where
  arr : Array (Placement × Int)
  pm : Array Nat
  sm : Array Nat

def grpW (l : List (Placement × Int)) : GrpW :=
  let st := l.map fun x => x.1.1.start
  ⟨l.toArray, (pmGo st 0).toArray, (smGo st).toArray⟩

-- the first `i` in `[lo, hi)` with `f i` (for `f` monotone), else `hi`
def firstGo (f : Nat → Bool) : (fuel lo hi : Nat) → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      if f mid then firstGo f fuel lo mid else firstGo f fuel (mid + 1) hi
    else lo

-- the hits of the group that may start in `[L, U]`, in order
def candWin (g : GrpW) (L U : Nat) : List (Placement × Int) :=
  let n := g.arr.size
  let p := firstGo (fun i => decide (L ≤ g.pm[i]!)) (n + 1) 0 n
  let q := firstGo (fun i => decide (U < g.sm[i]!)) (n + 1) 0 n
  (g.arr.extract p q).toList

def getGW (k : Nat) : List (Nat × GrpW) → GrpW
  | [] => grpW []
  | (k', g) :: r => if k' = k then g else getGW k r

def properPairsW (sl lo hi : Nat) (h1 h2 : List (Placement × Int)) : List PairHit :=
  let G := (grpB h2).map fun (k, l) => (k, grpW l)
  h1.flatMap fun a =>
    ((candWin (getGW (keyA a.1) G) (a.1.1.start - (hi + sl)) (a.1.1.start + hi + sl)).filter
      fun b => properPairU sl lo hi a.1 b.1).map fun b => (a, b)

theorem pmGo_length : ∀ (xs : List Nat) (m : Nat), (pmGo xs m).length = xs.length
  | [], _ => rfl
  | _ :: xs, _ => by simp [pmGo, pmGo_length xs]

theorem smGo_length : ∀ (xs : List Nat), (smGo xs).length = xs.length
  | [] => rfl
  | _ :: xs => by simp [smGo, smGo_length xs]

theorem pmGo_m : ∀ (xs : List Nat) (m i : Nat) (hi : i < xs.length),
    m ≤ (pmGo xs m)[i]'(by rw [pmGo_length]; exact hi)
  | [], _, _, hi => absurd hi (by simp)
  | x :: xs, m, i, hi => by
    cases i with
    | zero => simp only [pmGo, List.getElem_cons_zero]; exact Nat.le_max_left m x
    | succ i =>
      simp only [pmGo, List.getElem_cons_succ]
      exact Nat.le_trans (Nat.le_max_left m x) (pmGo_m xs _ i (by simpa using hi))

-- the running max: at least every earlier element
theorem pmGo_ge : ∀ (xs : List Nat) (m i j : Nat) (hji : j ≤ i) (hi : i < xs.length),
    xs[j]'(by omega) ≤ (pmGo xs m)[i]'(by rw [pmGo_length]; exact hi)
  | [], _, _, _, _, hi => absurd hi (by simp)
  | x :: xs, m, i, j, hji, hi => by
    cases i with
    | zero =>
      have : j = 0 := by omega
      subst this; simp only [pmGo, List.getElem_cons_zero]; exact Nat.le_max_right m x
    | succ i =>
      simp only [pmGo, List.getElem_cons_succ]
      cases j with
      | zero =>
        simp only [List.getElem_cons_zero]
        exact Nat.le_trans (Nat.le_max_right m x) (pmGo_m xs _ i (by simpa using hi))
      | succ j => simp only [List.getElem_cons_succ]; exact pmGo_ge xs _ i j (by omega) (by simpa using hi)

-- the running min from the right: at most every later element
theorem smGo_le : ∀ (xs : List Nat) (i j : Nat) (hij : i ≤ j) (hj : j < xs.length),
    (smGo xs)[i]'(by rw [smGo_length]; omega) ≤ xs[j]
  | [], _, _, _, hj => absurd hj (by simp)
  | x :: xs, i, j, hij, hj => by
    have head_le : ∀ (ys : List Nat) (j : Nat) (hj : j < ys.length) (h0 : 0 < (smGo ys).length),
        (smGo ys)[0] ≤ ys[j] := by
      intro ys
      induction ys with
      | nil => intro j hj; exact absurd hj (by simp)
      | cons y ys ih =>
        intro j hj _
        simp only [smGo, List.getElem_cons_zero]
        cases j with
        | zero =>
          simp only [List.getElem_cons_zero]
          split <;> omega
        | succ j =>
          simp only [List.getElem_cons_succ]
          have hl : 0 < (smGo ys).length := by rw [smGo_length]; simp at hj; omega
          have := ih j (by simpa using hj) hl
          split
          · rename_i h; rw [h] at hl; simp at hl
          · rename_i z r h
            have : (smGo ys)[0] = z := by simp [h]
            omega
    cases i with
    | zero =>
      have := head_le (x :: xs) j hj (by rw [smGo_length]; simp)
      exact this
    | succ i =>
      simp only [smGo, List.getElem_cons_succ]
      cases j with
      | zero => omega
      | succ j => simp only [List.getElem_cons_succ]; exact smGo_le xs i j (by omega) (by simpa using hj)

theorem pmGo_mono : ∀ (xs : List Nat) (m i j : Nat) (hij : i ≤ j) (hj : j < xs.length),
    (pmGo xs m)[i]'(by rw [pmGo_length]; omega) ≤ (pmGo xs m)[j]'(by rw [pmGo_length]; exact hj)
  | [], _, _, _, _, hj => absurd hj (by simp)
  | x :: xs, m, i, j, hij, hj => by
    cases j with
    | zero =>
      have : i = 0 := by omega
      subst this; exact Nat.le_refl _
    | succ j =>
      cases i with
      | zero =>
        simp only [pmGo, List.getElem_cons_zero, List.getElem_cons_succ]
        exact pmGo_m xs _ j (by simpa using hj)
      | succ i =>
        simp only [pmGo, List.getElem_cons_succ]
        exact pmGo_mono xs _ i j (by omega) (by simpa using hj)

theorem smHead_le (x : Nat) : ∀ r : List Nat, (match r with
    | [] => x
    | y :: _ => min x y) ≤ r.headD x
  | [] => Nat.le_refl _
  | y :: _ => Nat.min_le_right x y

theorem smGo_mono : ∀ (xs : List Nat) (i j : Nat) (hij : i ≤ j) (hj : j < xs.length),
    (smGo xs)[i]'(by rw [smGo_length]; omega) ≤ (smGo xs)[j]'(by rw [smGo_length]; exact hj)
  | [], _, _, _, hj => absurd hj (by simp)
  | x :: xs, i, j, hij, hj => by
    cases j with
    | zero =>
      have : i = 0 := by omega
      subst this; exact Nat.le_refl _
    | succ j =>
      have hl : 0 < (smGo xs).length := by rw [smGo_length]; simp at hj; omega
      cases i with
      | zero =>
        simp only [smGo, List.getElem_cons_zero, List.getElem_cons_succ]
        have h0 := smGo_mono xs 0 j (by omega) (by simpa using hj)
        have e : (smGo xs).headD x = (smGo xs)[0] := by
          rw [List.headD_eq_head?_getD, List.head?_eq_getElem?, List.getElem?_eq_getElem hl]; rfl
        exact Nat.le_trans (smHead_le x (smGo xs)) (e ▸ h0)
      | succ i =>
        simp only [smGo, List.getElem_cons_succ]
        exact smGo_mono xs i j (by omega) (by simpa using hj)

theorem firstGo_spec (f : Nat → Bool) (n : Nat) (hm : ∀ i j, i ≤ j → j < n → f i = true → f j = true) :
    ∀ fuel lo hi, lo ≤ hi → hi ≤ n → hi - lo < fuel → (∀ i, i < lo → f i = false) →
      (∀ i, hi ≤ i → i < n → f i = true) →
      (∀ i, i < firstGo f fuel lo hi → f i = false) ∧ (∀ i, firstGo f fuel lo hi ≤ i → i < n → f i = true)
  | 0, lo, hi, _, _, hf, _, _ => by omega
  | fuel + 1, lo, hi, hlh, hn, hf, hl, hh => by
    unfold firstGo
    by_cases hlt : lo < hi
    · simp only [hlt, ite_true]
      split
      · rename_i hmid
        exact firstGo_spec f n hm fuel lo ((lo + hi) / 2) (by omega) (by omega) (by omega) hl
          (fun i h1 h2 => hm _ i h1 h2 hmid)
      · rename_i hmid
        have hmid' : f ((lo + hi) / 2) = false := by simpa using hmid
        refine firstGo_spec f n hm fuel ((lo + hi) / 2 + 1) hi (by omega) hn (by omega) ?_ hh
        intro i hi'
        by_cases h : i < lo
        · exact hl i h
        · cases hfi : f i
          · rfl
          · have := hm i ((lo + hi) / 2) (by omega) (by omega) hfi
            rw [hmid'] at this; exact absurd this (by simp)
    · simp only [hlt, ite_false]
      exact ⟨hl, fun i h1 h2 => hh i (by omega) h2⟩

theorem filter_slice {α : Type} (P : α → Bool) (l : List α) (p q : Nat)
    (h1 : ∀ i (h : i < l.length), i < p → P l[i] = false)
    (h2 : ∀ i (h : i < l.length), q ≤ i → P l[i] = false) :
    l.filter P = ((l.drop p).take (q - p)).filter P := by
  conv => lhs; rw [← List.take_append_drop p l]
  rw [List.filter_append]
  have e1 : (l.take p).filter P = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    rw [List.getElem_take]
    simp only [List.length_take] at hi
    simpa using h1 i (by omega) (by omega)
  rw [e1, List.nil_append]
  conv => lhs; rw [← List.take_append_drop (q - p) (l.drop p)]
  rw [List.filter_append]
  have e2 : ((l.drop p).drop (q - p)).filter P = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    rw [List.getElem_drop, List.getElem_drop]
    simp only [List.length_drop] at hi
    simpa using h2 (p + (q - p + i)) (by omega) (by omega)
  rw [e2, List.append_nil]

theorem candWin_filter (l : List (Placement × Int)) (L U : Nat) (P : Placement × Int → Bool)
    (hP : ∀ b ∈ l, P b = true → L ≤ b.1.1.start ∧ b.1.1.start ≤ U) :
    (candWin (grpW l) L U).filter P = l.filter P := by
  unfold candWin grpW
  simp only [List.size_toArray]
  generalize hst : l.map (fun x => x.1.1.start) = st
  have hlen : st.length = l.length := by rw [← hst, List.length_map]
  have hpl : (pmGo st 0).length = l.length := by rw [pmGo_length, hlen]
  have hsl : (smGo st).length = l.length := by rw [smGo_length, hlen]
  have hpm : ∀ i (h : i < l.length), (pmGo st 0).toArray[i]! = (pmGo st 0)[i]'(by omega) := by
    intro i h; simp [show i < (pmGo st 0).length by omega]
  have hsm : ∀ i (h : i < l.length), (smGo st).toArray[i]! = (smGo st)[i]'(by omega) := by
    intro i h; simp [show i < (smGo st).length by omega]
  have hstI : ∀ i (h : i < l.length), st[i]'(by omega) = l[i].1.1.start := by
    intro i h; subst hst; simp
  have m1 : ∀ i j, i ≤ j → j < l.length → decide (L ≤ (pmGo st 0).toArray[i]!) = true →
      decide (L ≤ (pmGo st 0).toArray[j]!) = true := by
    intro i j hij hj h
    simp only [decide_eq_true_eq] at h ⊢
    rw [hpm i (by omega)] at h; rw [hpm j hj]
    exact Nat.le_trans h (pmGo_mono st 0 i j hij (by omega))
  have m2 : ∀ i j, i ≤ j → j < l.length → decide (U < (smGo st).toArray[i]!) = true →
      decide (U < (smGo st).toArray[j]!) = true := by
    intro i j hij hj h
    simp only [decide_eq_true_eq] at h ⊢
    rw [hsm i (by omega)] at h; rw [hsm j hj]
    exact Nat.lt_of_lt_of_le h (smGo_mono st i j hij (by omega))
  obtain ⟨p1, -⟩ := firstGo_spec _ l.length m1 (l.length + 1) 0 l.length (Nat.zero_le _) (Nat.le_refl _) (by omega)
    (fun i h => absurd h (Nat.not_lt_zero _)) (fun i h1 h2 => by omega)
  obtain ⟨-, q2⟩ := firstGo_spec _ l.length m2 (l.length + 1) 0 l.length (Nat.zero_le _) (Nat.le_refl _) (by omega)
    (fun i h => absurd h (Nat.not_lt_zero _)) (fun i h1 h2 => by omega)
  rw [Array.toList_extract]
  simp only [List.extract]
  symm
  apply filter_slice
  · intro i h hp
    have := p1 i hp
    simp only [decide_eq_false_iff_not, Nat.not_le] at this
    rw [hpm i h] at this
    have hge := pmGo_ge st 0 i i (Nat.le_refl _) (by omega)
    rw [hstI i h] at hge
    cases hb : P l[i]
    · rfl
    · have := hP l[i] (List.getElem_mem h) hb; omega
  · intro i h hq
    have := q2 i hq h
    simp only [decide_eq_true_eq] at this
    rw [hsm i h] at this
    have hle := smGo_le st i i (Nat.le_refl _) (by omega)
    rw [hstI i h] at hle
    cases hb : P l[i]
    · rfl
    · have := hP l[i] (List.getElem_mem h) hb; omega

theorem getGW_map (k : Nat) : ∀ G : List (Nat × List (Placement × Int)),
    getGW k (G.map fun (k, l) => (k, grpW l)) = grpW (getG k G)
  | [] => rfl
  | (k', l) :: r => by
    simp only [List.map_cons, getGW, getG]
    split
    · rfl
    · exact getGW_map k r

@[csimp] theorem properPairsF_eqW : @properPairsF = @properPairsW := by
  funext sl lo hi h1 h2
  unfold properPairsF properPairsW
  simp only [getGW_map]
  congr 1
  funext a
  congr 1
  rw [candWin_filter]
  intro b _ hb
  obtain ⟨-, -, e3, -, e5⟩ := properPairU_near sl lo hi a.1 b.1 hb
  constructor <;> omega

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

/-! ### Compiled `hitsKPFN`: chromosomes without a hit of the other mate are skipped (`hitsKPFN_eqG`) -/

/-- `hitsSKN`, a chromosome searched only when `gate` holds on it. -/
def hitsSKNG {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G : ByteArray) (offs : Array Nat)
    (pgs2 : Array PGen) (n t lim : Nat) (Rs : ByteArray) (keep : Nat → Nat → Nat → Bool) (gate : Nat → Bool) :
    List (Window × Nat) :=
  if !(List.range n).any gate then [] else
  let m := Rs.size / 25
  let Ls := Rs.size / m
  let K := packRP Rs
  let ps := prepG ix Rs m Ls
  let J := (ordG (ps.map (LookG.size ix)) m).take (sbound lim + 1)
  let lk := J.map fun j => (j, LookG.look ix G Rs (j * Ls) (Rs.size - j * Ls) ps[j]!)
  let us := unseen m J
  (List.range n).flatMap fun c =>
    if gate c then
      hitsCKN K Rs pgs2 (t + c) lim (slicesAt lk Rs.size Ls offs[c]! (GRead.size pgs2[t + c]!)) us Ls
        (keep (t + c) Rs.size)
    else []

theorem hitsCKN_none (K : RP) (R : ByteArray) (pgs2 : Array PGen) (c lim : Nat) (acc : List (Array Nat))
    (us : List Nat) (Ls : Nat) (sel : Nat → Bool) (h : ∀ D, sel D = false) :
    hitsCKN K R pgs2 c lim acc us Ls sel = [] := by
  unfold hitsCKN
  simp [h]

theorem hitsSKNG_eq {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G : ByteArray) (offs : Array Nat)
    (pgs2 : Array PGen) (n t lim : Nat) (Rs : ByteArray) (keep : Nat → Nat → Nat → Bool) (gate : Nat → Bool)
    (h : ∀ c D, c < n → gate c = false → keep (t + c) Rs.size D = false) :
    hitsSKNG ix G offs pgs2 n t lim Rs keep gate = hitsSKN ix G offs pgs2 n t lim Rs keep := by
  unfold hitsSKNG hitsSKN
  split
  · rename_i hn
    simp only [Bool.not_eq_true', List.any_eq_false, List.mem_range] at hn
    simp only []
    symm
    rw [List.flatMap_eq_nil_iff]
    intro c hc
    rw [List.mem_range] at hc
    exact hitsCKN_none _ _ _ _ _ _ _ _ _ (fun D => h c D hc (by simpa using hn c hc))
  simp only []
  rw [List.flatMap_def, List.flatMap_def]
  congr 1
  apply List.map_congr_left
  intro c hc
  rw [List.mem_range] at hc
  cases hg : gate c
  · rw [hitsCKN_none _ _ _ _ _ _ _ _ _ (fun D => h c D hc hg)]; rfl
  · rfl

def hitsAtKPNG {L Pp : Type} [LookG L Pp] [Inhabited Pp] (lim : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (pgs : Array PGen) (R : ByteArray) (keep : Nat → Nat → Nat → Bool) (gate : Nat → Bool) :
    Option (List (Placement × Int)) :=
  if fastT lim R then
    let n := pgs.size
    let pgs2 := pgs ++ pgs
    some ((hitsSKNG ix G offs pgs2 n 0 lim R keep gate ++
      hitsSKNG ix G offs pgs2 n n lim (revCompK R) keep gate).map fun x => (decB n x.1, -(x.2 : Int)))
  else none

/-- Compiled `hitsKPFN`: a chromosome is searched only when the other mate has a hit on it, and the
diagonal filter is a binary search on a table built once (`keepQ_eq`). -/
def hitsKPFNG {L Pp : Type} [LookG L Pp] [Inhabited Pp] (sl hi : Nat) (ix : L) (G : ByteArray) (offs : Array Nat)
    (pgs : Array PGen) (R : ByteArray) (c : Nat) (ys : List (Placement × Int)) : List (Placement × Int) :=
  let t := keepTab ys
  let M := maxStart ys
  match hitsAtKPNG c ix G offs pgs R (keepQ (hi + sl + gapBound sc0 (-(c : Int))) pgs.size t) (keepHas t M) with
  | some l => l
  | none => hitsKPF ix G offs pgs R c

theorem keepN_gate (sl hi n gb : Nat) (ys : List (Placement × Int)) (t c nR D : Nat) (ht : t = 0 ∨ t = n)
    (hc : c < n) (hg : (ys.any fun y => y.1.1.chr == c) = false) : keepN sl hi n gb ys (t + c) nR D = false := by
  have hv : (if t + c < n then t + c else t + c - n) = c := by
    rcases ht with h0 | hn
    · rw [h0, if_pos (by omega)]; omega
    · rw [hn, if_neg (by omega)]; omega
  unfold keepN
  rw [hv]
  rw [List.any_eq_false] at hg ⊢
  intro y hy h'
  simp only [Bool.and_eq_true] at h'
  exact hg y hy h'.1.1

@[csimp] theorem hitsKPFN_eqG : @hitsKPFN = @hitsKPFNG := by
  funext L Pp i1 i2 sl hi ix G offs pgs R c ys
  have e0 := hitsSKNG_eq ix G offs (pgs ++ pgs) pgs.size 0 c R (keepN sl hi pgs.size (gapBound sc0 (-(c : Int))) ys)
    (fun k => ys.any fun y => y.1.1.chr == k)
    (fun c' D hc hg => keepN_gate sl hi _ _ ys 0 c' _ D (Or.inl rfl) hc hg)
  have e1 := hitsSKNG_eq ix G offs (pgs ++ pgs) pgs.size pgs.size c (revCompK R)
    (keepN sl hi pgs.size (gapBound sc0 (-(c : Int))) ys) (fun k => ys.any fun y => y.1.1.chr == k)
    (fun c' D hc hg => keepN_gate sl hi _ _ ys _ c' _ D (Or.inr rfl) hc hg)
  have hq : keepQ (hi + sl + gapBound sc0 (-(c : Int))) pgs.size (keepTab ys) =
      keepN sl hi pgs.size (gapBound sc0 (-(c : Int))) ys :=
    funext fun vc => funext fun nR => funext fun D => keepQ_eq sl hi _ _ ys vc nR D
  have hg : keepHas (keepTab ys) (maxStart ys) = fun k => ys.any fun y => y.1.1.chr == k :=
    funext fun k => keepHas_eq ys k
  unfold hitsKPFN hitsKPFNG hitsAtKPNG hitsAtKPN
  simp only [hg]
  rw [hq]
  simp only [e0, e1]

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
#print axioms MapSpec.Fast.keepQ_eq
#print axioms MapSpec.Fast.hitsKPFN_eqG
#print axioms MapSpec.Fast.pairUKHN_mz_eq
#print axioms MapSpec.Fast.pairUKHN_tie
#print axioms MapSpec.Fast.properPairsF_eqW
