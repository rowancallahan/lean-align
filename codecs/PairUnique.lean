import PairConcat

/-!
# Codec `pairFastU`: pair-level uniqueness (DRAFT spec `pairSpecU`)

Against `pairSpecU` (spec/PairSpec.lean): among all proper pairs of hits, the
unique best by summed score.  One index over the concatenated genome, as
`pairFastC` (codecs/PairConcat.lean).

1. Both mates through the proved per-mate search (`mapChromsC`).  A mate with
   no hit at all (`pen > 12`): no pair (`none`).
2. Both mates unique and the two form a proper pair: that pair is the unique
   best pair (any other pair moves a mate to a strictly worse hit), so the
   answer is `pairFastC`'s.
3. Otherwise (a per-mate tie, or unique bests that are not a proper pair): the
   exact fallback.  All 4 seeds of each mate are looked up on both strands; every
   anchor diagonal gives 14 candidate windows (same length, and one gap of 1–3
   starting or ending on the diagonal), each scored exactly (`penF = penB`).  By
   the pigeonhole lemmas (`same_hit_mask`, `gap_support`) every hit has a clean
   seed on one of its diagonals, so the list is all hits with their penalties
   (`mem_hitsU`).  The best proper pair is then picked in one pass (`selU`).

    … → pairFastU lk lo hi ix G offs gbs R1 R2 = pairSpecU sc0 (-12) lo hi g m1 m2   (pairFastU_eq_pairSpecU)
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-! ## Algorithm -/

/-- Penalty of window `(st, len)` if `≤ lim ≤ 12` (exact there, `penFL_eq`); the fast
form of `penB`. -/
def penFL (R G : ByteArray) (st len lim : Nat) : Nat :=
  if st + len ≤ G.size then
    if len = R.size then 4 * hamSeeds R G st 0 (min 3 (lim / 4))
    else if gapLen R.size len ≤ 3 then gappedPen2 R G st len lim else 13
  else 13

/-- Windows `(st, len)` with a seed on anchor diagonal `A` (read length `n`): same
length, or one gap of 1–3 with the diagonal at the start or at the end. -/
def candW (n A : Nat) : List (Nat × Nat) :=
  (List.range 7).flatMap fun i => [(A - BIAS, n + i - 3), (A + 3 - i - BIAS, n + i - 3)]

/-- The candidates that can cost `≤ lim` (a gap costs `≥ 8`). -/
def candL (n A lim : Nat) : List (Nat × Nat) := if lim < 8 then [(A - BIAS, n)] else candW n A

/-- Merge (two increasing lists, equal entries kept once), onto `acc` reversed. -/
def mergeU : List Nat → List Nat → List Nat → List Nat
  | [], ys, acc => acc.reverseAux ys
  | xs, [], acc => acc.reverseAux xs
  | x :: xs, y :: ys, acc =>
    if x < y then mergeU xs (y :: ys) (x :: acc)
    else if y < x then mergeU (x :: xs) ys (y :: acc)
    else mergeU xs ys (x :: acc)
termination_by xs ys => xs.length + ys.length

/-- Placements of read `R'` (tagged with strand `s`) of penalty `≤ lim`, found from
the anchors of the seeds `js`, with their penalties (all of them when
`lim < 4·|js|`, `mem_hitsStrand`). -/
def hitsStrand {L P : Type} (lk : Look L P) (ix : L) (G : ByteArray) (offs : Array Nat)
    (gbs : Array ByteArray) (R' : ByteArray) (s : Strand) (js : List Nat) (lim : Nat) : List (Placement × Nat) :=
  let as := js.map fun j => (j, lk.look ix G R' j (lk.prep ix (seedHash R' j)))
  (List.range gbs.size).flatMap fun c =>
    let ds := as.foldl (fun acc ja =>
      mergeU acc ((sliceA ja.2 ja.1 offs[c]! gbs[c]!.size).toList.map (· / 16)) []) []
    ds.flatMap fun d => (candL R'.size d lim).filterMap fun w =>
      let k := penFL R' gbs[c]! w.1 w.2 lim
      if k ≤ lim then some ((⟨c, w.1, w.2⟩, s), k) else none

/-- Every placement of penalty `≤ lim ≤ 12`, both strands, with its penalty: the
`lim / 4 + 1` seeds with the smallest buckets on each strand suffice. -/
def hitsL {L P : Type} [Inhabited P] (lk : Look L P) (ix : L) (G : ByteArray) (offs : Array Nat)
    (gbs : Array ByteArray) (R : ByteArray) (lim : Nat) : List (Placement × Nat) :=
  let Rr := revCompB R
  hitsStrand lk ix G offs gbs R .fwd ((seedOrder lk ix (prepAll lk ix (seedHashes R))).take (lim / 4 + 1)) lim ++
    hitsStrand lk ix G offs gbs Rr .rev ((seedOrder lk ix (prepAll lk ix (seedHashes Rr))).take (lim / 4 + 1)) lim

/-- Keep the better of the best so far and `x` (`amb`: another key ties the best). -/
def addSel {β κ : Type} [DecidableEq κ] (key : β → κ) (sc : β → Int) (r : Option (β × Bool)) (x : β) :
    Option (β × Bool) :=
  match r with
  | none => some (x, false)
  | some (y, amb) =>
    if sc y < sc x then some (x, false)
    else if sc x = sc y ∧ key x ≠ key y then some (y, true) else some (y, amb)

/-- The element whose score beats every element with another key (one pass). -/
def selU {β κ : Type} [DecidableEq κ] (key : β → κ) (sc : β → Int) (l : List β) : Option β :=
  match l.foldl (addSel key sc) none with
  | some (y, false) => some y
  | _ => none

/-- Proper pairs of `h1 × h2`. -/
def pairsOf (lo hi : Nat) (h1 h2 : List (Placement × Int)) : List ((Placement × Int) × (Placement × Int)) :=
  h1.flatMap fun a => (h2.filter fun b => properPair lo hi a.1 b.1).map fun b => (a, b)

/-- The best of a list of pairs, in one pass. -/
def selPairs (ps : List ((Placement × Int) × (Placement × Int))) : Option ((Placement × Int) × (Placement × Int)) :=
  selU (fun p : (Placement × Int) × (Placement × Int) => (p.1.1, p.2.1)) (fun p => p.1.2 + p.2.2) ps

/-- `bestPair` in one pass. -/
def bestPairF (lo hi : Nat) (h1 h2 : List (Placement × Int)) : Option ((Placement × Int) × (Placement × Int)) :=
  selPairs (pairsOf lo hi h1 h2)

/-- Penalties → scores. -/
def toScore (h : List (Placement × Nat)) : List (Placement × Int) := h.map fun x => (x.1, -(x.2 : Int))

/-- `ilC` (codecs/PairConcat.lean), also returning the two strands' final states. -/
@[specialize] def ilCS {L P : Type} [Inhabited P] (lk : Look L P) (ix : L) (G : ByteArray)
    (gbs : Array ByteArray) (offs : Array Nat) (R1 R2 : ByteArray) (c1 c2 : Nat) (ps1 ps2 : Array P) :
    Nat → CS → CS → Best → Best × CS × CS
  | 0, s1, s2, b => (b, s1, s2)
  | f + 1, s1, s2, b =>
    let l2 := s2.live b
    if s1.live b && (!l2 || s1.k < s2.k || (s1.k == s2.k && s1.next lk ix ps1 ≤ s2.next lk ix ps2)) then
      let r := s1.adv lk ix G R1 gbs offs c1 ps1 b
      ilCS lk ix G gbs offs R1 R2 c1 c2 ps1 ps2 f r.1 s2 r.2
    else if l2 then
      let r := s2.adv lk ix G R2 gbs offs c2 ps2 b
      ilCS lk ix G gbs offs R1 R2 c1 c2 ps1 ps2 f s1 r.1 r.2
    else (b, s1, s2)

/-- `mapChromsC` with the final states of the forward and the reverse strand. -/
@[specialize] def mapChromsCS {L P : Type} [Inhabited P] (lk : Look L P) (ix : L) (G : ByteArray)
    (offs : Array Nat) (gbs : Array ByteArray) (R : ByteArray) (rf : Bool) : Best × CS × CS :=
  let n := gbs.size
  let Rr := revCompB R
  let ps := prepAll lk ix (seedHashes R)
  let pr := prepAll lk ix (seedHashes Rr)
  if rf then
    let r := ilCS lk ix G gbs offs Rr R n 0 pr ps 8 (CS.init lk ix pr n) (CS.init lk ix ps n) {}
    (r.1, r.2.2, r.2.1)
  else ilCS lk ix G gbs offs R Rr 0 n ps pr 8 (CS.init lk ix ps n) (CS.init lk ix pr n) {}

/-- Some entry of `ys` (increasing) has its diagonal within `W` of `d`. -/
@[inline] def nearA (ys : Array Nat) (d W : Nat) : Bool :=
  let i := lbA ys (16 * (d - W)) 0 ys.size
  decide (i < ys.size) && decide (ys[i]! / 16 ≤ d + W)

/-- Placements of read `R'` (strand `s`) of penalty `≤ lim` from the anchors a
search left in state `st`, scoring only the anchors with an anchor of the other
mate's opposite strand (state `o`) within `W` diagonals: only those can be in a
proper pair (all of these when `lim < 4·lookups`, `hitsCSF_complete`). -/
def hitsCSF (gbs : Array ByteArray) (R' : ByteArray) (s : Strand) (st o : CS) (W lim : Nat) :
    List (Placement × Nat) :=
  (List.range gbs.size).flatMap fun c =>
    let ys := o.as[c]!
    st.as[c]!.toList.flatMap fun e =>
      if nearA ys (e / 16) W then
        (candL R'.size (e / 16) lim).filterMap fun w =>
          let k := penFL R' gbs[c]! w.1 w.2 lim
          if k ≤ lim then some ((⟨c, w.1, w.2⟩, s), k) else none
      else []

/-- A mate's placements at its best penalty that can pair with the other mate's
(search results `r`, `o`; forward pairs with reverse). -/
def hitsBest (gbs : Array ByteArray) (W : Nat) (R : ByteArray) (r o : Best × CS × CS) : List (Placement × Int) :=
  toScore (hitsCSF gbs R .fwd r.2.1 o.2.2 W r.1.pen ++ hitsCSF gbs (revCompB R) .rev r.2.2 o.2.1 W r.1.pen)

/-- The exact fallback, given each mate's search result `r1`, `r2` (best penalty
`l1`, `l2`).  First only the placements at those penalties, from the anchors the
searches already hold: every pair sums to at least `l1 + l2`, so if any of them
pair properly, the best pair is among them.  Otherwise every placement within
the cap (all seeds looked up). -/
def pairSlowU {L P : Type} [Inhabited P] (lk : Look L P) (lo hi : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (gbs : Array ByteArray) (R1 R2 : ByteArray) (r1 r2 : Best × CS × CS) :
    Option ((Placement × Int) × (Placement × Int)) :=
  let ps := pairsOf lo hi (hitsBest gbs (hi + 128) R1 r1 r2) (hitsBest gbs (hi + 128) R2 r2 r1)
  if ps.isEmpty then
    bestPairF lo hi (toScore (hitsL lk ix G offs gbs R1 12)) (toScore (hitsL lk ix G offs gbs R2 12))
  else selPairs ps

def pairFastU {L P : Type} [Inhabited P] (lk : Look L P) (lo hi : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (gbs : Array ByteArray) (R1 R2 : ByteArray) :
    Option ((Placement × Int) × (Placement × Int)) :=
  let r1 := mapChromsCS lk ix G offs gbs R1 false
  if 12 < r1.1.pen then none else
  -- mate 2 of a proper pair is on the other strand: it takes ties
  let r2 := mapChromsCS lk ix G offs gbs R2 (decide (r1.1.chr < gbs.size))
  if 12 < r2.1.pen then none else
  match decodeJ gbs.size r1.1, decodeJ gbs.size r2.1 with
  | some a, some b =>
    if properPair lo hi a.1 b.1 then some (a, b) else pairSlowU lk lo hi ix G offs gbs R1 R2 r1 r2
  | _, _ => pairSlowU lk lo hi ix G offs gbs R1 R2 r1 r2

/-! ## Selection -/

section sel

variable {β κ : Type} [DecidableEq κ] (key : β → κ) (sc : β → Int)

/-- What the running selection holds after the elements `seen`. -/
def SelInv (seen : List β) : Option (β × Bool) → Prop
  | none => seen = []
  | some (y, amb) => y ∈ seen ∧ (∀ x ∈ seen, sc x ≤ sc y) ∧
      (amb = true ↔ ∃ x ∈ seen, sc x = sc y ∧ key x ≠ key y)

theorem selInv_add (seen : List β) (r : Option (β × Bool)) (h : SelInv key sc seen r) (x : β) :
    SelInv key sc (seen ++ [x]) (addSel key sc r x) := by
  match r, h with
  | none, h =>
    subst h
    simp only [addSel, SelInv, List.nil_append, List.mem_singleton, forall_eq, Int.le_refl, true_and]
    simp
  | some (y, amb), ⟨hy, hle, ha⟩ =>
    unfold addSel
    simp only []
    by_cases h1 : sc y < sc x
    · rw [if_pos h1]
      refine ⟨by simp, fun z hz => ?_, ?_⟩
      · rcases List.mem_append.mp hz with hz | hz
        · have := hle z hz; omega
        · simp at hz; subst hz; exact Int.le_refl _
      · simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
        intro z hz e
        rcases List.mem_append.mp hz with hz | hz
        · have := hle z hz; omega
        · simp at hz; subst hz; intro hk; exact hk rfl
    · rw [if_neg h1]
      by_cases h2 : sc x = sc y ∧ key x ≠ key y
      · rw [if_pos h2]
        refine ⟨List.mem_append_left _ hy, fun z hz => ?_, ?_⟩
        · rcases List.mem_append.mp hz with hz | hz
          · exact hle z hz
          · simp at hz; subst hz; omega
        · simp only [true_iff]; exact ⟨x, by simp, h2⟩
      · rw [if_neg h2]
        refine ⟨List.mem_append_left _ hy, fun z hz => ?_, ?_⟩
        · rcases List.mem_append.mp hz with hz | hz
          · exact hle z hz
          · simp at hz; subst hz; omega
        · rw [ha]
          constructor
          · rintro ⟨z, hz, e⟩; exact ⟨z, List.mem_append_left _ hz, e⟩
          · rintro ⟨z, hz, e⟩
            rcases List.mem_append.mp hz with hz | hz
            · exact ⟨z, hz, e⟩
            · simp at hz; subst hz; exact absurd e h2

theorem selInv_foldl : ∀ (l seen : List β) (r : Option (β × Bool)), SelInv key sc seen r →
    SelInv key sc (seen ++ l) (l.foldl (addSel key sc) r) := by
  intro l
  induction l with
  | nil => intro seen r h; simpa using h
  | cons x l ih =>
    intro seen r h
    have := ih (seen ++ [x]) _ (selInv_add key sc seen r h x)
    simpa using this

theorem selU_iff (l : List β) (hfun : ∀ x ∈ l, ∀ y ∈ l, key x = key y → x = y) (y : β) :
    selU key sc l = some y ↔ y ∈ l ∧ ∀ x ∈ l, sc x < sc y ∨ key x = key y := by
  have hI := selInv_foldl key sc l [] none rfl
  simp only [List.nil_append] at hI
  unfold selU
  constructor
  · intro h
    split at h
    · next z hz =>
      rw [hz] at hI
      obtain ⟨hm, hle, ha⟩ := hI
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨hm, fun x hx => ?_⟩
      by_cases e : key x = key z
      · exact Or.inr e
      · have := hle x hx
        rcases Nat.lt_or_ge 0 1 with _ | _ <;>
        · by_cases e2 : sc x = sc z
          · exact absurd (ha.mpr ⟨x, hx, e2, e⟩) (by simp)
          · left; omega
    · simp at h
  · rintro ⟨hy, hall⟩
    cases hr : l.foldl (addSel key sc) none with
    | none => rw [hr] at hI; simp [SelInv] at hI; subst hI; simp at hy
    | some r =>
      obtain ⟨z, amb⟩ := r
      rw [hr] at hI
      obtain ⟨hz, hle, ha⟩ := hI
      have hzy : z = y := by
        rcases hall z hz with h | h
        · have := hle y hy; omega
        · exact hfun z hz y hy h
      subst hzy
      cases amb with
      | false => rfl
      | true =>
        obtain ⟨x, hx, e1, e2⟩ := ha.mp rfl
        rcases hall x hx with h | h
        · omega
        · exact absurd h e2

/-- The `find?` form (as in `bestPair`) has the same characterization. -/
theorem findU_iff (same : β → β → Bool) (l : List β) (hfun : ∀ x ∈ l, ∀ y ∈ l, same x y = true → x = y)
    (y : β) :
    l.find? (fun p => l.all fun p' => decide (sc p' < sc p) || same p' p) = some y ↔
      y ∈ l ∧ ∀ x ∈ l, sc x < sc y ∨ same x y = true := by
  have hq : ∀ a : β, (l.all fun b => decide (sc b < sc a) || same b a) = true ↔
      ∀ b ∈ l, sc b < sc a ∨ same b a = true := by
    intro a; simp [List.all_eq_true]
  constructor
  · intro h
    have h' := List.find?_some h
    exact ⟨List.mem_of_find?_eq_some h, (hq y).1 h'⟩
  · rintro ⟨hm, hp⟩
    cases h : l.find? (fun a => l.all fun b => decide (sc b < sc a) || same b a) with
    | none => exact absurd ((hq y).2 hp) (by simpa using List.find?_eq_none.1 h y hm)
    | some c =>
      have h' := List.find?_some h
      have hc := (hq c).1 h'
      have hcm := List.mem_of_find?_eq_some h
      rcases hp c hcm with h1 | h1
      · rcases hc y hm with h2 | h2
        · omega
        · rw [hfun y hm c hcm h2]
      · rw [hfun c hcm y hm h1]

end sel

theorem mem_pairsOf (lo hi : Nat) (h1 h2 : List (Placement × Int)) (p : (Placement × Int) × (Placement × Int)) :
    p ∈ pairsOf lo hi h1 h2 ↔ p.1 ∈ h1 ∧ p.2 ∈ h2 ∧ properPair lo hi p.1.1 p.2.1 = true := by
  obtain ⟨a, b⟩ := p
  unfold pairsOf
  simp only [List.mem_flatMap, List.mem_map, List.mem_filter, Prod.mk.injEq]
  constructor
  · rintro ⟨a', ha, b', ⟨hb, hp⟩, rfl, rfl⟩; exact ⟨ha, hb, hp⟩
  · rintro ⟨ha, hb, hp⟩; exact ⟨a, ha, b, ⟨hb, hp⟩, rfl, rfl⟩

/-- A list of hits where a placement determines its score. -/
def Fun (h : List (Placement × Int)) : Prop := ∀ x ∈ h, ∀ y ∈ h, x.1 = y.1 → x.2 = y.2

/-- The best proper pair, characterized. -/
theorem bestPair_iff (lo hi : Nat) (h1 h2 : List (Placement × Int)) (f1 : Fun h1) (f2 : Fun h2)
    (p : (Placement × Int) × (Placement × Int)) :
    bestPair lo hi h1 h2 = some p ↔ p ∈ pairsOf lo hi h1 h2 ∧ ∀ x ∈ pairsOf lo hi h1 h2,
      x.1.2 + x.2.2 < p.1.2 + p.2.2 ∨ (x.1.1 = p.1.1 ∧ x.2.1 = p.2.1) := by
  have := findU_iff (fun p : (Placement × Int) × (Placement × Int) => p.1.2 + p.2.2)
    (fun p' p => decide (p'.1.1 = p.1.1 ∧ p'.2.1 = p.2.1)) (pairsOf lo hi h1 h2) (by
      rintro ⟨⟨a, sa⟩, ⟨b, sb⟩⟩ hx ⟨⟨a', sa'⟩, ⟨b', sb'⟩⟩ hy he
      simp only [decide_eq_true_eq] at he
      obtain ⟨rfl, rfl⟩ := he
      rw [mem_pairsOf] at hx hy
      have e1 : sa = sa' := f1 _ hx.1 _ hy.1 rfl
      have e2 : sb = sb' := f2 _ hx.2.1 _ hy.2.1 rfl
      rw [e1, e2]) p
  simp only [decide_eq_true_eq] at this
  exact this

theorem bestPairF_iff (lo hi : Nat) (h1 h2 : List (Placement × Int)) (f1 : Fun h1) (f2 : Fun h2)
    (p : (Placement × Int) × (Placement × Int)) :
    bestPairF lo hi h1 h2 = some p ↔ p ∈ pairsOf lo hi h1 h2 ∧ ∀ x ∈ pairsOf lo hi h1 h2,
      x.1.2 + x.2.2 < p.1.2 + p.2.2 ∨ (x.1.1 = p.1.1 ∧ x.2.1 = p.2.1) := by
  have := selU_iff (fun p : (Placement × Int) × (Placement × Int) => (p.1.1, p.2.1))
    (fun p => p.1.2 + p.2.2) (pairsOf lo hi h1 h2) (by
      rintro ⟨⟨a, sa⟩, ⟨b, sb⟩⟩ hx ⟨⟨a', sa'⟩, ⟨b', sb'⟩⟩ hy he
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rw [mem_pairsOf] at hx hy
      have e1 : sa = sa' := f1 _ hx.1 _ hy.1 rfl
      have e2 : sb = sb' := f2 _ hx.2.1 _ hy.2.1 rfl
      rw [e1, e2]) p
  simp only [Prod.mk.injEq] at this
  exact this

/-- `bestPairF` on lists with the same members as `bestPair`'s gives the same pair. -/
theorem bestPairF_eq (lo hi : Nat) (h1 h2 h1' h2' : List (Placement × Int)) (f1 : Fun h1) (f2 : Fun h2)
    (e1 : ∀ x, x ∈ h1' ↔ x ∈ h1) (e2 : ∀ x, x ∈ h2' ↔ x ∈ h2) :
    bestPairF lo hi h1' h2' = bestPair lo hi h1 h2 := by
  have f1' : Fun h1' := fun x hx y hy => f1 x ((e1 x).1 hx) y ((e1 y).1 hy)
  have f2' : Fun h2' := fun x hx y hy => f2 x ((e2 x).1 hx) y ((e2 y).1 hy)
  have ep : ∀ x, x ∈ pairsOf lo hi h1' h2' ↔ x ∈ pairsOf lo hi h1 h2 := fun x => by
    rw [mem_pairsOf, mem_pairsOf, e1, e2]
  apply Option.ext
  intro p
  rw [bestPairF_iff lo hi h1' h2' f1' f2', bestPair_iff lo hi h1 h2 f1 f2, ep]
  simp only [ep]

/-! ## Exact penalties -/

theorem penFL_eq (R G : ByteArray) (st len lim : Nat) (hn : 100 ≤ R.size) (hlim : lim ≤ 12) :
    (penB R G st len ≤ lim → penFL R G st len lim = penB R G st len) ∧
      (penFL R G st len lim ≤ lim → penFL R G st len lim = penB R G st len) := by
  unfold penFL penB
  split
  · split
    · rw [hamSeeds_spec R G st 0 _ (by simp only [q]; omega)
        (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
        (fun h => absurd h (by decide))]
      unfold penSame
      generalize preB R G st R.size = x
      by_cases hx : x ≤ 3
      · rw [if_pos hx]; constructor <;> intro h <;> omega
      · rw [if_neg hx]; constructor <;> intro h <;> omega
    · split
      · next hne _ =>
        rw [gappedPen2_spec R G st len lim hne hlim]
        generalize penGap R G st len = y
        by_cases hy : y ≤ lim
        · rw [if_pos hy]; exact ⟨fun _ => rfl, fun _ => rfl⟩
        · rw [if_neg hy]; constructor <;> intro h <;> omega
      · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem mem_mergeU : ∀ (xs ys acc : List Nat) (x : Nat), x ∈ mergeU xs ys acc ↔ x ∈ xs ∨ x ∈ ys ∨ x ∈ acc := by
  intro xs ys acc x
  induction xs, ys, acc using mergeU.induct with
  | case1 ys acc => rw [mergeU, List.reverseAux_eq]; simp only [List.mem_append, List.mem_reverse]; grind
  | case2 xs acc h =>
    rw [mergeU, List.reverseAux_eq]
    · simp only [List.mem_append, List.mem_reverse]; grind
    · exact h
  | case3 x' xs y ys acc h ih => rw [mergeU, if_pos h, ih]; simp only [List.mem_cons]; grind
  | case4 x' xs y ys acc h h' ih => rw [mergeU, if_neg h, if_pos h', ih]; simp only [List.mem_cons]; grind
  | case5 x' xs y ys acc h h' ih =>
    rw [mergeU, if_neg h, if_neg h', ih]
    have : x' = y := by omega
    subst this; simp only [List.mem_cons]; grind

theorem mem_foldl_mergeU (f : Nat × Array Nat → List Nat) :
    ∀ (l : List (Nat × Array Nat)) (acc : List Nat) (d : Nat),
      d ∈ l.foldl (fun acc ja => mergeU acc (f ja) []) acc ↔ d ∈ acc ∨ ∃ ja ∈ l, d ∈ f ja := by
  intro l
  induction l with
  | nil => intro acc d; simp
  | cons ja l ih =>
    intro acc d
    rw [List.foldl_cons, ih, mem_mergeU]
    simp only [List.not_mem_nil, or_false, List.mem_cons]
    constructor
    · rintro ((h | h) | ⟨jb, hj, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨ja, Or.inl rfl, h⟩
      · exact Or.inr ⟨jb, Or.inr hj, h⟩
    · rintro (h | ⟨jb, rfl | hj, h⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨jb, hj, h⟩

/-- A clean seed on diagonal `d` gives an anchor of the (sliced) lookup on that diagonal. -/
theorem anchor_of_seedBit (Gc R : ByteArray) (j d : Nat) (hj : j < 4) (a : Array Nat) (hl : LookOk Gc R j a)
    (h : seedBit Gc R j d ≠ 0) : ∃ e ∈ a.toList, e / 16 = d := by
  obtain ⟨h1, h2⟩ := (seedBit_ne Gc R j d).mp h
  refine ⟨anchorOf j (d - (BIAS - j * q)), (hl.2 _).mpr ⟨_, h2, rfl⟩, ?_⟩
  unfold anchorOf
  have hw : 2 ^ j < 16 := by
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> decide
  rw [show d - (BIAS - j * q) + (BIAS - j * q) = d by omega]
  generalize 2 ^ j = w at hw ⊢
  omega

theorem maskAt_ne (G R : ByteArray) (d : Nat) (h : maskAt G R d ≠ 0) : ∃ j, j < 4 ∧ seedBit G R j d ≠ 0 := by
  unfold maskAt at h
  by_cases h0 : seedBit G R 0 d = 0
  · by_cases h1 : seedBit G R 1 d = 0
    · by_cases h2 : seedBit G R 2 d = 0
      · exact ⟨3, by omega, by omega⟩
      · exact ⟨2, by omega, h2⟩
    · exact ⟨1, by omega, h1⟩
  · exact ⟨0, by omega, h0⟩

/-- The seeds of `js` as a mask. -/
def maskOf : List Nat → Nat
  | [] => 0
  | j :: js => maskOf js + 2 ^ j

theorem maskOf_spec : ∀ js : List Nat, js.Nodup → (∀ j ∈ js, j < 4) →
    maskOf js < 16 ∧ pop4 (maskOf js) = js.length ∧ ∀ i, i < 4 → bit (maskOf js) i = 1 → i ∈ js := by
  intro js
  induction js with
  | nil =>
    intro _ _
    refine ⟨by decide, rfl, fun i _ h => ?_⟩
    simp only [maskOf, bit, Nat.zero_div, Nat.zero_mod] at h
    omega
  | cons j js ih =>
    intro hnd hl
    have hnd' := List.nodup_cons.mp hnd
    obtain ⟨h1, h2, h3⟩ := ih hnd'.2 (fun i hi => hl i (List.mem_cons_of_mem _ hi))
    have hj := hl j List.mem_cons_self
    have h0 : bit (maskOf js) j = 0 := by
      have : bit (maskOf js) j < 2 := Nat.mod_lt _ (by omega)
      by_cases e : bit (maskOf js) j = 1
      · exact absurd (h3 j hj e) hnd'.1
      · omega
    obtain ⟨p1, p2⟩ := pop4_add _ h1 j hj h0
    refine ⟨p2, by simp only [maskOf, List.length_cons]; omega, fun i hi hb => ?_⟩
    simp only [maskOf] at hb
    rw [bit_add _ j i hj hi h1 h0] at hb
    split at hb
    · next e => exact e ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (h3 i hi hb)

theorem maskJ_ne (G R : ByteArray) (J d : Nat) (h : maskJ G R J d ≠ 0) :
    ∃ j, j < 4 ∧ bit J j = 1 ∧ seedBit G R j d ≠ 0 := by
  apply Classical.byContradiction
  intro hne
  apply h
  have z : ∀ j, j < 4 → (if bit J j = 1 then seedBit G R j d else 0) = 0 := fun j hj => by
    split
    · next hb => exact Classical.byContradiction fun h' => hne ⟨j, hj, hb, h'⟩
    · rfl
  unfold maskJ
  rw [z 0 (by omega), z 1 (by omega), z 2 (by omega), z 3 (by omega)]

/-- A hit of penalty `≤ lim < 4·|J|` has a seed of `J` clean on one of its two
diagonals (the start, or the end shifted by the read length), and is a candidate
of that diagonal. -/
theorem hit_candJ (R G : ByteArray) (st len lim J : Nat) (hn : 100 ≤ R.size) (hlim : lim ≤ 12)
    (hcov : lim < 4 * pop4 J) (hp : penB R G st len ≤ lim) :
    ∃ d, maskJ G R J d ≠ 0 ∧ (d = st + BIAS ∨ d = st + len + BIAS - R.size) ∧ (st, len) ∈ candL R.size d lim := by
  have hp' := hp
  unfold penB at hp'
  split at hp'
  · next hfit =>
    split at hp'
    · next hsame =>
      subst hsame
      by_cases h : maskJ G R J (st + BIAS) = 0
      · exfalso
        have hl := same_lower_J R G st hn hfit J (fun j hj hb => maskJ_zero G R J _ h j hj hb)
        unfold penSame at hp'
        split at hp' <;> omega
      · refine ⟨st + BIAS, h, Or.inl rfl, ?_⟩
        unfold candL
        split
        · rw [Nat.add_sub_cancel]; exact List.mem_singleton_self _
        · unfold candW
          simp only [List.mem_flatMap, List.mem_range, List.mem_cons, Prod.mk.injEq, List.not_mem_nil]
          exact ⟨3, by omega, Or.inl ⟨by omega, by omega⟩⟩
    · next hne =>
      split at hp'
      · next h3 =>
        have h8 := penB_gap_ge R G st len hne
        have hlen : R.size ≤ len + 3 ∧ len ≤ R.size + 3 := by unfold gapLen at h3; split at h3 <;> omega
        have hc : candL R.size = fun d lim' => if lim' < 8 then [(d - BIAS, R.size)] else candW R.size d := rfl
        by_cases h1 : maskJ G R J (st + BIAS) = 0
        · by_cases h2 : maskJ G R J (st + len + BIAS - R.size) = 0
          · exfalso
            have hl := gap_lower R G st len hn hfit hne h3 (by omega) J (fun j hj hb =>
              ⟨maskJ_zero G R J _ h1 j hj hb, maskJ_zero G R J _ h2 j hj hb⟩)
            omega
          · refine ⟨st + len + BIAS - R.size, h2, Or.inr rfl, ?_⟩
            rw [hc]; simp only [show ¬ lim < 8 by omega, if_false]
            unfold candW
            simp only [List.mem_flatMap, List.mem_range, List.mem_cons, Prod.mk.injEq, List.not_mem_nil]
            refine ⟨len + 3 - R.size, by omega, Or.inr (Or.inl ⟨?_, by omega⟩)⟩
            simp only [BIAS]; omega
        · refine ⟨st + BIAS, h1, Or.inl rfl, ?_⟩
          rw [hc]; simp only [show ¬ lim < 8 by omega, if_false]
          unfold candW
          simp only [List.mem_flatMap, List.mem_range, List.mem_cons, Prod.mk.injEq, List.not_mem_nil]
          exact ⟨len + 3 - R.size, by omega, Or.inl ⟨by omega, by omega⟩⟩
      · omega
  · omega

/-- The same with the seeds of a list `js`. -/
theorem hit_cand (R G : ByteArray) (st len lim : Nat) (js : List Nat) (hn : 100 ≤ R.size) (hlim : lim ≤ 12)
    (hnd : js.Nodup) (hjs : ∀ j ∈ js, j < 4) (hcov : lim < 4 * js.length) (hp : penB R G st len ≤ lim) :
    ∃ d, (∃ j ∈ js, seedBit G R j d ≠ 0) ∧ (st, len) ∈ candL R.size d lim := by
  obtain ⟨-, hpop, hbit⟩ := maskOf_spec js hnd hjs
  obtain ⟨d, hm, -, hc⟩ := hit_candJ R G st len lim (maskOf js) hn hlim (by omega) hp
  obtain ⟨j, hj, hb, hs⟩ := maskJ_ne G R _ d hm
  exact ⟨d, ⟨j, hbit j hj hb, hs⟩, hc⟩

section enum

variable {L P : Type} (lk : Look L P) (ix : L) (G : ByteArray) (offs : Array Nat) (gbs : Array ByteArray)

/-- The strand's enumeration: with `lim < 4·|js|`, exactly the windows of penalty
`≤ lim`, with their penalties. -/
theorem mem_hitsStrand (R' : ByteArray) (s : Strand) (js : List Nat) (lim : Nat) (hn : 100 ≤ R'.size)
    (hlim : lim ≤ 12) (hnd : js.Nodup) (hjs : ∀ j ∈ js, j < 4) (hcov : lim < 4 * js.length)
    (hsl : ∀ j, j < 4 → ∀ c, c < gbs.size →
      LookOk gbs[c]! R' j (sliceA (lk.look ix G R' j (lk.prep ix (seedHash R' j))) j offs[c]! gbs[c]!.size))
    (p : Placement) (k : Nat) :
    (p, k) ∈ hitsStrand lk ix G offs gbs R' s js lim ↔
      p.2 = s ∧ p.1.chr < gbs.size ∧ penB R' gbs[p.1.chr]! p.1.start p.1.len = k ∧ k ≤ lim := by
  obtain ⟨⟨c, st, len⟩, s'⟩ := p
  unfold hitsStrand
  simp only [List.mem_flatMap, List.mem_range, List.mem_filterMap]
  constructor
  · rintro ⟨c', hc, d, -, w, -, hw⟩
    split at hw
    · next hk =>
      simp only [Option.some.injEq, Prod.mk.injEq, Window.mk.injEq] at hw
      obtain ⟨⟨⟨rfl, rfl, rfl⟩, rfl⟩, rfl⟩ := hw
      exact ⟨rfl, hc, ((penFL_eq _ _ _ _ _ hn hlim).2 hk).symm, hk⟩
    · simp at hw
  · rintro ⟨rfl, hc, hpk, hk⟩
    refine ⟨c, hc, ?_⟩
    obtain ⟨d, ⟨j, hjm, hb⟩, hw⟩ := hit_cand R' gbs[c]! st len lim js hn hlim hnd hjs hcov (by omega)
    have hj := hjs j hjm
    obtain ⟨e, he, hed⟩ := anchor_of_seedBit _ _ j d hj _ (hsl j hj c hc) hb
    refine ⟨d, ?_, (st, len), hw, ?_⟩
    · rw [mem_foldl_mergeU]
      refine Or.inr ⟨(j, lk.look ix G R' j (lk.prep ix (seedHash R' j))), ?_, ?_⟩
      · simp only [List.mem_map]; exact ⟨j, hjm, rfl⟩
      · simp only [List.mem_map]; exact ⟨e, he, hed⟩
    · simp only []
      rw [(penFL_eq _ _ _ _ _ hn hlim).1 (by omega), hpk, if_pos hk]

/-- Both strands: exactly the placements of penalty `≤ lim`, with their penalties. -/
theorem mem_hitsL [Inhabited P] (R : ByteArray) (lim : Nat) (hn : 100 ≤ R.size) (hlim : lim ≤ 12)
    (hcat : catOk G offs gbs = true)
    (hlk : ∀ R' : ByteArray, ∀ j, j < 4 → LookOk G R' j (lk.look ix G R' j (lk.prep ix (seedHash R' j))))
    (p : Placement) (k : Nat) :
    (p, k) ∈ hitsL lk ix G offs gbs R lim ↔ cwP R gbs p.2 p.1 = k ∧ k ≤ lim := by
  have hsl : ∀ R' : ByteArray, ∀ j, j < 4 → ∀ c, c < gbs.size →
      LookOk gbs[c]! R' j (sliceA (lk.look ix G R' j (lk.prep ix (seedHash R' j))) j offs[c]! gbs[c]!.size) :=
    fun R' j hj c hc => sliceA_ok G gbs[c]! R' offs[c]! j hj _ (hlk R' j hj) (catOk_spec G offs gbs hcat c hc).1
      (catOk_spec G offs gbs hcat c hc).2
  have hrn : 100 ≤ (revCompB R).size := by rw [revCompB_size]; exact hn
  have ord : ∀ R' : ByteArray, List.Nodup ((seedOrder lk ix (prepAll lk ix (seedHashes R'))).take (lim / 4 + 1)) ∧
      (∀ j ∈ (seedOrder lk ix (prepAll lk ix (seedHashes R'))).take (lim / 4 + 1), j < 4) ∧
      lim < 4 * ((seedOrder lk ix (prepAll lk ix (seedHashes R'))).take (lim / 4 + 1)).length := by
    intro R'
    obtain ⟨h1, h2, h3⟩ := seedOrder_spec lk ix (prepAll lk ix (seedHashes R'))
    refine ⟨h1.sublist (List.take_sublist _ _), fun j hj => h2 j (List.mem_of_mem_take hj), ?_⟩
    rw [List.length_take, h3]; omega
  unfold hitsL
  simp only []
  rw [List.mem_append, mem_hitsStrand lk ix G offs gbs R .fwd _ lim hn hlim (ord R).1 (ord R).2.1 (ord R).2.2 (hsl R),
    mem_hitsStrand lk ix G offs gbs _ .rev _ lim hrn hlim (ord _).1 (ord _).2.1 (ord _).2.2 (hsl _)]
  obtain ⟨⟨c, st, len⟩, s⟩ := p
  cases s <;> simp only [cwP, cwG] <;> by_cases hc : c < gbs.size <;> simp [hc] <;> omega

theorem penB_len (R G : ByteArray) (st len : Nat) (h : penB R G st len ≤ 12) :
    R.size ≤ len + 3 ∧ len ≤ R.size + 3 := by
  unfold penB at h
  split at h
  · split at h
    · omega
    · split at h
      · next h3 => unfold gapLen at h3; split at h3 <;> omega
      · omega
  · omega

theorem nearA_of (ys : Array Nat) (hy : IncA ys) (d W e : Nat) (he : e ∈ ys.toList) (h1 : d ≤ e / 16 + W)
    (h2 : e / 16 ≤ d + W) : nearA ys d W = true := by
  obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.mp he
  simp only [Array.length_toList, Array.getElem_toList] at hk hke
  have hk' : ys[k]! = e := by rw [getElem!_pos ys k hk]; exact hke
  have L := lbA_spec ys (16 * (d - W)) hy 0 ys.size (Nat.le_refl _) (Nat.zero_le _) (fun k hk => by omega)
    (fun k _ hk => by omega)
  show (decide (lbA ys (16 * (d - W)) 0 ys.size < ys.size) &&
    decide (ys[lbA ys (16 * (d - W)) 0 ys.size]! / 16 ≤ d + W)) = true
  generalize lbA ys (16 * (d - W)) 0 ys.size = i at L ⊢
  have hik : i ≤ k := by
    apply Classical.byContradiction; intro hn
    have := L.1 k (by omega); rw [hk'] at this; omega
  have hle : ys[i]! ≤ e := by
    rcases Nat.lt_or_eq_of_le hik with h | h
    · have := hy i k h hk; omega
    · subst h; omega
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨by omega, by omega⟩

/-- A hit of penalty `≤ lim < 4·|J|` has an anchor (of the seeds `J`) within 3
diagonals of its start, whose candidates include it. -/
theorem anchor_near (R G : ByteArray) (as : Array Nat) (J st len lim : Nat) (hn : 100 ≤ R.size) (hlim : lim ≤ 12)
    (hcov : lim < 4 * pop4 J) (ha : AnchorsM (maskJ G R J) as) (hp : penB R G st len ≤ lim) :
    ∃ e ∈ as.toList, st + BIAS ≤ e / 16 + 3 ∧ e / 16 ≤ st + BIAS + 3 ∧ (st, len) ∈ candL R.size (e / 16) lim := by
  obtain ⟨d, hm, hd, hw⟩ := hit_candJ R G st len lim J hn hlim hcov hp
  have hl := penB_len R G st len (by omega)
  have hlt := ha.lt d
  refine ⟨d * 16 + maskJ G R J d, ha.complete d hm, ?_⟩
  rw [show (d * 16 + maskJ G R J d) / 16 = d by omega]
  refine ⟨by simp only [BIAS] at hd ⊢; omega, by simp only [BIAS] at hd ⊢; omega, hw⟩

theorem hitsCSF_sound (R' : ByteArray) (sd : Strand) (st o : CS) (W lim : Nat) (hn : 100 ≤ R'.size)
    (hlim : lim ≤ 12) (p : Placement) (k : Nat) (h : (p, k) ∈ hitsCSF gbs R' sd st o W lim) :
    p.2 = sd ∧ p.1.chr < gbs.size ∧ penB R' gbs[p.1.chr]! p.1.start p.1.len = k ∧ k ≤ lim := by
  obtain ⟨⟨c, st0, len⟩, s'⟩ := p
  unfold hitsCSF at h
  simp only [List.mem_flatMap, List.mem_range] at h
  obtain ⟨c', hc, e, -, he⟩ := h
  split at he
  · simp only [List.mem_filterMap] at he
    obtain ⟨w, -, hw⟩ := he
    split at hw
    · next hk =>
      simp only [Option.some.injEq, Prod.mk.injEq, Window.mk.injEq] at hw
      obtain ⟨⟨⟨rfl, rfl, rfl⟩, rfl⟩, rfl⟩ := hw
      exact ⟨rfl, hc, ((penFL_eq _ _ _ _ _ hn hlim).2 hk).symm, hk⟩
    · simp at hw
  · simp at he

/-- A window of penalty `≤ lim < 4·|J|` with an anchor of the other state within
`W − 3` diagonals of its start is listed. -/
theorem hitsCSF_complete (R' : ByteArray) (sd : Strand) (st o : CS) (W lim J : Nat) (hn : 100 ≤ R'.size)
    (hlim : lim ≤ 12) (hcov : lim < 4 * pop4 J) (c st0 len : Nat) (hc : c < gbs.size)
    (ha : AnchorsM (maskJ gbs[c]! R' J) st.as[c]!) (hy : IncA o.as[c]!) (hp : penB R' gbs[c]! st0 len ≤ lim)
    (hpart : ∃ e' ∈ o.as[c]!.toList, st0 + BIAS + 3 ≤ e' / 16 + W ∧ e' / 16 + 3 ≤ st0 + BIAS + W) :
    ((⟨c, st0, len⟩, sd), penB R' gbs[c]! st0 len) ∈ hitsCSF gbs R' sd st o W lim := by
  obtain ⟨e, he, h1, h2, hw⟩ := anchor_near R' gbs[c]! st.as[c]! J st0 len lim hn hlim hcov ha hp
  obtain ⟨e', he', h3, h4⟩ := hpart
  unfold hitsCSF
  simp only [List.mem_flatMap, List.mem_range]
  refine ⟨c, hc, e, he, ?_⟩
  rw [if_pos (nearA_of _ hy _ _ e' he' (by omega) (by omega))]
  simp only [List.mem_filterMap]
  refine ⟨(st0, len), hw, ?_⟩
  simp only []
  rw [(penFL_eq _ _ _ _ _ hn hlim).1 hp, if_pos hp]

end enum

/-! ## Against the spec -/

/-- Score of a placement within the cap ↔ its penalty (`key` in `decodeJ_eq_mapSpecBoth`). -/
theorem strandScore_cwP (g : Genome) (read : List Char) (gbs : Array ByteArray) (R : ByteArray)
    (hg : GenomeBytes gbs g) (hr : Encodes R read) (st : Strand) (w : Window) (s : Int) :
    (strandScore g read st w = some s ∧ -12 ≤ s) ↔ (cwP R gbs st w ≤ 12 ∧ s = -(cwP R gbs st w : Int)) := by
  cases st with
  | fwd =>
    show (windowScore sc0 read g w = some s ∧ -12 ≤ s) ↔ _
    rw [show cwP R gbs .fwd w = cwG R gbs w from rfl, cwG_eq g read gbs R hg hr]
    exact penOf_some _ s (windowScore_nonpos read g w)
  | rev =>
    show (windowScore sc0 (revComp read) g w = some s ∧ -12 ≤ s) ↔ _
    rw [show cwP R gbs .rev w = cwG (revCompB R) gbs w from rfl,
      cwG_eq g (revComp read) gbs (revCompB R) hg (revCompB_encodes R read hr)]
    exact penOf_some _ s (windowScore_nonpos (revComp read) g w)

theorem mem_hitsBoth_cwP (g : Genome) (read : List Char) (gbs : Array ByteArray) (R : ByteArray)
    (hg : GenomeBytes gbs g) (hr : Encodes R read) (x : Placement × Int) :
    x ∈ hitsBoth sc0 (-12) g read ↔ cwP R gbs x.1.2 x.1.1 ≤ 12 ∧ x.2 = -(cwP R gbs x.1.2 x.1.1 : Int) := by
  obtain ⟨p, s⟩ := x
  rw [mem_hitsBoth_sc0, ← strandScore_cwP g read gbs R hg hr]
  constructor
  · rintro ⟨-, h⟩; exact h
  · rintro h; exact ⟨strandScore_allWindows g read p.2 p.1 s h.1, h⟩

theorem fun_hitsBoth (g : Genome) (read : List Char) : Fun (hitsBoth sc0 (-12) g read) := by
  rintro ⟨a, sa⟩ ha ⟨b, sb⟩ hb (rfl : a = b)
  rw [mem_hitsBoth_sc0] at ha hb
  have := ha.2.1.symm.trans hb.2.1
  simpa using this

/-- With every hit looked at, a best above the cap means no hit at all. -/
theorem no_hit (g : Genome) (read : List Char) (gbs : Array ByteArray) (R : ByteArray) (b : Best)
    (hg : GenomeBytes gbs g) (hr : Encodes R read)
    (hb : ∃ S, Inv (cwJ R gbs) S b ∧ ∀ w, cwJ R gbs w ≤ 12 → S w) (hp : 12 < b.pen) :
    hitsBoth sc0 (-12) g read = [] := by
  obtain ⟨S, hi, hall⟩ := hb
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro x hx
  rw [mem_hitsBoth_cwP g read gbs R hg hr] at hx
  have h1 := cwJ_encJ R gbs x.1 hx.1
  have := hi.min _ (hall _ (by rw [h1]; exact hx.1))
  omega

theorem bestPair_nil_left (lo hi : Nat) (h2 : List (Placement × Int)) : bestPair lo hi [] h2 = none := by
  simp [bestPair]

theorem bestPair_nil_right (lo hi : Nat) (h1 : List (Placement × Int)) : bestPair lo hi h1 [] = none := by
  simp [bestPair]

/-- **Fast case.**  Unique per-mate bests forming a proper pair are the unique best pair. -/
theorem pairSpecU_of_unique (lo hi : Nat) (g : Genome) (m1 m2 : List Char) (a b : Placement × Int)
    (ha : mapSpecBoth sc0 (-12) g m1 = some a) (hb : mapSpecBoth sc0 (-12) g m2 = some b)
    (hp : properPair lo hi a.1 b.1 = true) : pairSpecU sc0 (-12) lo hi g m1 m2 = some (a, b) := by
  have ha' := (mapSpecBoth_iff g m1 a.1 a.2).mp ha
  have hb' := (mapSpecBoth_iff g m2 b.1 b.2).mp hb
  unfold pairSpecU
  rw [bestPair_iff lo hi _ _ (fun_hitsBoth g m1) (fun_hitsBoth g m2)]
  have mem : ∀ (m : List Char) (x : Placement × Int), x ∈ hitsBoth sc0 (-12) g m ↔
      strandScore g m x.1.2 x.1.1 = some x.2 ∧ -12 ≤ x.2 := fun m x => by
    rw [mem_hitsBoth_sc0]
    exact ⟨fun h => h.2, fun h => ⟨strandScore_allWindows g m _ _ _ h.1, h⟩⟩
  refine ⟨(mem_pairsOf _ _ _ _ _).mpr ⟨(mem _ _).mpr ha'.1, (mem _ _).mpr hb'.1, hp⟩, fun x hx => ?_⟩
  rw [mem_pairsOf] at hx
  obtain ⟨hx1, hx2, -⟩ := hx
  have h1 := ha'.2 x.1.1 x.1.2 ((mem _ _).mp hx1).1 ((mem _ _).mp hx1).2
  have h2 := hb'.2 x.2.1 x.2.2 ((mem _ _).mp hx2).1 ((mem _ _).mp hx2).2
  -- equal placements have equal scores
  have e1 : x.1.1 = a.1 → x.1.2 = a.2 := fun e => fun_hitsBoth g m1 _ hx1 _ ((mem _ _).mpr ha'.1) e
  have e2 : x.2.1 = b.1 → x.2.2 = b.2 := fun e => fun_hitsBoth g m2 _ hx2 _ ((mem _ _).mpr hb'.1) e
  show x.1.2 + x.2.2 < a.2 + b.2 ∨ (x.1.1 = a.1 ∧ x.2.1 = b.1)
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · left; omega
  · left; have := e2 h2; omega
  · left; have := e1 h1; omega
  · right; exact ⟨h1, h2⟩

/-- Each mate's placements with penalty `≤ lim` from `hitsL`, as scored hits. -/
theorem mem_toScore_hitsL {L P : Type} [Inhabited P] (lk : Look L P) (ix : L) (G : ByteArray)
    (offs : Array Nat) (g : Genome) (m : List Char) (gbs : Array ByteArray) (R : ByteArray) (lim : Nat)
    (hg : GenomeBytes gbs g) (hr : Encodes R m) (hcat : catOk G offs gbs = true)
    (hlk : ∀ R' : ByteArray, ∀ j, j < 4 → LookOk G R' j (lk.look ix G R' j (lk.prep ix (seedHash R' j))))
    (hn : 100 ≤ R.size) (hlim : lim ≤ 12) (x : Placement × Int) :
    x ∈ toScore (hitsL lk ix G offs gbs R lim) ↔ x ∈ hitsBoth sc0 (-12) g m ∧ -(lim : Int) ≤ x.2 := by
  rw [mem_hitsBoth_cwP g m gbs R hg hr]
  unfold toScore
  rw [List.mem_map]
  constructor
  · rintro ⟨⟨p, k⟩, hm, rfl⟩
    rw [mem_hitsL lk ix G offs gbs R lim hn hlim hcat hlk] at hm
    obtain ⟨rfl, hk⟩ := hm
    simp only
    exact ⟨⟨by omega, trivial⟩, by omega⟩
  · rintro ⟨⟨hk, hx⟩, hl⟩
    refine ⟨(x.1, cwP R gbs x.1.2 x.1.1),
      (mem_hitsL lk ix G offs gbs R lim hn hlim hcat hlk _ _).mpr ⟨rfl, by omega⟩, ?_⟩
    obtain ⟨p, s⟩ := x
    simp only at hx ⊢
    rw [hx]

/-- The per-mate best penalty bounds every hit's score. -/
theorem le_best (g : Genome) (read : List Char) (gbs : Array ByteArray) (R : ByteArray) (b : Best)
    (hg : GenomeBytes gbs g) (hr : Encodes R read)
    (hb : ∃ S, Inv (cwJ R gbs) S b ∧ ∀ w, cwJ R gbs w ≤ 12 → S w) :
    ∀ x ∈ hitsBoth sc0 (-12) g read, x.2 ≤ -(b.pen : Int) := by
  obtain ⟨S, hi, hall⟩ := hb
  intro x hx
  rw [mem_hitsBoth_cwP g read gbs R hg hr] at hx
  have h1 := cwJ_encJ R gbs x.1 hx.1
  have := hi.min _ (hall _ (by rw [h1]; exact hx.1))
  rw [h1] at this
  omega

theorem selPairs_iff (ps : List ((Placement × Int) × (Placement × Int)))
    (hf : ∀ x ∈ ps, ∀ y ∈ ps, x.1.1 = y.1.1 → x.2.1 = y.2.1 → x = y) (p : (Placement × Int) × (Placement × Int)) :
    selPairs ps = some p ↔ p ∈ ps ∧ ∀ x ∈ ps, x.1.2 + x.2.2 < p.1.2 + p.2.2 ∨ (x.1.1 = p.1.1 ∧ x.2.1 = p.2.1) := by
  have := selU_iff (fun p : (Placement × Int) × (Placement × Int) => (p.1.1, p.2.1))
    (fun p => p.1.2 + p.2.2) ps (fun x hx y hy he => by
      simp only [Prod.mk.injEq] at he; exact hf x hx y hy he.1 he.2) p
  simp only [Prod.mk.injEq] at this
  exact this

/-- **Restricting to the best pairs.**  If no proper pair of hits sums above `l`,
and `PS` holds exactly the proper pairs summing to `l` (and has one), the best pair
is the best of `PS`. -/
theorem bestPair_restrict (lo hi : Nat) (H1 H2 : List (Placement × Int))
    (PS : List ((Placement × Int) × (Placement × Int))) (l : Int) (f1 : Fun H1) (f2 : Fun H2)
    (sub : ∀ x, x ∈ PS ↔ x ∈ pairsOf lo hi H1 H2 ∧ l ≤ x.1.2 + x.2.2)
    (hmax : ∀ x ∈ pairsOf lo hi H1 H2, x.1.2 + x.2.2 ≤ l) (hne : PS.isEmpty = false) :
    selPairs PS = bestPair lo hi H1 H2 := by
  have hf : ∀ x ∈ pairsOf lo hi H1 H2, ∀ y ∈ pairsOf lo hi H1 H2, x.1.1 = y.1.1 → x.2.1 = y.2.1 → x = y := by
    rintro ⟨⟨a, sa⟩, ⟨b, sb⟩⟩ hx ⟨⟨a', sa'⟩, ⟨b', sb'⟩⟩ hy (rfl : a = a') (rfl : b = b')
    rw [mem_pairsOf] at hx hy
    have ea : sa = sa' := f1 _ hx.1 _ hy.1 rfl
    have eb : sb = sb' := f2 _ hx.2.1 _ hy.2.1 rfl
    rw [ea, eb]
  obtain ⟨y, hy⟩ : ∃ y, y ∈ PS := by
    cases h : PS with
    | nil => rw [h] at hne; simp at hne
    | cons y _ => exact ⟨y, List.mem_cons_self⟩
  apply Option.ext
  intro p
  rw [selPairs_iff _ (fun x hx z hz => hf x ((sub x).1 hx).1 z ((sub z).1 hz).1),
    bestPair_iff lo hi H1 H2 f1 f2]
  constructor
  · rintro ⟨hp, hall⟩
    obtain ⟨hp1, hp2⟩ := (sub p).1 hp
    refine ⟨hp1, fun x hx => ?_⟩
    by_cases hs : l ≤ x.1.2 + x.2.2
    · exact hall x ((sub x).2 ⟨hx, hs⟩)
    · left; omega
  · rintro ⟨hp, hall⟩
    obtain ⟨hy1, hy2⟩ := (sub y).1 hy
    have hpy : p = y := by
      rcases hall y hy1 with h | ⟨h1, h2⟩
      · have := hmax p hp; omega
      · exact (hf y hy1 p hp h1 h2).symm
    subst hpy
    exact ⟨hy, fun x hx => hall x ((sub x).1 hx).1⟩

/-! ## The searches' final states -/

theorem ilCS_fst {L P : Type} [Inhabited P] (lk : Look L P) (ix : L) (G : ByteArray) (gbs : Array ByteArray)
    (offs : Array Nat) (R1 R2 : ByteArray) (c1 c2 : Nat) (ps1 ps2 : Array P) :
    ∀ f s1 s2 b, (ilCS lk ix G gbs offs R1 R2 c1 c2 ps1 ps2 f s1 s2 b).1 =
      ilC lk ix G gbs offs R1 R2 c1 c2 ps1 ps2 f s1 s2 b := by
  intro f
  induction f with
  | zero => intro s1 s2 b; rfl
  | succ f ih =>
    intro s1 s2 b
    unfold ilCS ilC
    simp only []
    split
    · exact ih _ _ _
    · split
      · exact ih _ _ _
      · rfl

theorem mapChromsCS_fst {L P : Type} [Inhabited P] (lk : Look L P) (ix : L) (G : ByteArray) (offs : Array Nat)
    (gbs : Array ByteArray) (R : ByteArray) (rf : Bool) :
    (mapChromsCS lk ix G offs gbs R rf).1 = mapChromsC lk ix G offs gbs R rf := by
  unfold mapChromsCS mapChromsC
  cases rf <;> simp only [Bool.false_eq_true, if_false, if_true, ilCS_fst]

section twoS

variable (cw : Window → Nat) (hc13 : ∀ w, cw w ≤ 13) {L P : Type} [Inhabited P] (lk : Look L P) (ix : L)
  (G : ByteArray) (gbs : Array ByteArray) (offs : Array Nat) (R1 R2 : ByteArray) (c1 c2 : Nat)
  (hcw1 : ∀ c, c < gbs.size → ∀ st len, cw ⟨c1 + c, st, len⟩ = penB R1 gbs[c]! st len) (hn1 : 100 ≤ R1.size)
  (hsl1 : ∀ j, j < 4 → ∀ c, c < gbs.size →
    LookOk gbs[c]! R1 j (sliceA (lk.look ix G R1 j (lk.prep ix (seedHash R1 j))) j offs[c]! gbs[c]!.size))
  (hcw2 : ∀ c, c < gbs.size → ∀ st len, cw ⟨c2 + c, st, len⟩ = penB R2 gbs[c]! st len) (hn2 : 100 ≤ R2.size)
  (hsl2 : ∀ j, j < 4 → ∀ c, c < gbs.size →
    LookOk gbs[c]! R2 j (sliceA (lk.look ix G R2 j (lk.prep ix (seedHash R2 j))) j offs[c]! gbs[c]!.size))

include hc13 hcw1 hn1 hsl1 hcw2 hn2 hsl2

/-- At the end both strands are done (not live) and keep their states' invariants. -/
theorem ilCS_inv : ∀ (f : Nat) (s1 s2 : CS) (b : Best) (S : Window → Prop),
    SC cw R1 gbs c1 s1 b S → SC cw R2 gbs c2 s2 b S → s1.ord.length + s2.ord.length ≤ f →
    ∃ S', SC cw R1 gbs c1 (ilCS lk ix G gbs offs R1 R2 c1 c2 (prepAll lk ix (seedHashes R1))
        (prepAll lk ix (seedHashes R2)) f s1 s2 b).2.1 (ilCS lk ix G gbs offs R1 R2 c1 c2
        (prepAll lk ix (seedHashes R1)) (prepAll lk ix (seedHashes R2)) f s1 s2 b).1 S' ∧
      SC cw R2 gbs c2 (ilCS lk ix G gbs offs R1 R2 c1 c2 (prepAll lk ix (seedHashes R1))
        (prepAll lk ix (seedHashes R2)) f s1 s2 b).2.2 (ilCS lk ix G gbs offs R1 R2 c1 c2
        (prepAll lk ix (seedHashes R1)) (prepAll lk ix (seedHashes R2)) f s1 s2 b).1 S' ∧
      (ilCS lk ix G gbs offs R1 R2 c1 c2 (prepAll lk ix (seedHashes R1))
        (prepAll lk ix (seedHashes R2)) f s1 s2 b).2.1.live (ilCS lk ix G gbs offs R1 R2 c1 c2
        (prepAll lk ix (seedHashes R1)) (prepAll lk ix (seedHashes R2)) f s1 s2 b).1 = false ∧
      (ilCS lk ix G gbs offs R1 R2 c1 c2 (prepAll lk ix (seedHashes R1))
        (prepAll lk ix (seedHashes R2)) f s1 s2 b).2.2.live (ilCS lk ix G gbs offs R1 R2 c1 c2
        (prepAll lk ix (seedHashes R1)) (prepAll lk ix (seedHashes R2)) f s1 s2 b).1 = false := by
  have dead : ∀ (s : CS) b, s.ord.length = 0 → s.live b = false := fun s b h => by
    simp [CS.live, List.length_eq_zero_iff.mp h]
  have ne : ∀ (s : CS) b, s.live b = true → s.ord ≠ [] := fun s b h e => by simp [CS.live, e] at h
  intro f
  induction f with
  | zero =>
    intro s1 s2 b S h1 h2 hf
    exact ⟨S, h1, h2, dead s1 b (by omega), dead s2 b (by omega)⟩
  | succ f ih =>
    intro s1 s2 b S h1 h2 hf
    unfold ilCS
    simp only []
    split
    · next hc =>
      have hl1 : s1.live b = true := by simp only [Bool.and_eq_true] at hc; exact hc.1
      obtain ⟨S2, k1, hS, hp, hlen⟩ := advC_ok cw hc13 R1 gbs offs c1 hcw1 hn1 lk ix G hsl1 s1 b S h1
        (ne s1 b hl1)
      exact ih _ s2 _ S2 k1 (h2.mono cw R2 gbs c2 (k1.inv cw R1 gbs c1) hS hp) (by omega)
    · next hc =>
      split
      · next hl2 =>
        obtain ⟨S2, k2, hS, hp, hlen⟩ := advC_ok cw hc13 R2 gbs offs c2 hcw2 hn2 lk ix G hsl2 s2 b S h2
          (ne s2 b hl2)
        exact ih s1 _ _ S2 (h1.mono cw R1 gbs c1 (k2.inv cw R2 gbs c2) hS hp) k2 (by omega)
      · next hl2 =>
        have hl2' : s2.live b = false := by simpa using hl2
        have hl1 : s1.live b = false := by
          cases e : s1.live b
          · rfl
          · exact absurd (by simp [e, hl2']) hc
        exact ⟨S, h1, h2, hl1, hl2'⟩

end twoS

/-- A finished strand holds the anchors of seeds `J` with `best < 4·|J|`. -/
theorem sc_dead_anchors (cw : Window → Nat) (R' : ByteArray) (gbs : Array ByteArray) (base : Nat) (s : CS)
    (b : Best) (S : Window → Prop) (h : SC cw R' gbs base s b S) (hd : s.live b = false) (hp : b.pen ≤ 12) :
    ∃ J, J < 16 ∧ b.pen < 4 * pop4 J ∧ ∀ c, c < gbs.size → AnchorsM (maskJ gbs[c]! R' J) s.as[c]! := by
  obtain ⟨J, hJ, hk, -, -, -, hlen, -, -, hs⟩ := h
  refine ⟨J, hJ, ?_, fun c hc => (hs c hc).anchors⟩
  unfold CS.live at hd
  cases ho : s.ord with
  | nil => rw [ho] at hlen; simp at hlen; omega
  | cons j rest => rw [ho] at hd; simp at hd; omega

/-- Both strands of a finished search, as `sc_dead_anchors`. -/
theorem mapChromsCS_ok {L P : Type} [Inhabited P] (lk : Look L P) (ix : L) (G : ByteArray) (offs : Array Nat)
    (gbs : Array ByteArray) (R : ByteArray) (rf : Bool) (hn : 100 ≤ R.size) (hcat : catOk G offs gbs = true)
    (hlk : ∀ R' : ByteArray, ∀ j, j < 4 → LookOk G R' j (lk.look ix G R' j (lk.prep ix (seedHash R' j))))
    (hp : (mapChromsCS lk ix G offs gbs R rf).1.pen ≤ 12) :
    (∃ J, J < 16 ∧ (mapChromsCS lk ix G offs gbs R rf).1.pen < 4 * pop4 J ∧
      ∀ c, c < gbs.size → AnchorsM (maskJ gbs[c]! R J) (mapChromsCS lk ix G offs gbs R rf).2.1.as[c]!) ∧
    (∃ J, J < 16 ∧ (mapChromsCS lk ix G offs gbs R rf).1.pen < 4 * pop4 J ∧
      ∀ c, c < gbs.size → AnchorsM (maskJ gbs[c]! (revCompB R) J) (mapChromsCS lk ix G offs gbs R rf).2.2.as[c]!) := by
  have hrn : 100 ≤ (revCompB R).size := by rw [revCompB_size]; exact hn
  have hsl : ∀ R' : ByteArray, ∀ j, j < 4 → ∀ c, c < gbs.size →
      LookOk gbs[c]! R' j (sliceA (lk.look ix G R' j (lk.prep ix (seedHash R' j))) j offs[c]! gbs[c]!.size) :=
    fun R' j hj c hc => sliceA_ok G gbs[c]! R' offs[c]! j hj _ (hlk R' j hj) (catOk_spec G offs gbs hcat c hc).1
      (catOk_spec G offs gbs hcat c hc).2
  have cf : ∀ c, c < gbs.size → ∀ st len, cwJ R gbs ⟨0 + c, st, len⟩ = penB R gbs[c]! st len :=
    fun c hc st len => by unfold cwJ cwG; simp [hc]
  have cr : ∀ c, c < gbs.size → ∀ st len, cwJ R gbs ⟨gbs.size + c, st, len⟩ = penB (revCompB R) gbs[c]! st len :=
    fun c hc st len => by
      unfold cwJ cwG
      simp [hc, show ¬ gbs.size + c < gbs.size by omega, show gbs.size + c < 2 * gbs.size by omega]
  have i0 := inv_init _ (cwJ_le R gbs)
  have hl0 : (CS.init lk ix (prepAll lk ix (seedHashes R)) gbs.size).ord.length +
      (CS.init lk ix (prepAll lk ix (seedHashes (revCompB R))) gbs.size).ord.length ≤ 8 := by
    simp [CS.init, (seedOrder_spec lk ix (prepAll lk ix (seedHashes R))).2.2,
      (seedOrder_spec lk ix (prepAll lk ix (seedHashes (revCompB R)))).2.2]
  unfold mapChromsCS at hp ⊢
  cases rf with
  | false =>
    simp only [Bool.false_eq_true, if_false] at hp ⊢
    obtain ⟨S, h1, h2, d1, d2⟩ := ilCS_inv (cwJ R gbs) (cwJ_le R gbs) lk ix G gbs offs R (revCompB R) 0 gbs.size
      cf hn (hsl R) cr hrn (hsl _) 8 _ _ {} (fun _ => False)
      (initC_ok (cwJ R gbs) R gbs 0 lk ix {} _ i0) (initC_ok (cwJ R gbs) _ gbs gbs.size lk ix {} _ i0) hl0
    exact ⟨sc_dead_anchors _ _ _ _ _ _ _ h1 d1 hp, sc_dead_anchors _ _ _ _ _ _ _ h2 d2 hp⟩
  | true =>
    simp only [if_true] at hp ⊢
    obtain ⟨S, h1, h2, d1, d2⟩ := ilCS_inv (cwJ R gbs) (cwJ_le R gbs) lk ix G gbs offs (revCompB R) R gbs.size 0
      cr hrn (hsl _) cf hn (hsl R) 8 _ _ {} (fun _ => False)
      (initC_ok (cwJ R gbs) _ gbs gbs.size lk ix {} _ i0) (initC_ok (cwJ R gbs) R gbs 0 lk ix {} _ i0)
      (by rw [Nat.add_comm]; exact hl0)
    exact ⟨sc_dead_anchors _ _ _ _ _ _ _ h2 d2 hp, sc_dead_anchors _ _ _ _ _ _ _ h1 d1 hp⟩

theorem proper_close (lo hi : Nat) (a b : Placement) (h : properPair lo hi a b = true) (ha : a.1.len ≤ 106)
    (hb : b.1.len ≤ 106) :
    a.1.chr = b.1.chr ∧ a.2 ≠ b.2 ∧ a.1.start ≤ b.1.start + hi + 106 ∧ b.1.start ≤ a.1.start + hi + 106 := by
  obtain ⟨⟨c1, s1, l1⟩, t1⟩ := a
  obtain ⟨⟨c2, s2, l2⟩, t2⟩ := b
  simp only at ha hb ⊢
  cases t1 <;> cases t2 <;> simp [properPair] at h ⊢ <;> omega

theorem cwP_hit (R : ByteArray) (gbs : Array ByteArray) (t : Strand) (w : Window) (h : cwP R gbs t w ≤ 12) :
    w.chr < gbs.size ∧ penB (if t = .fwd then R else revCompB R) gbs[w.chr]! w.start w.len = cwP R gbs t w := by
  have hc := cwP_chr_lt R gbs (w, t) h
  cases t <;> simp [cwP, cwG, hc]

/-- Mate `R`'s listed placements are hits scoring at least `-best`. -/
theorem hitsBest_sound (g : Genome) (m : List Char) (gbs : Array ByteArray) (W : Nat) (R : ByteArray)
    (r o : Best × CS × CS) (hg : GenomeBytes gbs g) (hr : Encodes R m) (hn : 100 ≤ R.size) (hp : r.1.pen ≤ 12)
    (x : Placement × Int) (h : x ∈ hitsBest gbs W R r o) :
    x ∈ hitsBoth sc0 (-12) g m ∧ -(r.1.pen : Int) ≤ x.2 := by
  have hrn : 100 ≤ (revCompB R).size := by rw [revCompB_size]; exact hn
  rw [mem_hitsBoth_cwP g m gbs R hg hr]
  unfold hitsBest toScore at h
  rw [List.mem_map] at h
  obtain ⟨⟨⟨⟨c, st, len⟩, t⟩, k⟩, hm, rfl⟩ := h
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨rfl, hc, hpk, hk⟩ := hitsCSF_sound gbs R _ _ _ _ _ hn hp _ _ hm
    simp only [cwP, cwG, hc, if_true] at hpk ⊢
    exact ⟨⟨by omega, by rw [hpk]⟩, by omega⟩
  · obtain ⟨rfl, hc, hpk, hk⟩ := hitsCSF_sound gbs _ _ _ _ _ _ hrn hp _ _ hm
    simp only [cwP, cwG, hc, if_true] at hpk ⊢
    exact ⟨⟨by omega, by rw [hpk]⟩, by omega⟩

/-- Anchor facts of a finished search (both strands). -/
def StOk (gbs : Array ByteArray) (R : ByteArray) (r : Best × CS × CS) : Prop :=
  (∃ J, r.1.pen < 4 * pop4 J ∧ ∀ c, c < gbs.size → AnchorsM (maskJ gbs[c]! R J) r.2.1.as[c]!) ∧
  (∃ J, r.1.pen < 4 * pop4 J ∧ ∀ c, c < gbs.size → AnchorsM (maskJ gbs[c]! (revCompB R) J) r.2.2.as[c]!)

theorem incA_anchors (m : Nat → Nat) (as : Array Nat) (h : AnchorsM m as) : IncA as :=
  incA_of as (h.sorted.imp fun {a b} hab => by
    show a < b
    apply Classical.byContradiction; intro hn
    have : b / 16 ≤ a / 16 := Nat.div_le_div_right (by omega)
    omega)

/-- Mate `R`'s hits at its best penalty that pair properly with a hit of the other
mate (`R2`) at its best penalty are listed. -/
theorem hitsBest_complete (g : Genome) (m : List Char) (gbs : Array ByteArray) (lo hi : Nat) (R R2 : ByteArray)
    (r o : Best × CS × CS) (hg : GenomeBytes gbs g) (hr : Encodes R m) (hn : 100 ≤ R.size) (hn' : R.size ≤ 103)
    (hn2 : 100 ≤ R2.size) (hn2' : R2.size ≤ 103) (hp : r.1.pen ≤ 12) (hpo : o.1.pen ≤ 12)
    (sr : StOk gbs R r) (so : StOk gbs R2 o) (x : Placement × Int) (hx : x ∈ hitsBoth sc0 (-12) g m)
    (hl : -(r.1.pen : Int) ≤ x.2) (q : Placement) (hq : cwP R2 gbs q.2 q.1 ≤ o.1.pen)
    (hpq : properPair lo hi x.1 q = true ∨ properPair lo hi q x.1 = true) :
    x ∈ hitsBest gbs (hi + 128) R r o := by
  have hrn : 100 ≤ (revCompB R).size := by rw [revCompB_size]; exact hn
  have hrn2 : 100 ≤ (revCompB R2).size := by rw [revCompB_size]; exact hn2
  rw [mem_hitsBoth_cwP g m gbs R hg hr] at hx
  obtain ⟨p, s⟩ := x
  simp only at hx hl hpq ⊢
  obtain ⟨hx12, rfl⟩ := hx
  obtain ⟨hc, hpe⟩ := cwP_hit R gbs p.2 p.1 hx12
  obtain ⟨hqc, hqe⟩ := cwP_hit R2 gbs q.2 q.1 (by omega)
  have lp := penB_len _ _ _ _ (by rw [hpe]; exact hx12)
  have lq := penB_len _ _ _ _ (by rw [hqe]; omega)
  have hsz : ∀ t : Strand, (if t = .fwd then R else revCompB R).size = R.size := fun t => by
    cases t <;> simp [revCompB_size]
  have hsz2 : ∀ t : Strand, (if t = .fwd then R2 else revCompB R2).size = R2.size := fun t => by
    cases t <;> simp [revCompB_size]
  rw [hsz] at lp; rw [hsz2] at lq
  obtain ⟨hch, hst, hd1, hd2⟩ : p.1.chr = q.1.chr ∧ p.2 ≠ q.2 ∧ p.1.start ≤ q.1.start + hi + 106 ∧
      q.1.start ≤ p.1.start + hi + 106 := by
    rcases hpq with h | h
    · exact proper_close lo hi p q h (by omega) (by omega)
    · obtain ⟨a1, a2, a3, a4⟩ := proper_close lo hi q p h (by omega) (by omega)
      exact ⟨a1.symm, Ne.symm a2, a4, a3⟩
  obtain ⟨⟨c, st, len⟩, t⟩ := p
  obtain ⟨⟨c', st', len'⟩, t'⟩ := q
  simp only at hch hst hd1 hd2 hc hpe hqe hqc hq hl hx12 ⊢
  subst hch
  unfold hitsBest toScore
  rw [List.mem_map]
  refine ⟨((⟨c, st, len⟩, t), cwP R gbs t ⟨c, st, len⟩), ?_, rfl⟩
  obtain ⟨⟨Jf, cf, af⟩, ⟨Jr, cr, ar⟩⟩ := sr
  obtain ⟨⟨Kf, kf, bf⟩, ⟨Kr, kr, br⟩⟩ := so
  cases t <;> cases t' <;> simp only [ne_eq, not_true_eq_false, reduceCtorEq, not_false_eq_true] at hst
  · -- forward mate, partner on the reverse strand
    simp only [if_true] at hpe
    simp only [reduceCtorEq, if_false] at hqe
    apply List.mem_append_left
    obtain ⟨e', he', h1, h2, -⟩ := anchor_near (revCompB R2) gbs[c]! o.2.2.as[c]! Kr st' len' o.1.pen hrn2 hpo kr
      (br c hc) (by rw [hqe]; exact hq)
    have := hitsCSF_complete gbs R .fwd r.2.1 o.2.2 (hi + 128) r.1.pen Jf hn hp cf c st len hc (af c hc)
      (incA_anchors _ _ (br c hc)) (by rw [hpe]; omega) ⟨e', he', by simp only [BIAS] at *; omega,
        by simp only [BIAS] at *; omega⟩
    rwa [hpe] at this
  · -- reverse mate, partner on the forward strand
    simp only [reduceCtorEq, if_false] at hpe
    simp only [if_true] at hqe
    apply List.mem_append_right
    obtain ⟨e', he', h1, h2, -⟩ := anchor_near R2 gbs[c]! o.2.1.as[c]! Kf st' len' o.1.pen hn2 hpo kf
      (bf c hc) (by rw [hqe]; exact hq)
    have := hitsCSF_complete gbs (revCompB R) .rev r.2.2 o.2.1 (hi + 128) r.1.pen Jr hrn hp cr c st len hc
      (ar c hc) (incA_anchors _ _ (bf c hc)) (by rw [hpe]; omega) ⟨e', he', by simp only [BIAS] at *; omega,
        by simp only [BIAS] at *; omega⟩
    rwa [hpe] at this

theorem stOk_of {L P : Type} [Inhabited P] (lk : Look L P) (ix : L) (G : ByteArray) (offs : Array Nat)
    (gbs : Array ByteArray) (R : ByteArray) (rf : Bool) (hn : 100 ≤ R.size) (hcat : catOk G offs gbs = true)
    (hlk : ∀ R' : ByteArray, ∀ j, j < 4 → LookOk G R' j (lk.look ix G R' j (lk.prep ix (seedHash R' j))))
    (hp : (mapChromsCS lk ix G offs gbs R rf).1.pen ≤ 12) : StOk gbs R (mapChromsCS lk ix G offs gbs R rf) := by
  obtain ⟨⟨Jf, -, cf, af⟩, ⟨Jr, -, cr, ar⟩⟩ := mapChromsCS_ok lk ix G offs gbs R rf hn hcat hlk hp
  exact ⟨⟨Jf, cf, af⟩, ⟨Jr, cr, ar⟩⟩

/-- **The fallback is exact.** -/
theorem pairSlowU_eq {L P : Type} [Inhabited P] (lk : Look L P) (lo hi : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (g : Genome) (m1 m2 : List Char) (gbs : Array ByteArray) (R1 R2 : ByteArray) (rf1 rf2 : Bool)
    (hg : GenomeBytes gbs g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hcat : catOk G offs gbs = true)
    (hlk : ∀ R' : ByteArray, ∀ j, j < 4 → LookOk G R' j (lk.look ix G R' j (lk.prep ix (seedHash R' j))))
    (hn1 : 100 ≤ R1.size) (hn2 : 100 ≤ R2.size) (hn1' : R1.size ≤ 103) (hn2' : R2.size ≤ 103)
    (hl1 : (mapChromsCS lk ix G offs gbs R1 rf1).1.pen ≤ 12) (hl2 : (mapChromsCS lk ix G offs gbs R2 rf2).1.pen ≤ 12) :
    pairSlowU lk lo hi ix G offs gbs R1 R2 (mapChromsCS lk ix G offs gbs R1 rf1) (mapChromsCS lk ix G offs gbs R2 rf2) =
      pairSpecU sc0 (-12) lo hi g m1 m2 := by
  have E := fun (R : ByteArray) (m : List Char) (hr : Encodes R m) (hn : 100 ≤ R.size) (lim : Nat)
    (hlim : lim ≤ 12) => mem_toScore_hitsL lk ix G offs g m gbs R lim hg hr hcat hlk hn hlim
  have B := fun (R : ByteArray) (m : List Char) (hr : Encodes R m) (hn : 100 ≤ R.size) (rf : Bool) =>
    le_best g m gbs R (mapChromsCS lk ix G offs gbs R rf).1 hg hr (by
      rw [mapChromsCS_fst]
      exact mapChromsC_inv lk ix G offs gbs R rf hn hcat hlk)
  have s1 := stOk_of lk ix G offs gbs R1 rf1 hn1 hcat hlk hl1
  have s2 := stOk_of lk ix G offs gbs R2 rf2 hn2 hcat hlk hl2
  have b1 := B R1 m1 h1 hn1 rf1
  have b2 := B R2 m2 h2 hn2 rf2
  unfold pairSlowU pairSpecU
  simp only []
  generalize mapChromsCS lk ix G offs gbs R1 rf1 = r1 at hl1 s1 b1 ⊢
  generalize mapChromsCS lk ix G offs gbs R2 rf2 = r2 at hl2 s2 b2 ⊢
  split
  · apply bestPairF_eq lo hi _ _ _ _ (fun_hitsBoth g m1) (fun_hitsBoth g m2)
    · intro x; rw [E R1 m1 h1 hn1 12 (Nat.le_refl _)]
      constructor
      · exact fun h => h.1
      · intro h; exact ⟨h, by have := ((mem_hitsBoth_sc0 g m1 x.1 x.2).1 h).2.2; omega⟩
    · intro x; rw [E R2 m2 h2 hn2 12 (Nat.le_refl _)]
      constructor
      · exact fun h => h.1
      · intro h; exact ⟨h, by have := ((mem_hitsBoth_sc0 g m2 x.1 x.2).1 h).2.2; omega⟩
  · next hne =>
    have hcw : ∀ (R : ByteArray) (m : List Char), Encodes R m → ∀ x ∈ hitsBoth sc0 (-12) g m,
        x.2 = -(cwP R gbs x.1.2 x.1.1 : Int) ∧ cwP R gbs x.1.2 x.1.1 ≤ 12 := fun R m hr x hx => by
      have := (mem_hitsBoth_cwP g m gbs R hg hr x).1 hx; exact ⟨this.2, this.1⟩
    refine bestPair_restrict lo hi _ _ _ (-(r1.1.pen : Int) + -(r2.1.pen : Int)) (fun_hitsBoth g m1)
      (fun_hitsBoth g m2) (fun x => ?_) (fun x hx => ?_) (by simpa using hne)
    · rw [mem_pairsOf, mem_pairsOf]
      constructor
      · rintro ⟨ha, hb, hp⟩
        have u1 := hitsBest_sound g m1 gbs _ R1 r1 r2 hg h1 hn1 hl1 _ ha
        have u2 := hitsBest_sound g m2 gbs _ R2 r2 r1 hg h2 hn2 hl2 _ hb
        exact ⟨⟨u1.1, u2.1, hp⟩, by have := u1.2; have := u2.2; omega⟩
      · rintro ⟨⟨ha, hb, hp⟩, hs⟩
        have e1 := b1 _ ha; have e2 := b2 _ hb
        have c1 := hcw R1 m1 h1 _ ha; have c2 := hcw R2 m2 h2 _ hb
        refine ⟨hitsBest_complete g m1 gbs lo hi R1 R2 r1 r2 hg h1 hn1 hn1' hn2 hn2' hl1 hl2 s1 s2 _ ha
            (by omega) x.2.1 (by omega) (Or.inl hp),
          hitsBest_complete g m2 gbs lo hi R2 R1 r2 r1 hg h2 hn2 hn2' hn1 hn1' hl2 hl1 s2 s1 _ hb
            (by omega) x.1.1 (by omega) (Or.inr hp), hp⟩
    · rw [mem_pairsOf] at hx
      have := b1 _ hx.1; have := b2 _ hx.2.1; omega

/-! ## Top theorems -/

theorem pairFastU_eq_pairSpecU {L P : Type} [Inhabited P] (lk : Look L P) (lo hi : Nat) (ix : L)
    (G : ByteArray) (offs : Array Nat) (g : Genome) (m1 m2 : List Char) (gbs : Array ByteArray)
    (R1 R2 : ByteArray) (hg : GenomeBytes gbs g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2)
    (hcat : catOk G offs gbs = true)
    (hlk : ∀ R' : ByteArray, ∀ j, j < 4 → LookOk G R' j (lk.look ix G R' j (lk.prep ix (seedHash R' j))))
    (hok1 : fastOk R1 = true) (hok2 : fastOk R2 = true) :
    pairFastU lk lo hi ix G offs gbs R1 R2 = pairSpecU sc0 (-12) lo hi g m1 m2 := by
  have hn1 : 100 ≤ R1.size := by unfold fastOk q at hok1; simp at hok1; omega
  have hn2 : 100 ≤ R2.size := by unfold fastOk q at hok2; simp at hok2; omega
  have hn1' : R1.size ≤ 103 := by unfold fastOk q at hok1; simp at hok1; omega
  have hn2' : R2.size ≤ 103 := by unfold fastOk q at hok2; simp at hok2; omega
  unfold pairFastU
  simp only []
  have i1 := mapChromsC_inv lk ix G offs gbs R1 false hn1 hcat hlk
  rw [← mapChromsCS_fst] at i1
  generalize hrf : decide ((mapChromsCS lk ix G offs gbs R1 false).1.chr < gbs.size) = rf
  have i2 := mapChromsC_inv lk ix G offs gbs R2 rf hn2 hcat hlk
  rw [← mapChromsCS_fst] at i2
  split
  · next hp =>
    unfold pairSpecU; rw [no_hit g m1 gbs R1 _ hg h1 i1 hp, bestPair_nil_left]
  · split
    · next hp =>
      unfold pairSpecU; rw [no_hit g m2 gbs R2 _ hg h2 i2 hp, bestPair_nil_right]
    · split
      · next a b ha hb =>
        split
        · next hp =>
          rw [decodeJ_eq_mapSpecBoth g m1 gbs R1 _ hg h1 i1] at ha
          rw [decodeJ_eq_mapSpecBoth g m2 gbs R2 _ hg h2 i2] at hb
          exact (pairSpecU_of_unique lo hi g m1 m2 a b ha hb hp).symm
        · exact pairSlowU_eq lk lo hi ix G offs g m1 m2 gbs R1 R2 _ _ hg h1 h2 hcat hlk hn1 hn2 hn1' hn2'
            (by omega) (by omega)
      · exact pairSlowU_eq lk lo hi ix G offs g m1 m2 gbs R1 R2 _ _ hg h1 h2 hcat hlk hn1 hn2 hn1' hn2'
          (by omega) (by omega)

/-- Through the hashed index over the concatenation, checked at run time. -/
theorem pairFastU_hashed_eq_pairSpecU (lo hi : Nat) (ix : HIdx) (G : ByteArray) (offs : Array Nat) (g : Genome)
    (m1 m2 : List Char) (gbs : Array ByteArray) (R1 R2 : ByteArray) (hg : GenomeBytes gbs g)
    (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hcat : catOk G offs gbs = true) (hchk : checkIdx ix G = true)
    (hok1 : fastOk R1 = true) (hok2 : fastOk R2 = true) :
    pairFastU hLook lo hi ix G offs gbs R1 R2 = pairSpecU sc0 (-12) lo hi g m1 m2 :=
  pairFastU_eq_pairSpecU hLook lo hi ix G offs g m1 m2 gbs R1 R2 hg h1 h2 hcat
    (fun R' j hj => hLook_ok ix G R' j hj hchk) hok1 hok2

/-- Through the minimizer index over the concatenation, checked at run time. -/
theorem pairFastU_mz_eq_pairSpecU (lo hi : Nat) (ix : Mz.MzIdx) (G : ByteArray) (offs : Array Nat) (g : Genome)
    (m1 m2 : List Char) (gbs : Array ByteArray) (R1 R2 : ByteArray) (hg : GenomeBytes gbs g)
    (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hcat : catOk G offs gbs = true) (hchk : Mz.check2 ix G = true)
    (hok1 : fastOk R1 = true) (hok2 : fastOk R2 = true) :
    pairFastU mzL lo hi ix G offs gbs R1 R2 = pairSpecU sc0 (-12) lo hi g m1 m2 :=
  pairFastU_eq_pairSpecU mzL lo hi ix G offs g m1 m2 gbs R1 R2 hg h1 h2 hcat
    (fun R' j hj => mzLook_ok ix G R' j hj (by rw [← Mz.check2_eq]; exact hchk)) hok1 hok2

end MapSpec.Fast

#print axioms MapSpec.Fast.pairSlowU_eq
#print axioms MapSpec.Fast.pairFastU_eq_pairSpecU
#print axioms MapSpec.Fast.pairFastU_hashed_eq_pairSpecU
#print axioms MapSpec.Fast.pairFastU_mz_eq_pairSpecU
