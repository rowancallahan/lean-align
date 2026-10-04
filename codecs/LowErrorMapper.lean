import MapSpec                    -- the mapping specification (spec/, draft)
import MapperDefs                 -- pool
import MapperGapless              -- pool: gapless score, gap bound, gapless seed lemma
import SeedMapper                 -- the proved seed-and-index mapper (fallback)

/-!
# Codec `mapLowError`: exact Hamming fast path for near-perfect reads

The algorithm, then the theorems against `mapSpec`, then the proof.

Each seed hit gives one anchor: the window of the read's length that puts the
seed exactly where it was found.  The read is compared letter by letter with
each anchor window (stopping at `gapCap sc + 1` mismatches).  When the best
gapless score `S` found this way is above `gapOpen + gapExtend` and at least
`T`, every window that ties or beats `S` is a gapless window of the read's
length at one of these anchors, and its optimal score is its gapless score;
so the answer is decided from the anchors alone.  Otherwise the read goes to
`mapWith` (banded DP).
-/

namespace MapSpec

open AlignmentSpec

/-! ## The algorithm -/

/-- One window per seed hit: the read's length, starting where the seed hit
puts the read's first letter. -/
def anchorWindows (lookup : List Char → List (Nat × Nat)) (l0 : Nat) (read : List Char) (k : Nat) :
    List Window :=
  (List.range (k + 1)).flatMap fun j =>
    (lookup ((read.drop (j * (read.length / (k + 1)))).take l0)).filterMap fun place =>
      if j * (read.length / (k + 1)) ≤ place.2 then
        some { chr := place.1, start := place.2 - j * (read.length / (k + 1)), len := read.length }
      else none

/-- Mismatches of `ra[i..i+fuel)` against `ca[st+i..)`, added to `acc`;
`none` as soon as the count exceeds `cap`. -/
def hamLoop (ra ca : Array Char) (st cap : Nat) : Nat → Nat → Nat → Option Nat
  | 0, _, acc => some acc
  | fuel + 1, i, acc =>
    match ra[i]?, ca[st + i]? with
    | some x, some y =>
      let acc' := if x = y then acc else acc + 1
      if cap < acc' then none else hamLoop ra ca st cap fuel (i + 1) acc'
    | _, _ => none

/-- Gapless score of the read against a window of its length with at most
`cap` mismatches; `none` otherwise. -/
def gaplessA (sc : Scoring) (ra : Array Char) (ga : Array (Array Char)) (cap : Nat) (w : Window) :
    Option Int :=
  match ga[w.chr]? with
  | some ca =>
    if w.len = ra.size ∧ w.start + w.len ≤ ca.size then
      (hamLoop ra ca w.start cap ra.size 0 0).map fun h =>
        sc.matchScore * ((ra.size - h : Nat) : Int) + sc.mismatchScore * (h : Int)
    else none
  | none => none

/-- The anchors that pass the Hamming check, with their gapless scores. -/
def lowErrorHits (lookup : List Char → List (Nat × Nat)) (sc : Scoring) (ga : Array (Array Char))
    (l0 k : Nat) (read : List Char) (ra : Array Char) : List (Window × Int) :=
  (anchorWindows lookup l0 read k).filterMap fun w => (gaplessA sc ra ga (gapCap sc) w).map (w, ·)

/-- Decide from the anchors when the best gapless score is above
`gapOpen + gapExtend` and at least `T`; otherwise `mapWith`. -/
def mapLowError (lookup : List Char → List (Nat × Nat)) (score : Window → Option Int)
    (ga : Array (Array Char)) (sc : Scoring) (l0 : Nat) (T : Int) (k : Nat) (g : Genome)
    (read : List Char) : Option (Window × Int) :=
  if 0 < l0 ∧ l0 ≤ read.length / (k + 1) then
    let scored := lowErrorHits lookup sc ga l0 k read read.toArray
    match (scored.map (·.2)).max? with
    | some S =>
      if gapCost1 sc < S ∧ T ≤ S then selectUnique (scored.filter fun a => decide (S ≤ a.2))
      else mapWith lookup score l0 T k g read
    | none => mapWith lookup score l0 T k g read
  else mapWith lookup score l0 T k g read

/-- The genome as arrays, one per chromosome. -/
def genomeArrays (g : Genome) : Array (Array Char) :=
  (g.map fun c => c.seq.toArray).toArray

/-- Map one read through an index, with the fast path. -/
def mapLowErrorIndex (sc : Scoring) (T : Int) (idx : Index) (ga : Array (Array Char))
    (read : List Char) : Option (Window × Int) :=
  mapLowError idx.lookup (kernelScore sc read idx.genome) ga sc idx.l0 T (errBound sc T) idx.genome read

/-- Build the index and the genome arrays once, then map every read. -/
def mapReadsLowError (l0 : Nat) (sc : Scoring) (T : Int) (g : Genome) (reads : List (List Char)) :
    List (Option (Window × Int)) :=
  let idx := buildIndex l0 g
  let ga := genomeArrays g
  reads.map (mapLowErrorIndex sc T idx ga)

/-! ## The theorems

    LookupComplete g l0 lookup → (∀ w, score w = windowScore sc read g w) →
      mapLowError lookup score (genomeArrays g) sc l0 T (errBound sc T) g read
        = mapSpec sc T g read                                               (mapLowError_eq_mapSpec)
    mapReadsLowError l0 sc T g reads = reads.map (mapSpec sc T g)          (mapReadsLowError_eq_mapSpec)

for every scoring with `ValidScoring sc`.  They are at the end of this file. -/

/-! ## Proof -/

/-- List form of the gapless check. -/
def gaplessRef (sc : Scoring) (read : List Char) (g : Genome) (cap : Nat) (w : Window) : Option Int :=
  match windowSeq g w with
  | some ys => if ys.length = read.length ∧ hamming read ys ≤ cap then some (gaplessScore sc read ys)
               else none
  | none => none

theorem hamLoop_eq (ra ca : Array Char) (st cap : Nat) (fuel : Nat) :
    ∀ i acc, i + fuel ≤ ra.size → st + i + fuel ≤ ca.size → acc ≤ cap →
      hamLoop ra ca st cap fuel i acc =
        if acc + hamming ((ra.toList.drop i).take fuel) ((ca.toList.drop (st + i)).take fuel) ≤ cap
        then some (acc + hamming ((ra.toList.drop i).take fuel) ((ca.toList.drop (st + i)).take fuel))
        else none := by
  induction fuel with
  | zero => intro i acc _ _ hacc; simp [hamLoop, hamming, hacc]
  | succ fuel ih =>
    intro i acc h1 h2 hacc
    have hi : i < ra.size := by omega
    have hj : st + i < ca.size := by omega
    have hr : ra.toList.drop i = ra[i] :: ra.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hi)]; simp
    have hc : ca.toList.drop (st + i) = ca[st + i] :: ca.toList.drop (st + (i + 1)) := by
      rw [List.drop_eq_getElem_cons (by simpa using hj)]; simp [Nat.add_assoc]
    simp only [hamLoop, Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hj, hr, hc,
      List.take_succ_cons, hamming]
    by_cases hxy : ra[i] = ca[st + i]
    · simp only [hxy, if_true]
      rw [if_neg (by omega), ih (i + 1) acc (by omega) (by omega) hacc]
      simp only [Nat.zero_add]
    · simp only [hxy, if_false]
      by_cases hcap : cap < acc + 1
      · rw [if_pos hcap, if_neg (by omega)]
      · rw [if_neg hcap, ih (i + 1) (acc + 1) (by omega) (by omega) (by omega)]
        have : acc + (1 + hamming (List.take fuel (List.drop (i + 1) ra.toList))
            (List.take fuel (List.drop (st + (i + 1)) ca.toList))) =
            acc + 1 + hamming (List.take fuel (List.drop (i + 1) ra.toList))
            (List.take fuel (List.drop (st + (i + 1)) ca.toList)) := by omega
        rw [this]

theorem gaplessA_eq (sc : Scoring) (read : List Char) (g : Genome) (cap : Nat) (w : Window) :
    gaplessA sc read.toArray (genomeArrays g) cap w = gaplessRef sc read g cap w := by
  unfold gaplessA gaplessRef windowSeq genomeArrays
  simp only [List.getElem?_toArray, List.getElem?_map]
  cases hc : g[w.chr]? with
  | none => rfl
  | some chr =>
    simp only [Option.map_some, List.size_toArray]
    by_cases hfit : w.start + w.len ≤ chr.seq.length
    · rw [if_pos hfit]
      have hyl : ((chr.seq.drop w.start).take w.len).length = w.len := by
        simp; omega
      by_cases hn : w.len = read.length
      · rw [if_pos ⟨hn, hfit⟩]
        rw [hamLoop_eq _ _ _ _ _ 0 0 (by simp) (by simp; omega) (Nat.zero_le _)]
        simp only [Nat.zero_add, Nat.add_zero, List.drop_zero, List.take_length, hn]
        split <;> simp [gaplessScore] <;> omega
      · rw [if_neg (by omega)]; simp [hyl, hn]
    · rw [if_neg (by omega)]; simp [hfit]

theorem gaplessRef_some (sc : Scoring) (read : List Char) (g : Genome) (cap : Nat) (w : Window)
    (s : Int) (h : gaplessRef sc read g cap w = some s) :
    ∃ ys, windowSeq g w = some ys ∧ ys.length = read.length ∧ gaplessScore sc read ys = s := by
  unfold gaplessRef at h
  cases hw : windowSeq g w with
  | none => rw [hw] at h; cases h
  | some ys =>
    rw [hw] at h
    simp only at h
    split at h
    · rename_i hc; cases h; exact ⟨ys, rfl, hc.1, rfl⟩
    · cases h

/-- A passing anchor scoring above `gapOpen + gapExtend` has that score as its window score. -/
theorem windowScore_of_gaplessRef (sc : Scoring) (hv : ValidScoring sc) (read : List Char) (g : Genome)
    (cap : Nat) (w : Window) (s : Int) (h : gaplessRef sc read g cap w = some s) (hG : gapCost1 sc < s) :
    windowScore sc read g w = some s := by
  obtain ⟨ys, hw, hl, hs⟩ := gaplessRef_some sc read g cap w s h
  unfold windowScore
  rw [hw]
  obtain ⟨⟨p, bs⟩, hb⟩ := getBestAlignment_returns_some sc read ys
  have h1 := gapless_le_best sc read ys p bs hb hl.symm
  have h2 := best_gapless sc hv read ys p bs hb (by omega)
  simp [hb, h2.2.2, hs]

/-- **Consequence.**  A window whose score is above `gapOpen + gapExtend` has
the read's length, its score is its gapless score, and it passes the Hamming
check with cap `gapCap sc`. -/
theorem gaplessRef_of_windowScore (sc : Scoring) (hv : ValidScoring sc) (read : List Char) (g : Genome)
    (w : Window) (s : Int) (h : windowScore sc read g w = some s) (hG : gapCost1 sc < s) :
    gaplessRef sc read g (gapCap sc) w = some s := by
  unfold windowScore at h
  unfold gaplessRef
  cases hw : windowSeq g w with
  | none => rw [hw] at h; cases h
  | some ys =>
    rw [hw] at h
    simp only at h
    cases hb : getBestAlignment sc read ys with
    | none => rw [hb] at h; cases h
    | some best =>
      rw [hb] at h
      obtain ⟨p, bs⟩ := best
      have hbs : bs = s := by simpa using h
      subst hbs
      obtain ⟨hl, -, hgs⟩ := best_gapless sc hv read ys p bs hb hG
      have hcap : hamming read ys ≤ gapCap sc := by
        apply Classical.byContradiction
        intro hc
        have := gaplessScore_lt_of_cap sc hv read ys (by omega)
        omega
      simp [hl, hcap, hgs]

/-- **Coverage.**  Every window scoring above `gapOpen + gapExtend` and at least
`T` is an anchor window: its clean seed sits at exactly its own offset. -/
theorem mem_anchorWindows (lookup : List Char → List (Nat × Nat)) (l0 : Nat) (sc : Scoring)
    (hv : ValidScoring sc) (T : Int) (g : Genome) (hl : LookupComplete g l0 lookup)
    (read : List Char) (hcond : 0 < l0 ∧ l0 ≤ read.length / (errBound sc T + 1))
    (w : Window) (s : Int) (hscore : windowScore sc read g w = some s) (hG : gapCost1 sc < s)
    (hT : T ≤ s) :
    w ∈ anchorWindows lookup l0 read (errBound sc T) := by
  obtain ⟨c, st, len⟩ := w
  unfold windowScore at hscore
  cases hseq : windowSeq g ⟨c, st, len⟩ with
  | none => rw [hseq] at hscore; cases hscore
  | some ys =>
    rw [hseq] at hscore
    simp only at hscore
    cases hbest : getBestAlignment sc read ys with
    | none => rw [hbest] at hscore; cases hscore
    | some best =>
      rw [hbest] at hscore
      obtain ⟨path, bs⟩ := best
      have hsb : bs = s := by simpa using hscore
      subst hsb
      obtain ⟨-, hws⟩ := getBestAlignment_returns_a_valid_walk sc read ys path bs hbest
      obtain ⟨hlen, hp, -⟩ := best_gapless sc hv read ys path bs hbest hG
      rw [hp] at hws
      obtain ⟨j, hj, hjq, hseed⟩ :=
        gapless_clean_seed sc hv T read ys hlen (by rw [hws]; exact hT)
      generalize hq : read.length / (errBound sc T + 1) = q at *
      unfold windowSeq at hseq
      cases hc : g[c]? with
      | none => simp [hc] at hseq
      | some chromosome =>
        simp only [hc] at hseq
        split at hseq
        · next hfit =>
          have hys : ys = (chromosome.seq.drop st).take len := by simpa using hseq.symm
          have hyl : ys.length = len := by
            rw [hys, List.length_take, List.length_drop]; omega
          simp only [anchorWindows, hq]
          rw [List.mem_flatMap]
          refine ⟨j, List.mem_range.mpr (by omega), ?_⟩
          rw [List.mem_filterMap]
          refine ⟨(c, st + j * q), ?_, ?_⟩
          · have hkey : (read.drop (j * q)).take l0 = (chromosome.seq.drop (st + j * q)).take l0 := by
              have h1 := congrArg (List.take l0) hseed
              rw [List.take_take, List.take_take, Nat.min_eq_left hcond.2] at h1
              rw [← h1, hys, take_drop_window _ _ _ _ _ (by omega)]
            rw [hkey]
            exact hl c chromosome (st + j * q) hc (by omega)
          · simp only
            rw [if_pos (by omega)]
            have : st + j * q - j * q = st := by omega
            rw [this, hlen, hyl]
        · cases hseq

theorem mem_allWindows_of_score (sc : Scoring) (read : List Char) (g : Genome) (w : Window) (s : Int)
    (h : windowScore sc read g w = some s) : w ∈ allWindows g := by
  apply (mem_allWindows g w).mpr
  unfold windowScore at h
  cases hw : windowSeq g w with
  | none => rw [hw] at h; cases h
  | some _ => rfl

theorem mem_lowErrorHits (lookup : List Char → List (Nat × Nat)) (sc : Scoring) (g : Genome)
    (l0 k : Nat) (read : List Char) (w : Window) (s : Int) :
    (w, s) ∈ lowErrorHits lookup sc (genomeArrays g) l0 k read read.toArray ↔
      w ∈ anchorWindows lookup l0 read k ∧ gaplessRef sc read g (gapCap sc) w = some s := by
  unfold lowErrorHits
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨w', hw', h⟩
    cases hga : gaplessA sc read.toArray (genomeArrays g) (gapCap sc) w' with
    | none => rw [hga] at h; cases h
    | some s' =>
      rw [hga] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hw', by rw [← gaplessA_eq]; exact hga⟩
  · rintro ⟨hw, h⟩
    exact ⟨w, hw, by rw [gaplessA_eq, h]; rfl⟩

/-- The general theorem: with a complete lookup and a correct fallback scorer,
the fast-path mapper returns the specification's answer. -/
theorem mapLowError_eq_mapSpec (lookup : List Char → List (Nat × Nat)) (score : Window → Option Int)
    (l0 : Nat) (sc : Scoring) (hv : ValidScoring sc) (T : Int) (g : Genome) (read : List Char)
    (hl : LookupComplete g l0 lookup) (hs : ∀ w, score w = windowScore sc read g w) :
    mapLowError lookup score (genomeArrays g) sc l0 T (errBound sc T) g read = mapSpec sc T g read := by
  have hslow := mapWith_eq_mapSpec lookup score l0 sc hv T g read hl hs
  unfold mapLowError
  split
  · rename_i hcond
    simp only
    split
    · rename_i S hmax
      split
      · rename_i hSG
        have hfunH : ∀ a ∈ hitsOf (windowScore sc read g) T (allWindows g),
            ∀ b ∈ hitsOf (windowScore sc read g) T (allWindows g), a.1 = b.1 → a.2 = b.2 := by
          rintro ⟨w, s⟩ ha ⟨w', s'⟩ hb hww
          rw [mem_hitsOf] at ha hb
          simp only at hww
          subst hww
          have := ha.2.1.symm.trans hb.2.1
          simpa using this
        have hex : ∃ a ∈ hitsOf (windowScore sc read g) T (allWindows g), S ≤ a.2 := by
          obtain ⟨⟨w0, s0⟩, hm0, hs0⟩ := List.mem_map.mp (List.max?_mem hmax)
          simp only at hs0
          subst hs0
          rw [mem_lowErrorHits] at hm0
          have hws := windowScore_of_gaplessRef sc hv read g _ w0 s0 hm0.2 hSG.1
          exact ⟨(w0, s0), (mem_hitsOf _ _ _ _ _).mpr
            ⟨mem_allWindows_of_score sc read g w0 s0 hws, hws, hSG.2⟩, Int.le_refl _⟩
        unfold mapSpec
        rw [← selectUnique_filter _ S hfunH hex]
        apply selectUnique_congr
        · rintro ⟨w, s⟩
          simp only [List.mem_filter, decide_eq_true_eq, mem_lowErrorHits, mem_hitsOf, and_assoc]
          constructor
          · rintro ⟨-, hr, hSs⟩
            have hws := windowScore_of_gaplessRef sc hv read g _ w s hr (by omega)
            exact ⟨mem_allWindows_of_score sc read g w s hws, hws, by omega, hSs⟩
          · rintro ⟨-, hws, hT, hSs⟩
            exact ⟨mem_anchorWindows lookup l0 sc hv T g hl read hcond w s hws (by omega) hT,
              gaplessRef_of_windowScore sc hv read g w s hws (by omega), hSs⟩
        · rintro ⟨w, s⟩ ha ⟨w', s'⟩ hb hww
          simp only [List.mem_filter, mem_lowErrorHits] at ha hb
          simp only at hww
          subst hww
          have := ha.1.2.symm.trans hb.1.2
          simpa using this
      · exact hslow
    · exact hslow
  · exact hslow

/-- **One index, many reads.**  Every read gets the specification's answer. -/
theorem mapReadsLowError_eq_mapSpec (l0 : Nat) (sc : Scoring) (hv : ValidScoring sc) (T : Int)
    (g : Genome) (reads : List (List Char)) :
    mapReadsLowError l0 sc T g reads = reads.map (mapSpec sc T g) := by
  unfold mapReadsLowError
  apply List.map_congr_left
  intro read _
  exact mapLowError_eq_mapSpec _ _ l0 sc hv T g read (buildIndex_complete l0 g) (kernelScore_eq sc read g)

end MapSpec

#print axioms MapSpec.mapLowError_eq_mapSpec
#print axioms MapSpec.mapReadsLowError_eq_mapSpec
