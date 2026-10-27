import MapSpec                    -- the mapping specification (spec/, draft)
import MapperDefs                 -- pool
import MapperGapless              -- pool: gapless score, gap bound, gapless seed lemma
import MapperOneIndel             -- pool: walks scoring gapOpen + gapExtend are one indel
import SeedMapper                 -- the proved seed-and-index mapper (fallback)

/-!
# Codec `mapLowError`: exact Hamming fast path for near-perfect reads

The algorithm, then the theorems against `mapSpec`, then the proof.

Each seed hit gives one anchor: the window of the read's length that puts the
seed exactly where it was found.  The read is compared letter by letter with
each anchor window (stopping at `gapCap sc + 1` mismatches).  Let `S` be the
best gapless score found and `G = gapOpen + gapExtend`.

* `S > G` and `S ≥ T`: every window that ties or beats `S` is a gapless window
  of the read's length at one of these anchors, and its optimal score is its
  gapless score; the answer is decided from the anchors alone.
* otherwise, when `matchScore = 0` and `T ≤ G` (`gapStep`): no window scores
  above `G`; the windows scoring exactly `G` are the anchors with gapless score
  `G` and the windows that differ from the read by one deleted or inserted
  letter (checked letter by letter at seeds 0 and 1, shifted by one).  If there
  is any, the answer is decided from them.
* otherwise the read goes to `mapWith` (banded DP).
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

/-- `p[a..a+m) = q[b..b+m)`. -/
def eqLoop (p q : Array Char) (a b : Nat) : Nat → Bool
  | 0 => true
  | m + 1 =>
    match p[a]?, q[b]? with
    | some x, some y => if x = y then eqLoop p q (a + 1) (b + 1) m else false
    | _, _ => false

/-- `p[a..a+m+1)` with one letter removed is `q[b..b+m)`: skip the common
prefix, then the rest must match shifted by one. -/
def delLoop (p q : Array Char) (a b : Nat) : Nat → Bool
  | 0 => true
  | m + 1 =>
    match p[a]?, q[b]? with
    | some x, some y => if x = y then delLoop p q (a + 1) (b + 1) m else eqLoop p q (a + 1) b (m + 1)
    | _, _ => false

/-- The window is the read with one letter deleted, or the read is the window
with one letter deleted. -/
def indelA (ra : Array Char) (ga : Array (Array Char)) (w : Window) : Bool :=
  match ga[w.chr]? with
  | some ca =>
    if w.start + w.len ≤ ca.size then
      if w.len + 1 = ra.size then delLoop ra ca 0 w.start w.len
      else if w.len = ra.size + 1 then delLoop ca ra w.start 0 ra.size
      else false
    else false
  | none => false

/-- Windows one letter shorter or longer than the read, placed by seeds 0 and 1
with the shift a single indel can cause. -/
def indelWindows (lookup : List Char → List (Nat × Nat)) (l0 : Nat) (read : List Char) (k : Nat) :
    List Window :=
  (List.range 2).flatMap fun j =>
    (lookup ((read.drop (j * (read.length / (k + 1)))).take l0)).flatMap fun place =>
      [{ chr := place.1, start := place.2 + j - j * (read.length / (k + 1)), len := read.length - 1 },
       { chr := place.1, start := place.2 - j * (read.length / (k + 1)) - j, len := read.length + 1 }]

/-- When no window can beat `gapOpen + gapExtend` (and `matchScore = 0`,
`T ≤ gapOpen + gapExtend`): the windows scoring exactly that are the gapless
anchors with that score and the one-indel windows. -/
def gapStep (lookup : List Char → List (Nat × Nat)) (sc : Scoring) (ga : Array (Array Char))
    (l0 : Nat) (T : Int) (k : Nat) (read : List Char) (ra : Array Char) (scored : List (Window × Int))
    (fallback : Unit → Option (Window × Int)) : Option (Window × Int) :=
  if sc.matchScore = 0 ∧ T ≤ gapCost1 sc then
    let L := scored.filter (fun a => decide (gapCost1 sc ≤ a.2)) ++
      ((indelWindows lookup l0 read k).filter (indelA ra ga)).map (·, gapCost1 sc)
    if L.isEmpty then fallback () else selectUnique L
  else fallback ()

/-- Decide from the anchors when the best gapless score is above
`gapOpen + gapExtend` and at least `T`; when it is at most that, try
`gapStep`; otherwise `mapWith`. -/
def mapLowError (lookup : List Char → List (Nat × Nat)) (score : Window → Option Int)
    (ga : Array (Array Char)) (sc : Scoring) (l0 : Nat) (T : Int) (k : Nat) (g : Genome)
    (read : List Char) : Option (Window × Int) :=
  if 0 < l0 ∧ l0 ≤ read.length / (k + 1) then
    let ra := read.toArray
    let scored := lowErrorHits lookup sc ga l0 k read ra
    match (scored.map (·.2)).max? with
    | some S =>
      if gapCost1 sc < S ∧ T ≤ S then selectUnique (scored.filter fun a => decide (S ≤ a.2))
      else gapStep lookup sc ga l0 T k read ra scored (fun _ => mapWith lookup score l0 T k g read)
    | none => gapStep lookup sc ga l0 T k read ra scored (fun _ => mapWith lookup score l0 T k g read)
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

for every scoring with `ValidScoring sc`.  They are at the end of this file.
The facts they rest on (pool/mapper/MapperGapless.lean, MapperOneIndel.lean):

    walkScore_diags       equal lengths: all-diagonal walk = match·(n − hamming) + mismatch·hamming
    scoreWalk_gap_le      a valid walk with a gap scores ≤ gapOpen + gapExtend
    best_gapless          optimum > gapOpen + gapExtend → equal lengths, optimum = gapless score
    gapless_clean_seed    gapless walk ≥ T → a seed is clean at exactly its own offset
    one_gap_structure     matchScore = 0, walk with a gap ≥ gapOpen + gapExtend → one-letter deletion
    delOk_walk(')         a one-letter deletion gives a walk scoring gapOpen + gapExtend -/

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

/-- A passing anchor scoring at least `gapOpen + gapExtend` has that score as its window score. -/
theorem windowScore_of_gaplessRef (sc : Scoring) (hv : ValidScoring sc) (read : List Char) (g : Genome)
    (cap : Nat) (w : Window) (s : Int) (h : gaplessRef sc read g cap w = some s) (hG : gapCost1 sc ≤ s) :
    windowScore sc read g w = some s := by
  obtain ⟨ys, hw, hl, hs⟩ := gaplessRef_some sc read g cap w s h
  unfold windowScore
  rw [hw]
  obtain ⟨⟨p, bs⟩, hb⟩ := getBestAlignment_returns_some sc read ys
  have h1 := gapless_le_best sc read ys p bs hb hl.symm
  by_cases hlt : gapCost1 sc < bs
  · have h2 := best_gapless sc hv read ys p bs hb hlt
    simp [hb, h2.2.2, hs]
  · have : bs = s := by omega
    simp [hb, this]

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

theorem windowSeq_some (g : Genome) (c st len : Nat) (ys : List Char)
    (h : windowSeq g ⟨c, st, len⟩ = some ys) :
    ∃ chromosome, g[c]? = some chromosome ∧ st + len ≤ chromosome.seq.length ∧
      ys = (chromosome.seq.drop st).take len ∧ ys.length = len := by
  unfold windowSeq at h
  cases hc : g[c]? with
  | none => simp [hc] at h
  | some chromosome =>
    simp only [hc] at h
    split at h
    · next hfit =>
      have hys : ys = (chromosome.seq.drop st).take len := by simpa using h.symm
      refine ⟨chromosome, rfl, hfit, hys, ?_⟩
      rw [hys, List.length_take, List.length_drop]; omega
    · cases h

/-- A word of the read found at offset `o` of a window is reported by the lookup. -/
theorem lookup_of_word (lookup : List Char → List (Nat × Nat)) (l0 : Nat) (g : Genome)
    (hl : LookupComplete g l0 lookup) (c st len : Nat) (ys : List Char)
    (hseq : windowSeq g ⟨c, st, len⟩ = some ys) (word : List Char) (o : Nat)
    (ho : o + l0 ≤ ys.length) (hw : word = (ys.drop o).take l0) :
    (c, st + o) ∈ lookup word := by
  obtain ⟨chromosome, hc, hfit, hys, hyl⟩ := windowSeq_some g c st len ys hseq
  rw [hw, hys, take_drop_window _ _ _ _ _ (by omega)]
  exact hl c chromosome (st + o) hc (by omega)

/-- **Coverage.**  A window of the read's length whose gapless score is at
least `T` is an anchor window: its clean seed sits at exactly its own offset. -/
theorem mem_anchorWindows_gapless (lookup : List Char → List (Nat × Nat)) (l0 : Nat) (sc : Scoring)
    (hv : ValidScoring sc) (T : Int) (g : Genome) (hl : LookupComplete g l0 lookup)
    (read : List Char) (hcond : 0 < l0 ∧ l0 ≤ read.length / (errBound sc T + 1))
    (c st len : Nat) (ys : List Char) (hseq : windowSeq g ⟨c, st, len⟩ = some ys)
    (hlen : read.length = ys.length) (hT : T ≤ gaplessScore sc read ys) :
    (⟨c, st, len⟩ : Window) ∈ anchorWindows lookup l0 read (errBound sc T) := by
  obtain ⟨j, hj, hjq, hseed⟩ :=
    gapless_clean_seed sc hv T read ys hlen (by rw [walkScore_diags sc read ys hlen]; exact hT)
  obtain ⟨-, -, -, -, hyl⟩ := windowSeq_some g c st len ys hseq
  generalize hq : read.length / (errBound sc T + 1) = q at *
  simp only [anchorWindows, hq]
  rw [List.mem_flatMap]
  refine ⟨j, List.mem_range.mpr (by omega), ?_⟩
  rw [List.mem_filterMap]
  refine ⟨(c, st + j * q), ?_, ?_⟩
  · apply lookup_of_word lookup l0 g hl c st len ys hseq _ (j * q) (by omega)
    have h1 := congrArg (List.take l0) hseed
    rw [List.take_take, List.take_take, Nat.min_eq_left hcond.2] at h1
    exact h1.symm
  · simp only
    rw [if_pos (by omega)]
    have : st + j * q - j * q = st := by omega
    rw [this, hlen, hyl]

/-- **Coverage.**  Every window scoring above `gapOpen + gapExtend` and at least
`T` is an anchor window. -/
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
      obtain ⟨hlen, -, hgs⟩ := best_gapless sc hv read ys path bs hbest hG
      exact mem_anchorWindows_gapless lookup l0 sc hv T g hl read hcond c st len ys hseq hlen
        (by rw [← hgs]; exact hT)

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

theorem eqLoop_eq (p q : Array Char) (m : Nat) : ∀ a b, a + m ≤ p.size → b + m ≤ q.size →
    eqLoop p q a b m = decide ((p.toList.drop a).take m = (q.toList.drop b).take m) := by
  induction m with
  | zero => intro a b _ _; simp [eqLoop]
  | succ m ih =>
    intro a b ha hb
    have hpa : p.toList.drop a = p[a] :: p.toList.drop (a + 1) := by
      rw [List.drop_eq_getElem_cons (by simp; omega)]; simp
    have hqb : q.toList.drop b = q[b] :: q.toList.drop (b + 1) := by
      rw [List.drop_eq_getElem_cons (by simp; omega)]; simp
    simp only [eqLoop, Array.getElem?_eq_getElem (show a < p.size by omega),
      Array.getElem?_eq_getElem (show b < q.size by omega)]
    rw [ih (a + 1) (b + 1) (by omega) (by omega), hpa, hqb]
    by_cases hxy : p[a] = q[b] <;> simp [hxy]

theorem delLoop_eq (p q : Array Char) (m : Nat) : ∀ a b, a + m + 1 ≤ p.size → b + m ≤ q.size →
    delLoop p q a b m = delOk ((p.toList.drop a).take (m + 1)) ((q.toList.drop b).take m) := by
  induction m with
  | zero =>
    intro a b ha _
    have hpa : p.toList.drop a = p[a] :: p.toList.drop (a + 1) := by
      rw [List.drop_eq_getElem_cons (by simp; omega)]; simp
    rw [hpa]; simp [delLoop, delOk]
  | succ m ih =>
    intro a b ha hb
    have hpa : p.toList.drop a = p[a] :: p.toList.drop (a + 1) := by
      rw [List.drop_eq_getElem_cons (by simp; omega)]; simp
    have hqb : q.toList.drop b = q[b] :: q.toList.drop (b + 1) := by
      rw [List.drop_eq_getElem_cons (by simp; omega)]; simp
    simp only [delLoop, Array.getElem?_eq_getElem (show a < p.size by omega),
      Array.getElem?_eq_getElem (show b < q.size by omega)]
    rw [eqLoop_eq p q m.succ (a + 1) b (by omega) (by omega), ih (a + 1) (b + 1) (by omega) (by omega),
      hpa, hqb]
    simp only [List.take_succ_cons, delOk]
    by_cases hxy : p[a] = q[b] <;> simp [hxy] <;> congr

/-- List form of the one-indel check. -/
def indelRef (read : List Char) (g : Genome) (w : Window) : Bool :=
  match windowSeq g w with
  | some ys => (decide (ys.length + 1 = read.length) && delOk read ys) ||
               (decide (ys.length = read.length + 1) && delOk ys read)
  | none => false

theorem indelA_eq (read : List Char) (g : Genome) (w : Window) :
    indelA read.toArray (genomeArrays g) w = indelRef read g w := by
  unfold indelA indelRef windowSeq genomeArrays
  simp only [List.getElem?_toArray, List.getElem?_map]
  cases hc : g[w.chr]? with
  | none => rfl
  | some chr =>
    simp only [Option.map_some, List.size_toArray]
    by_cases hfit : w.start + w.len ≤ chr.seq.length
    · rw [if_pos hfit, if_pos hfit]
      have hyl : ((chr.seq.drop w.start).take w.len).length = w.len := by simp; omega
      simp only [hyl]
      by_cases h1 : w.len + 1 = read.length
      · rw [if_pos h1, delLoop_eq _ _ _ _ _ (by simp <;> omega) (by simp <;> omega)]
        simp only [List.drop_zero, h1, List.take_length]
        simp <;> omega
      · rw [if_neg h1]
        by_cases h2 : w.len = read.length + 1
        · rw [if_pos h2, delLoop_eq _ _ _ _ _ (by simp <;> omega) (by simp <;> omega)]
          simp only [List.drop_zero, List.take_length, ← h2]
          simp <;> omega
        · rw [if_neg h2]; simp [h1, h2]
    · rw [if_neg hfit, if_neg hfit]

/-- **One-indel windows.**  With `matchScore = 0`, a window passing the
one-indel check scores exactly `gapOpen + gapExtend`. -/
theorem windowScore_of_indelRef (sc : Scoring) (hv : ValidScoring sc) (hm : sc.matchScore = 0)
    (read : List Char) (g : Genome) (w : Window) (h : indelRef read g w = true) :
    windowScore sc read g w = some (gapCost1 sc) := by
  unfold indelRef at h
  unfold windowScore
  cases hw : windowSeq g w with
  | none => rw [hw] at h; cases h
  | some ys =>
    rw [hw] at h
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    have hne : read.length ≠ ys.length := by omega
    obtain ⟨p0, hp0, hs0⟩ : ∃ p, IsMonotoneWalk p read ys ∧ walkScore sc read ys p = gapCost1 sc := by
      rcases h with ⟨-, hd⟩ | ⟨-, hd⟩
      · exact delOk_walk sc hm read ys hd
      · exact delOk_walk' sc hm read ys hd
    obtain ⟨⟨p, bs⟩, hb⟩ := getBestAlignment_returns_some sc read ys
    have hge := getBestAlignment_returns_a_maximum_score sc read ys p bs p0 hb hp0
    obtain ⟨hpw, hps⟩ := getBestAlignment_returns_a_valid_walk sc read ys p bs hb
    have hg : Step.gapX ∈ p ∨ Step.gapY ∈ p := by
      apply Classical.byContradiction; intro hng
      exact hne (eq_diags_of_no_gap p read ys hpw hng).1
    have hle := scoreWalk_gap_le sc hv p read ys none (by simp) (by simp) hpw hg
    unfold walkScore at hps
    have : bs = gapCost1 sc := by omega
    simp [hb, this]

theorem errBound_pos (sc : Scoring) (hv : ValidScoring sc) (T : Int) (hT : T ≤ gapCost1 sc) :
    1 ≤ errBound sc T := by
  obtain ⟨h1, h2, h3, h4⟩ := hv
  unfold errBound
  unfold gapCost1 at hT
  have hc : 0 < min (-sc.mismatchScore) (-sc.gapExtend) := by omega
  have : 1 * min (-sc.mismatchScore) (-sc.gapExtend) ≤ -T := by omega
  have := Int.le_ediv_of_mul_le hc this
  omega

theorem take_erase (l : List Char) (i m : Nat) (hm : m ≤ i) :
    (l.take i ++ l.drop (i + 1)).take m = l.take m := by
  by_cases hi : i ≤ l.length
  · rw [List.take_append_of_le_length (by simp; omega), List.take_take, Nat.min_eq_left hm]
  · rw [List.take_of_length_le (show l.length ≤ i by omega), List.drop_of_length_le (by omega),
      List.append_nil]

theorem drop_erase (l : List Char) (i d : Nat) (hi : i < l.length) (hd : i ≤ d) :
    (l.take i ++ l.drop (i + 1)).drop d = l.drop (d + 1) := by
  rw [List.drop_append, List.drop_eq_nil_of_le (by simp; omega), List.nil_append, List.drop_drop]
  congr 1; simp; omega

/-- **Coverage.**  Every one-indel window is among `indelWindows`: seed 0 or
seed 1 is clean, at its own offset or shifted by one. -/
theorem mem_indelWindows (lookup : List Char → List (Nat × Nat)) (l0 : Nat) (g : Genome)
    (hl : LookupComplete g l0 lookup) (read : List Char) (k : Nat) (hk : 1 ≤ k)
    (hcond : 0 < l0 ∧ l0 ≤ read.length / (k + 1))
    (c st len : Nat) (ys : List Char) (hseq : windowSeq g ⟨c, st, len⟩ = some ys)
    (hd : (ys.length + 1 = read.length ∧ delOk read ys = true) ∨
          (ys.length = read.length + 1 ∧ delOk ys read = true)) :
    (⟨c, st, len⟩ : Window) ∈ indelWindows lookup l0 read k := by
  obtain ⟨-, -, -, -, hyl⟩ := windowSeq_some g c st len ys hseq
  have hkq : (k + 1) * (read.length / (k + 1)) ≤ read.length := by
    rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  generalize hq : read.length / (k + 1) = q at *
  have h2q : 2 * q ≤ read.length := by
    have : 2 * q ≤ (k + 1) * q := Nat.mul_le_mul_right q (by omega)
    omega
  unfold indelWindows
  simp only [hq, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false]
  rcases hd with ⟨hlen, hdel⟩ | ⟨hlen, hdel⟩
  · obtain ⟨i, hi, he⟩ := delOk_spec read ys hdel
    by_cases hqi : q ≤ i
    · refine ⟨0, by omega, (c, st), ?_, Or.inl ?_⟩
      · apply lookup_of_word lookup l0 g hl c st len ys hseq _ 0 (by omega)
        simp only [Nat.zero_mul, List.drop_zero]
        rw [he, take_erase _ _ _ (by omega)]
      · simp; omega
    · refine ⟨1, by omega, (c, st + (q - 1)), ?_, Or.inl ?_⟩
      · apply lookup_of_word lookup l0 g hl c st len ys hseq _ (q - 1) (by omega)
        rw [he, drop_erase _ _ _ hi (by omega)]
        congr 2; omega
      · simp; omega
  · obtain ⟨i, hi, he⟩ := delOk_spec ys read hdel
    by_cases hqi : q ≤ i
    · refine ⟨0, by omega, (c, st), ?_, Or.inr ?_⟩
      · apply lookup_of_word lookup l0 g hl c st len ys hseq _ 0 (by omega)
        simp only [Nat.zero_mul, List.drop_zero]
        rw [he, take_erase _ _ _ (by omega)]
      · simp; omega
    · refine ⟨1, by omega, (c, st + (q + 1)), ?_, Or.inr ?_⟩
      · apply lookup_of_word lookup l0 g hl c st len ys hseq _ (q + 1) (by omega)
        rw [he, Nat.one_mul, drop_erase _ _ _ hi (by omega)]
      · simp; omega

/-- **The `gapOpen + gapExtend` step.**  If no anchor's gapless score is above
`gapOpen + gapExtend`, `gapStep` returns the specification's answer (given
that its fallback does). -/
theorem gapStep_eq (lookup : List Char → List (Nat × Nat)) (l0 : Nat) (sc : Scoring)
    (hv : ValidScoring sc) (T : Int) (g : Genome) (read : List Char) (hl : LookupComplete g l0 lookup)
    (hcond : 0 < l0 ∧ l0 ≤ read.length / (errBound sc T + 1))
    (fallback : Unit → Option (Window × Int)) (hfb : fallback () = mapSpec sc T g read)
    (hmax : T ≤ gapCost1 sc → ∀ a ∈ lowErrorHits lookup sc (genomeArrays g) l0 (errBound sc T) read
      read.toArray, a.2 ≤ gapCost1 sc) :
    gapStep lookup sc (genomeArrays g) l0 T (errBound sc T) read read.toArray
      (lowErrorHits lookup sc (genomeArrays g) l0 (errBound sc T) read read.toArray) fallback =
      mapSpec sc T g read := by
  unfold gapStep
  split
  · rename_i hmT
    obtain ⟨hm, hTG⟩ := hmT
    simp only
    split
    · exact hfb
    · rename_i hne
      generalize hLdef : (List.filter (fun a => decide (gapCost1 sc ≤ a.2))
          (lowErrorHits lookup sc (genomeArrays g) l0 (errBound sc T) read read.toArray) ++
        List.map (fun x => (x, gapCost1 sc))
          (List.filter (indelA read.toArray (genomeArrays g)) (indelWindows lookup l0 read (errBound sc T))))
        = L at hne ⊢
      have hfwd : ∀ a ∈ L, a ∈ hitsOf (windowScore sc read g) T (allWindows g) ∧ gapCost1 sc ≤ a.2 := by
        rintro ⟨w, s⟩ ha
        rw [← hLdef, List.mem_append] at ha
        rcases ha with ha | ha
        · rw [List.mem_filter, mem_lowErrorHits] at ha
          simp only [decide_eq_true_eq] at ha
          have hws := windowScore_of_gaplessRef sc hv read g _ w s ha.1.2 ha.2
          exact ⟨(mem_hitsOf _ _ _ _ _).mpr ⟨mem_allWindows_of_score sc read g w s hws, hws, by omega⟩,
            ha.2⟩
        · rw [List.mem_map] at ha
          obtain ⟨w', hw', he⟩ := ha
          simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          rw [List.mem_filter, indelA_eq] at hw'
          have hws := windowScore_of_indelRef sc hv hm read g w' hw'.2
          exact ⟨(mem_hitsOf _ _ _ _ _).mpr ⟨mem_allWindows_of_score sc read g w' _ hws, hws, hTG⟩,
            Int.le_refl _⟩
      have hfunH : ∀ a ∈ hitsOf (windowScore sc read g) T (allWindows g),
          ∀ b ∈ hitsOf (windowScore sc read g) T (allWindows g), a.1 = b.1 → a.2 = b.2 := by
        rintro ⟨w, s⟩ ha ⟨w', s'⟩ hb hww
        rw [mem_hitsOf] at ha hb
        simp only at hww
        subst hww
        have := ha.2.1.symm.trans hb.2.1
        simpa using this
      obtain ⟨a0, ha0⟩ : ∃ a, a ∈ L := by
        cases L with
        | nil => simp at hne
        | cons a _ => exact ⟨a, List.mem_cons_self⟩
      unfold mapSpec
      rw [← selectUnique_filter _ (gapCost1 sc) hfunH ⟨a0, (hfwd a0 ha0).1, (hfwd a0 ha0).2⟩]
      apply selectUnique_congr
      · rintro ⟨w, s⟩
        rw [List.mem_filter]
        simp only [decide_eq_true_eq]
        constructor
        · intro ha; exact hfwd _ ha
        · rintro ⟨hH, hGs⟩
          rw [mem_hitsOf] at hH
          obtain ⟨-, hws, hT⟩ := hH
          have hsG : s = gapCost1 sc := by
            apply Classical.byContradiction; intro hne'
            have hlt : gapCost1 sc < s := by omega
            have hr := gaplessRef_of_windowScore sc hv read g w s hws hlt
            have hw := mem_anchorWindows lookup l0 sc hv T g hl read hcond w s hws hlt hT
            have := hmax hTG (w, s) ((mem_lowErrorHits _ _ _ _ _ _ _ _).mpr ⟨hw, hr⟩)
            simp only at this
            omega
          subst hsG
          rw [← hLdef, List.mem_append]
          obtain ⟨c, st, len⟩ := w
          have hws' := hws
          unfold windowScore at hws'
          cases hseq : windowSeq g ⟨c, st, len⟩ with
          | none => rw [hseq] at hws'; cases hws'
          | some ys =>
            rw [hseq] at hws'
            simp only at hws'
            cases hb : getBestAlignment sc read ys with
            | none => rw [hb] at hws'; cases hws'
            | some best =>
              rw [hb] at hws'
              obtain ⟨p, bs⟩ := best
              have hbs : bs = gapCost1 sc := by simpa using hws'
              obtain ⟨hpw, hps⟩ := getBestAlignment_returns_a_valid_walk sc read ys p bs hb
              by_cases hg : Step.gapX ∈ p ∨ Step.gapY ∈ p
              · have hd := one_gap_structure sc hv hm p read ys none (by simp) (by simp) hpw hg
                  (by unfold walkScore at hps; omega)
                right
                rw [List.mem_map]
                refine ⟨⟨c, st, len⟩, ?_, rfl⟩
                rw [List.mem_filter, indelA_eq]
                refine ⟨mem_indelWindows lookup l0 g hl read _ (errBound_pos sc hv T hTG) hcond
                  c st len ys hseq (by
                    rcases hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
                    · exact Or.inl ⟨by omega, h2⟩
                    · exact Or.inr ⟨h1, h2⟩), ?_⟩
                unfold indelRef
                rw [hseq]
                rcases hd with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
              · obtain ⟨hlen, hp⟩ := eq_diags_of_no_gap p read ys hpw hg
                rw [hp, walkScore_diags sc read ys hlen] at hps
                left
                rw [List.mem_filter, mem_lowErrorHits]
                refine ⟨⟨mem_anchorWindows_gapless lookup l0 sc hv T g hl read hcond c st len ys hseq
                  hlen (by omega), ?_⟩, by simp⟩
                have hcap : hamming read ys ≤ gapCap sc := by
                  apply Classical.byContradiction; intro hc
                  have := gaplessScore_lt_of_cap sc hv read ys (by omega)
                  omega
                unfold gaplessRef
                rw [hseq]
                simp [hlen, hcap, hps, hbs]
      · rintro a ha b hb hab
        exact hfunH a (hfwd a ha).1 b (hfwd b hb).1 hab
  · exact hfb

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
          have hws := windowScore_of_gaplessRef sc hv read g _ w0 s0 hm0.2 (Int.le_of_lt hSG.1)
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
      · rename_i hnot
        apply gapStep_eq lookup l0 sc hv T g read hl hcond _ hslow
        intro hTG a ha
        have h1 := ((List.max?_eq_some_iff).mp hmax).2 a.2 (List.mem_map_of_mem ha)
        have : S ≤ gapCost1 sc := by
          apply Classical.byContradiction; intro h
          exact hnot ⟨by omega, by omega⟩
        omega
    · rename_i hmax
      apply gapStep_eq lookup l0 sc hv T g read hl hcond _ hslow
      intro _ a ha
      have := List.max?_eq_none_iff.mp hmax
      rw [List.map_eq_nil_iff] at this
      rw [this] at ha
      cases ha
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
