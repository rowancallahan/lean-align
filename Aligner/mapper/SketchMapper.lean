import MapSpec                    -- the mapping specification (spec/, draft)
import MapperDefs                 -- pool
import MapperLists                -- pool: list and table lemmas
import MapperWalk2                -- pool: clean seed and window shape
import MapperSketch               -- pool: seed sketches (k-mer, minimizer, syncmer, …)
import SeedMapper                 -- kernelScore
import SeedMapper2                -- shapes, KeepComplete, seedOccurs

/-!
# Codec `sketchMapper`: seed-and-index mapper over any seed sketch

Same plan as `indexMapper2`, but the index stores only the summaries of a
`SeedSketch` (every k-mer, minimizers, closed syncmers, …) instead of every
word.  The read is cut into `seedBound sc T + 1` seeds of `q` letters; for
each seed one summary `(key, i)` of the seed is chosen by `pick` (any choice,
e.g. the one with the smallest bucket), every place `p` the lookup reports
for `key` gives the seed start `p - i`, `keep` may drop the place (e.g. when
the whole seed does not occur there), and the allowed window shapes around
the seed are emitted.

Completeness uses only the two `SeedSketch` properties (`conserved`,
`nonempty`) and `L ≤ q`: a hit window has a clean seed (`exists_clean_seed2`),
every summary of that seed is a summary of the genome at the seed's place,
and the lookup reports it.
-/

namespace MapSpec

open AlignmentSpec

/-! ## The algorithm -/

def sketchCandidates {κ : Type} (S : SeedSketch κ) (pick : List (κ × Nat) → Option (κ × Nat))
    (keep : List Char → Nat × Nat → Bool) (lookup : κ → List (Nat × Nat))
    (read : List Char) (k d d2 : Nat) : List Window :=
  let q := read.length / (k + 1)
  let sh := shapes d d2
  (List.range (k + 1)).flatMap fun j =>
    let seed := (read.drop (j * q)).take q
    match pick (S.sketch seed) with
    | none => []
    | some e =>
      ((lookup e.1).filter fun place =>
          decide (e.2 ≤ place.2) && keep seed (place.1, place.2 - e.2)).flatMap fun place =>
        sh.filterMap fun st =>
          if ((j * q + e.2 : Nat) : Int) + st.1 ≤ place.2 ∧ 0 ≤ (read.length : Int) + st.1 + st.2 then
            some { chr := place.1, start := ((place.2 : Int) - (j * q + e.2 : Nat) - st.1).toNat,
                   len := ((read.length : Int) + st.1 + st.2).toNat }
          else none

/-- Windows to score.  Seeds shorter than `S.L` fall back to every window. -/
def candidatesS {κ : Type} (S : SeedSketch κ) (pick : List (κ × Nat) → Option (κ × Nat))
    (keep : List Char → Nat × Nat → Bool) (lookup : κ → List (Nat × Nat))
    (g : Genome) (read : List Char) (k d d2 : Nat) : List Window :=
  if S.L ≤ read.length / (k + 1) then sketchCandidates S pick keep lookup read k d d2
  else allWindows g

def mapWithSketch {κ : Type} (S : SeedSketch κ) (pick : List (κ × Nat) → Option (κ × Nat))
    (keep : List Char → Nat × Nat → Bool) (lookup : κ → List (Nat × Nat))
    (score : Window → Option Int) (T : Int) (k d d2 : Nat) (g : Genome) (read : List Char) :
    Option (Window × Int) :=
  selectUnique (hitsOf score T (candidatesS S pick keep lookup g read k d d2))

/-- The summary minimising `f` (first one on ties). -/
def pickMin {α : Type} (f : α → Nat) : List α → Option α
  | [] => none
  | a :: l => some (l.foldl (fun b c => if f c < f b then c else b) a)

/-- Every summary of a chromosome, with its place. -/
def sketchEntries (S : SeedSketch (List Char)) (g : Genome) : List (List Char × (Nat × Nat)) :=
  (List.range g.length).flatMap fun c =>
    match g[c]? with
    | some chromosome => (S.sketch chromosome.seq).map fun e => (e.1, (c, e.2))
    | none => []

/-- Hash-table index of the sketch summaries. -/
def buildSketchIndex (S : SeedSketch (List Char)) (g : Genome) :
    Std.HashMap (List Char) (List (Nat × Nat)) :=
  buildTable (sketchEntries S g)

/-- Build the sketch index, map one read: smallest bucket per seed, whole
seed checked at each place. -/
def sketchMapper (S : SeedSketch (List Char)) (sc : Scoring) (T : Int) (g : Genome)
    (read : List Char) : Option (Window × Int) :=
  let idx := buildSketchIndex S g
  let lookup := fun key => idx.getD key []
  mapWithSketch S (pickMin fun e => (lookup e.1).length) (seedOccurs g) lookup
    (kernelScore sc read g) T (seedBound sc T) (gapBound sc T) (gapBound2 sc T) g read

def mapReadsSketch (S : SeedSketch (List Char)) (sc : Scoring) (T : Int) (g : Genome)
    (reads : List (List Char)) : List (Option (Window × Int)) :=
  let idx := buildSketchIndex S g
  let lookup := fun key => idx.getD key []
  reads.map fun read =>
    mapWithSketch S (pickMin fun e => (lookup e.1).length) (seedOccurs g) lookup
      (kernelScore sc read g) T (seedBound sc T) (gapBound sc T) (gapBound2 sc T) g read

/-! ## The theorems

    mapWithSketch S pick keep lookup score T (seedBound sc T) (gapBound sc T) (gapBound2 sc T) g read
      = mapSpec sc T g read                                        (mapWithSketch_eq_mapSpec)
    sketchMapper S sc T g read = mapSpec sc T g read               (sketchMapper_eq_mapSpec)
    mapReadsSketch S sc T g reads = reads.map (mapSpec sc T g)     (mapReadsSketch_eq_mapSpec)

for every `SeedSketch S` (instances: `kmerSketch k`, `minimizerSketch k w ord`,
`syncmerSketch k s ord hs`, any `windowSketch`/`ctxSketch`), given
`ValidScoring sc`, and for `mapWithSketch` a lookup that reports every
summary of the genome (`SketchLookupComplete`), a `pick` that chooses a
member of a nonempty list (`PickOk`), a `keep` that accepts every occurrence
(`KeepComplete`) and a scorer equal to `windowScore`. -/

/-! ## Proof -/

/-- The lookup reports every summary of every chromosome. -/
def SketchLookupComplete {κ : Type} (g : Genome) (sk : List Char → List (κ × Nat))
    (lookup : κ → List (Nat × Nat)) : Prop :=
  ∀ (c : Nat) (chromosome : Chromosome) (key : κ) (p : Nat), g[c]? = some chromosome →
    (key, p) ∈ sk chromosome.seq → (c, p) ∈ lookup key

/-- `pick` chooses a member of every nonempty list. -/
def PickOk {α : Type} (pick : List α → Option α) : Prop :=
  ∀ l : List α, l ≠ [] → ∃ e, pick l = some e ∧ e ∈ l

theorem pickMin_ok {α : Type} (f : α → Nat) : PickOk (pickMin f) := by
  have key : ∀ (l : List α) (a : α),
      l.foldl (fun b c => if f c < f b then c else b) a ∈ a :: l := by
    intro l
    induction l with
    | nil => intro a; simp
    | cons c l ih =>
      intro a
      rw [List.foldl_cons]
      split
      · exact List.mem_cons_of_mem _ (ih c)
      · rcases List.mem_cons.mp (ih a) with h | h
        · rw [h]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
  intro l hl
  cases l with
  | nil => exact absurd rfl hl
  | cons a l => exact ⟨_, rfl, key l a⟩

/-- Seed letters at offsets `offs` agree with the genome at `place` (the
index can store these letters next to each key, so the check needs no genome
access).  Offsets past the seed are ignored. -/
def lettersAgree (g : Genome) (offs : List Nat) (seed : List Char) (place : Nat × Nat) : Bool :=
  match g[place.1]? with
  | some c => offs.all fun t => !decide (t < seed.length) || seed[t]? == c.seq[place.2 + t]?
  | none => false

theorem lettersAgree_complete (g : Genome) (offs : List Nat) : KeepComplete g (lettersAgree g offs) := by
  intro c chromosome p w hc hp hw
  simp only [lettersAgree, hc, List.all_eq_true]
  intro t _
  by_cases ht : t < w.length
  · have : w[t]? = chromosome.seq[p + t]? := by
      conv => lhs; rw [← hw]
      rw [List.getElem?_take, if_pos ht, List.getElem?_drop]
    rw [List.getElem?_eq_getElem ht] at this
    simp [ht, this]
  · simp [ht]

/-- Every window the specification can report is among the candidates. -/
theorem mem_candidatesS {κ : Type} (S : SeedSketch κ) (pick : List (κ × Nat) → Option (κ × Nat))
    (keep : List Char → Nat × Nat → Bool) (lookup : κ → List (Nat × Nat))
    (sc : Scoring) (hv : ValidScoring sc) (T : Int) (g : Genome)
    (hl : SketchLookupComplete g S.sketch lookup) (hp : PickOk pick) (hk : KeepComplete g keep)
    (read : List Char) (w : Window) (s : Int)
    (hscore : windowScore sc read g w = some s) (hT : T ≤ s) :
    w ∈ candidatesS S pick keep lookup g read (seedBound sc T) (gapBound sc T) (gapBound2 sc T) := by
  unfold windowScore at hscore
  cases hseq : windowSeq g w with
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
      obtain ⟨hwalk, hws⟩ := getBestAlignment_returns_a_valid_walk sc read ys path bs hbest
      obtain ⟨j, hj, o, ho, hseed, hshape⟩ :=
        exists_clean_seed2 sc hv T read ys path hwalk (by rw [hws]; exact hT)
      unfold candidatesS
      split
      · rename_i hcond
        unfold windowSeq at hseq
        cases hc : g[w.chr]? with
        | none => rw [hc] at hseq; cases hseq
        | some chromosome =>
          rw [hc] at hseq
          simp only at hseq
          split at hseq
          · next hfit =>
            have hys : ys = (chromosome.seq.drop w.start).take w.len := by
              simpa using hseq.symm
            have hyl : ys.length = w.len := by
              rw [hys, List.length_take, List.length_drop]; omega
            generalize hk' : seedBound sc T = k at *
            generalize hq : read.length / (k + 1) = q at *
            have hjq : j * q + q ≤ read.length := by
              have h1 : (k + 1) * q ≤ read.length := by
                rw [← hq, Nat.mul_comm]; exact Nat.div_mul_le_self _ _
              have : j * q ≤ k * q := Nat.mul_le_mul_right q hj
              rw [Nat.add_mul] at h1; omega
            have hseedlen : ((read.drop (j * q)).take q).length = q := by
              simp; omega
            have hgen : (chromosome.seq.drop (w.start + o)).take q = (read.drop (j * q)).take q := by
              rw [← hseed, hys, take_drop_window _ _ _ _ _ (by omega)]
            -- the chosen summary of the clean seed is a summary of the chromosome
            obtain ⟨e, hpe, hem⟩ := hp _ (S.nonempty _ (by rw [hseedlen]; exact hcond))
            have hge := S.conserved _ chromosome.seq (w.start + o) (by rw [hseedlen]; omega)
              (by rw [hseedlen]; exact hgen) e hem
            simp only [sketchCandidates, hq]
            rw [List.mem_flatMap]
            refine ⟨j, List.mem_range.mpr (by omega), ?_⟩
            rw [hpe]
            simp only
            rw [List.mem_flatMap]
            refine ⟨(w.chr, w.start + o + e.2), ?_, ?_⟩
            · rw [List.mem_filter]
              refine ⟨hl w.chr chromosome e.1 _ hc hge, ?_⟩
              rw [Bool.and_eq_true]
              refine ⟨decide_eq_true (by omega), ?_⟩
              have : w.start + o + e.2 - e.2 = w.start + o := by omega
              simp only [this]
              exact hk w.chr chromosome (w.start + o) _ hc (by rw [hseedlen]; omega)
                (by rw [hseedlen]; exact hgen)
            · rw [List.mem_filterMap]
              refine ⟨_, mem_shapes _ _ _ _ hshape, ?_⟩
              rw [if_pos (by constructor <;> omega)]
              cases w
              simp only [Option.some.injEq, Window.mk.injEq] at *
              refine ⟨trivial, by omega, by omega⟩
          · cases hseq
      · exact (mem_allWindows g w).mpr (by rw [hseq]; rfl)

/-- **Any seed sketch.**  The mapper equals the specification. -/
theorem mapWithSketch_eq_mapSpec {κ : Type} (S : SeedSketch κ)
    (pick : List (κ × Nat) → Option (κ × Nat)) (keep : List Char → Nat × Nat → Bool)
    (lookup : κ → List (Nat × Nat)) (score : Window → Option Int)
    (sc : Scoring) (hv : ValidScoring sc) (T : Int) (g : Genome) (read : List Char)
    (hl : SketchLookupComplete g S.sketch lookup) (hp : PickOk pick) (hk : KeepComplete g keep)
    (hs : ∀ w, score w = windowScore sc read g w) :
    mapWithSketch S pick keep lookup score T (seedBound sc T) (gapBound sc T) (gapBound2 sc T) g read
      = mapSpec sc T g read := by
  unfold mapWithSketch mapSpec
  have hk' : score = windowScore sc read g := funext hs
  rw [hk']
  apply selectUnique_congr
  · rintro ⟨w, s⟩
    rw [mem_hitsOf, mem_hitsOf]
    constructor
    · rintro ⟨-, hs, hT⟩
      refine ⟨(mem_allWindows g w).mpr ?_, hs, hT⟩
      unfold windowScore at hs
      cases h : windowSeq g w with
      | none => rw [h] at hs; cases hs
      | some _ => rfl
    · rintro ⟨-, hs, hT⟩
      exact ⟨mem_candidatesS S pick keep lookup sc hv T g hl hp hk read w s hs hT, hs, hT⟩
  · rintro ⟨w, s⟩ ha ⟨w', s'⟩ hb hww
    rw [mem_hitsOf] at ha hb
    simp only at hww
    subst hww
    have := ha.2.1.symm.trans hb.2.1
    simpa using this

/-- The hash-table sketch index reports every summary. -/
theorem buildSketchIndex_complete (S : SeedSketch (List Char)) (g : Genome) :
    SketchLookupComplete g S.sketch fun key => (buildSketchIndex S g).getD key [] := by
  intro c chromosome key p hc he
  apply mem_buildTable
  rw [sketchEntries, List.mem_flatMap]
  have hlt : c < g.length := by
    rcases List.getElem?_eq_some_iff.mp hc with ⟨h, -⟩; exact h
  refine ⟨c, List.mem_range.mpr hlt, ?_⟩
  rw [hc]
  exact List.mem_map.mpr ⟨(key, p), he, rfl⟩

/-- **Genome and read, any sketch.** -/
theorem sketchMapper_eq_mapSpec (S : SeedSketch (List Char)) (sc : Scoring) (hv : ValidScoring sc)
    (T : Int) (g : Genome) (read : List Char) :
    sketchMapper S sc T g read = mapSpec sc T g read :=
  mapWithSketch_eq_mapSpec S _ _ _ _ sc hv T g read (buildSketchIndex_complete S g)
    (pickMin_ok _) (seedOccurs_complete g) (kernelScore_eq sc read g)

theorem mapReadsSketch_eq_mapSpec (S : SeedSketch (List Char)) (sc : Scoring) (hv : ValidScoring sc)
    (T : Int) (g : Genome) (reads : List (List Char)) :
    mapReadsSketch S sc T g reads = reads.map (mapSpec sc T g) := by
  unfold mapReadsSketch
  apply List.map_congr_left
  intro read _
  exact sketchMapper_eq_mapSpec S sc hv T g read

/-! Instances: `(w, k)` minimizers and closed `(k, s)` syncmers.  The
default scoring has 4 seeds of 25 letters for 100-letter reads, so
`w + k - 1 ≤ 25` (e.g. `k = 19, w = 7`) or `2k - s - 1 ≤ 25` (e.g.
`k = 15, s = 4`) keeps the seeded path. -/

theorem minimizerMapper_eq_mapSpec (k w : Nat) (ord : List Char → Nat) (sc : Scoring)
    (hv : ValidScoring sc) (T : Int) (g : Genome) (read : List Char) :
    sketchMapper (minimizerSketch k w ord) sc T g read = mapSpec sc T g read :=
  sketchMapper_eq_mapSpec _ sc hv T g read

theorem modMinimizerMapper_eq_mapSpec (k w t : Nat) (ord : List Char → Nat) (sc : Scoring)
    (hv : ValidScoring sc) (T : Int) (g : Genome) (read : List Char) :
    sketchMapper (modMinimizerSketch k w t ord) sc T g read = mapSpec sc T g read :=
  sketchMapper_eq_mapSpec _ sc hv T g read

theorem syncmerMapper_eq_mapSpec (k s : Nat) (ord : List Char → Nat) (hs : s < k) (sc : Scoring)
    (hv : ValidScoring sc) (T : Int) (g : Genome) (read : List Char) :
    sketchMapper (syncmerSketch k s ord hs) sc T g read = mapSpec sc T g read :=
  sketchMapper_eq_mapSpec _ sc hv T g read

/-- `minimizerSketch 19 7` and `syncmerSketch 15 4` keep the seeded path
for 100-letter reads under the default scoring. -/
example (ord : List Char → Nat) : (minimizerSketch 19 7 ord).L ≤ 100 / (seedBound ⟨0, -4, -6, -2⟩ (-12) + 1) := by
  rw [show (minimizerSketch 19 7 ord).L = 25 from rfl]; decide
example (ord : List Char → Nat) : (syncmerSketch 15 4 ord (by decide)).L ≤ 100 / (seedBound ⟨0, -4, -6, -2⟩ (-12) + 1) := by
  rw [show (syncmerSketch 15 4 ord (by decide)).L = 25 from rfl]; decide

end MapSpec

#print axioms MapSpec.lettersAgree_complete
#print axioms MapSpec.mapWithSketch_eq_mapSpec
#print axioms MapSpec.sketchMapper_eq_mapSpec
#print axioms MapSpec.mapReadsSketch_eq_mapSpec
#print axioms MapSpec.minimizerMapper_eq_mapSpec
#print axioms MapSpec.modMinimizerMapper_eq_mapSpec
#print axioms MapSpec.syncmerMapper_eq_mapSpec
