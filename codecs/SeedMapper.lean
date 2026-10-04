import MapSpec                    -- the mapping specification (spec/, draft)
import MapperDefs                 -- pool
import WfaU3                      -- the proved pairwise codec
import MapperWalk                 -- pool: a high-scoring alignment has an untouched seed
import MapperLists                -- pool: list and table lemmas

/-!
# Codec `indexMapper`: seed-and-index read mapper

The algorithm, then the theorems against `mapSpec`, then the proof.

The algorithm is written once, over any word lookup and any window scorer
(`mapWith`).  Its theorem needs two facts about them: the lookup reports at
least every place a word occurs (`LookupComplete`), and the scorer returns the
specification's score.  `indexMapper` is `mapWith` with the hash-table index
and the proved codec `wfaAlignU3`.  A faster index or scorer only has to prove
those two facts again.
-/

namespace MapSpec

open AlignmentSpec

/-! ## The algorithm -/

/-- Windows suggested by the seeds.  The read is cut into `k + 1` seeds of
length `n / (k + 1)`; each place the lookup reports for a seed's first `l0`
letters gives the windows whose start is within `k` of where that seed would
put the read, with lengths within `k` of the read's. -/
def seedCandidates (lookup : List Char → List (Nat × Nat)) (l0 : Nat) (read : List Char) (k : Nat) :
    List Window :=
  (List.range (k + 1)).flatMap fun j =>
    (lookup ((read.drop (j * (read.length / (k + 1)))).take l0)).flatMap fun place =>
      (List.range (2 * k + 1)).flatMap fun dp =>
        (List.range (2 * k + 1)).filterMap fun dl =>
          if j * (read.length / (k + 1)) + dp ≤ place.2 + k then
            some { chr := place.1, start := place.2 + k - j * (read.length / (k + 1)) - dp,
                   len := read.length + k - dl }
          else none

/-- Windows to score.  Reads too short to seed fall back to every window. -/
def candidates (lookup : List Char → List (Nat × Nat)) (l0 : Nat) (g : Genome) (read : List Char)
    (k : Nat) : List Window :=
  if 0 < l0 ∧ l0 ≤ read.length / (k + 1) then seedCandidates lookup l0 read k
  else allWindows g

/-- Score the candidate windows, keep those scoring at least `T`, return the
unique best. -/
def mapWith (lookup : List Char → List (Nat × Nat)) (score : Window → Option Int)
    (l0 : Nat) (T : Int) (k : Nat) (g : Genome) (read : List Char) : Option (Window × Int) :=
  selectUnique (hitsOf score T (candidates lookup l0 g read k))

/-- Every `l0`-letter word of the genome ↦ the places (chromosome, start) it occurs. -/
structure Index where
  genome : Genome
  l0 : Nat
  table : Std.HashMap (List Char) (List (Nat × Nat))

def buildIndex (l0 : Nat) (g : Genome) : Index :=
  { genome := g, l0 := l0,
    table := buildTable ((List.range g.length).flatMap fun c =>
      match g[c]? with
      | some chromosome => wordsOf l0 c chromosome.seq
      | none => []) }

def Index.lookup (idx : Index) (word : List Char) : List (Nat × Nat) :=
  idx.table.getD word []

/-- Score of the read against a window, computed by the proved codec. -/
def kernelScore (sc : Scoring) (read : List Char) (g : Genome) (w : Window) : Option Int :=
  match windowSeq g w with
  | some ys =>
    match wfaAlignU3 sc read.toArray ys.toArray with
    | some result => some result.2
    | none => none
  | none => none

/-- Map one read through an index. -/
def mapWithIndex (sc : Scoring) (T : Int) (idx : Index) (read : List Char) : Option (Window × Int) :=
  mapWith idx.lookup (kernelScore sc read idx.genome) idx.l0 T (errBound sc T) idx.genome read

/-- Build the index, then map one read. -/
def indexMapper (l0 : Nat) (sc : Scoring) (T : Int) (g : Genome) (read : List Char) : Option (Window × Int) :=
  mapWithIndex sc T (buildIndex l0 g) read

/-- Build the index once, then map every read through it. -/
def mapReads (l0 : Nat) (sc : Scoring) (T : Int) (g : Genome) (reads : List (List Char)) :
    List (Option (Window × Int)) :=
  let idx := buildIndex l0 g
  reads.map (mapWithIndex sc T idx)

/-! ## The theorems

    indexMapper l0 sc T genome read = mapSpec sc T genome read              (indexMapper_eq_mapSpec)
    idx = buildIndex l0 genome →
      mapWithIndex sc T idx read = indexMapper l0 sc T genome read          (mapWithIndex_eq_indexMapper)
    mapReads l0 sc T genome reads = reads.map (mapSpec sc T genome)         (mapReads_eq_mapSpec)

for every genome, read, threshold `T`, word length `l0`, and every scoring
with `ValidScoring sc`.  They are at the end of this file; everything before
them is their proof. -/

/-! ## Proof -/

/-- The lookup reports at least every place a word occurs. -/
def LookupComplete (g : Genome) (l0 : Nat) (lookup : List Char → List (Nat × Nat)) : Prop :=
  ∀ (c : Nat) (chromosome : Chromosome) (p : Nat), g[c]? = some chromosome →
    p + l0 ≤ chromosome.seq.length → (c, p) ∈ lookup ((chromosome.seq.drop p).take l0)

/-- A word of a window is a word of its chromosome. -/
theorem take_drop_window (seq : List Char) (st len o m : Nat) (h : o + m ≤ len) :
    (((seq.drop st).take len).drop o).take m = (seq.drop (st + o)).take m := by
  rw [List.drop_take, List.take_take, List.drop_drop]
  congr 1
  omega

/-- Every window the specification can report is among the candidates. -/
theorem mem_candidates (lookup : List Char → List (Nat × Nat)) (l0 : Nat) (sc : Scoring)
    (hv : ValidScoring sc) (T : Int) (g : Genome) (hl : LookupComplete g l0 lookup)
    (read : List Char) (w : Window) (s : Int)
    (hscore : windowScore sc read g w = some s) (hT : T ≤ s) :
    w ∈ candidates lookup l0 g read (errBound sc T) := by
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
      obtain ⟨hlen1, hlen2, j, hj, o, ho, hseed, ho1, ho2⟩ :=
        exists_clean_seed sc hv T read ys path hwalk (by rw [hws]; exact hT)
      unfold candidates
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
            simp only [seedCandidates]
            rw [List.mem_flatMap]
            refine ⟨j, List.mem_range.mpr (by omega), ?_⟩
            rw [List.mem_flatMap]
            refine ⟨(w.chr, w.start + o), ?_, ?_⟩
            · have hkey : (read.drop (j * (read.length / (errBound sc T + 1)))).take l0 =
                  (chromosome.seq.drop (w.start + o)).take l0 := by
                have h1 := congrArg (List.take l0) hseed
                rw [List.take_take, List.take_take, Nat.min_eq_left hcond.2] at h1
                rw [← h1, hys, take_drop_window _ _ _ _ _ (by omega)]
              rw [hkey]
              exact hl w.chr chromosome (w.start + o) hc (by omega)
            · simp only
              rw [List.mem_flatMap]
              refine ⟨o + errBound sc T - j * (read.length / (errBound sc T + 1)),
                List.mem_range.mpr (by omega), ?_⟩
              rw [List.mem_filterMap]
              refine ⟨read.length + errBound sc T - w.len, List.mem_range.mpr (by omega), ?_⟩
              rw [if_pos (by omega)]
              have h1 : w.start + o + errBound sc T - j * (read.length / (errBound sc T + 1)) -
                  (o + errBound sc T - j * (read.length / (errBound sc T + 1))) = w.start := by omega
              have h2 : read.length + errBound sc T - (read.length + errBound sc T - w.len) = w.len := by
                omega
              rw [h1, h2]
          · cases hseq
      · exact (mem_allWindows g w).mpr (by rw [hseq]; rfl)

/-- The general theorem: with a complete lookup and a correct scorer, the
algorithm returns the specification's answer. -/
theorem mapWith_eq_mapSpec (lookup : List Char → List (Nat × Nat)) (score : Window → Option Int)
    (l0 : Nat) (sc : Scoring) (hv : ValidScoring sc) (T : Int) (g : Genome) (read : List Char)
    (hl : LookupComplete g l0 lookup) (hs : ∀ w, score w = windowScore sc read g w) :
    mapWith lookup score l0 T (errBound sc T) g read = mapSpec sc T g read := by
  unfold mapWith mapSpec
  have hk : score = windowScore sc read g := funext hs
  rw [hk]
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
      exact ⟨mem_candidates lookup l0 sc hv T g hl read w s hs hT, hs, hT⟩
  · rintro ⟨w, s⟩ ha ⟨w', s'⟩ hb hww
    rw [mem_hitsOf] at ha hb
    simp only at hww
    subst hww
    have := ha.2.1.symm.trans hb.2.1
    simpa using this

/-- The hash-table index reports every place a word occurs. -/
theorem buildIndex_complete (l0 : Nat) (g : Genome) : LookupComplete g l0 (buildIndex l0 g).lookup := by
  intro c chromosome p hc hp
  apply mem_buildTable
  rw [List.mem_flatMap]
  have hlt : c < g.length := by
    rcases List.getElem?_eq_some_iff.mp hc with ⟨h, -⟩; exact h
  refine ⟨c, List.mem_range.mpr hlt, ?_⟩
  rw [hc]
  exact mem_wordsOf l0 c chromosome.seq p hp

/-- The codec's window score is the specification's. -/
theorem kernelScore_eq (sc : Scoring) (read : List Char) (g : Genome) (w : Window) :
    kernelScore sc read g w = windowScore sc read g w := by
  unfold kernelScore windowScore
  cases windowSeq g w with
  | none => rfl
  | some ys =>
    have h := wfaAlignU3_score sc read.toArray ys.toArray
    cases hk : wfaAlignU3 sc read.toArray ys.toArray <;>
      cases hb : getBestAlignment sc read ys <;> simp_all

/-- **Genome and read.**  Building the index and mapping through it gives
exactly the specification's answer. -/
theorem indexMapper_eq_mapSpec (l0 : Nat) (sc : Scoring) (hv : ValidScoring sc) (T : Int)
    (g : Genome) (read : List Char) :
    indexMapper l0 sc T g read = mapSpec sc T g read :=
  mapWith_eq_mapSpec _ _ l0 sc hv T g read (buildIndex_complete l0 g) (kernelScore_eq sc read g)

/-- **Index and read.**  Mapping through an index that is the one
`buildIndex` makes from the genome is `indexMapper`. -/
theorem mapWithIndex_eq_indexMapper (l0 : Nat) (sc : Scoring) (T : Int) (g : Genome) (idx : Index)
    (hidx : idx = buildIndex l0 g) (read : List Char) :
    mapWithIndex sc T idx read = indexMapper l0 sc T g read := by
  subst hidx; rfl

/-- So it is the specification's answer. -/
theorem mapWithIndex_eq_mapSpec (l0 : Nat) (sc : Scoring) (hv : ValidScoring sc) (T : Int)
    (g : Genome) (idx : Index) (hidx : idx = buildIndex l0 g) (read : List Char) :
    mapWithIndex sc T idx read = mapSpec sc T g read := by
  rw [mapWithIndex_eq_indexMapper l0 sc T g idx hidx]; exact indexMapper_eq_mapSpec l0 sc hv T g read

/-- **One index, many reads.**  Every read gets the specification's answer. -/
theorem mapReads_eq_mapSpec (l0 : Nat) (sc : Scoring) (hv : ValidScoring sc) (T : Int)
    (g : Genome) (reads : List (List Char)) :
    mapReads l0 sc T g reads = reads.map (mapSpec sc T g) := by
  unfold mapReads
  apply List.map_congr_left
  intro read _
  exact mapWithIndex_eq_mapSpec l0 sc hv T g _ rfl read

end MapSpec

#print axioms MapSpec.indexMapper_eq_mapSpec
#print axioms MapSpec.mapWithIndex_eq_indexMapper
#print axioms MapSpec.mapWithIndex_eq_mapSpec
#print axioms MapSpec.mapReads_eq_mapSpec
