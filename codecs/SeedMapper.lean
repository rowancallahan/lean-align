import MapSpec                    -- the mapping specification (spec/, draft)
import MapperDefs                 -- pool
import WfaU3                      -- the proved pairwise codec
import MapperWalk                 -- pool: a high-scoring alignment has an untouched seed
import MapperLists                -- pool: list and table lemmas

/-!
# Codec `indexMapper`: seed-and-index read mapper

The algorithm (build the index, look up seeds, score candidate windows with
`wfaAlignU3`, keep the unique best), then the theorem against `mapSpec`, then
its proof.
-/

namespace MapSpec

open AlignmentSpec

/-! ## The algorithm -/

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

/-- Windows suggested by the seeds.  The read is cut into `k + 1` seeds of
length `n / (k + 1)`; each place the index reports for a seed's first `l0`
letters gives the windows whose start is within `k` of where that seed would
put the read, with lengths within `k` of the read's. -/
def seedCandidates (idx : Index) (read : List Char) (k : Nat) : List Window :=
  (List.range (k + 1)).flatMap fun j =>
    (idx.table.getD ((read.drop (j * (read.length / (k + 1)))).take idx.l0) []).flatMap fun place =>
      (List.range (2 * k + 1)).flatMap fun dp =>
        (List.range (2 * k + 1)).filterMap fun dl =>
          if j * (read.length / (k + 1)) + dp ≤ place.2 + k then
            some { chr := place.1, start := place.2 + k - j * (read.length / (k + 1)) - dp,
                   len := read.length + k - dl }
          else none

/-- Windows to score.  Reads too short to seed fall back to every window. -/
def candidates (idx : Index) (read : List Char) (k : Nat) : List Window :=
  if 0 < idx.l0 ∧ idx.l0 ≤ read.length / (k + 1) then seedCandidates idx read k
  else allWindows idx.genome

/-- Score of the read against a window, computed by the proved codec. -/
def kernelScore (sc : Scoring) (read : List Char) (g : Genome) (w : Window) : Option Int :=
  match windowSeq g w with
  | some ys =>
    match wfaAlignU3 sc read.toArray ys.toArray with
    | some result => some result.2
    | none => none
  | none => none

def mapWithIndex (sc : Scoring) (T : Int) (idx : Index) (read : List Char) : Option (Window × Int) :=
  selectUnique (hitsOf (kernelScore sc read idx.genome) T (candidates idx read (errBound sc T)))

/-- Build the index, then map. -/
def indexMapper (l0 : Nat) (sc : Scoring) (T : Int) (g : Genome) (read : List Char) : Option (Window × Int) :=
  mapWithIndex sc T (buildIndex l0 g) read

/-! ## The theorem

    indexMapper l0 sc T genome read = mapSpec sc T genome read

for every genome, read, threshold `T`, index word length `l0`, and every
scoring with `ValidScoring sc`.  It is `indexMapper_eq_mapSpec` at the end of
this file; the lemmas before it are its proof. -/

/-! ## Proof -/

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

/-- A word of a window is a word of its chromosome. -/
theorem take_drop_window (seq : List Char) (st len o m : Nat) (h : o + m ≤ len) :
    (((seq.drop st).take len).drop o).take m = (seq.drop (st + o)).take m := by
  rw [List.drop_take, List.take_take, List.drop_drop]
  congr 1
  omega

/-- Every window the specification can report is among the candidates. -/
theorem mem_candidates (l0 : Nat) (sc : Scoring) (hv : ValidScoring sc) (T : Int) (g : Genome)
    (read : List Char) (w : Window) (s : Int)
    (hscore : windowScore sc read g w = some s) (hT : T ≤ s) :
    w ∈ candidates (buildIndex l0 g) read (errBound sc T) := by
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
        have hl0 : (buildIndex l0 g).l0 = l0 := rfl
        rw [hl0] at hcond
        simp only [seedCandidates, buildIndex]
        -- the window's chromosome and letters
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
            rw [List.mem_flatMap]
            refine ⟨j, List.mem_range.mpr (by omega), ?_⟩
            rw [List.mem_flatMap]
            refine ⟨(w.chr, w.start + o), ?_, ?_⟩
            · apply mem_buildTable
              rw [List.mem_flatMap]
              have hlt : w.chr < g.length := by
                rcases List.getElem?_eq_some_iff.mp hc with ⟨h, -⟩; exact h
              refine ⟨w.chr, List.mem_range.mpr hlt, ?_⟩
              rw [hc]
              have hw := mem_wordsOf l0 w.chr chromosome.seq (w.start + o) (by omega)
              have hkey : (read.drop (j * (read.length / (errBound sc T + 1)))).take l0 =
                  (chromosome.seq.drop (w.start + o)).take l0 := by
                have h1 := congrArg (List.take l0) hseed
                rw [List.take_take, List.take_take, Nat.min_eq_left hcond.2] at h1
                rw [← h1, hys, take_drop_window _ _ _ _ _ (by omega)]
              rw [hkey]; exact hw
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

/-- **The theorem.**  Building the index and mapping through it gives exactly
the specification's answer, for every genome and read. -/
theorem indexMapper_eq_mapSpec (l0 : Nat) (sc : Scoring) (hv : ValidScoring sc) (T : Int)
    (g : Genome) (read : List Char) :
    indexMapper l0 sc T g read = mapSpec sc T g read := by
  unfold indexMapper mapWithIndex mapSpec
  have hk : kernelScore sc read (buildIndex l0 g).genome = windowScore sc read g := by
    funext w; exact kernelScore_eq sc read g w
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
      exact ⟨mem_candidates l0 sc hv T g read w s hs hT, hs, hT⟩
  · rintro ⟨w, s⟩ ha ⟨w', s'⟩ hb hww
    rw [mem_hitsOf] at ha hb
    simp only at hww
    subst hww
    have := ha.2.1.symm.trans hb.2.1
    simpa using this

/-- The same statement for an index that is the one built from the genome. -/
theorem mapWithIndex_eq_mapSpec (l0 : Nat) (sc : Scoring) (hv : ValidScoring sc) (T : Int)
    (g : Genome) (idx : Index) (hidx : idx = buildIndex l0 g) (read : List Char) :
    mapWithIndex sc T idx read = mapSpec sc T g read := by
  subst hidx; exact indexMapper_eq_mapSpec l0 sc hv T g read


end MapSpec

#print axioms MapSpec.indexMapper_eq_mapSpec
#print axioms MapSpec.mapWithIndex_eq_mapSpec
