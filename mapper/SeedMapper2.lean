import MapSpec                    -- the mapping specification (spec/, draft)
import MapperDefs                 -- pool
import WfaU3                      -- the proved pairwise codec
import MapperWalk2                -- pool: clean seed and window shape from the affine cost
import MapperLists                -- pool: list and table lemmas
import SeedMapper                 -- LookupComplete, Index, kernelScore and their lemmas

/-!
# Codec `indexMapper2`: seed-and-index read mapper with sharper bounds

Same plan as `indexMapper`, with bounds that use the affine gap cost
(`pool/mapper/MapperWalk2.lean`):

* the read is cut into `seedBound sc T + 1` seeds (4 for the default scoring
  and `T = −12`, instead of 7);
* each seed hit gives only the windows whose start shift `s` and end shift
  `t` satisfy `shapeOk (gapBound sc T) (gapBound2 sc T) s t`
  (19 for the default scoring, instead of 169).

A seed hit can also be filtered by `keep` before its windows are made.
`keep` may drop a hit only where the full seed does not occur in the genome
(`KeepComplete`).  Two instances: keep everything (`mapWith2`), or keep a hit
only when the whole seed matches the genome there (`mapWith2V`).
-/

namespace MapSpec

open AlignmentSpec

/-! ## The algorithm -/

/-- The allowed (start shift, end shift) pairs. -/
def shapes (d d2 : Nat) : List (Int × Int) :=
  ((List.range (2 * d + 1)).flatMap fun (a : Nat) =>
    (List.range (2 * d + 1)).map fun (b : Nat) => ((a : Int) - d, (b : Int) - d)).filter
    fun st => decide (shapeOk d d2 st.1 st.2)

example : (shapes 3 0).length = 19 := by decide +kernel

/-- Windows suggested by the seeds.  The read is cut into `k + 1` seeds of
`q = n / (k + 1)` letters.  For each place the lookup reports for a seed's
first `l0` letters, and that `keep` accepts for the whole seed, emit the
windows with start `place - j*q - s` and length `n + s + t` for each allowed
shape `(s, t)`. -/
def seedCandidatesK (keep : List Char → Nat × Nat → Bool) (lookup : List Char → List (Nat × Nat))
    (l0 : Nat) (read : List Char) (k d d2 : Nat) : List Window :=
  let q := read.length / (k + 1)
  let sh := shapes d d2
  (List.range (k + 1)).flatMap fun j =>
    let seed := (read.drop (j * q)).take q
    ((lookup (seed.take l0)).filter (keep seed)).flatMap fun place =>
      sh.filterMap fun st =>
        if ((j * q : Nat) : Int) + st.1 ≤ place.2 ∧ 0 ≤ (read.length : Int) + st.1 + st.2 then
          some { chr := place.1, start := ((place.2 : Int) - (j * q : Nat) - st.1).toNat,
                 len := ((read.length : Int) + st.1 + st.2).toNat }
        else none

/-- Windows to score.  Reads too short to seed fall back to every window. -/
def candidatesK (keep : List Char → Nat × Nat → Bool) (lookup : List Char → List (Nat × Nat))
    (l0 : Nat) (g : Genome) (read : List Char) (k d d2 : Nat) : List Window :=
  if 0 < l0 ∧ l0 ≤ read.length / (k + 1) then seedCandidatesK keep lookup l0 read k d d2
  else allWindows g

def mapWithK (keep : List Char → Nat × Nat → Bool) (lookup : List Char → List (Nat × Nat))
    (score : Window → Option Int) (l0 : Nat) (T : Int) (k d d2 : Nat) (g : Genome)
    (read : List Char) : Option (Window × Int) :=
  selectUnique (hitsOf score T (candidatesK keep lookup l0 g read k d d2))

/-- Does `seed` occur in the genome at `place`? -/
def seedOccurs (g : Genome) (seed : List Char) (place : Nat × Nat) : Bool :=
  match g[place.1]? with
  | some c => (c.seq.drop place.2).take seed.length == seed
  | none => false

/-- Every seed hit kept. -/
def mapWith2 (lookup : List Char → List (Nat × Nat)) (score : Window → Option Int)
    (l0 : Nat) (T : Int) (k d d2 : Nat) (g : Genome) (read : List Char) : Option (Window × Int) :=
  mapWithK (fun _ _ => true) lookup score l0 T k d d2 g read

/-- Seed hits kept only where the whole seed occurs. -/
def mapWith2V (lookup : List Char → List (Nat × Nat)) (score : Window → Option Int)
    (l0 : Nat) (T : Int) (k d d2 : Nat) (g : Genome) (read : List Char) : Option (Window × Int) :=
  mapWithK (seedOccurs g) lookup score l0 T k d d2 g read

def mapWithIndex2 (sc : Scoring) (T : Int) (idx : Index) (read : List Char) : Option (Window × Int) :=
  mapWith2 idx.lookup (kernelScore sc read idx.genome) idx.l0 T
    (seedBound sc T) (gapBound sc T) (gapBound2 sc T) idx.genome read

def mapWithIndex2V (sc : Scoring) (T : Int) (idx : Index) (read : List Char) : Option (Window × Int) :=
  mapWith2V idx.lookup (kernelScore sc read idx.genome) idx.l0 T
    (seedBound sc T) (gapBound sc T) (gapBound2 sc T) idx.genome read

def indexMapper2 (l0 : Nat) (sc : Scoring) (T : Int) (g : Genome) (read : List Char) :
    Option (Window × Int) :=
  mapWithIndex2 sc T (buildIndex l0 g) read

def indexMapper2V (l0 : Nat) (sc : Scoring) (T : Int) (g : Genome) (read : List Char) :
    Option (Window × Int) :=
  mapWithIndex2V sc T (buildIndex l0 g) read

def mapReads2 (l0 : Nat) (sc : Scoring) (T : Int) (g : Genome) (reads : List (List Char)) :
    List (Option (Window × Int)) :=
  let idx := buildIndex l0 g
  reads.map (mapWithIndex2 sc T idx)

def mapReads2V (l0 : Nat) (sc : Scoring) (T : Int) (g : Genome) (reads : List (List Char)) :
    List (Option (Window × Int)) :=
  let idx := buildIndex l0 g
  reads.map (mapWithIndex2V sc T idx)

/-! ## The theorems

    mapWith2  lookup score l0 T (seedBound sc T) (gapBound sc T) (gapBound2 sc T) g read
      = mapSpec sc T g read                                                  (mapWith2_eq_mapSpec)
    mapWith2V … = mapSpec sc T g read                                        (mapWith2V_eq_mapSpec)
    indexMapper2 l0 sc T g read = mapSpec sc T g read                        (indexMapper2_eq_mapSpec)
    indexMapper2V l0 sc T g read = mapSpec sc T g read                       (indexMapper2V_eq_mapSpec)
    mapReads2 l0 sc T g reads = reads.map (mapSpec sc T g)                   (mapReads2_eq_mapSpec)
    mapReads2V l0 sc T g reads = reads.map (mapSpec sc T g)                  (mapReads2V_eq_mapSpec)

given `ValidScoring sc`, and for `mapWith2`/`mapWith2V` a complete lookup
(`LookupComplete g l0 lookup`) and a scorer equal to `windowScore`. -/

/-! ## Proof -/

/-- `keep` accepts every place where the seed occurs. -/
def KeepComplete (g : Genome) (keep : List Char → Nat × Nat → Bool) : Prop :=
  ∀ (c : Nat) (chromosome : Chromosome) (p : Nat) (w : List Char), g[c]? = some chromosome →
    p + w.length ≤ chromosome.seq.length → (chromosome.seq.drop p).take w.length = w →
    keep w (c, p) = true

theorem keepAll_complete (g : Genome) : KeepComplete g (fun _ _ => true) :=
  fun _ _ _ _ _ _ _ => rfl

theorem seedOccurs_complete (g : Genome) : KeepComplete g (seedOccurs g) := by
  intro c chromosome p w hc _ hw
  simp [seedOccurs, hc, hw]

theorem mem_shapes (d d2 : Nat) (s t : Int) (h : shapeOk d d2 s t) : (s, t) ∈ shapes d d2 := by
  unfold shapes
  rw [List.mem_filter]
  refine ⟨?_, decide_eq_true h⟩
  have h1 := h.1
  rw [List.mem_flatMap]
  refine ⟨(s + d).toNat, List.mem_range.mpr (by omega), ?_⟩
  rw [List.mem_map]
  refine ⟨(t + d).toNat, List.mem_range.mpr (by omega), ?_⟩
  simp only [Prod.mk.injEq]
  omega

/-- Every window the specification can report is among the candidates. -/
theorem mem_candidatesK (keep : List Char → Nat × Nat → Bool) (lookup : List Char → List (Nat × Nat))
    (l0 : Nat) (sc : Scoring) (hv : ValidScoring sc) (T : Int) (g : Genome)
    (hl : LookupComplete g l0 lookup) (hk : KeepComplete g keep)
    (read : List Char) (w : Window) (s : Int)
    (hscore : windowScore sc read g w = some s) (hT : T ≤ s) :
    w ∈ candidatesK keep lookup l0 g read (seedBound sc T) (gapBound sc T) (gapBound2 sc T) := by
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
      unfold candidatesK
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
            simp only [seedCandidatesK, hq]
            rw [List.mem_flatMap]
            refine ⟨j, List.mem_range.mpr (by omega), ?_⟩
            rw [List.mem_flatMap]
            refine ⟨(w.chr, w.start + o), ?_, ?_⟩
            · rw [List.mem_filter]
              constructor
              · have hkey : ((read.drop (j * q)).take q).take l0 =
                    (chromosome.seq.drop (w.start + o)).take l0 := by
                  rw [← hgen, List.take_take, Nat.min_eq_left hcond.2]
                rw [hkey]
                exact hl w.chr chromosome (w.start + o) hc (by omega)
              · exact hk w.chr chromosome (w.start + o) _ hc (by rw [hseedlen]; omega)
                  (by rw [hseedlen]; exact hgen)
            · rw [List.mem_filterMap]
              refine ⟨_, mem_shapes _ _ _ _ hshape, ?_⟩
              rw [if_pos (by constructor <;> omega)]
              cases w
              simp only [Option.some.injEq, Window.mk.injEq] at *
              refine ⟨trivial, by omega, by omega⟩
          · cases hseq
      · exact (mem_allWindows g w).mpr (by rw [hseq]; rfl)

/-- The general theorem, for any `keep` that accepts every occurrence. -/
theorem mapWithK_eq_mapSpec (keep : List Char → Nat × Nat → Bool)
    (lookup : List Char → List (Nat × Nat)) (score : Window → Option Int)
    (l0 : Nat) (sc : Scoring) (hv : ValidScoring sc) (T : Int) (g : Genome) (read : List Char)
    (hl : LookupComplete g l0 lookup) (hk : KeepComplete g keep)
    (hs : ∀ w, score w = windowScore sc read g w) :
    mapWithK keep lookup score l0 T (seedBound sc T) (gapBound sc T) (gapBound2 sc T) g read
      = mapSpec sc T g read := by
  unfold mapWithK mapSpec
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
      exact ⟨mem_candidatesK keep lookup l0 sc hv T g hl hk read w s hs hT, hs, hT⟩
  · rintro ⟨w, s⟩ ha ⟨w', s'⟩ hb hww
    rw [mem_hitsOf] at ha hb
    simp only at hww
    subst hww
    have := ha.2.1.symm.trans hb.2.1
    simpa using this

/-- **Lookup and scorer.**  Same hypotheses as `mapWith_eq_mapSpec`. -/
theorem mapWith2_eq_mapSpec (lookup : List Char → List (Nat × Nat)) (score : Window → Option Int)
    (l0 : Nat) (sc : Scoring) (hv : ValidScoring sc) (T : Int) (g : Genome) (read : List Char)
    (hl : LookupComplete g l0 lookup) (hs : ∀ w, score w = windowScore sc read g w) :
    mapWith2 lookup score l0 T (seedBound sc T) (gapBound sc T) (gapBound2 sc T) g read
      = mapSpec sc T g read :=
  mapWithK_eq_mapSpec _ lookup score l0 sc hv T g read hl (keepAll_complete g) hs

/-- With full-seed verification, still the specification's answer. -/
theorem mapWith2V_eq_mapSpec (lookup : List Char → List (Nat × Nat)) (score : Window → Option Int)
    (l0 : Nat) (sc : Scoring) (hv : ValidScoring sc) (T : Int) (g : Genome) (read : List Char)
    (hl : LookupComplete g l0 lookup) (hs : ∀ w, score w = windowScore sc read g w) :
    mapWith2V lookup score l0 T (seedBound sc T) (gapBound sc T) (gapBound2 sc T) g read
      = mapSpec sc T g read :=
  mapWithK_eq_mapSpec _ lookup score l0 sc hv T g read hl (seedOccurs_complete g) hs

theorem indexMapper2_eq_mapSpec (l0 : Nat) (sc : Scoring) (hv : ValidScoring sc) (T : Int)
    (g : Genome) (read : List Char) :
    indexMapper2 l0 sc T g read = mapSpec sc T g read :=
  mapWith2_eq_mapSpec _ _ l0 sc hv T g read (buildIndex_complete l0 g) (kernelScore_eq sc read g)

theorem indexMapper2V_eq_mapSpec (l0 : Nat) (sc : Scoring) (hv : ValidScoring sc) (T : Int)
    (g : Genome) (read : List Char) :
    indexMapper2V l0 sc T g read = mapSpec sc T g read :=
  mapWith2V_eq_mapSpec _ _ l0 sc hv T g read (buildIndex_complete l0 g) (kernelScore_eq sc read g)

theorem mapWithIndex2_eq_mapSpec (l0 : Nat) (sc : Scoring) (hv : ValidScoring sc) (T : Int)
    (g : Genome) (idx : Index) (hidx : idx = buildIndex l0 g) (read : List Char) :
    mapWithIndex2 sc T idx read = mapSpec sc T g read := by
  subst hidx; exact indexMapper2_eq_mapSpec l0 sc hv T g read

theorem mapWithIndex2V_eq_mapSpec (l0 : Nat) (sc : Scoring) (hv : ValidScoring sc) (T : Int)
    (g : Genome) (idx : Index) (hidx : idx = buildIndex l0 g) (read : List Char) :
    mapWithIndex2V sc T idx read = mapSpec sc T g read := by
  subst hidx; exact indexMapper2V_eq_mapSpec l0 sc hv T g read

theorem mapReads2_eq_mapSpec (l0 : Nat) (sc : Scoring) (hv : ValidScoring sc) (T : Int)
    (g : Genome) (reads : List (List Char)) :
    mapReads2 l0 sc T g reads = reads.map (mapSpec sc T g) := by
  unfold mapReads2
  apply List.map_congr_left
  intro read _
  exact mapWithIndex2_eq_mapSpec l0 sc hv T g _ rfl read

theorem mapReads2V_eq_mapSpec (l0 : Nat) (sc : Scoring) (hv : ValidScoring sc) (T : Int)
    (g : Genome) (reads : List (List Char)) :
    mapReads2V l0 sc T g reads = reads.map (mapSpec sc T g) := by
  unfold mapReads2V
  apply List.map_congr_left
  intro read _
  exact mapWithIndex2V_eq_mapSpec l0 sc hv T g _ rfl read

end MapSpec

#print axioms MapSpec.mapWith2_eq_mapSpec
#print axioms MapSpec.mapWith2V_eq_mapSpec
#print axioms MapSpec.indexMapper2_eq_mapSpec
#print axioms MapSpec.indexMapper2V_eq_mapSpec
#print axioms MapSpec.mapWithIndex2_eq_mapSpec
#print axioms MapSpec.mapWithIndex2V_eq_mapSpec
#print axioms MapSpec.mapReads2_eq_mapSpec
#print axioms MapSpec.mapReads2V_eq_mapSpec
