import SeedMapper
import MapperBandFast

/-!
# Codec `bandScore`: capped banded score-only window scorer

Part 1: a scorer only has to be right about windows scoring at least `T`
(`ScoreFaithful`); `mapWith` with such a scorer is `mapSpec`.

Part 2: `bandScore`, the window scorer built on the banded kernel `bandEnd`
(`pool/mapper/MapperBandKernel.lean`, proof in `MapperBandProof.lean`;
the leaner `bandEnd2` in `MapperBandFast.lean` is the one used here), is
faithful (`bandScore_faithful`), so `bandMapper` = `mapSpec`
(`bandMapper_eq_mapSpec`).  `bandEnd` scores all `2B+1` windows ending at one
place in a single pass; `bandScore` exposes one of them per call.

Choice of input format: read and chromosomes are `ByteArray`s, one byte per
letter, related to the `List Char` genome by `Encodes` (byte = letter code;
`toBytes` builds them when every letter is `< 256`).
-/

namespace MapSpec

open AlignmentSpec

/-- The scorer agrees with the specification on every score `≥ T`, and on
nothing else. -/
def ScoreFaithful (sc : Scoring) (T : Int) (read : List Char) (g : Genome)
    (score : Window → Option Int) : Prop :=
  ∀ w s, (score w = some s ∧ T ≤ s) ↔ (windowScore sc read g w = some s ∧ T ≤ s)

/-- `hitsOf` only looks at scores `≥ T`. -/
theorem hitsOf_congr_faithful (sc : Scoring) (T : Int) (read : List Char) (g : Genome)
    (score : Window → Option Int) (hf : ScoreFaithful sc T read g score) (ws : List Window) :
    hitsOf score T ws = hitsOf (windowScore sc read g) T ws := by
  unfold hitsOf
  induction ws with
  | nil => rfl
  | cons w ws ih =>
  rw [List.filterMap_cons, List.filterMap_cons, ih]
  congr 1
  have h := hf w
  cases h1 : score w with
  | none =>
    cases h2 : windowScore sc read g w with
    | none => rfl
    | some s =>
      by_cases hT : T ≤ s
      · have := (h s).mpr ⟨h2, hT⟩; rw [h1] at this; cases this.1
      · simp [hT]
  | some s =>
    by_cases hT : T ≤ s
    · have := (h s).mp ⟨h1, hT⟩
      rw [this.1]
    · simp only [hT, if_false]
      cases h2 : windowScore sc read g w with
      | none => rfl
      | some s' =>
        by_cases hT' : T ≤ s'
        · have := (h s').mpr ⟨h2, hT'⟩; rw [h1] at this
          simp at this; omega
        · simp [hT']

/-- **Faithful scorer.**  With a complete lookup and a scorer faithful at
threshold `T`, the mapper returns the specification's answer. -/
theorem mapWith_eq_mapSpec_of_faithful (lookup : List Char → List (Nat × Nat))
    (score : Window → Option Int) (l0 : Nat) (sc : Scoring) (hv : ValidScoring sc) (T : Int)
    (g : Genome) (read : List Char) (hl : LookupComplete g l0 lookup)
    (hf : ScoreFaithful sc T read g score) :
    mapWith lookup score l0 T (errBound sc T) g read = mapSpec sc T g read := by
  have h : mapWith lookup score l0 T (errBound sc T) g read =
      mapWith lookup (windowScore sc read g) l0 T (errBound sc T) g read := by
    unfold mapWith
    rw [hitsOf_congr_faithful sc T read g score hf]
  rw [h]
  exact mapWith_eq_mapSpec lookup _ l0 sc hv T g read hl (fun _ => rfl)


/-! ## Part 2: the banded scorer -/

/-- One byte per letter (letters must be `< 256`). -/
def toBytes (cs : List Char) : ByteArray := ⟨(cs.map fun c => c.toNat.toUInt8).toArray⟩

theorem toBytes_encodes (cs : List Char) (h : ∀ c ∈ cs, c.toNat < 256) : Encodes (toBytes cs) cs := by
  refine ⟨by simp [toBytes, ByteArray.size], fun i hi => ?_⟩
  have hc := h cs[i] (List.getElem_mem hi)
  show ((cs.map fun (c : Char) => c.toNat.toUInt8).toArray[i]!).toNat = _
  rw [getElem!_pos _ i (by simpa using hi)]
  simp only [List.getElem_toArray, List.getElem_map, Nat.toUInt8, UInt8.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (by omega)]

/-- The chromosomes as bytes. -/
def GenomeBytes (gbs : Array ByteArray) (g : Genome) : Prop :=
  gbs.size = g.length ∧ ∀ c (h1 : c < gbs.size) (h2 : c < g.length), Encodes gbs[c] g[c].seq

def genomeBytes (g : Genome) : Array ByteArray := (g.map fun c => toBytes c.seq).toArray

theorem genomeBytes_ok (g : Genome) (h : ∀ c : Chromosome, c ∈ g → ∀ x : Char, x ∈ c.seq → x.toNat < 256) :
    GenomeBytes (genomeBytes g) g := by
  refine ⟨by simp [genomeBytes], fun c h1 h2 => ?_⟩
  simp only [genomeBytes, List.getElem_toArray, List.getElem_map]
  exact toBytes_encodes _ (h _ (List.getElem_mem h2))

/-- Score of one window through the banded kernel: `none` when the window
does not fit, is more than `B` letters longer or shorter than the read, or
when the kernel finds every window ending where it ends below `T`. -/
def bandScore (sc : Scoring) (T : Int) (B : Nat) (rb : ByteArray) (gbs : Array ByteArray)
    (w : Window) : Option Int :=
  if h : w.chr < gbs.size then
    if w.start + w.len ≤ gbs[w.chr].size ∧ rb.size ≤ w.len + B ∧ w.len ≤ rb.size + B then
      match bandEnd2 sc T B rb gbs[w.chr] (w.start + w.len) with
      | some A => some A[w.len + B - rb.size + 1]!
      | none => none
    else none
  else none

theorem faithful_of_rel {T c v s : Int} (h : Rel T c v) :
    (some c = some s ∧ T ≤ s) ↔ (some v = some s ∧ T ≤ s) := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · rintro ⟨hc, hs⟩
    cases hc
    exact ⟨by rw [h2 hs], hs⟩
  · rintro ⟨hc, hs⟩
    cases hc
    exact ⟨by rw [h1 hs], hs⟩

/-- **The banded scorer is faithful** at `T`, for every band `B` with
`BandOK sc T B` (for example `bandOf sc T`; 3 for the default scoring). -/
theorem bandScore_faithful (sc : Scoring) (hv : ValidScoring sc) (T : Int) (B : Nat)
    (hb : BandOK sc T B) (read : List Char) (g : Genome) (rb : ByteArray) (gbs : Array ByteArray)
    (hr : Encodes rb read) (hg : GenomeBytes gbs g) :
    ScoreFaithful sc T read g (bandScore sc T B rb gbs) := by
  intro w s
  unfold bandScore
  by_cases hc : w.chr < gbs.size
  · rw [dif_pos hc]
    have hc' : w.chr < g.length := hg.1 ▸ hc
    have henc := hg.2 w.chr hc hc'
    have hseq : windowSeq g w = if w.start + w.len ≤ g[w.chr].seq.length then
        some (seg g[w.chr].seq w.start (w.start + w.len)) else none := by
      unfold windowSeq
      rw [List.getElem?_eq_getElem hc']
      simp [seg]
    by_cases hfit : w.start + w.len ≤ g[w.chr].seq.length
    · rw [if_pos hfit] at hseq
      have hws := windowScore_eq_sv sc read g w _ hseq
      have hcv : sv sc read (seg g[w.chr].seq w.start (w.start + w.len)) none =
          cv sc read g[w.chr].seq (w.start + w.len) none 0 w.start := by simp [cv]
      rw [hws, hcv]
      have hsz : gbs[w.chr].size = g[w.chr].seq.length := henc.1
      have hn : rb.size = read.length := hr.1
      by_cases hband : rb.size ≤ w.len + B ∧ w.len ≤ rb.size + B
      · rw [if_pos ⟨by omega, hband⟩]
        have hk := bandEnd2_spec sc hv T B hb read g[w.chr].seq (w.start + w.len) hfit rb gbs[w.chr]
          hr henc
        have hval : Valid read.length B (w.start + w.len) 0 (w.len + B - rb.size) := by
          unfold Valid; omega
        have hp : pOf read.length B (w.start + w.len) 0 (w.len + B - rb.size) = w.start := by
          unfold pOf; omega
        revert hk
        cases bandEnd2 sc T B rb gbs[w.chr] (w.start + w.len) with
        | some A =>
          intro hk
          have hrel := hk.2 _ (by omega) hval
          rw [hp] at hrel
          exact faithful_of_rel hrel
        | none =>
          intro hk
          have hlt := (hk w.start (by omega)).1
          simp only [reduceCtorEq, false_and, false_iff, not_and, Option.some.injEq]
          intro hs; omega
      · rw [if_neg (by omega)]
        have hoff := cv_off_band sc hv T B hb read g[w.chr].seq (w.start + w.len) hfit none 0 w.start
          (by omega)
        simp only [thr] at hoff
        simp only [reduceCtorEq, false_and, false_iff, not_and, Option.some.injEq]
        intro hs; omega
    · rw [if_neg hfit] at hseq
      have hsz : gbs[w.chr].size = g[w.chr].seq.length := henc.1
      rw [if_neg (by omega)]
      simp [windowScore, hseq]
  · rw [dif_neg hc]
    have : windowSeq g w = none := by
      unfold windowSeq
      rw [List.getElem?_eq_none (by have := hg.1; omega)]
    simp [windowScore, this]

/-- The mapper with the banded scorer. -/
def bandMapper (lookup : List Char → List (Nat × Nat)) (l0 : Nat) (sc : Scoring) (T : Int)
    (g : Genome) (gbs : Array ByteArray) (read : List Char) (rb : ByteArray) : Option (Window × Int) :=
  mapWith lookup (bandScore sc T (bandOf sc T) rb gbs) l0 T (errBound sc T) g read

/-- **Mapper with the banded scorer = specification**, for a complete
lookup, a valid scoring, and read and chromosomes given as bytes. -/
theorem bandMapper_eq_mapSpec (lookup : List Char → List (Nat × Nat)) (l0 : Nat) (sc : Scoring)
    (hv : ValidScoring sc) (T : Int) (g : Genome) (gbs : Array ByteArray) (read : List Char)
    (rb : ByteArray) (hl : LookupComplete g l0 lookup) (hr : Encodes rb read)
    (hg : GenomeBytes gbs g) :
    bandMapper lookup l0 sc T g gbs read rb = mapSpec sc T g read :=
  mapWith_eq_mapSpec_of_faithful lookup _ l0 sc hv T g read hl
    (bandScore_faithful sc hv T (bandOf sc T) (bandOf_ok sc hv T) read g rb gbs hr hg)

/-- Same, with the index of `SeedMapper`. -/
theorem bandMapper_index_eq_mapSpec (l0 : Nat) (sc : Scoring) (hv : ValidScoring sc) (T : Int)
    (g : Genome) (read : List Char) (h : ∀ c : Chromosome, c ∈ g → ∀ x : Char, x ∈ c.seq → x.toNat < 256)
    (hread : ∀ x ∈ read, x.toNat < 256) :
    bandMapper (buildIndex l0 g).lookup l0 sc T g (genomeBytes g) read (toBytes read) =
      mapSpec sc T g read :=
  bandMapper_eq_mapSpec _ l0 sc hv T g _ read _ (buildIndex_complete l0 g)
    (toBytes_encodes read hread) (genomeBytes_ok g h)

end MapSpec

#print axioms MapSpec.mapWith_eq_mapSpec_of_faithful
#print axioms MapSpec.bandEnd_spec
#print axioms MapSpec.bandEnd2_spec
#print axioms MapSpec.bandScore_faithful
#print axioms MapSpec.bandMapper_eq_mapSpec
#print axioms MapSpec.bandMapper_index_eq_mapSpec
