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

/-! ## Part 2: the banded scorer -/

/-- The chromosomes as bytes. -/
def GenomeBytes (gbs : Array ByteArray) (g : Genome) : Prop :=
  gbs.size = g.length ∧ ∀ c (h1 : c < gbs.size) (h2 : c < g.length), Encodes gbs[c] g[c].seq

/-- Score of one window through the banded kernel: `none` when the window
does not fit, is more than `B` letters longer or shorter than the read, or
when the kernel finds every window ending where it ends below `T`. -/
@[specialize] def bandScore {Gt : Type} [GRead Gt] (sc : Scoring) (T : Int) (B : Nat) (rb : ByteArray) (gbs : Array Gt)
    (w : Window) : Option Int :=
  if h : w.chr < gbs.size then
    if w.start + w.len ≤ GRead.size gbs[w.chr] ∧ rb.size ≤ w.len + B ∧ w.len ≤ rb.size + B then
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
  unfold bandScore; try simp -zeta only [GRead.get_bytes, GRead.size_bytes]
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

end MapSpec

#print axioms MapSpec.bandEnd_spec
#print axioms MapSpec.bandEnd2_spec
#print axioms MapSpec.bandScore_faithful
