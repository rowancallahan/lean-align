import Proofs.Whole
import TierHeur

/-! # M2: reporting the found pair (placements and CIGARs)

The router answers on the packed genome as ONE sequence (`Proofs/Whole.lean`). For a reported mate
we get a CIGAR from a fast unproved aligner (`TierHeur.bandDP` at the mate's window; or the router's
own checked runs), re-check it with the proved `MapSpec.Fast.chkCand` (`chkCand_sound`: a real
alignment of the read at that placement with that score), and move the placement from the whole
sequence back to its chromosome (`alignment_unshift`). Any failure (check fails, the window crosses
a chromosome end, the pair is not proper) reports nothing for the pair: the bounds-only answer stays
correct. -/

namespace Spec.Report

open Bridge

/-! ## Old CIGAR → new report -/

-- one mate's line from an old placement and its runs
def mateReportOf (x : MapSpec.Placement × Int) (runs : List (AlignmentSpec.Step × Nat)) : MateReport :=
  ⟨newPlacement x.1, (encodeCigar ((AlignmentSpec.expandCigar runs.toArray).map Hits.newStepOf)).toArray, x.2⟩

theorem newStrand_orient (read : Read) (s : MapSpec.Strand) :
    (newStrand s).orient read = MapSpec.Fast.strandRead read s := by
  cases s <;> simp [newStrand, Strand.orient, MapSpec.Fast.strandRead, reverseComplement, MapSpec.revComp,
    Hits.complement_eq]

-- a re-checked CIGAR is an alignment that prints as `mateReportOf`
theorem alignment_of_cigar {genome : Genome} {read : Read} {x : MapSpec.Placement × Int}
    {runs : List (AlignmentSpec.Step × Nat)} (h : MapSpec.Fast.CigarOk (oldGenome genome) read x runs) :
    ∃ a : GenomicAlignment genome read, a.report = mateReportOf x runs := by
  obtain ⟨⟨⟨c, st, len⟩, sd⟩, sc⟩ := x
  obtain ⟨ys, hws, hw, hs⟩ := h
  simp only at hws hw hs
  rw [← newStrand_orient] at hw hs
  have hfit : (newPlacement ((⟨c, st, len⟩, sd) : MapSpec.Placement)).reference genome = some ys := by
    refine (Hits.reference_iff _ _ _).2 ⟨by simp [newPlacement], ?_⟩
    have e : st + len - st = len := by omega
    simpa [newPlacement, e, Hits.og, oldGenome] using hws
  refine ⟨⟨_, ys, hfit, Hits.pathOfWalk hw⟩, ?_⟩
  have hsc := Hits.score_pathOfWalk hw
  simp only [GenomicAlignment.report, mateReportOf, Path.cigar, GenomicAlignment.score]
  congr 1
  exact hsc.trans hs

/-! ## Back from the whole sequence to its chromosome -/

section unshift
variable {genome : Genome} {name : String} {W : Read} {off : Nat → Nat}

-- a placement on the whole sequence, moved to chromosome `c` starting at `o`
def unshiftP (c o : Nat) (p : Placement) : Placement :=
  { p with chromosome := c, start := p.start - o, stop := p.stop - o }

theorem reference_unshift
    (hslice : ∀ c chr, genome[c]? = some chr →
      off c + chr.seq.length ≤ W.length ∧ chr.seq = (W.drop (off c)).take chr.seq.length)
    {p : Placement} {ref : Read} (h : p.reference [⟨name, W⟩] = some ref) (c : Nat) (chr : Chromosome)
    (hc : genome[c]? = some chr) (h1 : off c ≤ p.start) (h2 : p.stop ≤ off c + chr.seq.length) :
    (unshiftP c (off c) p).reference genome = some ref := by
  obtain ⟨-, hseq⟩ := hslice c chr hc
  unfold Placement.reference at h ⊢
  have h0 : p.chromosome = 0 := by
    rcases hp : p.chromosome with _ | k
    · rfl
    · rw [hp] at h; simp at h
  rw [h0] at h
  simp only [List.getElem?_cons_zero] at h
  split at h
  · rename_i hp
    cases h
    simp only [unshiftP, hc]
    have hc1 : p.start - off c ≤ p.stop - off c := by omega
    have hc2 : p.stop - off c ≤ chr.seq.length := by omega
    simp only [hc1, hc2, and_self, ite_true, Option.some.injEq]
    generalize hL : chr.seq.length = L at hc2 hseq h2
    rw [hseq, List.drop_take, List.drop_drop, List.take_take]
    have e1 : min (p.stop - off c - (p.start - off c)) (L - (p.start - off c)) = p.stop - p.start := by omega
    have e2 : off c + (p.start - off c) = p.start := by omega
    rw [e1, e2]
  · cases h

-- an alignment on the whole sequence inside chromosome `c` is one on the genome, same path and score
theorem alignment_unshift
    (hslice : ∀ c chr, genome[c]? = some chr →
      off c + chr.seq.length ≤ W.length ∧ chr.seq = (W.drop (off c)).take chr.seq.length)
    {read : Read} (b : GenomicAlignment [⟨name, W⟩] read) (c : Nat) (chr : Chromosome)
    (hc : genome[c]? = some chr) (h1 : off c ≤ b.placement.start)
    (h2 : b.placement.stop ≤ off c + chr.seq.length) :
    ∃ a : GenomicAlignment genome read,
      a.report = { b.report with placement := unshiftP c (off c) b.placement } :=
  ⟨⟨unshiftP c (off c) b.placement, b.reference, reference_unshift hslice b.fits c chr hc h1 h2, b.path⟩, rfl⟩

end unshift

/-! ## The reporter (runtime) -/

open MapSpec.Fast

-- the CIGAR at `x` from the unproved banded DP on the window's letters (every result is re-checked)
def alignAt (G : PGen) (R Rr : ByteArray) (x : MapSpec.Placement × Int) :
    Option ((MapSpec.Placement × Int) × List (AlignmentSpec.Step × Nat)) :=
  let X := if x.1.2 = .fwd then R else Rr
  let W := TierHeur.winL G x.1.1.start (x.1.1.start + x.1.1.len)
  match TierHeur.bandDP X W 0 16 1000000 with
  | some (cs, len, pen, runs) => some ((⟨⟨x.1.1.chr, x.1.1.start + cs, len⟩, x.1.2⟩, -(pen : Int)), runs)
  | none => none

-- the chromosome holding letters `[s, e)` of the whole sequence
def chromOf (offs ns : Array Nat) (s e : Nat) : Option Nat :=
  (List.range ns.size).find? fun c => decide (offs[c]! ≤ s) && decide (e ≤ offs[c]! + ns[c]!)

-- a proposed alignment `h` with CIGAR `runs` (whole sequence `pgs`): re-checked, moved to its chromosome
def checkMove (pgs : Array PGen) (offs ns : Array Nat) (R : ByteArray)
    (h : MapSpec.Placement × Int) (runs : List (AlignmentSpec.Step × Nat)) : Option MateReport :=
  if chkCand pgs R (revCompK R) h runs then
    let r := mateReportOf h runs
    match chromOf offs ns r.placement.start r.placement.stop with
    | some c => some { r with placement := unshiftP c offs[c]! r.placement }
    | none => none
  else none

-- the proposed CIGAR of a mate placed at `x`: the router's checked runs, else the banded DP
def proposal (pgs : Array PGen) (R : ByteArray) (m : MateX) (x : MapSpec.Placement × Int) :
    Option ((MapSpec.Placement × Int) × List (AlignmentSpec.Step × Nat)) :=
  if m.cg then some (x, m.runs) else alignAt pgs[0]! R (revCompK R) x

-- one mate's line
def mateOf (pgs : Array PGen) (offs ns : Array Nat) (R : ByteArray) (m : MateX) : Option MateReport :=
  (m.pl.bind (proposal pgs R m)).bind fun (h, runs) => checkMove pgs offs ns R h runs

-- tags whose mates' placements form the pair in hand
def reportable : Tag → Bool
  | .t1 | .t1g | .t1u | .t2b | .t2 => true
  | _ => false

-- the pair in hand, printed, when both mates re-check and the pair is proper
def foundOf (slack lo hi : Nat) (pgs : Array PGen) (offs ns : Array Nat) (R1 R2 : ByteArray)
    (t : TierOut) : Option PairReport :=
  if reportable t.tag then
    match mateOf pgs offs ns R1 t.m1, mateOf pgs offs ns R2 t.m2 with
    | some a, some b =>
      if MapSpec.properPairU slack lo hi (oldPlacement a.placement) (oldPlacement b.placement) then
        some ⟨a, b⟩
      else none
    | _, _ => none
  else none

/-! ## The reporter is sound -/

section sound
variable {genome : Genome} {G : PGen} {offs ns : Array Nat}

theorem chromOf_some {s e c : Nat} (h : chromOf offs ns s e = some c) :
    c < ns.size ∧ offs[c]! ≤ s ∧ e ≤ offs[c]! + ns[c]! := by
  unfold chromOf at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  exact ⟨List.mem_range.1 hm, hp⟩

theorem checkMove_sound
    (hslice : ∀ (c : Nat) (chr : Chromosome), genome[c]? = some chr →
      offs[c]! + chr.seq.length ≤ (decodeRead (MapSpec.Mz.unpack G)).length ∧
      chr.seq = ((decodeRead (MapSpec.Mz.unpack G)).drop offs[c]!).take chr.seq.length)
    (hchr : ∀ c, c < ns.size → ∃ chr : Chromosome, genome[c]? = some chr ∧ chr.seq.length = ns[c]!)
    (R : ByteArray) (x : MapSpec.Placement × Int) (runs : List (AlignmentSpec.Step × Nat)) (r : MateReport)
    (h : checkMove (cutAll G #[0] #[G.n]) offs ns R x runs = some r) :
    ∃ a : GenomicAlignment genome (decodeRead R), a.report = r := by
  unfold checkMove at h
  split at h
  · rename_i hc
    obtain ⟨hcig, -⟩ := chkCand_sound _ _ (Whole.genomeBytes_whole G) R _ (encodes_decodeRead R) _ runs hc
    obtain ⟨b, hb⟩ := alignment_of_cigar hcig
    dsimp only at h
    split at h
    · rename_i c hcO
      cases h
      obtain ⟨hcn, h1, h2⟩ := chromOf_some hcO
      obtain ⟨chr, hgc, hlen⟩ := hchr c hcn
      have hpl : b.placement = (mateReportOf x runs).placement := congrArg MateReport.placement hb
      obtain ⟨a, ha⟩ := alignment_unshift (name := "") (W := decodeRead (MapSpec.Mz.unpack G))
        (off := fun c => offs[c]!) hslice b c chr hgc (by rw [hpl]; exact h1) (by rw [hpl, hlen]; exact h2)
      refine ⟨a, ha.trans ?_⟩
      show MateReport.mk (unshiftP c offs[c]! b.placement) b.report.cigar b.report.score = _
      rw [hpl, hb]
    · cases h
  · cases h

theorem mateOf_sound
    (hslice : ∀ (c : Nat) (chr : Chromosome), genome[c]? = some chr →
      offs[c]! + chr.seq.length ≤ (decodeRead (MapSpec.Mz.unpack G)).length ∧
      chr.seq = ((decodeRead (MapSpec.Mz.unpack G)).drop offs[c]!).take chr.seq.length)
    (hchr : ∀ c, c < ns.size → ∃ chr : Chromosome, genome[c]? = some chr ∧ chr.seq.length = ns[c]!)
    (R : ByteArray) (m : MateX) (r : MateReport)
    (h : mateOf (cutAll G #[0] #[G.n]) offs ns R m = some r) :
    ∃ a : GenomicAlignment genome (decodeRead R), a.report = r := by
  unfold mateOf at h
  cases hp : (m.pl.bind (proposal (cutAll G #[0] #[G.n]) R m)) with
  | none => rw [hp] at h; cases h
  | some q =>
    rw [hp] at h
    exact checkMove_sound hslice hchr R q.1 q.2 r h

theorem foundOf_sound
    (hslice : ∀ (c : Nat) (chr : Chromosome), genome[c]? = some chr →
      offs[c]! + chr.seq.length ≤ (decodeRead (MapSpec.Mz.unpack G)).length ∧
      chr.seq = ((decodeRead (MapSpec.Mz.unpack G)).drop offs[c]!).take chr.seq.length)
    (hchr : ∀ c, c < ns.size → ∃ chr : Chromosome, genome[c]? = some chr ∧ chr.seq.length = ns[c]!)
    (insertSettings : InsertSettings) (R1 R2 : ByteArray) (t : TierOut) (rep : PairReport)
    (h : foundOf insertSettings.dovetailSlack insertSettings.range.1 insertSettings.range.2
      (cutAll G #[0] #[G.n]) offs ns R1 R2 t = some rep) :
    ∃ pair : PairAlignment genome (decodeRead R1) (decodeRead R2),
      pair.report = rep ∧ pair.IsProper insertSettings.range insertSettings.dovetailSlack := by
  unfold foundOf at h
  split at h
  · split at h
    · rename_i a b h1 h2
      split at h
      · rename_i hp
        cases h
        obtain ⟨x, hx⟩ := mateOf_sound hslice hchr R1 _ a h1
        obtain ⟨y, hy⟩ := mateOf_sound hslice hchr R2 _ b h2
        refine ⟨⟨x, y⟩, by simp only [PairAlignment.report, hx, hy], ?_⟩
        rw [isProper_iff]
        have px : x.placement = a.placement := by rw [← hx]; rfl
        have py : y.placement = b.placement := by rw [← hy]; rfl
        simp only [px, py]
        exact hp
      · cases h
    · cases h
  · cases h

end sound

/-! ## The answer with the found pair -/

-- `a` with `found := f`
def withFound (a : PairAnswer) (f : Option PairReport) : PairAnswer := { a with found := f }

-- a bounds-only correct answer stays correct with any found pair that is a real proper pair
theorem withFound_correct {insertSettings : InsertSettings} {genome : Genome} {m1 m2 : Read}
    (a : PairAnswer) (f : Option PairReport) (ha : a.Correct insertSettings genome m1 m2)
    (hu : a.uniqueness = .unknown)
    (hf : ∀ rep, f = some rep → ∃ pair : PairAlignment genome m1 m2,
      pair.report = rep ∧ pair.IsProper insertSettings.range insertSettings.dovetailSlack) :
    (withFound a f).Correct insertSettings genome m1 m2 := by
  refine ⟨hf, ha.2.1, ?_⟩
  simp [withFound, hu]

end Spec.Report
