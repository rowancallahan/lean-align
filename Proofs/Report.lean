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

-- runs merged: zero counts dropped, equal neighbours joined (`encodeCigar` of their expansion, `encodeCigar_expand`)
def mergeRuns : List (Step × Nat) → List (Step × Nat)
  | [] => []
  | (_, 0) :: rest => mergeRuns rest
  | (s, n + 1) :: rest =>
    match mergeRuns rest with
    | [] => [(s, n + 1)]
    | (t, k) :: tl => if s = t then (s, n + 1 + k) :: tl else (s, n + 1) :: (t, k) :: tl

theorem encodeCigar_replicate (s : Step) (rest : List Step) : ∀ n,
    encodeCigar (List.replicate (n + 1) s ++ rest) =
      match encodeCigar rest with
      | [] => [(s, n + 1)]
      | (t, k) :: tl => if s = t then (s, n + 1 + k) :: tl else (s, n + 1) :: (t, k) :: tl
  | 0 => by
    simp only [List.replicate, List.cons_append, List.nil_append, encodeCigar]
    cases encodeCigar rest with
    | nil => rfl
    | cons h tl => obtain ⟨t, k⟩ := h; simp only [Nat.add_comm]
  | n + 1 => by
    rw [List.replicate_succ, List.cons_append, encodeCigar, encodeCigar_replicate s rest n]
    cases encodeCigar rest with
    | nil => simp
    | cons h tl =>
      obtain ⟨t, k⟩ := h
      by_cases hst : s = t
      · subst hst; simp; omega
      · simp [hst]

theorem encodeCigar_expand : ∀ runs : List (Step × Nat),
    encodeCigar (runs.flatMap fun (s, n) => List.replicate n s) = mergeRuns runs
  | [] => rfl
  | (s, 0) :: rest => by simp [mergeRuns, encodeCigar_expand rest]
  | (s, n + 1) :: rest => by
    rw [List.flatMap_cons, encodeCigar_replicate, encodeCigar_expand rest, mergeRuns]

-- one mate's line from an old placement and its runs
def mateReportOf (x : MapSpec.Placement × Int) (runs : List (AlignmentSpec.Step × Nat)) : MateReport :=
  ⟨newPlacement x.1, (mergeRuns (runs.map fun (s, n) => (Hits.newStepOf s, n))).toArray, x.2⟩

theorem mateReportOf_cigar (runs : List (AlignmentSpec.Step × Nat)) :
    encodeCigar ((AlignmentSpec.expandCigar runs.toArray).map Hits.newStepOf) =
      mergeRuns (runs.map fun (s, n) => (Hits.newStepOf s, n)) := by
  rw [← encodeCigar_expand]
  congr 1
  simp only [AlignmentSpec.expandCigar, List.map_flatMap, List.flatMap_map, List.map_replicate]

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
  · show (encodeCigar ((AlignmentSpec.expandCigar runs.toArray).map Hits.newStepOf)).toArray = _
    rw [mateReportOf_cigar]
  · exact hsc.trans hs

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

-- runs for the read over exactly `x`'s window from the unproved banded DP (every result is re-checked)
-- The DP's bound is the router's penalty + 1: `checkMove` keeps only runs whose re-checked score is `x.2`,
-- and runs of penalty ≥ `−x.2 + 1` can never pass, so cells at or above it are not needed (same lines).
def alignAt (G : PGen) (R Rr : ByteArray) (x : MapSpec.Placement × Int) : Option (List (AlignmentSpec.Step × Nat)) :=
  let X := if x.1.2 = .fwd then R else Rr
  let W := TierHeur.winL G x.1.1.start (x.1.1.start + x.1.1.len)
  match TierHeur.bandDP X W 0 16 ((-x.2).toNat + 1) with
  | some (cs, len, _, runs) => if cs == 0 && len == x.1.1.len then some runs else none
  | none => none

-- the one chromosome whose slice of the whole sequence holds letters `[s, e)` (none: no or several)
def chromOf (offs ns : Array Nat) (s e : Nat) : Option Nat :=
  match (List.range ns.size).filter (fun c => decide (offs[c]! ≤ s) && decide (e ≤ offs[c]! + ns[c]!)) with
  | [c] => some c
  | _ => none

-- `chromOf` without the list: chromosomes `c, c + 1, …` (`k` of them), `r` = the one match so far
-- (a second match ends the scan with `none`).  Compiled code runs it (`chromOf_eqL`).
def chromGo (offs ns : Array Nat) (s e : Nat) : Nat → Nat → Option Nat → Option Nat
  | 0, _, r => r
  | k + 1, c, none =>
    if decide (offs[c]! ≤ s) && decide (e ≤ offs[c]! + ns[c]!) then chromGo offs ns s e k (c + 1) (some c)
    else chromGo offs ns s e k (c + 1) none
  | k + 1, c, some d =>
    if decide (offs[c]! ≤ s) && decide (e ≤ offs[c]! + ns[c]!) then none
    else chromGo offs ns s e k (c + 1) (some d)

-- the one element of `r` and `l` together (none: no or several)
def onlyOf : Option Nat → List Nat → Option Nat
  | none, [c] => some c
  | some d, [] => some d
  | _, _ => none

theorem chromGo_eq (offs ns : Array Nat) (s e : Nat) : ∀ k c r,
    chromGo offs ns s e k c r =
      onlyOf r ((List.range' c k).filter (fun c => decide (offs[c]! ≤ s) && decide (e ≤ offs[c]! + ns[c]!)))
  | 0, c, none => rfl
  | 0, c, some d => rfl
  | k + 1, c, none => by
    rw [List.range'_succ, List.filter_cons, chromGo]
    by_cases h : (decide (offs[c]! ≤ s) && decide (e ≤ offs[c]! + ns[c]!)) = true
    · rw [if_pos h, if_pos h, chromGo_eq offs ns s e k (c + 1)]
      cases (List.range' (c + 1) k).filter _ <;> rfl
    · rw [if_neg h, if_neg h, chromGo_eq offs ns s e k (c + 1)]
  | k + 1, c, some d => by
    rw [List.range'_succ, List.filter_cons, chromGo]
    by_cases h : (decide (offs[c]! ≤ s) && decide (e ≤ offs[c]! + ns[c]!)) = true
    · rw [if_pos h, if_pos h]; rfl
    · rw [if_neg h, if_neg h, chromGo_eq offs ns s e k (c + 1)]

theorem ausN_le (a : Array Nat) : a.usize.toNat ≤ a.size := by
  show a.size.toUSize.toNat ≤ a.size
  rw [Nat.toUSize_eq, USize.toNat_ofNat']; exact Nat.mod_le _ _

-- `chromGo` with the index in `USize` and the entries read by `uget` (`chromGoU_eq`)
def chromGoU (offs ns : @& Array Nat) (s e : Nat) (k c : USize) (r : Option Nat) : Option Nat :=
  if k = 0 then r
  else if h : c < offs.usize ∧ c < ns.usize then
    let o := offs.uget c (Nat.lt_of_lt_of_le h.1 (ausN_le offs))
    let hit := decide (o ≤ s) && decide (e ≤ o + ns.uget c (Nat.lt_of_lt_of_le h.2 (ausN_le ns)))
    match r with
    | none => if hit then chromGoU offs ns s e (k - 1) (c + 1) (some c.toNat) else chromGoU offs ns s e (k - 1) (c + 1) none
    | some d => if hit then none else chromGoU offs ns s e (k - 1) (c + 1) (some d)
  else r
termination_by k.toNat
decreasing_by
  all_goals
    have : k.toNat ≠ 0 := fun e => by apply ‹¬ k = 0›; exact USize.toNat_inj.mp (by rw [e]; rfl)
    rw [USize.toNat_sub_of_le _ _ (by show (1 : USize).toNat ≤ k.toNat; rw [MapSpec.Fast.pgu_one]; omega),
      MapSpec.Fast.pgu_one]
    omega

theorem chromGoU_eq (offs ns : Array Nat) (s e : Nat) (ho : offs.size < 4294967295) (hn : ns.size < 4294967295) :
    ∀ (k : Nat) (kU cU : USize) (c : Nat) (r : Option Nat), kU.toNat = k → cU.toNat = c →
      c + k ≤ offs.size → c + k ≤ ns.size → chromGoU offs ns s e kU cU r = chromGo offs ns s e k c r := by
  have hso : offs.usize.toNat = offs.size := MapSpec.Fast.pgu_n _ (by omega)
  have hsn : ns.usize.toNat = ns.size := MapSpec.Fast.pgu_n _ (by omega)
  intro k
  induction k with
  | zero =>
    intro kU cU c r hk _ _ _
    have : kU = 0 := USize.toNat_inj.mp (by rw [hk]; rfl)
    rw [chromGoU, if_pos this]; cases r <;> rfl
  | succ k ih =>
    intro kU cU c r hk hc h1 h2
    have hk0 : ¬ kU = 0 := fun e => by rw [e] at hk; simp at hk
    have h : cU < offs.usize ∧ cU < ns.usize :=
      ⟨by show cU.toNat < offs.usize.toNat; omega, by show cU.toNat < ns.usize.toNat; omega⟩
    have ek : (kU - 1).toNat = k := by
      rw [USize.toNat_sub_of_le _ _ (by show (1 : USize).toNat ≤ kU.toNat; rw [MapSpec.Fast.pgu_one]; omega),
        MapSpec.Fast.pgu_one, hk]; rfl
    have ec : (cU + 1).toNat = c + 1 := by
      rw [MapSpec.Fast.pgu_add _ _ (by rw [MapSpec.Fast.pgu_one]; omega), MapSpec.Fast.pgu_one, hc]
    have go : offs.uget cU (Nat.lt_of_lt_of_le h.1 (ausN_le offs)) = offs[c]! := by
      rw [getElem!_pos offs c (by omega)]; subst hc; rfl
    have gn : ns.uget cU (Nat.lt_of_lt_of_le h.2 (ausN_le ns)) = ns[c]! := by
      rw [getElem!_pos ns c (by omega)]; subst hc; rfl
    rw [chromGoU, if_neg hk0, dif_pos h]
    simp only [go, gn]
    by_cases hh : (decide (offs[c]! ≤ s) && decide (e ≤ offs[c]! + ns[c]!)) = true
    · cases r with
      | none => rw [chromGo, if_pos hh]; dsimp only; rw [if_pos hh, ih _ _ _ _ ek ec (by omega) (by omega), hc]
      | some d => rw [chromGo]; simp only [hh, ↓reduceIte]
    · cases r with
      | none => rw [chromGo, if_neg hh]; dsimp only; rw [if_neg hh, ih _ _ _ _ ek ec (by omega) (by omega)]
      | some d => rw [chromGo]; simp only [hh, Bool.false_eq_true, ↓reduceIte]; rw [ih _ _ _ _ ek ec (by omega) (by omega)]

@[inline] def chromOfL (offs ns : Array Nat) (s e : Nat) : Option Nat :=
  if offs.size < 4294967295 ∧ ns.size < 4294967295 ∧ ns.size ≤ offs.size then
    chromGoU offs ns s e ns.size.toUSize 0 none
  else chromGo offs ns s e ns.size 0 none

@[csimp] theorem chromOf_eqL : @chromOf = @chromOfL := by
  funext offs ns s e
  have hL : chromOfL offs ns s e = chromGo offs ns s e ns.size 0 none := by
    unfold chromOfL; split
    · rename_i h
      exact chromGoU_eq offs ns s e h.1 h.2.1 ns.size _ 0 0 none (MapSpec.Fast.pgu_n _ (by omega)) rfl
        (by omega) (by omega)
    · rfl
  rw [hL, chromGo_eq, chromOf, List.range_eq_range']
  cases (List.range' 0 ns.size).filter _ with
  | nil => rfl
  | cons a t => cases t <;> rfl

/-! ### The gap-free check as a byte compare (`chkCandD_ok`: it implies `chkCand` on `[(diag, n)]`) -/

-- penalty sum of `k` read letters `X[i ..]` against `G[st + i ..]`, mismatch −4
def diagPen (X : ByteArray) (G : PGen) (st : Nat) : Nat → Nat → Int → Int
  | 0, _, acc => acc
  | k + 1, i, acc => diagPen X G st k (i + 1) (acc + if X.get! i == G.get (st + i) then 0 else -4)

-- `diagPen` as −4 × the mismatch count `hamming` (bound `k`: no early stop), so the compiled code runs
-- `hamming`'s machine-word loop (`diagPen_eqH`)
theorem diagPen_ham (X : ByteArray) (G : PGen) (st L : Nat) : ∀ k i (acc : Int) m, m + k ≤ L →
    diagPen X G st k i acc = acc + 4 * (m : Int) - 4 * (MapSpec.Fast.hamming X G st L i (i + k) m : Nat)
  | 0, i, acc, m, _ => by
    rw [diagPen, MapSpec.Fast.hamming, if_neg (show ¬ i < i + 0 by omega)]; omega
  | k + 1, i, acc, m, hm => by
    have e : i + (k + 1) = i + 1 + k := by omega
    rw [diagPen, MapSpec.Fast.hamming, if_pos (show i < i + (k + 1) by omega), e]
    show _ = acc + 4 * (m : Int) - 4 * ((if (X.get! i != G.get (st + i)) = true then
      (if L < m + 1 then m + 1 else MapSpec.Fast.hamming X G st L (i + 1) (i + 1 + k) (m + 1))
      else MapSpec.Fast.hamming X G st L (i + 1) (i + 1 + k) m : Nat) : Int)
    by_cases h : X.get! i = G.get (st + i)
    · have h1 : (X.get! i == G.get (st + i)) = true := by simpa using h
      have h2 : ¬ (X.get! i != G.get (st + i)) = true := by simpa using h
      rw [if_pos h1, if_neg h2, diagPen_ham X G st L k (i + 1) _ m (by omega)]; omega
    · have h1 : ¬ (X.get! i == G.get (st + i)) = true := by simpa using h
      have h2 : (X.get! i != G.get (st + i)) = true := by simpa using h
      rw [if_neg h1, if_pos h2, if_neg (show ¬ L < m + 1 by omega),
        diagPen_ham X G st L k (i + 1) _ (m + 1) (by omega)]
      push_cast; omega

@[inline] def diagPenH (X : ByteArray) (G : PGen) (st k i : Nat) (acc : Int) : Int :=
  acc - 4 * (MapSpec.Fast.hamming X G st k i (i + k) 0 : Nat)

@[csimp] theorem diagPen_eqH : @diagPen = @diagPenH := by
  funext X G st k i acc
  rw [diagPenH, diagPen_ham X G st k k i acc 0 (by omega)]; omega

def chkCandD (pgs : Array PGen) (R Rr : ByteArray) (h : MapSpec.Placement × Int) : Bool :=
  let X := if h.1.2 = .fwd then R else Rr
  decide (h.1.1.chr < pgs.size) && decide (h.1.1.start + h.1.1.len ≤ pgs[h.1.1.chr]!.n) && decide (h.2 ≤ 0) &&
    X.size == R.size && h.1.1.len == R.size && diagPen X pgs[h.1.1.chr]! h.1.1.start R.size 0 0 == h.2

theorem ofNat_byte_inj (a b : UInt8) : Char.ofNat a.toNat = Char.ofNat b.toNat ↔ a = b := by
  constructor
  · intro h
    have := congrArg Char.toNat h
    rw [Bridge.toNat_ofNat_lt _ a.toNat_lt, Bridge.toNat_ofNat_lt _ b.toNat_lt] at this
    exact UInt8.toNat_inj.mp this
  · intro h; rw [h]

theorem walk_diag (X : ByteArray) (G : PGen) (st n : Nat) (xa ya : Array Char)
    (hxs : xa.size = n) (hys : ya.size = n)
    (hx : ∀ t (h : t < xa.size), xa[t] = Char.ofNat (X.get! t).toNat)
    (hy : ∀ t (h : t < ya.size), ya[t] = Char.ofNat (G.get (st + t)).toNat) :
    ∀ k i prev acc, i + k = n →
      AlignmentSpec.walkCheckA MapSpec.sc0 xa ya (List.replicate k .diag) i i prev acc = some (diagPen X G st k i acc)
  | 0, i, prev, acc, h => by
    simp only [List.replicate, AlignmentSpec.walkCheckA, diagPen]
    rw [Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by omega)]
  | k + 1, i, prev, acc, h => by
    simp only [List.replicate, AlignmentSpec.walkCheckA, diagPen]
    rw [Array.getElem?_eq_getElem (by omega), Array.getElem?_eq_getElem (by omega)]
    simp only
    rw [walk_diag X G st n xa ya hxs hys hx hy k (i + 1) _ _ (by omega)]
    congr 2
    rw [hx i (by omega), hy i (by omega)]
    unfold AlignmentSpec.diagCost
    by_cases e : X.get! i = G.get (st + i)
    · simp [e, MapSpec.sc0]
    · have : ¬ Char.ofNat (X.get! i).toNat = Char.ofNat (G.get (st + i)).toNat := fun h => e ((ofNat_byte_inj _ _).1 h)
      simp [e, this, MapSpec.sc0]

theorem chkCandD_ok (pgs : Array PGen) (R Rr : ByteArray) (h : MapSpec.Placement × Int)
    (hc : chkCandD pgs R Rr h = true) : chkCand pgs R Rr h [(AlignmentSpec.Step.diag, R.size)] = true := by
  unfold chkCandD at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, hX⟩, hlen⟩, hd⟩ := hc
  unfold chkCand rescoreRuns
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩
  rw [AlignmentSpec.checkRuns_check]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [walk_diag (if h.1.2 = .fwd then R else Rr) pgs[h.1.1.chr]! h.1.1.start R.size _ _
    (by simp [hX]) (by simp [hlen]) (fun t ht => by simp) (fun t ht => by simp) R.size 0 none 0 (by omega)]
  exact congrArg some hd

-- the alignment at `x` (whole sequence `pgs`) with CIGAR `runs`: re-checked, moved to its chromosome
-- the line of an alignment at `x` (whole sequence) with CIGAR `runs`, moved to its chromosome
def moveTo (offs ns : Array Nat) (x : MapSpec.Placement × Int) (runs : List (AlignmentSpec.Step × Nat)) :
    Option MateReport :=
  let r := mateReportOf x runs
  match chromOf offs ns r.placement.start r.placement.stop with
  | some c => some { r with placement := unshiftP c offs[c]! r.placement }
  | none => none

def checkMove (pgs : Array PGen) (offs ns : Array Nat) (R : ByteArray)
    (x : MapSpec.Placement × Int) (runs : List (AlignmentSpec.Step × Nat)) : Option MateReport :=
  if chkCand pgs R (revCompK R) x runs then moveTo offs ns x runs else none

-- the gap-free CIGAR checked by the byte compare (`checkMoveD_eq`)
def checkMoveD (pgs : Array PGen) (offs ns : Array Nat) (R : ByteArray) (x : MapSpec.Placement × Int) :
    Option MateReport :=
  if chkCandD pgs R (revCompK R) x then moveTo offs ns x [(AlignmentSpec.Step.diag, R.size)] else none

theorem checkMoveD_eq {pgs : Array PGen} {offs ns : Array Nat} {R : ByteArray} {x : MapSpec.Placement × Int}
    {r : MateReport} (h : checkMoveD pgs offs ns R x = some r) :
    checkMove pgs offs ns R x [(AlignmentSpec.Step.diag, R.size)] = some r := by
  unfold checkMoveD at h
  split at h
  · rename_i hc
    unfold checkMove
    rw [if_pos (chkCandD_ok _ _ _ _ hc)]
    exact h
  · cases h

-- the CIGAR of a mate placed at `x`: the router's checked runs, else the banded DP
def mateRuns (pgs : Array PGen) (R : ByteArray) (m : MateX) (x : MapSpec.Placement × Int) :
    Option (List (AlignmentSpec.Step × Nat)) :=
  if m.cg then some m.runs else alignAt pgs[0]! R (revCompK R) x

-- one mate's line, at the router's placement and score: first a CIGAR without gaps (when the window
-- has the read's length), else `mateRuns` (`<|>` is lazy: the banded DP runs only when needed)
def mateOf (pgs : Array PGen) (offs ns : Array Nat) (R : ByteArray) (m : MateX) : Option MateReport :=
  m.pl.bind fun x =>
    (if x.1.1.len == R.size then checkMoveD pgs offs ns R x else none) <|>
      (mateRuns pgs R m x).bind (checkMove pgs offs ns R x)

-- tags whose mates' placements form the pair in hand (T1gm: one tied best pair; T1um: the T2 pair)
def reportable (ties : Bool) : Tag → Bool
  | .t1 | .t1g | .t1u | .t2b | .t2 => true
  | .t1gm | .t1um => ties
  | _ => false

-- the pair in hand, printed, when both mates re-check and the pair is proper
def foundOf (ties : Bool) (slack lo hi : Nat) (pgs : Array PGen) (offs ns : Array Nat) (R1 R2 : ByteArray)
    (t : TierOut) : Option PairReport :=
  if reportable ties t.tag then
    match mateOf pgs offs ns R1 t.m1, mateOf pgs offs ns R2 t.m2 with
    | some a, some b =>
      if MapSpec.properPairU slack lo hi (oldPlacement a.placement) (oldPlacement b.placement) then
        some ⟨a, b⟩
      else none
    | _, _ => none
  else none

/-! ## Stage 5: a fallback pair when the router has no proper pair in hand (unproved search) -/

-- a proper pair of two printed mates
def pairOf (slack lo hi : Nat) (a b : Option MateReport) : Option PairReport :=
  match a, b with
  | some a, some b =>
    if MapSpec.properPairU slack lo hi (oldPlacement a.placement) (oldPlacement b.placement) then some ⟨a, b⟩
    else none
  | _, _ => none

-- up to `k` anchors per strand for a mate: hits of its rarest seed, each with its gap-free placement and score
-- (whole sequence: chromosome 0), best first
def anchorsOf (pk : PkMz) (pgs : Array PGen) (R : ByteArray) (s : PrepM MzP) (k : Nat) :
    List (MapSpec.Placement × Int) := Id.run do
  let n := R.size
  let m := n / 25
  if m == 0 then return []
  let Ls := n / m
  let G := pgs[0]!
  let mut out : Array (MapSpec.Placement × Int) := #[]
  for b in [0:2] do
    let pp := if b == 0 then s.ps else s.pr
    let Rx := if b == 0 then R else s.Rr
    let mut best : Option (Nat × Nat) := none
    for j in [0:m] do
      let p := pp[j]!
      if p.ok then
        let z := LookG.size pk p
        if z != 0 && best.all (fun r => z < r.1) then best := some (z, j)
    if let some (_, j) := best then
      let a := LookG.look pk ByteArray.empty Rx (j * Ls) (n - j * Ls) pp[j]!
      for e in a.extract 0 k do
        let D := e / 16
        if n ≤ D && D ≤ G.n then
          let mm := TierHeur.hamD R s.Rr pgs b D n
          out := out.push ((⟨0, D - n, n⟩, if b == 0 then .fwd else .rev), -((4 * mm : Nat) : Int))
  return (out.qsort fun x y => y.2 < x.2).toList

-- the other mate aligned inside the proper-pair window of `x` (seed vote, banded DP: `TierHeur.nearY`)
def nearOf (pk : PkMz) (pgs : Array PGen) (hi : Nat) (R : ByteArray) (s : PrepM MzP) (x : MapSpec.Placement) :
    Option ((MapSpec.Placement × Int) × List (AlignmentSpec.Step × Nat)) :=
  let fwd := x.2 == .rev
  let ws := if fwd then x.1.start + x.1.len - min (x.1.start + x.1.len) hi else x.1.start
  let we := if fwd then x.1.start + x.1.len else x.1.start + hi
  let X := if fwd then R else s.Rr
  let sv := TierHeur.seedVote pk #[0] 0 ws we X (if fwd then s.ps else s.pr)
  (TierHeur.nearY X pgs[0]! ws we 8 1000000 1000000 12 sv true false).map fun (st, len, pen, runs) =>
    (((⟨0, st, len⟩, if fwd then .fwd else .rev), -(pen : Int)), runs)

-- mate `R` at anchor `x`: (its line, the other mate's line near it)
def tryAt (pk : PkMz) (pgs : Array PGen) (offs ns : Array Nat) (hi : Nat) (R : ByteArray)
    (m : MateX) (R' : ByteArray) (s' : PrepM MzP) (x : MapSpec.Placement × Int) : Option MateReport × Option MateReport :=
  (mateOf pgs offs ns R { m with pl := some x, cg := m.cg && m.pl == some x },
   (nearOf pk pgs hi R' s' x.1).bind fun (h, runs) => checkMove pgs offs ns R' h runs)

-- the fallback: mate 1 at its router placement or its anchors, then mate 2 likewise; the first proper pair
def fallbackOf (k : Nat) (pk : PkMz) (slack lo hi : Nat) (pgs : Array PGen) (offs ns : Array Nat) (R1 R2 : ByteArray)
    (t : TierOut) : Option PairReport :=
  let s1 : PrepM MzP := prepMate pk R1
  let s2 : PrepM MzP := prepMate pk R2
  let c1 := t.m1.pl.toList ++ anchorsOf pk pgs R1 s1 k
  match c1.findSome? fun x => pairOf slack lo hi (tryAt pk pgs offs ns hi R1 t.m1 R2 s2 x).1
      (tryAt pk pgs offs ns hi R1 t.m1 R2 s2 x).2 with
  | some p => some p
  | none =>
    let c2 := t.m2.pl.toList ++ anchorsOf pk pgs R2 s2 k
    c2.findSome? fun x => pairOf slack lo hi (tryAt pk pgs offs ns hi R2 t.m2 R1 s1 x).2
      (tryAt pk pgs offs ns hi R2 t.m2 R1 s1 x).1

/-! ## The reporter is sound -/

section sound
variable {genome : Genome} {G : PGen} {offs ns : Array Nat}

theorem chromOf_some {s e c : Nat} (h : chromOf offs ns s e = some c) :
    c < ns.size ∧ offs[c]! ≤ s ∧ e ≤ offs[c]! + ns[c]! ∧
      ∀ c', c' < ns.size → offs[c']! ≤ s → e ≤ offs[c']! + ns[c']! → c' = c := by
  unfold chromOf at h
  split at h
  · rename_i c0 hl
    cases h
    have hm : c ∈ (List.range ns.size).filter
        (fun c => decide (offs[c]! ≤ s) && decide (e ≤ offs[c]! + ns[c]!)) := by rw [hl]; simp
    rw [List.mem_filter, List.mem_range] at hm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
    refine ⟨hm.1, hm.2.1, hm.2.2, fun c' hc' h1 h2 => ?_⟩
    have hm' : c' ∈ (List.range ns.size).filter
        (fun c => decide (offs[c]! ≤ s) && decide (e ≤ offs[c]! + ns[c]!)) := by
      rw [List.mem_filter, List.mem_range]; simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hc', h1, h2⟩
    rw [hl] at hm'
    simpa using hm'
  · cases h

-- what a printed mate is: an alignment at the router's placement `x` (moved to chromosome `c`, the only
-- one holding it) with the router's score
def MateAt (genome : Genome) (offs ns : Array Nat) (read : Read) (x : MapSpec.Placement × Int)
    (a : GenomicAlignment genome read) : Prop :=
  ∃ c, c < ns.size ∧ a.placement = unshiftP c offs[c]! (newPlacement x.1) ∧ a.score = x.2 ∧
    ∀ c', c' < ns.size → offs[c']! ≤ (newPlacement x.1).start → (newPlacement x.1).stop ≤ offs[c']! + ns[c']! → c' = c

theorem checkMove_sound
    (hslice : ∀ (c : Nat) (chr : Chromosome), genome[c]? = some chr →
      offs[c]! + chr.seq.length ≤ (decodeRead (MapSpec.Mz.unpack G)).length ∧
      chr.seq = ((decodeRead (MapSpec.Mz.unpack G)).drop offs[c]!).take chr.seq.length)
    (hchr : ∀ c, c < ns.size → ∃ chr : Chromosome, genome[c]? = some chr ∧ chr.seq.length = ns[c]!)
    (R : ByteArray) (x : MapSpec.Placement × Int) (runs : List (AlignmentSpec.Step × Nat)) (r : MateReport)
    (h : checkMove (cutAll G #[0] #[G.n]) offs ns R x runs = some r) :
    ∃ a : GenomicAlignment genome (decodeRead R), a.report = r ∧ MateAt genome offs ns (decodeRead R) x a := by
  unfold checkMove moveTo at h
  split at h
  · rename_i hc
    obtain ⟨hcig, -⟩ := chkCand_sound _ _ (Whole.genomeBytes_whole G) R _ (encodes_decodeRead R) _ runs hc
    obtain ⟨b, hb⟩ := alignment_of_cigar hcig
    dsimp only at h
    split at h
    · rename_i c hcO
      cases h
      obtain ⟨hcn, h1, h2, huq⟩ := chromOf_some hcO
      obtain ⟨chr, hgc, hlen⟩ := hchr c hcn
      have hpl : b.placement = (mateReportOf x runs).placement := congrArg MateReport.placement hb
      obtain ⟨a, ha⟩ := alignment_unshift (name := "") (W := decodeRead (MapSpec.Mz.unpack G))
        (off := fun c => offs[c]!) hslice b c chr hgc (by rw [hpl]; exact h1) (by rw [hpl, hlen]; exact h2)
      have har : a.report = { mateReportOf x runs with placement := unshiftP c offs[c]! (mateReportOf x runs).placement } := by
        refine ha.trans ?_
        show MateReport.mk (unshiftP c offs[c]! b.placement) b.report.cigar b.report.score = _
        rw [hpl, hb]
      refine ⟨a, har, c, hcn, congrArg MateReport.placement har, congrArg MateReport.score har, huq⟩
    · cases h
  · cases h

theorem mateOf_sound
    (hslice : ∀ (c : Nat) (chr : Chromosome), genome[c]? = some chr →
      offs[c]! + chr.seq.length ≤ (decodeRead (MapSpec.Mz.unpack G)).length ∧
      chr.seq = ((decodeRead (MapSpec.Mz.unpack G)).drop offs[c]!).take chr.seq.length)
    (hchr : ∀ c, c < ns.size → ∃ chr : Chromosome, genome[c]? = some chr ∧ chr.seq.length = ns[c]!)
    (R : ByteArray) (m : MateX) (r : MateReport)
    (h : mateOf (cutAll G #[0] #[G.n]) offs ns R m = some r) :
    ∃ x, m.pl = some x ∧ ∃ a : GenomicAlignment genome (decodeRead R), a.report = r ∧
      MateAt genome offs ns (decodeRead R) x a := by
  unfold mateOf at h
  cases hp : m.pl with
  | none => rw [hp] at h; cases h
  | some x =>
    rw [hp] at h
    simp only [Option.bind_some] at h
    refine ⟨x, rfl, ?_⟩
    cases h0 : (if x.1.1.len == R.size then checkMoveD (cutAll G #[0] #[G.n]) offs ns R x else none) with
    | some r0 =>
      rw [h0] at h
      cases h
      split at h0
      · exact checkMove_sound hslice hchr R x _ r (checkMoveD_eq h0)
      · cases h0
    | none =>
      rw [h0] at h
      cases hr : mateRuns (cutAll G #[0] #[G.n]) R m x with
      | none => rw [hr] at h; cases h
      | some runs =>
        rw [hr] at h
        exact checkMove_sound hslice hchr R x runs r h

theorem foundOf_sound
    (hslice : ∀ (c : Nat) (chr : Chromosome), genome[c]? = some chr →
      offs[c]! + chr.seq.length ≤ (decodeRead (MapSpec.Mz.unpack G)).length ∧
      chr.seq = ((decodeRead (MapSpec.Mz.unpack G)).drop offs[c]!).take chr.seq.length)
    (hchr : ∀ c, c < ns.size → ∃ chr : Chromosome, genome[c]? = some chr ∧ chr.seq.length = ns[c]!)
    (insertSettings : InsertSettings) (R1 R2 : ByteArray) (t : TierOut) (rep : PairReport)
    (ties : Bool) (h : foundOf ties insertSettings.dovetailSlack insertSettings.range.1 insertSettings.range.2
      (cutAll G #[0] #[G.n]) offs ns R1 R2 t = some rep) :
    ∃ pair : PairAlignment genome (decodeRead R1) (decodeRead R2),
      pair.report = rep ∧ pair.IsProper insertSettings.range insertSettings.dovetailSlack ∧
      ∃ x y, t.m1.pl = some x ∧ t.m2.pl = some y ∧
        MateAt genome offs ns (decodeRead R1) x pair.first ∧ MateAt genome offs ns (decodeRead R2) y pair.second := by
  unfold foundOf at h
  split at h
  · split at h
    · rename_i a b h1 h2
      split at h
      · rename_i hp
        cases h
        obtain ⟨x, hx1, p, hpr, hpx⟩ := mateOf_sound hslice hchr R1 _ a h1
        obtain ⟨y, hy1, q, hqr, hqy⟩ := mateOf_sound hslice hchr R2 _ b h2
        refine ⟨⟨p, q⟩, by simp only [PairAlignment.report, hpr, hqr], ?_, x, y, hx1, hy1, hpx, hqy⟩
        rw [isProper_iff]
        have px : p.placement = a.placement := by rw [← hpr]; rfl
        have py : q.placement = b.placement := by rw [← hqr]; rfl
        simp only [px, py]
        exact hp
      · cases h
    · cases h
  · cases h

theorem pairOf_sound (insertSettings : InsertSettings) {m1 m2 : Read} {a b : Option MateReport} {p : PairReport}
    (ha : ∀ r, a = some r → ∃ x : GenomicAlignment genome m1, x.report = r)
    (hb : ∀ r, b = some r → ∃ y : GenomicAlignment genome m2, y.report = r)
    (h : pairOf insertSettings.dovetailSlack insertSettings.range.1 insertSettings.range.2 a b = some p) :
    ∃ pair : PairAlignment genome m1 m2,
      pair.report = p ∧ pair.IsProper insertSettings.range insertSettings.dovetailSlack := by
  unfold pairOf at h
  split at h
  · rename_i a b
    split at h
    · rename_i hp
      cases h
      obtain ⟨x, hx⟩ := ha a rfl
      obtain ⟨y, hy⟩ := hb b rfl
      refine ⟨⟨x, y⟩, by simp only [PairAlignment.report, hx, hy], ?_⟩
      rw [isProper_iff]
      have px : x.placement = a.placement := by rw [← hx]; rfl
      have py : y.placement = b.placement := by rw [← hy]; rfl
      simp only [px, py]
      exact hp
    · cases h
  · cases h

theorem tryAt_sound
    (hslice : ∀ (c : Nat) (chr : Chromosome), genome[c]? = some chr →
      offs[c]! + chr.seq.length ≤ (decodeRead (MapSpec.Mz.unpack G)).length ∧
      chr.seq = ((decodeRead (MapSpec.Mz.unpack G)).drop offs[c]!).take chr.seq.length)
    (hchr : ∀ c, c < ns.size → ∃ chr : Chromosome, genome[c]? = some chr ∧ chr.seq.length = ns[c]!)
    (pk : PkMz) (hi : Nat) (R : ByteArray) (m : MateX) (R' : ByteArray) (s' : PrepM MzP)
    (x : MapSpec.Placement × Int) :
    (∀ r, (tryAt pk (cutAll G #[0] #[G.n]) offs ns hi R m R' s' x).1 = some r →
      ∃ a : GenomicAlignment genome (decodeRead R), a.report = r) ∧
    (∀ r, (tryAt pk (cutAll G #[0] #[G.n]) offs ns hi R m R' s' x).2 = some r →
      ∃ b : GenomicAlignment genome (decodeRead R'), b.report = r) := by
  unfold tryAt
  refine ⟨fun r h => ?_, fun r h => ?_⟩
  · dsimp only at h
    obtain ⟨_, -, a, ha, -⟩ := mateOf_sound hslice hchr R _ r h
    exact ⟨a, ha⟩
  · dsimp only at h
    cases hn : nearOf pk (cutAll G #[0] #[G.n]) hi R' s' x.1 with
    | none => rw [hn] at h; cases h
    | some q =>
      rw [hn] at h
      obtain ⟨a, ha, -⟩ := checkMove_sound hslice hchr R' q.1 q.2 r h
      exact ⟨a, ha⟩

theorem fallbackOf_sound
    (hslice : ∀ (c : Nat) (chr : Chromosome), genome[c]? = some chr →
      offs[c]! + chr.seq.length ≤ (decodeRead (MapSpec.Mz.unpack G)).length ∧
      chr.seq = ((decodeRead (MapSpec.Mz.unpack G)).drop offs[c]!).take chr.seq.length)
    (hchr : ∀ c, c < ns.size → ∃ chr : Chromosome, genome[c]? = some chr ∧ chr.seq.length = ns[c]!)
    (k : Nat) (pk : PkMz) (insertSettings : InsertSettings) (R1 R2 : ByteArray) (t : TierOut) (p : PairReport)
    (h : fallbackOf k pk insertSettings.dovetailSlack insertSettings.range.1 insertSettings.range.2
      (cutAll G #[0] #[G.n]) offs ns R1 R2 t = some p) :
    ∃ pair : PairAlignment genome (decodeRead R1) (decodeRead R2),
      pair.report = p ∧ pair.IsProper insertSettings.range insertSettings.dovetailSlack := by
  unfold fallbackOf at h
  simp only at h
  split at h
  · rename_i q hq
    cases h
    obtain ⟨x, -, hx⟩ := List.exists_of_findSome?_eq_some hq
    have T := tryAt_sound hslice hchr pk insertSettings.range.2 R1 t.m1 R2 (prepMate pk R2) x
    exact pairOf_sound insertSettings T.1 T.2 hx
  · obtain ⟨x, -, hx⟩ := List.exists_of_findSome?_eq_some h
    have T := tryAt_sound hslice hchr pk insertSettings.range.2 R2 t.m2 R1 (prepMate pk R1) x
    exact pairOf_sound insertSettings T.2 T.1 hx

end sound

end Spec.Report

/-! ## Stage 3: what T1 / T1g / T1u prove about the hits, at every threshold -/

namespace Spec.Report
open MapSpec MapSpec.Fast Bridge

-- every proper pair of hits scores at most `(x, y)`, and only `(x, y)`'s placements reach it
def UniqHits (sl lo hi : Nat) (g : MapSpec.Genome) (m1 m2 : List Char) (x y : MapSpec.Placement × Int) : Prop :=
  ∀ p q : MapSpec.Placement × Int,
    (p, q) ∈ properPairs sl lo hi (hitsBoth sc0 p.2 g m1) (hitsBoth sc0 q.2 g m2) →
    p.2 + q.2 ≤ x.2 + y.2 ∧ (x.2 + y.2 ≤ p.2 + q.2 → p.1 = x.1 ∧ q.1 = y.1)

theorem hit_lower {T T' : Int} {g : MapSpec.Genome} {m : List Char} {p : MapSpec.Placement × Int}
    (h : p ∈ hitsBoth sc0 T g m) (hT : T' ≤ p.2) : p ∈ hitsBoth sc0 T' g m := by
  obtain ⟨pl, s⟩ := p
  rw [mem_hitsBoth_T] at h ⊢
  exact ⟨h.1, h.2.1, hT⟩

-- the unique best of a mate (any cap) at the same score has the same placement
theorem same_of_mapSpecBoth {T0 : Int} {g : MapSpec.Genome} {m : List Char} {x p : MapSpec.Placement × Int}
    (h : mapSpecBoth sc0 T0 g m = some x) (hp : p ∈ hitsBoth sc0 p.2 g m) (he : x.2 ≤ p.2) : p.1 = x.1 := by
  have hx := mapSpecBoth_mem h
  have hT : T0 ≤ x.2 := by
    obtain ⟨pl, s⟩ := x
    rw [mem_hitsBoth_T] at hx; exact hx.2.2
  have hp' := hit_lower hp (Int.le_trans hT he)
  unfold mapSpecBoth at h
  rw [selectUniqueBy_eq_some_iff _ (hitsBoth_scoreFun _ _ _ _)] at h
  rcases h.2 p hp' with hlt | heq
  · omega
  · exact heq

theorem uniqHits_t1 {sl lo hi : Nat} {g : MapSpec.Genome} {m1 m2 : List Char} {c1 c2 : Nat}
    {x y : MapSpec.Placement × Int} (h : pairSpecT (-(c1 : Int)) (-(c2 : Int)) lo hi g m1 m2 = some (x, y)) :
    UniqHits sl lo hi g m1 m2 x y := by
  unfold pairSpecT at h
  cases h1 : mapSpecBoth sc0 (-(c1 : Int)) g m1 <;> cases h2 : mapSpecBoth sc0 (-(c2 : Int)) g m2 <;>
    rw [h1, h2] at h <;> simp only [reduceCtorEq] at h
  rename_i a b
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro p q hpq
    rw [mem_properPairs] at hpq
    obtain ⟨hp, hq, -⟩ := hpq
    simp only at hp hq
    have lp := Bridge.le_of_mapSpecBoth h1 hp
    have lq := Bridge.le_of_mapSpecBoth h2 hq
    refine ⟨by omega, fun hs => ⟨same_of_mapSpecBoth h1 hp (by omega), same_of_mapSpecBoth h2 hq (by omega)⟩⟩
  · cases h

theorem uniqHits_ut {sl lo hi g0 : Nat} {g : MapSpec.Genome} {m1 m2 : List Char} {x y : MapSpec.Placement × Int}
    (hall : ∀ P1 P2 : Nat, g0 ≤ P1 → g0 ≤ P2 → ∃ x' y', some x = some x' ∧ some y = some y' ∧
      pairSpecUT sc0 dcost0 sl lo hi (-(P1 : Int)) (-(P2 : Int)) g m1 m2 = some (x', y')) :
    UniqHits sl lo hi g m1 m2 x y := by
  intro p q hpq
  have hpq0 := hpq
  rw [mem_properPairs] at hpq0
  obtain ⟨hp, hq, hprop⟩ := hpq0
  obtain ⟨c1, c2⟩ := Bridge.cap_le (g0 := g0) (hitsBoth_nonpos _ _ _ _ hp)
  obtain ⟨c3, c4⟩ := Bridge.cap_le (g0 := g0) (hitsBoth_nonpos _ _ _ _ hq)
  obtain ⟨x', y', ex, ey, hs⟩ := hall _ _ c1 c3
  cases ex; cases ey
  have hmem : (p, q) ∈ properPairs sl lo hi (hitsBoth sc0 (-((max g0 (-p.2).toNat : Nat) : Int)) g m1)
      (hitsBoth sc0 (-((max g0 (-q.2).toNat : Nat) : Int)) g m2) :=
    mem_properPairs.2 ⟨hit_lower hp c2, hit_lower hq c4, hprop⟩
  refine ⟨Bridge.le_of_pairSpecUT hs hmem, fun hge => ?_⟩
  unfold pairSpecUT at hs
  rw [bestPairD_iff _ _ _ _ _ _ (hitsBoth_scoreFun _ _ _ _) (hitsBoth_scoreFun _ _ _ _)] at hs
  rcases hs.2 _ hmem with hlt | ⟨e1, e2⟩
  · rw [Bridge.pairScoreD_dcost0, Bridge.pairScoreD_dcost0] at hlt; simp only at hlt; omega
  · exact ⟨e1, e2⟩

theorem new_old (p : Spec.Placement) (h : p.start ≤ p.stop) : newPlacement (oldPlacement p) = p := by
  obtain ⟨c, st, e, sd⟩ := p
  simp only at h
  cases sd <;> simp [newPlacement, oldPlacement, newStrand, oldStrand] <;> omega

section unique
variable {genome : Genome} {G : PGen} {offs ns : Array Nat}

-- an alignment on the genome whose shift is the hit `z`, inside the only chromosome `c` holding `z`,
-- is at `z` moved to `c`
theorem placement_back
    (hchr : ∀ c, c < ns.size → ∃ chr : Chromosome, genome[c]? = some chr ∧ chr.seq.length = ns[c]!)
    (hlen : genome.length = ns.size)
    {read : Read} (a : GenomicAlignment genome read) (b : GenomicAlignment (Whole.wholeOf G) read)
    (z : MapSpec.Placement) (c : Nat)
    (hb : b.placement = Whole.shift (fun c => offs[c]!) a.placement) (hz : oldPlacement b.placement = z)
    (hu : ∀ c', c' < ns.size → offs[c']! ≤ (newPlacement z).start → (newPlacement z).stop ≤ offs[c']! + ns[c']! → c' = c) :
    a.placement = unshiftP c offs[c]! (newPlacement z) := by
  have hnz : newPlacement z = Whole.shift (fun c => offs[c]!) a.placement := by
    rw [← hz, new_old _ (start_le_stop b), hb]
  have hfit := a.fits
  unfold Placement.reference at hfit
  cases hg : genome[a.placement.chromosome]? with
  | none => rw [hg] at hfit; cases hfit
  | some chr =>
    rw [hg] at hfit
    have hin : a.placement.stop ≤ chr.seq.length := by
      by_cases hc : a.placement.start ≤ a.placement.stop ∧ a.placement.stop ≤ chr.seq.length
      · exact hc.2
      · simp [hc] at hfit
    have hcl : a.placement.chromosome < ns.size := by
      rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hg).1
    obtain ⟨chr', hg', hl'⟩ := hchr _ hcl
    rw [hg] at hg'
    cases hg'
    have hcc := hu a.placement.chromosome hcl (by rw [hnz]; simp [Whole.shift])
      (by rw [hnz]; simp only [Whole.shift]; omega)
    rw [hnz, ← hcc]
    generalize a.placement = q
    obtain ⟨qc, qs, qe, qst⟩ := q
    simp [unshiftP, Whole.shift]

theorem unique_of_uniqHits
    (hslice : ∀ (c : Nat) (chr : Chromosome), genome[c]? = some chr →
      offs[c]! + chr.seq.length ≤ (decodeRead (MapSpec.Mz.unpack G)).length ∧
      chr.seq = ((decodeRead (MapSpec.Mz.unpack G)).drop offs[c]!).take chr.seq.length)
    (hchr : ∀ c, c < ns.size → ∃ chr : Chromosome, genome[c]? = some chr ∧ chr.seq.length = ns[c]!)
    (hlen : genome.length = ns.size)
    (insertSettings : InsertSettings) {m1 m2 : Read} {x y : MapSpec.Placement × Int}
    (hU : UniqHits insertSettings.dovetailSlack insertSettings.range.1 insertSettings.range.2
      (oldGenome (Whole.wholeOf G)) m1 m2 x y)
    (P : PairAlignment genome m1 m2) (hP : P.IsProper insertSettings.range insertSettings.dovetailSlack)
    (h1 : MateAt genome offs ns m1 x P.first) (h2 : MateAt genome offs ns m2 y P.second) :
    P.IsUniqueBestProper insertSettings := by
  obtain ⟨c1, -, hp1, hs1, hu1⟩ := h1
  obtain ⟨c2, -, hp2, hs2, hu2⟩ := h2
  have hPs : P.score = x.2 + y.2 := by simp only [PairAlignment.score, hs1, hs2]
  have key : ∀ Q : PairAlignment genome m1 m2, Q.IsProper insertSettings.range insertSettings.dovetailSlack →
      Q.score ≤ x.2 + y.2 ∧ (x.2 + y.2 ≤ Q.score → Q.placements = P.placements) := by
    intro Q hQ
    obtain ⟨b1, hb1, hsb1⟩ := Whole.alignment_shift (name := "") (W := decodeRead (MapSpec.Mz.unpack G))
      (off := fun c => offs[c]!) hslice Q.first
    obtain ⟨b2, hb2, hsb2⟩ := Whole.alignment_shift (name := "") (W := decodeRead (MapSpec.Mz.unpack G))
      (off := fun c => offs[c]!) hslice Q.second
    have hQ' := Whole.isProper_shift Q ⟨b1, b2⟩ hb1 hb2 hQ
    rw [isProper_iff] at hQ'
    obtain ⟨s1, l1, hm1⟩ := hit_of_alignment b1 b1.score (Int.le_refl _)
    obtain ⟨s2, l2, hm2⟩ := hit_of_alignment b2 b2.score (Int.le_refl _)
    have hm := hU (oldPlacement b1.placement, s1) (oldPlacement b2.placement, s2)
      (mem_properPairs.2 ⟨hit_lower hm1 (Int.le_refl _), hit_lower hm2 (Int.le_refl _), hQ'⟩)
    simp only at hm
    have hsc : Q.score = b1.score + b2.score := by simp only [PairAlignment.score, hsb1, hsb2]
    refine ⟨by omega, fun hge => ?_⟩
    obtain ⟨e1, e2⟩ := hm.2 (by omega)
    have q1 := placement_back hchr hlen Q.first b1 x.1 c1 hb1 e1 hu1
    have q2 := placement_back hchr hlen Q.second b2 y.1 c2 hb2 e2 hu2
    simp only [PairAlignment.placements, q1, q2, hp1, hp2]
  refine ⟨⟨hP, fun Q hQ => by rw [hPs]; exact (key Q hQ).1⟩, fun Q hQ hne => ?_⟩
  rw [hPs]
  by_cases hge : x.2 + y.2 ≤ Q.score
  · exact absurd ((key Q hQ).2 hge) hne
  · omega

end unique

theorem uniqHits_of_tierOk {sl lo hi : Nat} {g : MapSpec.Genome} {m1 m2 : List Char} {O1 O2 : Option ByteArray}
    {t : TierOut} {x y : MapSpec.Placement × Int} (hok : TierOk sl lo hi g m1 m2 O1 O2 t)
    (ht : t.tag = .t1 ∨ t.tag = .t1g ∨ t.tag = .t1u) (hx : t.m1.pl = some x) (hy : t.m2.pl = some y) :
    UniqHits sl lo hi g m1 m2 x y := by
  unfold TierOk at hok
  rcases ht with h | h | h <;> rw [h] at hok
  · obtain ⟨x', y', hx', hy', hs⟩ := hok
    rw [hx] at hx'; rw [hy] at hy'
    cases hx'; cases hy'
    exact uniqHits_t1 hs
  · obtain ⟨-, -, hall⟩ := hok
    refine uniqHits_ut (g0 := t.g0) fun P1 P2 h1 h2 => ?_
    obtain ⟨x', y', hx', hy', hs⟩ := hall P1 P2 h1 h2
    exact ⟨x', y', by rw [← hx]; exact hx', by rw [← hy]; exact hy', hs⟩
  · obtain ⟨-, hall⟩ := hok
    refine uniqHits_ut (g0 := t.g0) fun P1 P2 h1 h2 => ?_
    obtain ⟨x', y', hx', hy', hs⟩ := hall P1 P2 h1 h2
    exact ⟨x', y', by rw [← hx]; exact hx', by rw [← hy]; exact hy', hs⟩

/-! ## The answer -/

-- T1 / T1g / T1u with the pair printed: the unique best proper pair
def uniqOf (t : TierOut) (f : Option PairReport) : Uniqueness :=
  match f, t.tag with
  | some _, .t1 | some _, .t1g | some _, .t1u => .unique
  | _, _ => .unknown

-- the router's answer with the pair in hand printed when it re-checks
-- (stage 5) with no proper pair from the router, the fallback runs when the bound is at least `fb`
-- `rescue`: also when the bound is junk but a mate has a placement in hand (mate rescue)
def answerOfPair (ties : Bool) (fb : Option Int) (rescue : Bool) (pk : PkMz) (insertSettings : InsertSettings)
    (pgs : Array PGen) (offs ns : Array Nat) (R1 R2 : ByteArray) (t : TierOut) : PairAnswer :=
  let f := foundOf ties insertSettings.dovetailSlack insertSettings.range.1 insertSettings.range.2 pgs offs ns R1 R2 t
  let g := match f, fb with
    | none, some T =>
      if T ≤ Bridge.boundOf t || (rescue && (t.m1.pl.isSome || t.m2.pl.isSome)) then
        fallbackOf 16 pk insertSettings.dovetailSlack insertSettings.range.1 insertSettings.range.2 pgs offs ns R1 R2 t
      else none
    | _, _ => f
  { Bridge.answerOf t with found := g, uniqueness := uniqOf t f }

theorem answerOfPair_correct {genome : Genome} {G : PGen} {offs ns : Array Nat}
    (hslice : ∀ (c : Nat) (chr : Chromosome), genome[c]? = some chr →
      offs[c]! + chr.seq.length ≤ (decodeRead (MapSpec.Mz.unpack G)).length ∧
      chr.seq = ((decodeRead (MapSpec.Mz.unpack G)).drop offs[c]!).take chr.seq.length)
    (hchr : ∀ c, c < ns.size → ∃ chr : Chromosome, genome[c]? = some chr ∧ chr.seq.length = ns[c]!)
    (hlen : genome.length = ns.size)
    (ties : Bool) (fb : Option Int) (rescue : Bool) (pk : PkMz) (insertSettings : InsertSettings) (R1 R2 : ByteArray) (t : TierOut)
    (hok : TierOk insertSettings.dovetailSlack insertSettings.range.1 insertSettings.range.2
      (oldGenome (Whole.wholeOf G)) (decodeRead R1) (decodeRead R2) (some R1) (some R2) t)
    (ha : CorrectU insertSettings genome (decodeRead R1) (decodeRead R2) (Bridge.answerOf t)) :
    CorrectU insertSettings genome (decodeRead R1) (decodeRead R2)
      (answerOfPair ties fb rescue pk insertSettings (cutAll G #[0] #[G.n]) offs ns R1 R2 t) := by
  unfold answerOfPair
  generalize hf : foundOf ties insertSettings.dovetailSlack insertSettings.range.1 insertSettings.range.2
    (cutAll G #[0] #[G.n]) offs ns R1 R2 t = f
  refine ⟨fun rep h => ?_, ha.2.1, ?_⟩
  · simp only at h
    cases f with
    | some f0 =>
      have h' : f0 = rep := by cases fb <;> simpa using h
      subst h'
      obtain ⟨pair, hr, hp, -⟩ := foundOf_sound hslice hchr insertSettings R1 R2 t _ ties hf
      exact ⟨pair, hr, hp⟩
    | none =>
      cases fb with
      | none => simp at h
      | some T =>
        simp only at h
        split at h
        · exact fallbackOf_sound hslice hchr 16 pk insertSettings R1 R2 t rep h
        · cases h
  · cases f with
    | none => simp [uniqOf]
    | some rep =>
      obtain ⟨pair, hr, hp, x, y, hx, hy, h1, h2⟩ := foundOf_sound hslice hchr insertSettings R1 R2 t rep ties hf
      have hu : t.tag = .t1 ∨ t.tag = .t1g ∨ t.tag = .t1u → pair.IsUniqueBestProper insertSettings := fun ht =>
        unique_of_uniqHits hslice hchr hlen insertSettings (uniqHits_of_tierOk hok ht hx hy) pair hp h1 h2
      cases htag : t.tag <;> simp only [uniqOf, htag]
      · exact ⟨rep, rfl, pair, hr, hu (.inl htag)⟩
      · exact ⟨rep, rfl, pair, hr, hu (.inr (.inl htag))⟩
      · exact ⟨rep, rfl, pair, hr, hu (.inr (.inr htag))⟩

end Spec.Report
