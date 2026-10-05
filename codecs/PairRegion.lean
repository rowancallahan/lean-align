import WgPacked

/-!
# Codec `pairRegionKP`: the second mate is first searched only near the first

`pairDispatchKP` maps both mates over the whole genome.  But a pair is reported
only when the mates form a proper pair, so once mate `A` maps to `a`, a proper
partner of `a` lies on `a`'s chromosome, in a region of about `hi` letters
(`regionB`): the fragment bounds fix one end, and a hit at `T = −P` is at most
`bandOf sc0 (−P)` letters longer than the read (`len_le_of_score`).  Running the
proved search on that region alone (a one-chromosome genome: `region_absent`)
and finding no hit proves the pair is `none` without searching mate `B`
over the whole genome.  Otherwise `B` is mapped as usual.

The mate searched first is the one with the cheaper lookups (`costP`, any
choice is exact); each mate's seeds are prepared once (`prepMate`) for both the
choice and the search (`mapFastGBKPp_prep`).  The region search looks up only the index entries inside the
region (`mzLookRP`: binary search in the bucket, scan stops past the region), and
the region bytes alone are its genome.

* `properPair` is symmetric                                     (properPair_comm)
* a hit at `T = −P` is at most `bandOf` letters longer than the read (len_le_of_score)
* region lookups = full lookups cut to the region, exact on its bytes (lookupPPR_eq, lookOk_cut, lookOk_rg)
* no region hit ⇒ no hit of the spec in the region               (region_absent, regionNoHitKP_sound)
* `pairRegionKP` = `pairSpecT` (per-mate thresholds)            (pairRegionKP_mz_eq)
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-! ## Algorithm -/

/-- Where a proper partner (read of `n` letters, `T = −P`) of placement `b` lies on
`b`'s chromosome: letters `[x0, x1)` (before clipping to the chromosome). -/
def regionB (P lo hi n : Nat) (b : Placement) : Nat × Nat :=
  let sl := n + bandOf sc0 (-(P : Int))
  if b.2 = Strand.rev then
    -- partner forward: start in `[end − hi, end − lo]`
    (b.1.start + b.1.len - hi, b.1.start + b.1.len - lo + sl)
  else
    -- partner reverse: end in `[start + lo, start + hi]`
    (b.1.start + lo - sl, b.1.start + hi)

/-! ### Lookups cut to a region

Places in a bucket increase (`Mz.check`), so the entries of a bucket inside letters
`[a, b)` of the genome are found by a binary search and a scan that stops at the
first place past `b`. -/

section MzR
open Mz

/-- Binary search: the first entry `t ∈ [l, r)` with place `≥ x` (places increase). -/
def lbSlot (ix : MzIdx) (x : Nat) : (fuel l r : Nat) → Nat
  | 0, l, _ => l
  | f + 1, l, r =>
    if l < r then
      let m := (l + r) / 2
      if ix.posOf (ix.slot m) < x then lbSlot ix x f (m + 1) r else lbSlot ix x f l m
    else l

/-- Where the region scan of bucket `[l, r)` starts: the binary search, checked
(every earlier place is below `x`), else `l`. -/
@[inline] def startSlot (ix : MzIdx) (x l r : Nat) : Nat :=
  let t := lbSlot ix x 64 l r
  if decide (l < t) && decide (t ≤ r) && decide (ix.posOf (ix.slot (t - 1)) < x) then t else l

/-- `scanAP` cut to seed starts in `[a, b − q]`, counted from `a`; stops at the first
place past the region. -/
def scanAPR (ix : MzIdx) (G : PGen) (R : ByteArray) (s o key bw aw pmo o2 n1 a2 n2 hi base a b : Nat) (t : Nat)
    (acc : Array Nat) : Array Nat :=
  if t < hi then
    let pos := ix.posOf (ix.slot t)
    if b + o < pos + Mz.q then acc else
    scanAPR ix G R s o key bw aw pmo o2 n1 a2 n2 hi base a b (t + 1)
      (if decide (a + o ≤ pos) && okAtP ix G R s o key bw aw pmo o2 n1 a2 n2 t then
        acc.push (anc base 0 (pos - o - a)) else acc)
  else acc
termination_by hi - t

/-- `lookupPP` cut to the region `[a, b)`. -/
@[inline] def lookupPPR (ix : MzIdx) (G : PGen) (R : ByteArray) (s : Nat) (p : MzP) (base a b : Nat) : Array Nat :=
  let o := p.o
  let v := p.v
  let m1 := min o ix.c
  let m2 := min (ix.w - 1 - o) ix.c
  scanAPR ix G R s o (p.h &&& ix.kbM) ((v >>> (2 * (Mz.q - o))) &&& ix.pm[m1]!)
    ((v >>> (2 * (Mz.q - o - ix.k - m2))) &&& ix.pm[m2]!) ix.pm[m1]! (2 * (ix.c - m2))
    (o - m1) (ix.k + m2) (ix.w - 1 - o - m2)
    (ix.hiB p.b) base a b (startSlot ix (a + o) (ix.loB p.b) (ix.hiB p.b)) #[]

end MzR

/-- Keep an anchor (`bit = 0`) whose seed lies in `[a, b)`, counted from `a`. -/
@[inline] def cutAnc (base a b e : Nat) : Option Nat :=
  let p := e / 16 - base
  if a ≤ p && p + q ≤ b then some (anc base 0 (p - a)) else none

/-- Lookups cut to letters `[a, b)` of the packed genome, places counted from `a`. -/
def mzLookRP (ix : Mz.MzIdx) (G : PGen) (a b : Nat) (R : ByteArray) (s base : Nat) (p : MzP) : Array Nat :=
  if p.ok then lookupPPR ix G R s p base a b
  else (lookupSeedAP ix G R s base 0).filterMap (cutAnc base a b)

/-- A minimizer index on its packed genome, cut to a region `[a, b)`. -/
abbrev RgMz := PkMz × Nat × Nat

instance : LookG RgMz MzP :=
  ⟨fun r => mzPrep r.1.1, fun r => mzSize r.1.1, fun r _ R s base p => mzLookRP r.1.1 r.1.2 r.2.1 r.2.2 R s base p⟩

/-- `true`: read `R` certainly has no hit at `T = −P` (either strand) where a proper
partner of `b` could lie.  The proved search on the region alone (a view of the
packed chromosome, lookups `rl a b` cut to it). -/
def regionNoHitKP {L Pp : Type} [LookG L Pp] [Inhabited Pp] (P lo hi : Nat) (rl : Nat → Nat → L) (G : ByteArray)
    (offs : Array Nat) (pgs : Array PGen) (R : ByteArray) (b : Placement) : Bool :=
  let c := b.1.chr
  if c < pgs.size && fastT P R then
    let x := regionB P lo hi R.size b
    let x1 := min x.2 pgs[c]!.n
    if x.1 < x1 then
      let v := view pgs[c]! x.1 (x1 - x.1)
      decide (P < (mapChromsGBKG P (rl (offs[c]! + x.1) (offs[c]! + x1)) G #[0] #[v] #[v] R).pen)
    else false
  else false

/-- A read prepared once: reverse complement, packed words of both strands, and the
prepared seeds of both strands (used for the mate-order choice and the search). -/
structure PrepM (Pp : Type) where
  Rr : ByteArray
  K1 : RP
  K2 : RP
  ps : Array Pp
  pr : Array Pp

@[inline] def prepMate {L Pp : Type} [LookG L Pp] (ix : L) (R : ByteArray) : PrepM Pp :=
  let Rr := revCompK R
  let K1 := packRP R
  let K2 := packRP Rr
  let m := R.size / 25
  let Ls := R.size / m
  ⟨Rr, K1, K2, prepGK ix R K1 m Ls, prepGK ix Rr K2 m Ls⟩

/-- Lookup cost proxy of a prepared read: its `sbound P + 1` smallest buckets, worse
strand (only picks which mate goes first). -/
def costP {L Pp : Type} [LookG L Pp] (ix : L) (P : Nat) (s : PrepM Pp) : Nat :=
  let one := fun (a : Array Pp) =>
    (((a.toList.map (LookG.size ix)).mergeSort (· ≤ ·)).take (sbound P + 1)).foldl (· + ·) 0
  max (one s.ps) (one s.pr)

/-- `mapFastGBKP` from a prepared read. -/
def mapFastGBKPp {L Pp : Type} [LookG L Pp] [Inhabited Pp] (P : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (pgs : Array PGen) (R : ByteArray) (s : PrepM Pp) : Option (Placement × Int) :=
  if fastT P R then
    decodeP pgs.size P (mapChromsGBFG (kerHKG R s.K1 (pgs ++ pgs) (pgs ++ pgs))
      (kerHKG s.Rr s.K2 (pgs ++ pgs) (pgs ++ pgs)) P ix G offs pgs R s.Rr s.ps s.pr)
  else mapSpecBoth sc0 (-(P : Int)) (decodeGenomeB (pgs.map Mz.unpack)) (decodeBytes R)

theorem mapFastGBKPp_prep {L Pp : Type} [LookG L Pp] [Inhabited Pp] (P : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (pgs : Array PGen) (R : ByteArray) :
    mapFastGBKPp P ix G offs pgs R (prepMate ix R) = mapFastGBKP P ix G offs pgs R := rfl

/-- Mate `A` over the genome; mate `B` near it first, over the genome only when
the region has a hit. -/
@[inline] def pairRegionStep (lo hi : Nat) (mA : Option (Placement × Int)) (nh : Placement → Bool)
    (mB : Unit → Option (Placement × Int)) : Option ((Placement × Int) × (Placement × Int)) :=
  match mA with
  | none => none
  | some a =>
    if nh a.1 then none else
    match mB () with
    | none => none
    | some b => if properPair lo hi a.1 b.1 then some (a, b) else none

/-- **Pairs, mate-anchored**: length dispatch (`T = −16` / `−12` per mate), word
kernels, packed genome; the cheaper mate first. -/
def pairRegionKP {L Pp L2 Pp2 : Type} [LookG L Pp] [Inhabited Pp] [LookG L2 Pp2] [Inhabited Pp2] (lo hi : Nat)
    (ix : L) (rl : Nat → Nat → L2) (G : ByteArray)
    (offs : Array Nat) (pgs : Array PGen) (R1 R2 : ByteArray) : Option ((Placement × Int) × (Placement × Int)) :=
  let P1 := penOf R1
  let P2 := penOf R2
  let s1 := prepMate ix R1
  let s2 := prepMate ix R2
  if costP ix P2 s2 < costP ix P1 s1 then
    (pairRegionStep lo hi (mapFastGBKPp P2 ix G offs pgs R2 s2) (regionNoHitKP P1 lo hi rl G offs pgs R1)
      (fun _ => mapFastGBKPp P1 ix G offs pgs R1 s1)).map fun x => (x.2, x.1)
  else
    pairRegionStep lo hi (mapFastGBKPp P1 ix G offs pgs R1 s1) (regionNoHitKP P2 lo hi rl G offs pgs R2)
      (fun _ => mapFastGBKPp P2 ix G offs pgs R2 s2)

/-! ## Proofs: pairs -/

theorem properPair_comm (lo hi : Nat) (a b : Placement) : properPair lo hi a b = properPair lo hi b a := by
  rcases a with ⟨wa, sa⟩
  rcases b with ⟨wb, sb⟩
  cases sa <;> cases sb <;> simp [properPair]

/-- Region step = both mates, when a region without hits rules out a proper partner. -/
theorem pairRegionStep_eq (lo hi : Nat) (mA mB : Option (Placement × Int)) (nh : Placement → Bool)
    (hnh : ∀ a b, nh a = true → mB = some b → properPair lo hi a b.1 = false) :
    pairRegionStep lo hi mA nh (fun _ => mB) = pairLazy lo hi mA (fun _ => mB) := by
  cases mA with
  | none => rfl
  | some a =>
    cases mB with
    | none => simp [pairRegionStep, pairLazy]
    | some b =>
      by_cases h : nh a.1 = true
      · have := hnh a.1 b h rfl
        simp [pairRegionStep, pairLazy, h, this]
      · simp [pairRegionStep, pairLazy, h]

/-! ## Proofs: the region -/

/-- A hit at `T = −P` fits in its chromosome and is at most `bandOf sc0 (−P)`
letters longer than the read. -/
theorem len_le_of_score (P : Nat) (g : Genome) (read : List Char) (st : Strand) (w : Window) (s : Int)
    (hs : strandScore g read st w = some s) (hT : -(P : Int) ≤ s) :
    ∃ ch, g[w.chr]? = some ch ∧ w.start + w.len ≤ ch.seq.length ∧
      w.len ≤ read.length + bandOf sc0 (-(P : Int)) := by
  have key : ∀ r : List Char, r.length = read.length → windowScore sc0 r g w = some s →
      ∃ ch, g[w.chr]? = some ch ∧ w.start + w.len ≤ ch.seq.length ∧
        w.len ≤ read.length + bandOf sc0 (-(P : Int)) := by
    intro r hrl h
    cases hq : windowSeq g w with
    | none => unfold windowScore at h; rw [hq] at h; simp at h
    | some ys =>
      rw [windowScore_eq_sv sc0 r g w ys hq] at h
      simp only [Option.some.injEq] at h
      unfold windowSeq at hq
      cases hc : g[w.chr]? with
      | none => rw [hc] at hq; simp at hq
      | some ch =>
        rw [hc] at hq
        simp only at hq
        split at hq
        · next hle =>
          simp only [Option.some.injEq] at hq
          have hyl : ys.length = w.len := by rw [← hq]; simp; omega
          refine ⟨ch, rfl, hle, ?_⟩
          apply Classical.byContradiction
          intro hn
          have hlt := sv_lt_thr sc0 valid_sc0 (-(P : Int)) (bandOf sc0 (-(P : Int)))
            (bandOf_ok sc0 valid_sc0 _) r ys none (by rw [hyl, hrl]; omega)
          simp only [thr] at hlt
          omega
        · simp at hq
  cases st with
  | fwd => exact key read rfl hs
  | rev => exact key (revComp read) (by simp [revComp]) hs

/-- The letters of a window inside `[x0, x1)` of chromosome `c` are those of the
one-chromosome genome holding `[x0, x1)`. -/
theorem windowSeq_region (g : Genome) (c : Nat) (hc : c < g.length) (x0 x1 : Nat)
    (hx1 : x1 ≤ (g[c]).seq.length) (w : Window) (hw : w.chr = c) (h0 : x0 ≤ w.start)
    (h1 : w.start + w.len ≤ x1) :
    windowSeq [⟨"", ((g[c]).seq.drop x0).take (x1 - x0)⟩] ⟨0, w.start - x0, w.len⟩ = windowSeq g w := by
  rcases w with ⟨wc, st, len⟩
  simp only at hw h0 h1
  subst hw
  unfold windowSeq
  simp only [List.getElem?_cons_zero,
    List.getElem?_eq_getElem hc, List.length_take, List.length_drop]
  rw [if_pos (by omega), if_pos (by omega)]
  simp only [Option.some.injEq, List.drop_take, List.drop_drop, List.take_take]
  rw [show x0 + (st - x0) = st by omega, Nat.min_eq_left (by omega)]

section region
variable (P : Nat) (read : List Char) (g : Genome) (gbs : Array ByteArray) (R : ByteArray)
  (hg : GenomeBytes gbs g) (hr : Encodes R read)

include hg hr

/-- **Region absence.**  If the search over bytes `B` = letters `[x0, x1)` of
chromosome `c` alone (lookups exact on `B`) ends above `P`, the read has no hit at
`T = −P` on either strand inside `[x0, x1)` of chromosome `c`. -/
theorem region_absent (c x0 x1 : Nat) (B : ByteArray) (hc : c < gbs.size) (hx : x0 ≤ x1)
    (hx1 : x1 ≤ gbs[c]!.size) (hB : B.size = x1 - x0)
    (hBi : ∀ i, i < x1 - x0 → B.get! i = gbs[c]!.get! (x0 + i))
    {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L)
    (hlk : ∀ (R' : ByteArray) s base, s + q ≤ R'.size →
      LookOkS B R' s base 0 (LookG.look ix B R' s base (LookG.prep ix (seedHashAt R' s))))
    (hf : fastT P R = true) (hpen : P < (mapChromsGB P ix B #[0] #[B] R).pen)
    (st : Strand) (w : Window) (s : Int) (hw : w.chr = c) (h0 : x0 ≤ w.start) (h1 : w.start + w.len ≤ x1)
    (hs : strandScore g read st w = some s) (hT : -(P : Int) ≤ s) : False := by
  have hgl : gbs.size = g.length := hg.1
  have hc' : c < g.length := by omega
  have hgc : gbs[c]! = gbs[c] := getElem!_pos gbs c hc
  have henc := hg.2 c hc hc'
  have hL : gbs[c]!.size = (g[c]).seq.length := by rw [hgc]; exact henc.1
  let gR : Genome := [⟨"", ((g[c]).seq.drop x0).take (x1 - x0)⟩]
  have hgR : GenomeBytes #[B] gR := by
    refine ⟨rfl, fun c' h1 h2 => ?_⟩
    have hc0 : c' = 0 := by simp at h1; omega
    subst hc0
    refine ⟨by simp [gR, hB]; omega, fun i hi => ?_⟩
    simp only [gR, List.getElem_cons_zero, List.length_take, List.length_drop] at hi ⊢
    show (B.get! i).toNat = _
    rw [hBi i (by omega), hgc, henc.2 (x0 + i) (by omega)]
    simp [List.getElem_take, List.getElem_drop]
  have hcatR : catOk B #[0] #[B] = true := by
    unfold catOk
    simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
    intro c' hc''
    have hc0 : c' = 0 := by simp at hc''; omega
    subst hc0
    simp only [List.getElem!_toArray, List.getElem!_cons_zero]
    refine ⟨by omega, ?_⟩
    rw [eqRun_spec]
    intro t _
    rfl
  unfold fastT at hf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
  obtain ⟨S, hi, hall⟩ := mapChromsGB_inv P read gR #[B] R hgR hr ix B #[0] hcatR hlk hf.1 hf.2
  have hx1' : x1 ≤ (g[c]).seq.length := by omega
  have hseq := windowSeq_region g c hc' x0 x1 hx1' w hw h0 h1
  have no : ∀ w', cwB P read gR w' ≤ P → False := fun w' h => by
    have := hi.min w' (hall w' h); omega
  cases st with
  | fwd =>
    have e : windowScore sc0 read gR ⟨0, w.start - x0, w.len⟩ = some s := by
      unfold windowScore; rw [hseq]; exact hs
    have hcw := ((cwT_iff P read gR _ s).mp ⟨e, hT⟩).1
    apply no ⟨0, w.start - x0, w.len⟩
    unfold cwB; rw [if_pos (by simp [gR])]; exact hcw
  | rev =>
    have e : windowScore sc0 (revComp read) gR ⟨0, w.start - x0, w.len⟩ = some s := by
      unfold windowScore; rw [hseq]; exact hs
    have hcw := ((cwT_iff P (revComp read) gR _ s).mp ⟨e, hT⟩).1
    apply no ⟨1, w.start - x0, w.len⟩
    unfold cwB; rw [if_neg (by simp [gR])]; exact hcw

end region

/-- A proper partner of `b` lies in `regionB` (when it fits on the chromosome). -/
theorem partner_in_region (P lo hi n : Nat) (b p : Placement) (hpp : properPair lo hi b p = true)
    (hlen : p.1.len ≤ n + bandOf sc0 (-(P : Int))) :
    p.1.chr = b.1.chr ∧ (regionB P lo hi n b).1 ≤ p.1.start ∧
      p.1.start + p.1.len ≤ (regionB P lo hi n b).2 := by
  rcases b with ⟨⟨bc, bs, bl⟩, bt⟩
  rcases p with ⟨⟨pc, ps, pl⟩, pt⟩
  simp only at hlen ⊢
  cases bt <;> cases pt <;> simp [properPair, regionB] at hpp ⊢ <;> omega

/-! ## Proofs: lookups cut to a region -/

section MzRP
open Mz

theorem scanAP_toList (ix : MzIdx) (G : PGen) (R : ByteArray) (s o key bw aw pmo o2 n1 a2 n2 hi base bit : Nat) :
    ∀ n t acc, hi - t = n →
      (scanAP ix G R s o key bw aw pmo o2 n1 a2 n2 hi base bit t acc).toList = acc.toList ++
        (List.range' t n).filterMap (fun t => if okAtP ix G R s o key bw aw pmo o2 n1 a2 n2 t then
          some (anc base bit (ix.posOf (ix.slot t) - o)) else none) := by
  intro n
  induction n with
  | zero => intro t acc hn; rw [scanAP, if_neg (by omega)]; simp
  | succ n ih =>
    intro t acc hn
    rw [scanAP, if_pos (by omega), ih (t + 1) _ (by omega), List.range'_succ, List.filterMap_cons]
    split <;> simp

theorem okAtP_le {ix : MzIdx} {G : PGen} {R : ByteArray} {s o key bw aw pmo o2 n1 a2 n2 t : Nat}
    (h : okAtP ix G R s o key bw aw pmo o2 n1 a2 n2 t = true) : o ≤ ix.posOf (ix.slot t) := by
  unfold okAtP at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2.1

theorem cutAnc_pb (base a b p : Nat) :
    cutAnc base a b ((p + base) * 16 + 0) = if a ≤ p ∧ p + q ≤ b then some ((p - a + base) * 16 + 0) else none := by
  unfold cutAnc anc
  rw [show ((p + base) * 16 + 0) / 16 - base = p by omega]
  by_cases h : a ≤ p ∧ p + q ≤ b
  · rw [if_pos h, if_pos (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact h)]
  · rw [if_neg h, if_neg (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact h)]

/-- The anchors the region scan keeps, as a function of the entry. -/
theorem cutAnc_okAt {ix : MzIdx} {G : PGen} {R : ByteArray} {s o key bw aw pmo o2 n1 a2 n2 : Nat} (base a b t : Nat) :
    (if okAtP ix G R s o key bw aw pmo o2 n1 a2 n2 t then some (anc base 0 (ix.posOf (ix.slot t) - o)) else none).bind
        (cutAnc base a b) =
      if okAtP ix G R s o key bw aw pmo o2 n1 a2 n2 t && decide (a + o ≤ ix.posOf (ix.slot t)) &&
        decide (ix.posOf (ix.slot t) + Mz.q ≤ b + o) then
        some (anc base 0 (ix.posOf (ix.slot t) - o - a)) else none := by
  by_cases hk : okAtP ix G R s o key bw aw pmo o2 n1 a2 n2 t = true
  · have hle := okAtP_le hk
    rw [if_pos hk, Option.bind_some]
    unfold anc
    rw [cutAnc_pb]
    simp only [hk, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
    by_cases h2 : a + o ≤ ix.posOf (ix.slot t) ∧ ix.posOf (ix.slot t) + Mz.q ≤ b + o
    · rw [if_pos (by simp only [q, Mz.q] at h2 ⊢; omega), if_pos h2]
    · rw [if_neg (by simp only [q, Mz.q] at h2 ⊢; omega), if_neg h2]
  · rw [if_neg hk, if_neg (by simp [hk])]
    rfl

theorem scanAPR_toList (ix : MzIdx) (G : PGen) (R : ByteArray) (s o key bw aw pmo o2 n1 a2 n2 lo hi base a b : Nat)
    (hs : ∀ j, lo ≤ j → j + 1 < hi → ix.posOf (ix.slot j) < ix.posOf (ix.slot (j + 1))) :
    ∀ n t acc, lo ≤ t → hi - t = n →
      (scanAPR ix G R s o key bw aw pmo o2 n1 a2 n2 hi base a b t acc).toList = acc.toList ++
        (List.range' t n).filterMap (fun t => if okAtP ix G R s o key bw aw pmo o2 n1 a2 n2 t &&
          decide (a + o ≤ ix.posOf (ix.slot t)) && decide (ix.posOf (ix.slot t) + Mz.q ≤ b + o) then
          some (anc base 0 (ix.posOf (ix.slot t) - o - a)) else none) := by
  intro n
  induction n with
  | zero => intro t acc _ hn; rw [scanAPR, if_neg (by omega)]; simp
  | succ n ih =>
    intro t acc hlo hn
    rw [scanAPR, if_pos (by omega)]
    simp only []
    by_cases hst : b + o < ix.posOf (ix.slot t) + Mz.q
    · rw [if_pos hst]
      have hnil : ∀ m j, t ≤ j → j + m ≤ hi →
          (List.range' j m).filterMap (fun t => if okAtP ix G R s o key bw aw pmo o2 n1 a2 n2 t &&
            decide (a + o ≤ ix.posOf (ix.slot t)) && decide (ix.posOf (ix.slot t) + Mz.q ≤ b + o) then
            some (anc base 0 (ix.posOf (ix.slot t) - o - a)) else none) = [] := by
        intro m
        induction m with
        | zero => intro j _ _; rfl
        | succ m ihm =>
          intro j hj hjm
          rw [List.range'_succ, List.filterMap_cons, ihm (j + 1) (by omega) (by omega)]
          have hmono : ix.posOf (ix.slot t) ≤ ix.posOf (ix.slot j) := by
            by_cases hj' : j = t
            · subst hj'; exact Nat.le_refl _
            · have := lt_of_steps (fun t => ix.posOf (ix.slot t)) lo hi hs (j - t - 1) t hlo (by omega)
              rw [show t + (j - t - 1) + 1 = j by omega] at this
              exact Nat.le_of_lt this
          rw [if_neg (by simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]; intro _ _; omega)]
      rw [hnil (n + 1) t (Nat.le_refl _) (by omega)]
      simp
    · rw [if_neg hst, ih (t + 1) _ (by omega) (by omega), List.range'_succ, List.filterMap_cons]
      have e : (okAtP ix G R s o key bw aw pmo o2 n1 a2 n2 t && decide (a + o ≤ ix.posOf (ix.slot t)) &&
          decide (ix.posOf (ix.slot t) + Mz.q ≤ b + o)) =
          (decide (a + o ≤ ix.posOf (ix.slot t)) && okAtP ix G R s o key bw aw pmo o2 n1 a2 n2 t) := by
        rw [show decide (ix.posOf (ix.slot t) + Mz.q ≤ b + o) = true from decide_eq_true (by omega), Bool.and_true,
          Bool.and_comm]
      rw [e]
      split <;> simp

theorem startSlot_spec (ix : MzIdx) (x l r : Nat) :
    l ≤ startSlot ix x l r ∧ (l ≤ r → startSlot ix x l r ≤ r) ∧
      (l < startSlot ix x l r → ix.posOf (ix.slot (startSlot ix x l r - 1)) < x) := by
  unfold startSlot
  simp only []
  split
  · next h =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨by omega, fun _ => h.1.2, fun _ => h.2⟩
  · exact ⟨Nat.le_refl _, id, fun h => absurd h (Nat.lt_irrefl _)⟩

/-- The region scan is the full scan, cut (places increase in the bucket). -/
theorem lookupPPR_eq (ix : MzIdx) (G : PGen) (R : ByteArray) (s : Nat) (p : MzP) (base a b : Nat)
    (hs : ∀ j, ix.loB p.b ≤ j → j + 1 < ix.hiB p.b → ix.posOf (ix.slot j) < ix.posOf (ix.slot (j + 1))) :
    (lookupPPR ix G R s p base a b).toList = (lookupPP ix G R s p base 0).toList.filterMap (cutAnc base a b) := by
  unfold lookupPPR lookupPP
  simp only []
  obtain ⟨h1, h2, h3⟩ := startSlot_spec ix (a + p.o) (ix.loB p.b) (ix.hiB p.b)
  generalize startSlot ix (a + p.o) (ix.loB p.b) (ix.hiB p.b) = t0 at h1 h2 h3
  rw [scanAPR_toList _ _ _ _ _ _ _ _ _ _ _ _ _ (ix.loB p.b) _ _ _ _ hs _ t0 #[] h1 rfl,
    scanAP_toList _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ #[] rfl]
  simp only [List.nil_append, List.filterMap_filterMap]
  simp only [cutAnc_okAt]
  generalize hF : (fun t => if okAtP ix G R s p.o (p.h &&& ix.kbM) ((p.v >>> (2 * (Mz.q - p.o))) &&& ix.pm[min p.o ix.c]!)
      ((p.v >>> (2 * (Mz.q - p.o - ix.k - min (ix.w - 1 - p.o) ix.c))) &&& ix.pm[min (ix.w - 1 - p.o) ix.c]!)
      ix.pm[min p.o ix.c]! (2 * (ix.c - min (ix.w - 1 - p.o) ix.c)) (p.o - min p.o ix.c)
      (ix.k + min (ix.w - 1 - p.o) ix.c) (ix.w - 1 - p.o - min (ix.w - 1 - p.o) ix.c) t &&
      decide (a + p.o ≤ ix.posOf (ix.slot t)) && decide (ix.posOf (ix.slot t) + Mz.q ≤ b + p.o) then
      some (anc base 0 (ix.posOf (ix.slot t) - p.o - a)) else none) = F
  by_cases hlr : ix.loB p.b ≤ ix.hiB p.b
  · have hsplit : List.range' (ix.loB p.b) (ix.hiB p.b - ix.loB p.b) =
        List.range' (ix.loB p.b) (t0 - ix.loB p.b) ++ List.range' t0 (ix.hiB p.b - t0) := by
      have := h2 hlr
      have e1 : List.range' (ix.loB p.b) (ix.hiB p.b - ix.loB p.b) =
          List.range' (ix.loB p.b) ((t0 - ix.loB p.b) + (ix.hiB p.b - t0)) := by congr 1; omega
      rw [e1, ← List.range'_append_1, show ix.loB p.b + (t0 - ix.loB p.b) = t0 by omega]
    rw [hsplit, List.filterMap_append]
    have hnil : (List.range' (ix.loB p.b) (t0 - ix.loB p.b)).filterMap F = [] := by
      rw [List.filterMap_eq_nil_iff]
      intro j hj
      rw [List.mem_range'_1] at hj
      have hlt : ix.posOf (ix.slot j) < a + p.o := by
        have h3' := h3 (by omega)
        by_cases hj' : j = t0 - 1
        · rw [hj']; exact h3'
        · have := lt_of_steps (fun t => ix.posOf (ix.slot t)) (ix.loB p.b) (ix.hiB p.b) hs (t0 - 1 - j - 1) j hj.1
            (by have := h2 hlr; omega)
          rw [show j + (t0 - 1 - j - 1) + 1 = t0 - 1 by omega] at this
          omega
      rw [← hF]
      simp only []
      rw [if_neg (by simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]; intro _ h; omega)]
    rw [hnil, List.nil_append]
  · rw [show ix.hiB p.b - ix.loB p.b = 0 by omega, show ix.hiB p.b - t0 = 0 by omega]
    rfl

end MzRP

/-- Region lookups are the full lookups, cut. -/
theorem mzLookRP_eq (ix : Mz.MzIdx) (G : PGen) (a b : Nat) (R : ByteArray) (s base : Nat) (p : MzP)
    (hs : p.ok = true → ∀ j, ix.loB p.b ≤ j → j + 1 < ix.hiB p.b → ix.posOf (ix.slot j) < ix.posOf (ix.slot (j + 1))) :
    (mzLookRP ix G a b R s base p).toList = (mzLookSP ix G R s base p).toList.filterMap (cutAnc base a b) := by
  unfold mzLookRP mzLookSP
  split
  · next h => exact lookupPPR_eq ix G R s p base a b (hs h)
  · rw [Array.toList_filterMap]

/-- Cutting exact lookups of `Gu` to `[a, b)` gives exact lookups of the bytes `B`
of `[a, b)`. -/
theorem lookOk_cut (Gu B R : ByteArray) (s base a b : Nat) (a0 c0 : Array Nat) (h : LookOkS Gu R s base 0 a0)
    (hb : b ≤ Gu.size) (hB : B.size = b - a) (hBi : ∀ i, i < b - a → B.get! i = Gu.get! (a + i))
    (hc : c0.toList = a0.toList.filterMap (cutAnc base a b)) : LookOkS B R s base 0 c0 := by
  unfold LookOkS at h ⊢
  obtain ⟨hp, hm⟩ := h
  rw [hc]
  refine ⟨?_, fun e => ?_⟩
  · have hp' : a0.toList.Pairwise (fun x y => x < y ∧ (∃ p, x = (p + base) * 16 + 0) ∧ ∃ p, y = (p + base) * 16 + 0) :=
      hp.imp_of_mem fun hx hy hxy =>
        ⟨hxy, ((hm _).1 hx).imp fun _ hq => hq.2, ((hm _).1 hy).imp fun _ hq => hq.2⟩
    rw [List.pairwise_filterMap]
    refine hp'.imp ?_
    rintro x y ⟨hxy, ⟨p, rfl⟩, ⟨p', rfl⟩⟩ u hu v hv
    rw [cutAnc_pb] at hu hv
    split at hu
    · split at hv
      · simp only [Option.some.injEq] at hu hv
        omega
      · cases hv
    · cases hu
  · rw [List.mem_filterMap]
    constructor
    · rintro ⟨x, hx, hcx⟩
      obtain ⟨p, hmp, rfl⟩ := (hm x).1 hx
      rw [cutAnc_pb] at hcx
      split at hcx
      · next hin =>
        simp only [Option.some.injEq] at hcx
        refine ⟨p - a, ⟨by rw [hB]; omega, fun k hk => ?_⟩, hcx.symm⟩
        rw [hBi _ (by omega), show a + (p - a + k) = p + k by omega]
        exact hmp.2 k hk
      · cases hcx
    · rintro ⟨p', hmp', rfl⟩
      have hl := hmp'.1
      rw [hB] at hl
      have hq : q = 25 := rfl
      refine ⟨(a + p' + base) * 16 + 0, (hm _).2 ⟨a + p', ⟨by omega, fun k hk => ?_⟩, rfl⟩, ?_⟩
      · rw [show a + p' + k = a + (p' + k) by omega, ← hBi _ (by omega)]
        exact hmp'.2 k hk
      · rw [cutAnc_pb, if_pos (by omega)]
        congr 2
        omega

/-- **Region lookups are exact** on the bytes of the region, for an index passing
`check2P`. -/
theorem lookOk_rg (ix : Mz.MzIdx) (PG : PGen) (hchk : Mz.check2P ix PG = true) (a b : Nat) (B : ByteArray)
    (hb : b ≤ (Mz.unpack PG).size) (hB : B.size = b - a)
    (hBi : ∀ i, i < b - a → B.get! i = (Mz.unpack PG).get! (a + i)) :
    ∀ (R' : ByteArray) s base, s + q ≤ R'.size →
      LookOkS B R' s base 0 (LookG.look ((((ix, PG) : PkMz), a, b) : RgMz) B R' s base
        (LookG.prep ((((ix, PG) : PkMz), a, b) : RgMz) (seedHashAt R' s))) := by
  intro R' s base hs
  have hc : Mz.check ix (Mz.unpack PG) = true := by
    rw [← Mz.check2_eq, ← Mz.check2P_eq (Mz.rep_unpack PG)]; exact hchk
  have hg := Mz.good_of_check hc
  apply lookOk_cut (Mz.unpack PG) B R' s base a b _ _ (lookOk_pk ix PG hchk R' s base hs) hb hB hBi
  show (mzLookRP ix PG a b R' s base (mzPrep ix (seedHashAt R' s))).toList = _
  rw [mzLookRP_eq]
  · rfl
  · intro hok j h1 h2
    cases hh : seedHashAt R' s with
    | none => rw [hh] at hok; simp [mzPrep] at hok
    | some y =>
      rw [hh] at h1 h2
      simp only [mzPrep] at h1 h2
      exact (Mz.entryOk_spec hg.k_le31 (Mz.c_le31 hg)
        (Mz.sound_of_check hc _ (Mz.bucket_lt hg _) j h1 (by omega)) _ _ rfl rfl).2.2.2.2.2 h2
/-! ## Proofs: the packed region search -/

/-- The search on one packed view is the byte search on its letters (lookups in any
`G'` the index ignores). -/
theorem mapChromsGBKG_one {L Pp : Type} [LookG L Pp] [Inhabited Pp] (P : Nat) (ix : L) (G G' : ByteArray)
    (hG : ∀ R s base p, LookG.look ix G R s base p = LookG.look ix G' R s base p) (o : Nat) (v : PGen)
    (R : ByteArray) : mapChromsGBKG P ix G #[o] #[v] #[v] R = mapChromsGB P ix G' #[o] #[Mz.unpack v] R := by
  rw [mapChromsGBKG_unpack, mapChromsGBK_eq_rep P ix G _ _ #[v] (repAllK_unpack #[v])]
  have e : (#[v].map Mz.unpack) = #[Mz.unpack v] := by simp
  rw [e]
  simp only [mapChromsGB, ilG_congrG ix G G' hG]

section packed
variable (P lo hi : Nat) (read : List Char) (g : Genome) (pgs : Array PGen) (R : ByteArray)
  (hg : GenomeBytes (pgs.map Mz.unpack) g) (hr : Encodes R read)
  {L Pp : Type} [LookG L Pp] [Inhabited Pp] (rl : Nat → Nat → L) (G G' : ByteArray) (offs : Array Nat)
  (hG : ∀ a b (G1 : ByteArray) R s base p, LookG.look (rl a b) G R s base p = LookG.look (rl a b) G1 R s base p)
  (hcat : catOk G' offs (pgs.map Mz.unpack) = true)
  (hlk : ∀ a b (B : ByteArray), b ≤ G'.size → B.size = b - a → (∀ i, i < b - a → B.get! i = G'.get! (a + i)) →
    ∀ (R' : ByteArray) s base, s + q ≤ R'.size →
      LookOkS B R' s base 0 (LookG.look (rl a b) B R' s base (LookG.prep (rl a b) (seedHashAt R' s))))

include hg hr hG hcat hlk

/-- **Region absence, packed.**  When `regionNoHitKP` says so, no hit of the read at
`T = −P` is a proper partner of `b`. -/
theorem regionNoHitKP_sound (b : Placement) (h : regionNoHitKP P lo hi rl G offs pgs R b = true)
    (p : Placement) (s : Int) (hs : strandScore g read p.2 p.1 = some s) (hT : -(P : Int) ≤ s) :
    properPair lo hi b p = false := by
  unfold regionNoHitKP at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  split at h
  · next hcf =>
    obtain ⟨hc, hf⟩ := hcf
    split at h
    · next hx =>
      simp only [decide_eq_true_eq] at h
      generalize hx' : regionB P lo hi R.size b = x at hx h
      generalize hv : view pgs[b.1.chr]! x.1 (min x.2 pgs[b.1.chr]!.n - x.1) = v at h
      rw [mapChromsGBKG_one P _ G (Mz.unpack v) (hG _ _ (Mz.unpack v))] at h
      apply Bool.eq_false_iff.mpr
      intro hpp
      have hrl : read.length = R.size := hr.1.symm
      obtain ⟨ch, hch, hfit, hlen⟩ := len_le_of_score P g read p.2 p.1 s hs hT
      obtain ⟨hchr, hx0, hx1⟩ := partner_in_region P lo hi R.size b p hpp (by omega)
      rw [hx'] at hx0 hx1
      have hsz : (pgs.map Mz.unpack).size = pgs.size := by simp
      have hgc : (pgs.map Mz.unpack)[b.1.chr]! = Mz.unpack pgs[b.1.chr]! := by
        rw [getElem!_pos (pgs.map Mz.unpack) b.1.chr (by rw [hsz]; exact hc), getElem!_pos pgs b.1.chr hc]
        simp
      have hn : (Mz.unpack pgs[b.1.chr]!).size = pgs[b.1.chr]!.n := (Mz.rep_unpack _).1.symm
      have hchl : ch.seq.length = pgs[b.1.chr]!.n := by
        have hc' : b.1.chr < g.length := by rw [← hg.1, hsz]; exact hc
        rw [hchr, List.getElem?_eq_getElem hc'] at hch
        simp only [Option.some.injEq] at hch
        subst hch
        have := (hg.2 b.1.chr (by rw [hsz]; exact hc) hc').1
        rw [← this, ← getElem!_pos (pgs.map Mz.unpack) b.1.chr (by rw [hsz]; exact hc), hgc, hn]
      have hBs : (Mz.unpack v).size = min x.2 pgs[b.1.chr]!.n - x.1 := by
        rw [← (Mz.rep_unpack _).1, ← hv]; rfl
      have hBi : ∀ i, i < min x.2 pgs[b.1.chr]!.n - x.1 →
          (Mz.unpack v).get! i = (pgs.map Mz.unpack)[b.1.chr]!.get! (x.1 + i) := fun i hi => by
        rw [hgc, ← (Mz.rep_unpack _).2, ← (Mz.rep_unpack _).2, ← hv]
        have h2 : x.1 + i < pgs[b.1.chr]!.n := by omega
        simp only [PGen.get, view, hi, h2, if_true, Nat.add_assoc]
        rfl
      -- the chromosome in `G'`
      have hcat' := hcat
      unfold catOk at hcat'
      simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hcat'
      obtain ⟨hcs, hce⟩ := hcat' b.1.chr (by rw [hsz]; exact hc)
      rw [eqRun_spec] at hce
      rw [hgc, hn] at hcs
      have hlk' := hlk (offs[b.1.chr]! + x.1) (offs[b.1.chr]! + min x.2 pgs[b.1.chr]!.n) (Mz.unpack v)
        (by omega) (by rw [hBs]; omega) (fun i hi => by
          rw [hBi i (by omega)]
          have := hce (x.1 + i) (by rw [hgc, hn]; omega)
          rw [Nat.zero_add] at this
          rw [← this, Nat.add_assoc])
      exact region_absent P read g (pgs.map Mz.unpack) R hg hr b.1.chr x.1
        (min x.2 pgs[b.1.chr]!.n) _ (by rw [hsz]; exact hc) (by omega) (by rw [hgc, hn]; omega)
        hBs hBi _ hlk' hf h p.2 p.1 s hchr hx0 (by omega) hs hT
    · simp at h
  · simp at h

end packed

/-- **Packed genome, word kernels, length dispatch, mate-anchored** (`T = −16` /
`−12` per mate; region lookups cut to the region): `pairRegionKP` is `pairSpecT`. -/
theorem pairRegionKP_mz_eq (lo hi : Nat) (g : Genome) (m1 m2 : List Char) (ix : Mz.MzIdx) (G : PGen)
    (offs ns : Array Nat) (R1 R2 : ByteArray) (hcut : cutOk G offs ns = true)
    (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2)
    (hchk : Mz.check2P ix G = true) :
    pairRegionKP lo hi ((ix, G) : PkMz) (fun a b => ((((ix, G) : PkMz), a, b) : RgMz)) ByteArray.empty offs
      (cutAll G offs ns) R1 R2 =
      pairSpecT (-(penOf R1 : Int)) (-(penOf R2 : Int)) lo hi g m1 m2 := by
  have hG : ∀ R s base p, LookG.look ((ix, G) : PkMz) ByteArray.empty R s base p =
      LookG.look ((ix, G) : PkMz) (Mz.unpack G) R s base p := fun _ _ _ _ => rfl
  have hcat := catOk_cut G offs ns hcut
  have hlk := lookOk_pk ix G hchk
  have hm : ∀ P R m, Encodes R m →
      mapFastGBKP P ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) R = mapSpecBoth sc0 (-(P : Int)) g m := by
    intro P R m hr
    rw [mapFastGBKP_eq, mapFastGB_congrG ((ix, G) : PkMz) ByteArray.empty (Mz.unpack G) hG]
    exact mapFastGB_eq_mapSpecBoth P g m _ R _ _ offs hg hr hcat hlk
  have hn : ∀ P R m, Encodes R m → ∀ a b,
      regionNoHitKP P lo hi (fun a b => ((((ix, G) : PkMz), a, b) : RgMz)) ByteArray.empty offs
        (cutAll G offs ns) R a = true →
      mapSpecBoth sc0 (-(P : Int)) g m = some b → properPair lo hi a b.1 = false := by
    intro P R m hr a b h hb
    obtain ⟨⟨hs, hT⟩, -⟩ := (mapSpecBoth_iffT _ g m b.1 b.2).mp hb
    exact regionNoHitKP_sound P lo hi m g _ R hg hr _ ByteArray.empty (Mz.unpack G) offs
      (fun _ _ _ _ _ _ _ => rfl) hcat (fun a b B hb hB hBi => lookOk_rg ix G hchk a b B hb hB hBi) a h b.1 b.2 hs hT
  unfold pairRegionKP pairSpecT
  simp only [mapFastGBKPp_prep, hm _ R1 m1 h1, hm _ R2 m2 h2]
  split
  · rw [pairRegionStep_eq lo hi _ _ _ (fun a b h hb => hn _ R1 m1 h1 a b h hb), pairLazy_match]
    cases mapSpecBoth sc0 (-(penOf R1 : Int)) g m1 <;> cases mapSpecBoth sc0 (-(penOf R2 : Int)) g m2 <;>
      simp only [Option.map_none]
    next a b =>
      rw [properPair_comm]
      split <;> simp
  · rw [pairRegionStep_eq lo hi _ _ _ (fun a b h hb => hn _ R2 m2 h2 a b h hb), pairLazy_match]
    cases mapSpecBoth sc0 (-(penOf R1 : Int)) g m1 <;> cases mapSpecBoth sc0 (-(penOf R2 : Int)) g m2 <;> rfl

end MapSpec.Fast

#print axioms MapSpec.Fast.region_absent
#print axioms MapSpec.Fast.regionNoHitKP_sound
#print axioms MapSpec.Fast.pairRegionKP_mz_eq
