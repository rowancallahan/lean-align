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

The mate searched first is the one with the cheaper lookups (`seedCost`, any
choice is exact).

* `properPair` is symmetric                                     (properPair_comm)
* a hit at `T = −P` is at most `bandOf` letters longer than the read (len_le_of_score)
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

/-- Lookup cost proxy of a read: its `sbound P + 1` smallest buckets, worse strand
(only picks which mate goes first). -/
def seedCost {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (P : Nat) (R : ByteArray) : Nat :=
  let m := R.size / 25
  if m = 0 then 0 else
  let Ls := R.size / m
  let one := fun (X : ByteArray) =>
    ((((prepG ix X m Ls).toList.map (LookG.size ix)).mergeSort (· ≤ ·)).take (sbound P + 1)).foldl (· + ·) 0
  max (one R) (one (revCompB2 R))

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
  if seedCost ix P2 R2 < seedCost ix P1 R1 then
    (pairRegionStep lo hi (mapFastGBKP P2 ix G offs pgs R2) (regionNoHitKP P1 lo hi rl G offs pgs R1)
      (fun _ => mapFastGBKP P1 ix G offs pgs R1)).map fun x => (x.2, x.1)
  else
    pairRegionStep lo hi (mapFastGBKP P1 ix G offs pgs R1) (regionNoHitKP P2 lo hi rl G offs pgs R2)
      (fun _ => mapFastGBKP P2 ix G offs pgs R2)

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
  {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G : ByteArray) (offs : Array Nat)
  (hcat : catOk G offs gbs = true)
  (hlk : ∀ (R' : ByteArray) s base, s + q ≤ R'.size →
    LookOkS G R' s base 0 (LookG.look ix G R' s base (LookG.prep ix (seedHashAt R' s))))

include hg hr hcat hlk

/-- **Region absence.**  If the search over bytes `B` = letters `[x0, x1)` of
chromosome `c` (at `offs[c] + x0` in `G`) ends above `P`, the read has no hit at
`T = −P` on either strand inside `[x0, x1)` of chromosome `c`. -/
theorem region_absent (c x0 x1 : Nat) (B : ByteArray) (hc : c < gbs.size) (hx : x0 ≤ x1)
    (hx1 : x1 ≤ gbs[c]!.size) (hB : B.size = x1 - x0)
    (hBi : ∀ i, i < x1 - x0 → B.get! i = gbs[c]!.get! (x0 + i))
    (hf : fastT P R = true) (hpen : P < (mapChromsGB P ix G #[offs[c]! + x0] #[B] R).pen)
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
  have hcatR : catOk G #[offs[c]! + x0] #[B] = true := by
    unfold catOk at hcat ⊢
    simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hcat ⊢
    obtain ⟨hcs, hce⟩ := hcat c hc
    intro c' hc''
    have hc0 : c' = 0 := by simp at hc''; omega
    subst hc0
    simp only [List.getElem!_toArray, List.getElem!_cons_zero]
    refine ⟨by rw [hB]; omega, ?_⟩
    rw [eqRun_spec] at hce ⊢
    intro t ht
    rw [hB] at ht
    have := hce (x0 + t) (by omega)
    simp only [Nat.zero_add] at this ⊢
    rw [hBi t ht, ← this, Nat.add_assoc]
  unfold fastT at hf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
  obtain ⟨S, hi, hall⟩ := mapChromsGB_inv P read gR #[B] R hgR hr ix G #[offs[c]! + x0] hcatR hlk hf.1 hf.2
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
  {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G G' : ByteArray) (offs : Array Nat)
  (hG : ∀ R s base p, LookG.look ix G R s base p = LookG.look ix G' R s base p)
  (hcat : catOk G' offs (pgs.map Mz.unpack) = true)
  (hlk : ∀ (R' : ByteArray) s base, s + q ≤ R'.size →
    LookOkS G' R' s base 0 (LookG.look ix G' R' s base (LookG.prep ix (seedHashAt R' s))))

include hg hr hG hcat hlk

/-- **Region absence, packed.**  When `regionNoHitKP` says so, no hit of the read at
`T = −P` is a proper partner of `b`. -/
theorem regionNoHitKP_sound (b : Placement) (h : regionNoHitKP P lo hi ix G offs pgs R b = true)
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
      rw [mapChromsGBKG_one P ix G G' hG] at h
      apply Bool.eq_false_iff.mpr
      intro hpp
      have hrl : read.length = R.size := hr.1.symm
      obtain ⟨ch, hch, hfit, hlen⟩ := len_le_of_score P g read p.2 p.1 s hs hT
      obtain ⟨hchr, hx0, hx1⟩ := partner_in_region P lo hi R.size b p hpp (by omega)
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
      generalize hx : regionB P lo hi R.size b = x at hx0 hx1 h
      exact region_absent P read g (pgs.map Mz.unpack) R hg hr ix G' offs hcat hlk b.1.chr x.1
        (min x.2 pgs[b.1.chr]!.n) _ (by rw [hsz]; exact hc) (by omega) (by rw [hgc, hn]; omega)
        (by rw [← (Mz.rep_unpack _).1]; rfl)
        (fun i hi => by
          rw [hgc, ← (Mz.rep_unpack _).2, ← (Mz.rep_unpack _).2]
          have h2 : x.1 + i < pgs[b.1.chr]!.n := by omega
          simp only [PGen.get, view, hi, h2, if_true, Nat.add_assoc]
          rfl)
        hf h p.2 p.1 s hchr hx0 (by omega) hs hT
    · simp at h
  · simp at h

end packed

/-- **Packed genome, word kernels, length dispatch, mate-anchored** (`T = −16` /
`−12` per mate): `pairRegionKP` is `pairSpecT`. -/
theorem pairRegionKP_mz_eq (lo hi : Nat) (g : Genome) (m1 m2 : List Char) (ix : Mz.MzIdx) (G : PGen)
    (offs ns : Array Nat) (R1 R2 : ByteArray) (hcut : cutOk G offs ns = true)
    (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2)
    (hchk : Mz.check2P ix G = true) :
    pairRegionKP lo hi ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) R1 R2 =
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
      regionNoHitKP P lo hi ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) R a = true →
      mapSpecBoth sc0 (-(P : Int)) g m = some b → properPair lo hi a b.1 = false := by
    intro P R m hr a b h hb
    obtain ⟨⟨hs, hT⟩, -⟩ := (mapSpecBoth_iffT _ g m b.1 b.2).mp hb
    exact regionNoHitKP_sound P lo hi m g _ R hg hr _ ByteArray.empty (Mz.unpack G) offs hG hcat hlk a h b.1 b.2 hs hT
  unfold pairRegionKP pairSpecT
  simp only [hm _ R1 m1 h1, hm _ R2 m2 h2]
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
