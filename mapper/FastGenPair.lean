import FastGenMz
import PairConcat

/-!
# Codec `pairFastGB`: the general path on both strands, one concatenated index

The general fast mapper (`codecs/FastGen.lean`, any read length, `T = −P`) on both
strands and proper pairs, in the form of `pairFastC` (codecs/PairConcat.lean):

* one index over the concatenated genome `G` (chromosome `c` at `offs[c]`,
  checked by `catOk`); each seed is looked up once in `G`, its anchors are cut
  into per-chromosome slices (`sliceG`, binary search);
* the read and its reverse complement are virtual chromosomes `c` and `n + c`
  of `gbs ++ gbs`, sharing one `Best`;
* phase 1 interleaves the two strands' lookups (`ilG`: the live strand with
  fewer lookups goes next; a strand stops once `sbound (min best P)` is below
  its lookup count), then stages K and B (`chromKBS`) run per virtual chromosome
  on its slices, stage K behind the exact seed filter (`chromKBS_cover`).

    … → mapFastGB P ix G offs gbs R = mapSpecBoth sc0 (−P) g read            (mapFastGB_eq_mapSpecBoth)
    … → pairFastGB P lo hi ix G offs gbs R1 R2 = pairSpec sc0 (−P) lo hi g m1 m2 (pairFastGB_eq_pairSpec)
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-! ## Algorithm -/

/-- Anchors of a lookup in `G` (anchor `(p + base)·16`) whose seed lies in the
chromosome at `o` of length `len`, in its coordinates. -/
@[inline] def sliceG (a : Array Nat) (base o len : Nat) : Array Nat :=
  (a.extract (lbA a (16 * (o + base)) 0 a.size) (lbA a (16 * (o + len + 1 + base - q)) 0 a.size)).map
    (· - 16 * o)

/-- `sliceG` without building an array for an empty slice (`sliceG_eqE`). -/
@[inline] def sliceGE (a : Array Nat) (base o len : Nat) : Array Nat :=
  let i := lbA a (16 * (o + base)) 0 a.size
  let j := lbA a (16 * (o + len + 1 + base - q)) 0 a.size
  if j ≤ i then #[] else (a.extract i j).map (· - 16 * o)

/-- Compiled code runs `sliceGE`. -/
@[csimp] theorem sliceG_eqE : @sliceG = @sliceGE := by
  funext a base o len
  unfold sliceG sliceGE
  simp only []
  split
  · next h =>
    apply Array.ext
    · simp; omega
    · intro k h1 h2; simp at h2
  · rfl

/-- One strand: seeds left, seeds looked up (newest first), slices per chromosome
(newest first). -/
structure GS where
  ord : List Nat
  J : List Nat
  acc : Array (List (Array Nat))

instance : Inhabited GS := ⟨⟨[], [], #[]⟩⟩

@[inline] def GS.live (P : Nat) (s : GS) (b : Best) : Bool :=
  !s.ord.isEmpty && !decide (sbound (min b.pen P) < s.J.length)

/-- Slice of seed lookup `a` (base `bs`) on chromosome `c`, its windows added. -/
@[inline] def advC {Gt : Type} [GRead Gt] [Inhabited Gt] (R : ByteArray) (gbs2 : Array Gt) (offs : Array Nat) (t P bs : Nat) (a : Array Nat)
    (r : Array (List (Array Nat)) × Best) (c : Nat) : Array (List (Array Nat)) × Best :=
  let sl := sliceG a bs offs[c]! (GRead.size gbs2[t + c]!)
  (r.1.set! c (sl :: r.1[c]!),
    sl.foldl (fun b e => addK R gbs2 (t + c) (min P 16) ((e / 16 : Nat) - (R.size : Int)) R.size b) r.2)

/-- One seed lookup of a strand (read `R`, virtual chromosomes `t + c`). -/
@[inline] def GS.adv {Gt : Type} [GRead Gt] [Inhabited Gt] {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G R : ByteArray)
    (gbs2 : Array Gt) (offs : Array Nat) (n t P Ls : Nat) (ps : Array Pp) (s : GS) (b : Best) : GS × Best :=
  match s.ord with
  | [] => (s, b)
  | j :: rest =>
    let r := (List.range n).foldl (advC R gbs2 offs t P (R.size - j * Ls)
      (LookG.look ix G R (j * Ls) (R.size - j * Ls) ps[j]!)) (s.acc, b)
    (⟨rest, j :: s.J, r.1⟩, r.2)

/-- Two strands, one lookup at a time: the live strand with fewer lookups. -/
@[specialize] def ilG {Gt : Type} [GRead Gt] [Inhabited Gt] {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G R1 R2 : ByteArray)
    (gbs2 : Array Gt) (offs : Array Nat) (n P Ls : Nat) (ps1 ps2 : Array Pp) :
    Nat → GS → GS → Best → GS × GS × Best
  | 0, s1, s2, b => (s1, s2, b)
  | f + 1, s1, s2, b =>
    let l2 := s2.live P b
    if s1.live P b && (!l2 || decide (s1.J.length ≤ s2.J.length)) then
      let r := s1.adv ix G R1 gbs2 offs n 0 P Ls ps1 b
      ilG ix G R1 R2 gbs2 offs n P Ls ps1 ps2 f r.1 s2 r.2
    else if l2 then
      let r := s2.adv ix G R2 gbs2 offs n n P Ls ps2 b
      ilG ix G R1 R2 gbs2 offs n P Ls ps1 ps2 f s1 r.1 r.2
    else (s1, s2, b)

/-- `complB` as a table (`complTab_get`): no branches on the letters. -/
def complTab : ByteArray := ⟨(Array.range 256).map fun i => complB i.toUInt8⟩

/-- Reverse complement, one byte at a time (`revCompB2_eq`: it is `revCompB`). -/
def rcAux (R : ByteArray) : Nat → ByteArray → ByteArray
  | 0, acc => acc
  | i + 1, acc => rcAux R i (acc.push (complTab.get! (R.get! i).toNat))

@[inline] def revCompB2 (R : ByteArray) : ByteArray := rcAux R R.size (ByteArray.emptyWithCapacity R.size)

/-- Prepared seeds of a read. -/
@[inline] def prepG {L Pp : Type} [LookG L Pp] (ix : L) (R : ByteArray) (m Ls : Nat) : Array Pp :=
  (Array.range m).map fun j => LookG.prep ix (seedHashAt R (j * Ls))

/-- Both strands: virtual chromosomes `c` (read) and `n + c` (reverse complement). -/
@[specialize] def mapChromsGB {Gt : Type} [GRead Gt] [Inhabited Gt] {L Pp : Type} [LookG L Pp] [Inhabited Pp] (P : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (gbs : Array Gt) (R : ByteArray) : Best :=
  let n := gbs.size
  let gbs2 := gbs ++ gbs
  let Rr := revCompB2 R
  let m := R.size / 25
  let Ls := R.size / m
  let ps := prepG ix R m Ls
  let pr := prepG ix Rr m Ls
  let x := ilG ix G R Rr gbs2 offs n P Ls ps pr (2 * m + 1)
    ⟨ordG (ps.map (LookG.size ix)) m, [], Array.replicate n []⟩
    ⟨ordG (pr.map (LookG.size ix)) m, [], Array.replicate n []⟩ (initP P)
  let b := (List.range n).foldl (fun b c => chromKBS R gbs2 c P x.1.acc[c]! x.1.J b) x.2.2
  (List.range n).foldl (fun b c => chromKBS Rr gbs2 (n + c) P x.2.1.acc[c]! x.2.1.J b) b

/-- Virtual window → placement. -/
def decodeP (n P : Nat) (b : Best) : Option (Placement × Int) :=
  match resultP P b with
  | some (c, st, len, pen) =>
    some ((if c < n then (⟨c, st, len⟩, Strand.fwd) else (⟨c - n, st, len⟩, Strand.rev)), -(pen : Int))
  | none => none

/-- Map one read on both strands at `T = −P`; reads with too few seeds take the
specification itself. -/
def mapFastGB {L Pp : Type} [LookG L Pp] [Inhabited Pp] (P : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (gbs : Array ByteArray) (R : ByteArray) : Option (Placement × Int) :=
  if fastT P R then decodeP gbs.size P (mapChromsGB P ix G offs gbs R)
  else mapSpecBoth sc0 (-(P : Int)) (decodeGenomeB gbs) (decodeBytes R)

/-- A proper pair at `T = −P`. -/
def pairFastGB {L Pp : Type} [LookG L Pp] [Inhabited Pp] (P lo hi : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (gbs : Array ByteArray) (R1 R2 : ByteArray) :
    Option ((Placement × Int) × (Placement × Int)) :=
  match mapFastGB P ix G offs gbs R1, mapFastGB P ix G offs gbs R2 with
  | some a, some b => if properPair lo hi a.1 b.1 then some (a, b) else none
  | _, _ => none

/-! ## The reverse complement -/

theorem complTab_get (b : UInt8) : complTab.get! b.toNat = complB b := by
  have h := b.toNat_lt
  unfold complTab
  simp only [ByteArray.get!]
  rw [getElem!_pos _ _ (by simpa using h)]
  simp

theorem rcAux_toList (R : ByteArray) : ∀ i (acc : ByteArray), i ≤ R.size →
    (rcAux R i acc).data.toList = acc.data.toList ++ ((R.data.toList.take i).map complB).reverse := by
  intro i
  induction i with
  | zero => intro acc _; simp [rcAux]
  | succ i ih =>
    intro acc hi
    rw [rcAux, complTab_get, ih _ (by omega), ByteArray.data_push, Array.toList_push]
    have hlt : i < R.data.toList.length := by rw [Array.length_toList, ByteArray.size_data]; omega
    have hget : R.get! i = R.data.toList[i] := by
      cases R with
      | mk d =>
        simp only [ByteArray.get!, Array.getElem_toList]
        exact getElem!_pos d i (by simpa using hlt)
    rw [List.take_add_one, List.getElem?_eq_getElem hlt]
    simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.append_assoc, List.singleton_append, hget]

theorem revCompB2_eq (R : ByteArray) : revCompB2 R = revCompB R := by
  unfold revCompB2 revCompB
  have h := rcAux_toList R R.size (ByteArray.emptyWithCapacity R.size) (Nat.le_refl _)
  rw [List.take_of_length_le (by rw [Array.length_toList, ByteArray.size_data]; exact Nat.le_refl _)] at h
  have h0 : (ByteArray.emptyWithCapacity R.size).data.toList = [] := rfl
  rw [h0, List.nil_append] at h
  cases e : rcAux R R.size (ByteArray.emptyWithCapacity R.size) with
  | mk d =>
    rw [e] at h
    congr 1
    apply Array.ext'
    rw [h, Array.toList_reverse, Array.toList_map]

/-! ## Slices -/

/-- **A slice of a lookup in `G` is a complete sorted lookup in the chromosome.** -/
theorem sliceG_ok (G Gc R : ByteArray) (s base o : Nat) (a : Array Nat) (hl : LookOkS G R s base 0 a)
    (hfit : o + Gc.size ≤ G.size) (heq : ∀ i, i < Gc.size → G.get! (o + i) = Gc.get! i) :
    (sliceG a base o Gc.size).toList.Pairwise (· < ·) ∧
      ∀ p, MatchAt Gc p R s → (p + base) * 16 + 0 ∈ (sliceG a base o Gc.size).toList := by
  have ha := incA_of a hl.1
  have mem := mem_lb_extract a ha (16 * (o + base)) (16 * (o + Gc.size + 1 + base - q))
  unfold sliceG
  generalize hx : a.extract _ _ = x at mem
  have hpx : x.toList.Pairwise (· < ·) := by
    rw [← hx, Array.toList_extract, List.extract_eq_take_drop]
    exact hl.1.sublist ((List.take_sublist _ _).trans (List.drop_sublist _ _))
  refine ⟨?_, fun p hp => ?_⟩
  · rw [Array.toList_map, List.pairwise_map]
    refine hpx.imp_of_mem (fun {e1 e2} h1 h2 hlt => ?_)
    have := ((mem e1).mp h1).2.1
    omega
  · rw [Array.toList_map, List.mem_map]
    have hm : MatchAt G (o + p) R s := ⟨by have := hp.1; omega, fun k hk => by
      rw [Nat.add_assoc, heq _ (by have := hp.1; omega)]; exact hp.2 k hk⟩
    refine ⟨(o + p + base) * 16 + 0, (mem _).mpr ⟨(hl.2 _).mpr ⟨_, hm, by omega⟩, ?_, ?_⟩, by omega⟩
    · omega
    · have := hp.1; have hq : q = 25 := rfl; omega

/-! ## Penalties of virtual windows -/

/-- Penalty of a virtual window: chromosomes `0..n-1` with the read, `n..2n-1`
with its reverse complement. -/
def cwB (P : Nat) (read : List Char) (g : Genome) (w : Window) : Nat :=
  if w.chr < g.length then cwT P read g w else cwT P (revComp read) g ⟨w.chr - g.length, w.start, w.len⟩

theorem cwB_le (P : Nat) (read : List Char) (g : Genome) (w : Window) : cwB P read g w ≤ P + 1 := by
  unfold cwB; split <;> exact cwT_le _ _ _ _

theorem windowSeq_app_left (g : Genome) (w : Window) (h : w.chr < g.length) : windowSeq (g ++ g) w = windowSeq g w := by
  unfold windowSeq; rw [List.getElem?_append_left h]

theorem windowSeq_app_right (g : Genome) (c st len : Nat) :
    windowSeq (g ++ g) ⟨g.length + c, st, len⟩ = windowSeq g ⟨c, st, len⟩ := by
  unfold windowSeq; simp only []; rw [List.getElem?_append_right (by omega)]; simp

theorem cwT_app_left (P : Nat) (r : List Char) (g : Genome) (w : Window) (h : w.chr < g.length) :
    cwT P r (g ++ g) w = cwT P r g w := by
  unfold cwT windowScore; rw [windowSeq_app_left g w h]

theorem cwT_app_right (P : Nat) (r : List Char) (g : Genome) (c st len : Nat) :
    cwT P r (g ++ g) ⟨g.length + c, st, len⟩ = cwT P r g ⟨c, st, len⟩ := by
  unfold cwT windowScore; rw [windowSeq_app_right]

theorem genomeBytes_app (gbs : Array ByteArray) (g : Genome) (hg : GenomeBytes gbs g) :
    GenomeBytes (gbs ++ gbs) (g ++ g) := by
  obtain ⟨hsz, henc⟩ := hg
  refine ⟨by simp [hsz], fun c h1 h2 => ?_⟩
  by_cases hc : c < gbs.size
  · have hc' : c < g.length := by omega
    simp only [Array.getElem_append, List.getElem_append, hc, hc', dite_true]
    exact henc c hc hc'
  · have hc' : ¬ c < g.length := by omega
    simp only [Array.size_append, List.length_append] at h1 h2
    simp only [Array.getElem_append, List.getElem_append, hc, hc', dite_false]
    have e : c - gbs.size = c - g.length := by omega
    simp only [e]
    exact henc _ (by omega) (by omega)

theorem gbs2_get (gbs : Array ByteArray) (t c : Nat) (ht : t = 0 ∨ t = gbs.size) (hc : c < gbs.size) :
    (gbs ++ gbs)[t + c]! = gbs[c]! := by
  have h1 : t + c < (gbs ++ gbs).size := by simp; omega
  rw [getElem!_pos (gbs ++ gbs) (t + c) h1, getElem!_pos gbs c hc]
  rcases ht with rfl | rfl
  · simp only [Nat.zero_add, Array.getElem_append, hc, dite_true]
  · have : ¬ gbs.size + c < gbs.size := by omega
    simp only [Array.getElem_append, this, dite_false, Nat.add_sub_cancel_left]

/-! ## Decoding -/

/-- Placement penalty. -/
def cwS (P : Nat) (read : List Char) (g : Genome) : Strand → Window → Nat
  | .fwd => cwT P read g
  | .rev => cwT P (revComp read) g

theorem cwT_chr_lt (P : Nat) (r : List Char) (g : Genome) (w : Window) (h : cwT P r g w ≤ P) : w.chr < g.length := by
  apply Classical.byContradiction; intro hc
  have : windowScore sc0 r g w = none := by
    unfold windowScore windowSeq; rw [List.getElem?_eq_none (by omega)]
  unfold cwT at h; rw [this] at h; simp only [] at h; omega

def encB (n : Nat) : Placement → Window
  | (w, .fwd) => w
  | (w, .rev) => ⟨n + w.chr, w.start, w.len⟩

def decB (n : Nat) (w : Window) : Placement :=
  if w.chr < n then (⟨w.chr, w.start, w.len⟩, Strand.fwd) else (⟨w.chr - n, w.start, w.len⟩, Strand.rev)

theorem cwS_chr_lt (P : Nat) (read : List Char) (g : Genome) (p : Placement) (h : cwS P read g p.2 p.1 ≤ P) :
    p.1.chr < g.length := by
  rcases p with ⟨w, st⟩; cases st <;> exact cwT_chr_lt P _ g w h

theorem cwB_encB (P : Nat) (read : List Char) (g : Genome) (p : Placement) (h : cwS P read g p.2 p.1 ≤ P) :
    cwB P read g (encB g.length p) = cwS P read g p.2 p.1 := by
  have hc := cwS_chr_lt P read g p h
  rcases p with ⟨⟨c, st, len⟩, s⟩
  simp only at hc
  cases s
  · simp [encB, cwB, cwS, hc]
  · have h1 : ¬ g.length + c < g.length := by omega
    simp [encB, cwB, cwS, h1]

theorem cwB_chr_lt (P : Nat) (read : List Char) (g : Genome) (w : Window) (h : cwB P read g w ≤ P) :
    w.chr < 2 * g.length := by
  unfold cwB at h
  split at h
  · omega
  · have := cwT_chr_lt P _ g _ h; simp only at this; omega

theorem cwS_decB (P : Nat) (read : List Char) (g : Genome) (w : Window) :
    cwS P read g (decB g.length w).2 (decB g.length w).1 = cwB P read g w := by
  rcases w with ⟨c, st, len⟩
  unfold decB cwB
  by_cases hc : c < g.length
  · simp [hc, cwS]
  · simp [hc, cwS]

theorem decB_encB (n : Nat) (p : Placement) (h : p.1.chr < n) : decB n (encB n p) = p := by
  rcases p with ⟨⟨c, st, len⟩, s⟩
  simp only at h
  cases s
  · simp [encB, decB, h]
  · have h1 : ¬ n + c < n := by omega
    simp [encB, decB, h1]

theorem encB_decB (n : Nat) (w : Window) (h : w.chr < 2 * n) : encB n (decB n w) = w := by
  rcases w with ⟨c, st, len⟩
  unfold decB
  by_cases hc : c < n
  · simp [hc, encB]
  · simp only [hc, if_false, encB]
    simp only [Window.mk.injEq, and_true]
    omega

theorem mem_hitsBoth_T (T : Int) (g : Genome) (read : List Char) (p : Placement) (s : Int) :
    (p, s) ∈ hitsBoth sc0 T g read ↔
      p.1 ∈ allWindows g ∧ strandScore g read p.2 p.1 = some s ∧ T ≤ s := by
  obtain ⟨w, st⟩ := p
  unfold hitsBoth
  rw [List.mem_append, List.mem_map, List.mem_map]
  cases st with
  | fwd =>
    show _ ↔ w ∈ allWindows g ∧ windowScore sc0 read g w = some s ∧ T ≤ s
    rw [← mem_hitsOf]
    constructor
    · rintro (⟨⟨w', s'⟩, h, he⟩ | ⟨⟨w', s'⟩, h, he⟩)
      · simp only [Prod.mk.injEq] at he
        obtain ⟨⟨rfl, -⟩, rfl⟩ := he
        exact h
      · simp at he
    · intro h; exact Or.inl ⟨(w, s), h, rfl⟩
  | rev =>
    show _ ↔ w ∈ allWindows g ∧ windowScore sc0 (revComp read) g w = some s ∧ T ≤ s
    rw [← mem_hitsOf]
    constructor
    · rintro (⟨⟨w', s'⟩, h, he⟩ | ⟨⟨w', s'⟩, h, he⟩)
      · simp at he
      · simp only [Prod.mk.injEq] at he
        obtain ⟨⟨rfl, -⟩, rfl⟩ := he
        exact h
    · intro h; exact Or.inr ⟨(w, s), h, rfl⟩

theorem mapSpecBoth_iffT (T : Int) (g : Genome) (read : List Char) (p : Placement) (s : Int) :
    mapSpecBoth sc0 T g read = some (p, s) ↔
      (strandScore g read p.2 p.1 = some s ∧ T ≤ s) ∧
      ∀ p' s', strandScore g read p'.2 p'.1 = some s' → T ≤ s' → s' < s ∨ p' = p := by
  unfold mapSpecBoth
  rw [selectUniqueBy_eq_some_iff _ (by
    rintro ⟨a, sa⟩ ha ⟨b, sb⟩ hb (rfl : a = b)
    rw [mem_hitsBoth_T] at ha hb
    have := ha.2.1.symm.trans hb.2.1
    simpa using this)]
  constructor
  · rintro ⟨hm, h3⟩
    rw [mem_hitsBoth_T] at hm
    exact ⟨⟨hm.2.1, hm.2.2⟩, fun p' s' h4 h5 =>
      h3 (p', s') ((mem_hitsBoth_T _ _ _ _ _).2
        ⟨strandScore_allWindows g read p'.2 p'.1 s' h4, h4, h5⟩)⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨(mem_hitsBoth_T _ _ _ _ _).2
      ⟨strandScore_allWindows g read p.2 p.1 s h1, h1, h2⟩, fun ⟨p', s'⟩ hb => ?_⟩
    rw [mem_hitsBoth_T] at hb
    exact h3 p' s' hb.2.1 hb.2.2

/-- **Decoding.**  A best that keeps the invariant over all virtual windows, with
every virtual hit added, decodes to `mapSpecBoth`. -/
theorem decodeP_eq (P : Nat) (g : Genome) (read : List Char) (S : Window → Prop) (b : Best)
    (h : InvP P (cwB P read g) S b) (hall : ∀ w, cwB P read g w ≤ P → S w) :
    decodeP g.length P b = mapSpecBoth sc0 (-(P : Int)) g read := by
  have res := resultP_spec P (cwB P read g) S b h hall
  have key : ∀ (st : Strand) w' s', (strandScore g read st w' = some s' ∧ -(P : Int) ≤ s') ↔
      (cwS P read g st w' ≤ P ∧ s' = -(cwS P read g st w' : Int)) := by
    intro st w' s'
    cases st with
    | fwd => exact cwT_iff P read g w' s'
    | rev => exact cwT_iff P (revComp read) g w' s'
  apply Option.ext
  rintro ⟨p, s⟩
  rw [mapSpecBoth_iffT]
  have dspec : decodeP g.length P b = some (p, s) ↔
      (cwS P read g p.2 p.1 ≤ P ∧ s = -(cwS P read g p.2 p.1 : Int)) ∧
      ∀ p', cwS P read g p'.2 p'.1 ≤ P → p' ≠ p → cwS P read g p.2 p.1 < cwS P read g p'.2 p'.1 := by
    constructor
    · intro hd
      unfold decodeP at hd
      split at hd
      · next c st len pen hr =>
        obtain ⟨e1, e2, e3⟩ := (res ⟨c, st, len⟩ pen).mp hr
        simp only [Option.some.injEq, Prod.mk.injEq] at hd
        obtain ⟨hp, hs⟩ := hd
        have hpd : p = decB g.length ⟨c, st, len⟩ := by rw [← hp]; rfl
        have hcp : cwS P read g p.2 p.1 = pen := by rw [hpd, cwS_decB, e1]
        refine ⟨⟨by omega, by rw [← hs, hcp]⟩, fun p' h1 h2 => ?_⟩
        rw [hcp, ← cwB_encB P read g p' h1]
        apply e3 _ (by rw [cwB_encB P read g p' h1]; exact h1)
        intro he
        apply h2
        rw [hpd, ← he, decB_encB _ _ (cwS_chr_lt P read g p' h1)]
      · exact absurd hd (by simp)
    · rintro ⟨⟨h1, rfl⟩, h3⟩
      have hr : resultP P b = some ((encB g.length p).chr, (encB g.length p).start,
          (encB g.length p).len, cwS P read g p.2 p.1) := by
        refine (res _ _).mpr ⟨cwB_encB P read g p h1, h1, fun w' h4 h5 => ?_⟩
        have := h3 (decB g.length w') (by rw [cwS_decB]; exact h4) (by
          intro he; apply h5; rw [← he, encB_decB _ _ (cwB_chr_lt P read g w' h4)])
        rwa [cwS_decB] at this
      have hd := decB_encB g.length p (cwS_chr_lt P read g p h1)
      unfold decodeP
      rw [hr]
      simp only [Option.some.injEq, Prod.mk.injEq, and_true]
      exact hd
  rw [dspec]
  constructor
  · rintro ⟨⟨h1, rfl⟩, h3⟩
    refine ⟨(key p.2 p.1 _).mpr ⟨h1, rfl⟩, fun p' s' h4 h5 => ?_⟩
    obtain ⟨h6, rfl⟩ := (key p'.2 p'.1 s').mp ⟨h4, h5⟩
    by_cases hp : p' = p
    · right; exact hp
    · left; have := h3 p' h6 hp; omega
  · rintro ⟨h1, h3⟩
    obtain ⟨h1a, rfl⟩ := (key p.2 p.1 s).mp h1
    refine ⟨⟨h1a, rfl⟩, fun p' h4 h5 => ?_⟩
    rcases h3 p' _ ((key p'.2 p'.1 _).mpr ⟨h4, rfl⟩).1 ((key p'.2 p'.1 _).mpr ⟨h4, rfl⟩).2 with h6 | h6
    · omega
    · exact absurd h6 h5

/-! ## One strand's lookups -/

section strand
variable (P : Nat) (read : List Char) (g : Genome) (gbs : Array ByteArray) (hg : GenomeBytes gbs g)
  {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G : ByteArray) (offs : Array Nat)
  (Rs : ByteArray) (reads : List Char) (hrs : Encodes Rs reads) (t : Nat)
  (hcwc : ∀ c, c < gbs.size → ∀ st len, cwB P read g ⟨t + c, st, len⟩ = cwT P reads (g ++ g) ⟨t + c, st, len⟩)
  (Ls : Nat) (ps : Array Pp)

/-- Slice of seed `j`'s lookup on chromosome `c`. -/
def arrS (c j : Nat) : Array Nat :=
  sliceG (LookG.look ix G Rs (j * Ls) (Rs.size - j * Ls) ps[j]!) (Rs.size - j * Ls) offs[c]! (gbs ++ gbs)[t + c]!.size

/-- A strand's state: slices of the looked-up seeds, seeds looked up + left = `ord0`,
same-length windows of the slices added. -/
def GSok (S : Window → Prop) (ord0 : List Nat) (s : GS) : Prop :=
  s.acc.size = gbs.size ∧ (∀ c, c < gbs.size → s.acc[c]! = s.J.map (arrS gbs ix G offs Rs t Ls ps c)) ∧
    s.J.reverse ++ s.ord = ord0 ∧
    ∀ c, c < gbs.size → ∀ j ∈ s.J, ∀ e ∈ (arrS gbs ix G offs Rs t Ls ps c j).toList, ∀ w,
      GX P reads (g ++ g) Rs (t + c) (min P 16) e w → S w

theorem GSok.mono {S S' : Window → Prop} {ord0 : List Nat} {s : GS}
    (h : GSok P g gbs ix G offs Rs reads t Ls ps S ord0 s) (hS : ∀ w, S w → S' w) :
    GSok P g gbs ix G offs Rs reads t Ls ps S' ord0 s :=
  ⟨h.1, h.2.1, h.2.2.1, fun c hc j hj e he w hw => hS w (h.2.2.2 c hc j hj e he w hw)⟩

include hg hrs hcwc

theorem advC_fold (j : Nat) (ht : t = 0 ∨ t = gbs.size) :
    ∀ (l : List Nat) (r : Array (List (Array Nat)) × Best) (S : Window → Prop), l.Nodup →
      (∀ c ∈ l, c < gbs.size) → r.1.size = gbs.size → InvP P (cwB P read g) S r.2 →
      ∃ S', InvP P (cwB P read g) S' (l.foldl (advC Rs (gbs ++ gbs) offs t P (Rs.size - j * Ls)
          (LookG.look ix G Rs (j * Ls) (Rs.size - j * Ls) ps[j]!)) r).2 ∧
        (∀ w, S w → S' w) ∧
        (l.foldl (advC Rs (gbs ++ gbs) offs t P (Rs.size - j * Ls)
          (LookG.look ix G Rs (j * Ls) (Rs.size - j * Ls) ps[j]!)) r).2.pen ≤ r.2.pen ∧
        (l.foldl (advC Rs (gbs ++ gbs) offs t P (Rs.size - j * Ls)
          (LookG.look ix G Rs (j * Ls) (Rs.size - j * Ls) ps[j]!)) r).1.size = gbs.size ∧
        (∀ c, c < gbs.size → (l.foldl (advC Rs (gbs ++ gbs) offs t P (Rs.size - j * Ls)
          (LookG.look ix G Rs (j * Ls) (Rs.size - j * Ls) ps[j]!)) r).1[c]! =
            if c ∈ l then arrS gbs ix G offs Rs t Ls ps c j :: r.1[c]! else r.1[c]!) ∧
        (∀ c ∈ l, ∀ e ∈ (arrS gbs ix G offs Rs t Ls ps c j).toList, ∀ w,
          GX P reads (g ++ g) Rs (t + c) (min P 16) e w → S' w) := by
  have hg2 := genomeBytes_app gbs g hg
  intro l
  induction l with
  | nil =>
    intro r S _ _ hsz hi
    exact ⟨S, hi, fun w hw => hw, Nat.le_refl _, hsz, fun c _ => by simp, fun c hc => by simp at hc⟩
  | cons c l ih =>
    intro r S hnd hl hsz hi
    have hnd' := List.nodup_cons.mp hnd
    have hc : c < gbs.size := hl c List.mem_cons_self
    rw [List.foldl_cons]
    have hf := foldl_invP P (cwB P read g)
      (fun b e => addK Rs (gbs ++ gbs) (t + c) (min P 16) ((e / 16 : Nat) - (Rs.size : Int)) Rs.size b)
      (fun e w => GX P reads (g ++ g) Rs (t + c) (min P 16) e w)
      (fun e S b h => addK_inv P reads (g ++ g) (gbs ++ gbs) Rs hg2 hrs (cwB P read g) (cwB_le P read g)
        (t + c) (min P 16) (by simp; omega) (hcwc c hc) (Nat.min_le_left _ _) (Nat.min_le_right _ _) _ _ S b h)
      (arrS gbs ix G offs Rs t Ls ps c j).toList S r.2 hi
    have hfp := foldl_pen
      (fun b e => addK Rs (gbs ++ gbs) (t + c) (min P 16) ((e / 16 : Nat) - (Rs.size : Int)) Rs.size b)
      (fun b e => addK_pen _ _ _ _ _ _ b) (arrS gbs ix G offs Rs t Ls ps c j).toList r.2
    rw [Array.foldl_toList] at hf hfp
    generalize hr' : advC Rs (gbs ++ gbs) offs t P (Rs.size - j * Ls)
      (LookG.look ix G Rs (j * Ls) (Rs.size - j * Ls) ps[j]!) r c = r'
    have e2 : r'.2 = (arrS gbs ix G offs Rs t Ls ps c j).foldl
        (fun b e => addK Rs (gbs ++ gbs) (t + c) (min P 16) ((e / 16 : Nat) - (Rs.size : Int)) Rs.size b) r.2 := by
      rw [← hr']; rfl
    have e1 : r'.1 = r.1.set! c (arrS gbs ix G offs Rs t Ls ps c j :: r.1[c]!) := by rw [← hr']; rfl
    rw [← e2] at hf hfp
    have esz : r'.1.size = gbs.size := by rw [e1]; simp [hsz]
    obtain ⟨S', i', s', p', z', a', c'⟩ := ih r' _ hnd'.2 (fun c' h' => hl c' (List.mem_cons_of_mem _ h')) esz hf
    refine ⟨S', i', fun w hw => s' w (Or.inl hw), Nat.le_trans p' hfp, z', fun c2 hc2 => ?_, fun c2 hc2 e he w hw => ?_⟩
    · rw [a' c2 hc2, e1, getElem!_set!']
      by_cases h1 : c2 = c
      · subst h1; simp [hsz, hc, hnd'.1]
      · have h2 : ¬ c = c2 := fun e => h1 e.symm
        simp [h1, h2]
    · rcases List.mem_cons.mp hc2 with rfl | hc2
      · exact s' w (Or.inr ⟨e, he, hw⟩)
      · exact c' c2 hc2 e he w hw

theorem advG_ok (ht : t = 0 ∨ t = gbs.size) (ord0 : List Nat) (s : GS) (j : Nat) (rest : List Nat)
    (hs : s.ord = j :: rest) (S : Window → Prop) (b : Best)
    (hok : GSok P g gbs ix G offs Rs reads t Ls ps S ord0 s) (hi : InvP P (cwB P read g) S b) :
    ∃ S', InvP P (cwB P read g) S' (s.adv ix G Rs (gbs ++ gbs) offs gbs.size t P Ls ps b).2 ∧
      (∀ w, S w → S' w) ∧ (s.adv ix G Rs (gbs ++ gbs) offs gbs.size t P Ls ps b).2.pen ≤ b.pen ∧
      GSok P g gbs ix G offs Rs reads t Ls ps S' ord0 (s.adv ix G Rs (gbs ++ gbs) offs gbs.size t P Ls ps b).1 ∧
      (s.adv ix G Rs (gbs ++ gbs) offs gbs.size t P Ls ps b).1.ord = rest ∧
      (s.adv ix G Rs (gbs ++ gbs) offs gbs.size t P Ls ps b).1.J = j :: s.J := by
  obtain ⟨hsz, hacc, hord, hwin⟩ := hok
  obtain ⟨S', i', s', p', z', a', c'⟩ := advC_fold P read g gbs hg ix G offs Rs reads hrs t hcwc Ls ps j ht
    (List.range gbs.size) (s.acc, b) S List.nodup_range (fun c hc => List.mem_range.mp hc) hsz hi
  unfold GS.adv
  rw [hs]
  simp only []
  refine ⟨S', i', s', p', ⟨z', fun c hc => ?_, ?_, fun c hc j' hj' e he w hw => ?_⟩, by simp, by simp⟩
  · rw [a' c hc, if_pos (List.mem_range.mpr hc), hacc c hc]; rfl
  · rw [← hord, hs]; simp
  · rcases List.mem_cons.mp hj' with rfl | hj'
    · exact c' c (List.mem_range.mpr hc) e he w hw
    · exact s' w (hwin c hc j' hj' e he w hw)

end strand

/-! ## Both strands interleaved -/

section both
variable (P : Nat) (read : List Char) (g : Genome) (gbs : Array ByteArray) (hg : GenomeBytes gbs g)
  {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G : ByteArray) (offs : Array Nat)
  (R1 R2 : ByteArray) (reads1 reads2 : List Char) (h1 : Encodes R1 reads1) (h2 : Encodes R2 reads2)
  (hcw1 : ∀ c, c < gbs.size → ∀ st len, cwB P read g ⟨0 + c, st, len⟩ = cwT P reads1 (g ++ g) ⟨0 + c, st, len⟩)
  (hcw2 : ∀ c, c < gbs.size → ∀ st len,
    cwB P read g ⟨gbs.size + c, st, len⟩ = cwT P reads2 (g ++ g) ⟨gbs.size + c, st, len⟩)
  (Ls : Nat) (ps1 ps2 : Array Pp) (ord1 ord2 : List Nat)

include hg h1 h2 hcw1 hcw2

theorem ilG_ok : ∀ (f : Nat) (s1 s2 : GS) (b : Best) (S : Window → Prop),
    GSok P g gbs ix G offs R1 reads1 0 Ls ps1 S ord1 s1 →
    GSok P g gbs ix G offs R2 reads2 gbs.size Ls ps2 S ord2 s2 →
    InvP P (cwB P read g) S b → s1.ord.length + s2.ord.length < f →
    ∃ S', InvP P (cwB P read g) S' (ilG ix G R1 R2 (gbs ++ gbs) offs gbs.size P Ls ps1 ps2 f s1 s2 b).2.2 ∧
      (∀ w, S w → S' w) ∧ (ilG ix G R1 R2 (gbs ++ gbs) offs gbs.size P Ls ps1 ps2 f s1 s2 b).2.2.pen ≤ b.pen ∧
      GSok P g gbs ix G offs R1 reads1 0 Ls ps1 S' ord1 (ilG ix G R1 R2 (gbs ++ gbs) offs gbs.size P Ls ps1 ps2 f s1 s2 b).1 ∧
      GSok P g gbs ix G offs R2 reads2 gbs.size Ls ps2 S' ord2
        (ilG ix G R1 R2 (gbs ++ gbs) offs gbs.size P Ls ps1 ps2 f s1 s2 b).2.1 ∧
      (ilG ix G R1 R2 (gbs ++ gbs) offs gbs.size P Ls ps1 ps2 f s1 s2 b).1.live P
        (ilG ix G R1 R2 (gbs ++ gbs) offs gbs.size P Ls ps1 ps2 f s1 s2 b).2.2 = false ∧
      (ilG ix G R1 R2 (gbs ++ gbs) offs gbs.size P Ls ps1 ps2 f s1 s2 b).2.1.live P
        (ilG ix G R1 R2 (gbs ++ gbs) offs gbs.size P Ls ps1 ps2 f s1 s2 b).2.2 = false := by
  intro f
  induction f with
  | zero => intro s1 s2 b S _ _ _ hf; omega
  | succ f ih =>
    intro s1 s2 b S o1 o2 hi hf
    unfold ilG
    simp only []
    split
    · next hc =>
      simp only [Bool.and_eq_true] at hc
      have hne : s1.ord ≠ [] := by
        intro he; unfold GS.live at hc; simp [he] at hc
      obtain ⟨j, rest, hjr⟩ : ∃ j rest, s1.ord = j :: rest := by
        cases h : s1.ord with
        | nil => exact absurd h hne
        | cons j rest => exact ⟨j, rest, rfl⟩
      obtain ⟨S1, i1, e1, p1, k1, r1, -⟩ := advG_ok P read g gbs hg ix G offs R1 reads1 h1 0 hcw1 Ls ps1
        (Or.inl rfl) ord1 s1 j rest hjr S b o1 hi
      obtain ⟨S2, i2, e2, p2, k2, k3, l1, l2⟩ := ih _ s2 _ S1 k1 (o2.mono P g gbs ix G offs R2 reads2 gbs.size Ls ps2 e1) i1
        (by rw [r1]; rw [hjr] at hf; simp at hf; omega)
      exact ⟨S2, i2, fun w hw => e2 w (e1 w hw), Nat.le_trans p2 p1, k2, k3, l1, l2⟩
    · next hc1 =>
      split
      · next hc =>
        have hne : s2.ord ≠ [] := by
          intro he; unfold GS.live at hc; simp [he] at hc
        obtain ⟨j, rest, hjr⟩ : ∃ j rest, s2.ord = j :: rest := by
          cases h : s2.ord with
          | nil => exact absurd h hne
          | cons j rest => exact ⟨j, rest, rfl⟩
        obtain ⟨S1, i1, e1, p1, k1, r1, -⟩ := advG_ok P read g gbs hg ix G offs R2 reads2 h2 gbs.size hcw2 Ls ps2
          (Or.inr rfl) ord2 s2 j rest hjr S b o2 hi
        obtain ⟨S2, i2, e2, p2, k2, k3, l1, l2⟩ := ih s1 _ _ S1 (o1.mono P g gbs ix G offs R1 reads1 0 Ls ps1 e1) k1 i1
          (by rw [r1]; rw [hjr] at hf; simp at hf; omega)
        exact ⟨S2, i2, fun w hw => e2 w (e1 w hw), Nat.le_trans p2 p1, k2, k3, l1, l2⟩
      · next hc2 =>
        simp only [Bool.not_eq_true] at hc2
        refine ⟨S, hi, fun w hw => hw, Nat.le_refl _, o1, o2, ?_, hc2⟩
        simp only [hc2, Bool.not_false, Bool.true_or, Bool.and_true, Bool.not_eq_true] at hc1
        exact hc1

end both

/-! ## Stages K and B per virtual chromosome -/

theorem addBS_pen' (P : Nat) (R : ByteArray) (gbs : Array ByteArray) (c D : Nat) (opt : Option (Array Int))
    (b : Best) (sh : Int × Int) : (addBS P R gbs c D opt b sh).pen ≤ b.pen := by
  unfold addBS; simp only []; split
  · exact add_pen_le _ _ _ _ _
  · exact Nat.le_refl _

theorem chromKB_pen (P : Nat) (R : ByteArray) (gbs : Array ByteArray) (c : Nat) (acc : List (Array Nat)) (b : Best) :
    (chromKB R gbs c P acc b).pen ≤ b.pen := by
  have hK : ∀ lim shs ds b, (stageK R gbs c lim shs ds b).pen ≤ b.pen := fun lim shs ds b => by
    unfold stageK
    exact foldl_pen _ (fun b D => foldl_pen _ (fun b sh => addK_pen _ _ _ _ _ _ b) _ b) _ b
  have hB : ∀ shs bs ds b, (stageB P R gbs c shs bs ds b).pen ≤ b.pen := fun shs bs ds b => by
    unfold stageB
    refine foldl_pen _ (fun b D => foldl_pen _ (fun b bb => ?_) bs b) ds b
    unfold stageBD; split
    · exact foldl_pen _ (fun b sh => addBS_pen' _ R gbs c D _ b sh) _ b
    · exact Nat.le_refl _
  unfold chromKB
  simp only [stageKP_fun, ite_self, shapesT_eq, shapesKT_eq]
  have h2 : (if 0 < gapBound sc0 (-((min b.pen P : Nat) : Int)) then
      stageK R gbs c (min P 16) ((shapesAt (min b.pen P)).filter (· != (0, 0)))
        (diagsB acc (acc.length - sbound (min (min P 16) (min b.pen P))) (2 * gapBound sc0 (-((min b.pen P : Nat) : Int)))) b
      else b).pen ≤ b.pen := by
    split
    · exact hK _ _ _ _
    · exact Nat.le_refl _
  generalize (if 0 < gapBound sc0 (-((min b.pen P : Nat) : Int)) then _ else b) = b2 at h2 ⊢
  split
  · exact Nat.le_trans (hB _ _ _ _) h2
  · exact h2

theorem chromKBS_pen (P : Nat) (R : ByteArray) (gbs : Array ByteArray) (c : Nat) (acc : List (Array Nat))
    (J : List Nat) (b : Best) : (chromKBS R gbs c P acc J b).pen ≤ b.pen := by
  have hK : ∀ lim shs ds b, (stageK R gbs c lim shs ds b).pen ≤ b.pen := fun lim shs ds b => by
    unfold stageK
    exact foldl_pen _ (fun b D => foldl_pen _ (fun b sh => addK_pen _ _ _ _ _ _ b) _ b) _ b
  have hB : ∀ shs bs ds b, (stageB P R gbs c shs bs ds b).pen ≤ b.pen := fun shs bs ds b => by
    unfold stageB
    refine foldl_pen _ (fun b D => foldl_pen _ (fun b bb => ?_) bs b) ds b
    unfold stageBD; split
    · exact foldl_pen _ (fun b sh => addBS_pen' _ R gbs c D _ b sh) _ b
    · exact Nat.le_refl _
  have hS : ∀ (body : Nat → Best → Best), (∀ D b, (body D b).pen ≤ b.pen) →
      ∀ us Ls lim ds b, (stageKS body R gbs[c]! acc us Ls lim ds b).pen ≤ b.pen := by
    intro body hb us Ls lim ds b
    unfold stageKS
    refine foldl_pen _ (fun b D => ?_) ds b
    split
    · exact hb _ _
    · exact Nat.le_refl _
  unfold chromKBS
  simp only [stageKP_fun, ite_self, shapesT_eq, shapesKT_eq]
  have h2 : (if 0 < gapBound sc0 (-((min b.pen P : Nat) : Int)) then
      stageKS (fun D b' => stageK R gbs c (min P 16) ((shapesAt (min b.pen P)).filter (· != (0, 0))) [D] b')
        R gbs[c]! acc (unseen (R.size / 25) J) (R.size / (R.size / 25)) (min P 16) (diags acc) b
      else b).pen ≤ b.pen := by
    split
    · exact hS _ (fun D b' => hK _ _ _ _) _ _ _ _ _
    · exact Nat.le_refl _
  generalize (if 0 < gapBound sc0 (-((min b.pen P : Nat) : Int)) then _ else b) = b2 at h2 ⊢
  split
  · exact Nat.le_trans (hS _ (fun D b' => hB _ _ _ _) _ _ _ _ _) h2
  · exact h2

section kb
variable (P : Nat) (read : List Char) (g : Genome) (gbs : Array ByteArray) (hg : GenomeBytes gbs g)
  {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G : ByteArray) (offs : Array Nat)
  (hcat : catOk G offs gbs = true)
  (Rs : ByteArray) (reads : List Char) (hrs : Encodes Rs reads) (t : Nat) (ht : t = 0 ∨ t = gbs.size)
  (hcwc : ∀ c, c < gbs.size → ∀ st len, cwB P read g ⟨t + c, st, len⟩ = cwT P reads (g ++ g) ⟨t + c, st, len⟩)
  (hm : 0 < Rs.size / 25) (hsb : sbound P < Rs.size / 25)
  (ps : Array Pp) (Ls : Nat) (hLs : Ls = Rs.size / (Rs.size / 25))
  (hps : ∀ j, j < Rs.size / 25 → ps[j]! = LookG.prep ix (seedHashAt Rs (j * Ls)))
  (hlk : ∀ s base, s + q ≤ Rs.size → LookOkS G Rs s base 0 (LookG.look ix G Rs s base (LookG.prep ix (seedHashAt Rs s))))
  (ord0 : List Nat) (hnd : ord0.Nodup) (hlt : ∀ j ∈ ord0, j < Rs.size / 25) (hlen : ord0.length = Rs.size / 25)

include hg hcat hrs ht hcwc hm hsb hLs hps hlk hnd hlt hlen

set_option maxHeartbeats 1000000 in
/-- Stages K and B over a strand's chromosomes. -/
theorem kbFold (s : GS) : ∀ (l : List Nat) (S : Window → Prop) (b : Best), (∀ c ∈ l, c < gbs.size) →
    GSok P g gbs ix G offs Rs reads t Ls ps S ord0 s →
    InvP P (cwB P read g) S b → (sbound (min b.pen P) < s.J.length ∨ s.ord = []) →
    ∃ S', InvP P (cwB P read g) S'
        (l.foldl (fun b c => chromKBS Rs (gbs ++ gbs) (t + c) P s.acc[c]! s.J b) b) ∧
      (∀ w, S w → S' w) ∧
      (l.foldl (fun b c => chromKBS Rs (gbs ++ gbs) (t + c) P s.acc[c]! s.J b) b).pen ≤ b.pen ∧
      ∀ c ∈ l, ∀ w, w.chr = t + c → cwB P read g w ≤ P → S' w := by
  have hg2 := genomeBytes_app gbs g hg
  subst hLs
  intro l
  induction l with
  | nil => intro S b _ _ hi _; exact ⟨S, hi, fun w hw => hw, Nat.le_refl _, fun c hc => by simp at hc⟩
  | cons c l ih =>
    intro S b hl hok hi hst
    have hc : c < gbs.size := hl c List.mem_cons_self
    have hc2 : t + c < (gbs ++ gbs).size := by simp; omega
    obtain ⟨hsz, hacc, hord, hwin⟩ := hok
    have hJ : List.Sublist s.J.reverse ord0 := by rw [← hord]; exact List.sublist_append_left _ _
    have hcatc := catOk_spec G offs gbs hcat c hc
    have hgc := gbs2_get gbs t c ht hc
    obtain ⟨S1, i1, s1, c1⟩ := chromKBS_cover P reads (g ++ g) (gbs ++ gbs) Rs hg2 hrs (t + c) hc2 hm hsb
      (cwB P read g) (cwB_le P read g) (hcwc c hc) (arrS gbs ix G offs Rs t (Rs.size / (Rs.size / 25)) ps c)
      (fun j hj => by
        unfold arrS
        rw [hps j hj]
        have hfit := seed_fits Rs.size j hm hj
        rw [hgc]
        exact sliceG_ok G gbs[c]! Rs _ _ _ _ (hlk _ _ hfit) hcatc.1 hcatc.2)
      s.J.reverse (hJ.nodup hnd) (fun j hj => hlt j (hJ.subset hj)) s.J (fun j => List.mem_reverse.symm) S b hi
      (fun j hj e he w hw => hwin c hc j (List.mem_reverse.mp hj) e he w hw)
      (by
        rcases hst with h | h
        · left; rw [List.length_reverse]; exact h
        · right; rw [h, List.append_nil] at hord; rw [hord, hlen])
    rw [List.map_reverse, List.reverse_reverse, ← hacc c hc] at i1 c1
    have hpen := chromKBS_pen P Rs (gbs ++ gbs) (t + c) s.acc[c]! s.J b
    simp only [List.foldl_cons]
    generalize chromKBS Rs (gbs ++ gbs) (t + c) P s.acc[c]! s.J b = b1 at i1 c1 hpen
    -- the windows of chromosome `t + c` not added cannot beat or tie the best
    have i1' := inv_skipP P (cwB P read g) (cwB_le P read g) S1
      (fun w => w.chr = t + c ∧ cwB P read g w ≤ P ∧ ¬ S1 w) b1 i1 (by
        rintro w ⟨hwc, hwP, hnot⟩
        left
        apply Classical.byContradiction; intro hle
        apply hnot (c1 w hwc _)
        obtain ⟨wc, wst, wlen⟩ := w
        simp only at hwc; subst hwc
        rw [← hcwc c hc]; omega)
    obtain ⟨S2, i2, s2, p2, c2⟩ := ih _ b1 (fun c' h' => hl c' (List.mem_cons_of_mem _ h'))
      ⟨hsz, hacc, hord, fun c' hc' j hj e he w hw => Or.inl (s1 w (hwin c' hc' j hj e he w hw))⟩ i1'
      (by
        rcases hst with h | h
        · left; have := sbound_mono (min b1.pen P) (min b.pen P) (by omega); omega
        · right; exact h)
    refine ⟨S2, i2, fun w hw => s2 w (Or.inl (s1 w hw)), Nat.le_trans p2 hpen, fun c' hc' w hwc hwP => ?_⟩
    rcases List.mem_cons.mp hc' with rfl | hc'
    · apply s2
      by_cases h : S1 w
      · exact Or.inl h
      · exact Or.inr ⟨hwc, hwP, h⟩
    · exact c2 c' hc' w hwc hwP

end kb

/-! ## All chromosomes, both strands -/

theorem prepG_get {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (R : ByteArray) (m Ls j : Nat) (hj : j < m) :
    (prepG ix R m Ls)[j]! = LookG.prep ix (seedHashAt R (j * Ls)) := by
  unfold prepG
  rw [getElem!_pos _ j (by simpa using hj)]
  simp

theorem gsInit_ok (P : Nat) (g : Genome) (gbs : Array ByteArray) {L Pp : Type} [LookG L Pp] [Inhabited Pp]
    (ix : L) (G : ByteArray) (offs : Array Nat) (Rs : ByteArray) (reads : List Char) (t Ls : Nat) (ps : Array Pp)
    (ord0 : List Nat) :
    GSok P g gbs ix G offs Rs reads t Ls ps (fun _ => False) ord0 ⟨ord0, [], Array.replicate gbs.size []⟩ := by
  refine ⟨by simp, fun c hc => ?_, by simp, fun c _ j hj => by simp at hj⟩
  rw [getElem!_pos _ c (by simpa using hc)]
  simp

theorem mapSpecBoth_seqs (T : Int) (g g' : Genome) (read : List Char) (h : g.map (·.seq) = g'.map (·.seq)) :
    mapSpecBoth sc0 T g read = mapSpecBoth sc0 T g' read := by
  have hl : g.length = g'.length := by simpa using congrArg List.length h
  have hc : ∀ c : Nat, (g[c]?).map (fun x : Chromosome => x.seq) = (g'[c]?).map (fun x : Chromosome => x.seq) := by
    intro c; rw [← List.getElem?_map, ← List.getElem?_map, h]
  have hws : windowSeq g = windowSeq g' := by
    funext w
    unfold windowSeq
    have := hc w.chr
    cases h1 : g[w.chr]? <;> cases h2 : g'[w.chr]? <;> simp_all
  have haw : allWindows g = allWindows g' := by
    unfold allWindows
    rw [hl]
    congr 1
    funext c
    have := hc c
    cases h1 : g[c]? <;> cases h2 : g'[c]? <;> simp_all
  unfold mapSpecBoth hitsBoth windowScore
  rw [hws, haw]

section top
variable (P : Nat) (read : List Char) (g : Genome) (gbs : Array ByteArray) (R : ByteArray)
  (hg : GenomeBytes gbs g) (hr : Encodes R read)
  {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G : ByteArray) (offs : Array Nat)
  (hcat : catOk G offs gbs = true)
  (hlk : ∀ (R' : ByteArray) s base, s + q ≤ R'.size →
    LookOkS G R' s base 0 (LookG.look ix G R' s base (LookG.prep ix (seedHashAt R' s))))

include hg hr hcat hlk

set_option maxHeartbeats 1000000 in
/-- **Both strands.**  `mapChromsGB` ends with the invariant over a set containing
every virtual hit. -/
theorem mapChromsGB_inv (hm : 0 < R.size / 25) (hsb : sbound P < R.size / 25) :
    ∃ S, InvP P (cwB P read g) S (mapChromsGB P ix G offs gbs R) ∧ ∀ w, cwB P read g w ≤ P → S w := by
  have hn : gbs.size = g.length := hg.1
  have hrr := revCompB_encodes R read hr
  have hsz := revCompB_size R
  have hcw1 : ∀ c, c < gbs.size → ∀ st len,
      cwB P read g ⟨0 + c, st, len⟩ = cwT P read (g ++ g) ⟨0 + c, st, len⟩ := by
    intro c hc st len
    rw [Nat.zero_add, cwT_app_left P read g _ (by simp only; omega)]
    unfold cwB; rw [if_pos (by simp only; omega)]
  have hcw2 : ∀ c, c < gbs.size → ∀ st len,
      cwB P read g ⟨gbs.size + c, st, len⟩ = cwT P (revComp read) (g ++ g) ⟨gbs.size + c, st, len⟩ := by
    intro c hc st len
    rw [hn, cwT_app_right]
    unfold cwB; rw [if_neg (by simp only; omega)]
    simp
  unfold mapChromsGB
  simp only [revCompB2_eq]
  generalize hLs : R.size / (R.size / 25) = Ls
  generalize hps : prepG ix R (R.size / 25) Ls = ps
  generalize hpr : prepG ix (revCompB R) (R.size / 25) Ls = pr
  obtain ⟨nd1, lt1, len1⟩ := ordG_spec (ps.map (LookG.size ix)) (R.size / 25)
  obtain ⟨nd2, lt2, len2⟩ := ordG_spec (pr.map (LookG.size ix)) (R.size / 25)
  generalize ordG (ps.map (LookG.size ix)) (R.size / 25) = ord1 at nd1 lt1 len1
  generalize ordG (pr.map (LookG.size ix)) (R.size / 25) = ord2 at nd2 lt2 len2
  obtain ⟨S1, i1, -, -, o1, o2, l1, l2⟩ := ilG_ok P read g gbs hg ix G offs R (revCompB R) read (revComp read)
    hr hrr hcw1 hcw2 Ls ps pr ord1 ord2 (2 * (R.size / 25) + 1) _ _ (initP P) (fun _ => False)
    (gsInit_ok P g gbs ix G offs R read 0 Ls ps ord1) (gsInit_ok P g gbs ix G offs (revCompB R) (revComp read) gbs.size Ls pr ord2)
    (inv_initP P (cwB P read g)) (by simp only []; omega)
  generalize ilG ix G R (revCompB R) (gbs ++ gbs) offs gbs.size P Ls ps pr (2 * (R.size / 25) + 1) _ _ (initP P) = x
    at i1 o1 o2 l1 l2
  have stop : ∀ (s : GS) (b : Best), s.live P b = false → sbound (min b.pen P) < s.J.length ∨ s.ord = [] := by
    intro s b h
    unfold GS.live at h
    cases ho : s.ord with
    | nil => right; rfl
    | cons j rest =>
      left; rw [ho] at h; simpa using h
  obtain ⟨S2, i2, s2, p2, c2⟩ := kbFold P read g gbs hg ix G offs hcat R read hr 0 (Or.inl rfl) hcw1 hm hsb
    ps Ls hLs.symm (fun j hj => by rw [← hps]; exact prepG_get ix R _ _ j hj) (hlk R) ord1 nd1 lt1 len1 x.1
    (List.range gbs.size) S1 x.2.2 (fun c hc => List.mem_range.mp hc) o1 i1 (stop _ _ l1)
  simp only [Nat.zero_add] at i2 p2 c2
  generalize (List.range gbs.size).foldl (fun b c => chromKBS R (gbs ++ gbs) c P x.1.acc[c]! x.1.J b) x.2.2 = b1 at i2 p2 c2
  obtain ⟨S3, i3, s3, -, c3⟩ := kbFold P read g gbs hg ix G offs hcat (revCompB R) (revComp read) hrr gbs.size
    (Or.inr rfl) hcw2 (by rw [hsz]; exact hm) (by rw [hsz]; exact hsb) pr Ls (by rw [hsz, hLs])
    (fun j hj => by rw [← hpr]; rw [hsz] at hj; exact prepG_get ix _ _ _ j hj) (hlk _) ord2 nd2
    (by rw [hsz]; exact lt2) (by rw [hsz]; exact len2) x.2.1
    (List.range gbs.size) S2 b1 (fun c hc => List.mem_range.mp hc) (o2.mono P g gbs ix G offs _ _ _ Ls pr s2) i2
    (by
      rcases stop _ _ l2 with h | h
      · left; have := sbound_mono (min b1.pen P) (min x.2.2.pen P) (by omega); omega
      · right; exact h)
  refine ⟨S3, i3, fun w hw => ?_⟩
  have hw2 := cwB_chr_lt P read g w hw
  by_cases hwc : w.chr < gbs.size
  · exact s3 w (c2 w.chr (List.mem_range.mpr hwc) w rfl hw)
  · exact c3 (w.chr - gbs.size) (List.mem_range.mpr (by omega)) w (by omega) hw

end top

/-! ## Top theorems -/

/-- **Both strands at `T = −P`.**  With byte-encoded genome and read, the
concatenation `G` checked by `catOk`, and an index over `G` whose lookups are
complete (`LookOkS`, e.g. from the runtime checker), `mapFastGB` is `mapSpecBoth`. -/
theorem mapFastGB_eq_mapSpecBoth {L Pp : Type} [LookG L Pp] [Inhabited Pp] (P : Nat) (g : Genome)
    (read : List Char) (gbs : Array ByteArray) (R : ByteArray) (ix : L) (G : ByteArray) (offs : Array Nat)
    (hg : GenomeBytes gbs g) (hr : Encodes R read) (hcat : catOk G offs gbs = true)
    (hlk : ∀ (R' : ByteArray) s base, s + q ≤ R'.size →
      LookOkS G R' s base 0 (LookG.look ix G R' s base (LookG.prep ix (seedHashAt R' s)))) :
    mapFastGB P ix G offs gbs R = mapSpecBoth sc0 (-(P : Int)) g read := by
  unfold mapFastGB
  split
  · next hok =>
    unfold fastT at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨S, hi, hall⟩ := mapChromsGB_inv P read g gbs R hg hr ix G offs hcat hlk hok.1 hok.2
    rw [hg.1]
    exact decodeP_eq P g read S _ hi hall
  · rw [decodeBytes_of_encodes R read hr]
    apply mapSpecBoth_seqs
    obtain ⟨hsz, henc⟩ := hg
    unfold decodeGenomeB
    apply List.ext_getElem
    · simp [hsz]
    · intro i h1 h2
      simp only [List.getElem_map, Array.getElem_toList]
      exact decodeBytes_of_encodes _ _ (henc i (by simpa using h1) (by simpa using h2))

/-- **Proper pairs at `T = −P`.** -/
theorem pairFastGB_eq_pairSpec {L Pp : Type} [LookG L Pp] [Inhabited Pp] (P lo hi : Nat) (g : Genome)
    (m1 m2 : List Char) (gbs : Array ByteArray) (R1 R2 : ByteArray) (ix : L) (G : ByteArray) (offs : Array Nat)
    (hg : GenomeBytes gbs g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hcat : catOk G offs gbs = true)
    (hlk : ∀ (R' : ByteArray) s base, s + q ≤ R'.size →
      LookOkS G R' s base 0 (LookG.look ix G R' s base (LookG.prep ix (seedHashAt R' s)))) :
    pairFastGB P lo hi ix G offs gbs R1 R2 = pairSpec sc0 (-(P : Int)) lo hi g m1 m2 := by
  unfold pairFastGB pairSpec
  rw [mapFastGB_eq_mapSpecBoth P g m1 gbs R1 ix G offs hg h1 hcat hlk,
    mapFastGB_eq_mapSpecBoth P g m2 gbs R2 ix G offs hg h2 hcat hlk]
  cases mapSpecBoth sc0 (-(P : Int)) g m1 <;> cases mapSpecBoth sc0 (-(P : Int)) g m2 <;> rfl

/-! ## Hashed and minimizer index over `G` -/

theorem lookG_hashed (G : ByteArray) (ix : HIdx) (hchk : checkAll #[ix] #[G] = true) :
    ∀ (R' : ByteArray) s base, s + q ≤ R'.size →
      LookOkS G R' s base 0 (LookG.look ix G R' s base (LookG.prep ix (seedHashAt R' s))) := by
  intro R' s base h
  simpa using lookAllG_hashed #[G] #[ix] hchk 0 (by simp) R' s base h

theorem lookG_mz (G : ByteArray) (ix : Mz.MzIdx) (hchk : checkAllMz #[ix] #[G] = true) :
    ∀ (R' : ByteArray) s base, s + q ≤ R'.size →
      LookOkS G R' s base 0 (LookG.look ix G R' s base (LookG.prep ix (seedHashAt R' s))) := by
  intro R' s base h
  simpa using lookAllG_mz #[G] #[ix] hchk 0 (by simp) R' s base h

/-- **Proper pairs, hashed index over the concatenation.** -/
theorem pairFastGB_hashed_eq_pairSpec (P lo hi : Nat) (g : Genome) (m1 m2 : List Char) (gbs : Array ByteArray)
    (R1 R2 : ByteArray) (ix : HIdx) (G : ByteArray) (offs : Array Nat)
    (hg : GenomeBytes gbs g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hcat : catOk G offs gbs = true)
    (hchk : checkAll #[ix] #[G] = true) :
    pairFastGB P lo hi ix G offs gbs R1 R2 = pairSpec sc0 (-(P : Int)) lo hi g m1 m2 :=
  pairFastGB_eq_pairSpec P lo hi g m1 m2 gbs R1 R2 ix G offs hg h1 h2 hcat (lookG_hashed G ix hchk)

/-- **Proper pairs, minimizer index over the concatenation.** -/
theorem pairFastGB_mz_eq_pairSpec (P lo hi : Nat) (g : Genome) (m1 m2 : List Char) (gbs : Array ByteArray)
    (R1 R2 : ByteArray) (ix : Mz.MzIdx) (G : ByteArray) (offs : Array Nat)
    (hg : GenomeBytes gbs g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hcat : catOk G offs gbs = true)
    (hchk : checkAllMz #[ix] #[G] = true) :
    pairFastGB P lo hi ix G offs gbs R1 R2 = pairSpec sc0 (-(P : Int)) lo hi g m1 m2 :=
  pairFastGB_eq_pairSpec P lo hi g m1 m2 gbs R1 R2 ix G offs hg h1 h2 hcat (lookG_mz G ix hchk)

end MapSpec.Fast

#print axioms MapSpec.Fast.mapFastGB_eq_mapSpecBoth
#print axioms MapSpec.Fast.pairFastGB_eq_pairSpec
#print axioms MapSpec.Fast.pairFastGB_hashed_eq_pairSpec
#print axioms MapSpec.Fast.pairFastGB_mz_eq_pairSpec
