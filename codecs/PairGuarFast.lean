import PairGuarantee
import PairLadderF

/-!
# The fast pair-level guarantee (`pairGF`), proved

The kernel of the bench's `pairGX`, rebuilt so that every step is proved:

* **One mate enumerated** (`X`: the mate whose cheapest seeds have the smallest buckets;
  sizes are free).  Its hits within `G` come from `sbound G + 2` of its rarest seeds
  (`hitsAtKP3`): at `G = 4` the three rarest, and the support filter (`kfilt`, radius 0
  below 8) keeps the diagonals in at least two of their buckets: the pairwise
  intersections of the bench.  Exact (`mem_hitsAtKP3_mz`).
* **The partner by a window scan** (`partnerK`): for each hit `x` of `X`, every start of the
  other mate `Y` that a proper pair with `x` allows (opposite strand, same chromosome, fragment
  in `[lo, hi]`), through the word kernel at `G − pen x`.  Below penalty 8 every hit is
  gapless, so the windows have `Y`'s length.  Exact on that region (`mem_partnerK`).
* **The answer** from the pairs found (`decideP`): the best pair if unique, else a tie.

    pairGF … = some (r, seen) →  r = pairSpecUT … (−P1) (−P2) (any caps ≥ G), when some
    proper pair has pair score ≥ −G; seen ↔ such a pair exists; r = none ∧ seen → pairTie.

The length condition: the enumerated mate has `fastT G` (G = 4: ≥ 50 bp); the partner any length.
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-! ## Part A: the enumerated mate's hits, from `sbound lim + 2` seeds -/

/-- `hitsS` with one more seed looked up. -/
def hitsS3 {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G : ByteArray) (offs : Array Nat)
    (gbs2 : Array ByteArray) (n t lim : Nat) (Rs : ByteArray) : List (Window × Nat) :=
  let m := Rs.size / 25
  let Ls := Rs.size / m
  let ps := prepG ix Rs m Ls
  let J := (ordG (ps.map (LookG.size ix)) m).take (sbound lim + 2)
  let lk := J.map fun j => (j, LookG.look ix G Rs (j * Ls) (Rs.size - j * Ls) ps[j]!)
  let us := unseen m J
  (List.range n).flatMap fun c =>
    hitsC Rs gbs2 (t + c) lim (slicesAt lk Rs.size Ls offs[c]! gbs2[t + c]!.size) us Ls

def hitsAtB3 {L Pp : Type} [LookG L Pp] [Inhabited Pp] (lim : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (gbs : Array ByteArray) (R : ByteArray) : Option (List (Placement × Int)) :=
  if fastT lim R then
    let n := gbs.size
    let gbs2 := gbs ++ gbs
    some ((hitsS3 ix G offs gbs2 n 0 lim R ++ hitsS3 ix G offs gbs2 n n lim (revCompB2 R)).map
      fun x => (decB n x.1, -(x.2 : Int)))
  else none

section strand3
variable (lim : Nat) (read : List Char) (g : Genome) (gbs : Array ByteArray) (hg : GenomeBytes gbs g)
  {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G : ByteArray) (offs : Array Nat)
  (hcat : catOk G offs gbs = true)
  (Rs : ByteArray) (reads : List Char) (hrs : Encodes Rs reads) (t : Nat) (ht : t = 0 ∨ t = gbs.size)
  (hcwc : ∀ c, c < gbs.size → ∀ st len,
    cwB lim read g ⟨t + c, st, len⟩ = cwT lim reads (g ++ g) ⟨t + c, st, len⟩)
  (hm : 0 < Rs.size / 25) (hsb : sbound lim < Rs.size / 25) (hl16 : lim ≤ 16)
  (hlk : ∀ s base, s + q ≤ Rs.size →
    LookOkS G Rs s base 0 (LookG.look ix G Rs s base (LookG.prep ix (seedHashAt Rs s))))

include hg hcat hrs ht hcwc hm hsb hl16 hlk in
set_option maxHeartbeats 1000000 in
theorem hitsS3_mem (w : Window) (k : Nat) :
    (w, k) ∈ hitsS3 ix G offs (gbs ++ gbs) gbs.size t lim Rs ↔
      (∃ c, c < gbs.size ∧ w.chr = t + c) ∧ k ≤ lim ∧ cwB lim read g w = k := by
  have hg2 := genomeBytes_app gbs g hg
  unfold hitsS3
  simp only [List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨c, hc, hmem⟩
    have hc2 : t + c < (gbs ++ gbs).size := by simp; omega
    obtain ⟨h1, h2, h3⟩ := hitsC_sound reads (g ++ g) (gbs ++ gbs) Rs hg2 hrs (t + c) lim hc2 hl16 _ _ _ w k hmem
    refine ⟨⟨c, hc, h1⟩, h2, ?_⟩
    obtain ⟨wc, wst, wlen⟩ := w
    simp only at h1; subst h1
    rw [hcwc c hc]; exact h3
  · rintro ⟨⟨c, hc, hwc⟩, hk, hcw⟩
    have hc2 : t + c < (gbs ++ gbs).size := by simp; omega
    refine ⟨c, hc, ?_⟩
    have hcw' : cwT lim reads (g ++ g) w = k := by
      obtain ⟨wc, wst, wlen⟩ := w
      simp only at hwc; subst hwc
      rw [← hcwc c hc]; exact hcw
    have hgc := gbs2_get gbs t c ht hc
    have hcatc := catOk_spec G offs gbs hcat c hc
    obtain ⟨nd, lt, len⟩ := ordG_spec ((prepG ix Rs (Rs.size / 25) (Rs.size / (Rs.size / 25))).map
      (LookG.size ix)) (Rs.size / 25)
    have hsub := List.take_sublist (sbound lim + 2) (ordG ((prepG ix Rs (Rs.size / 25)
      (Rs.size / (Rs.size / 25))).map (LookG.size ix)) (Rs.size / 25))
    have H := hitsC_complete reads (g ++ g) (gbs ++ gbs) Rs hg2 hrs (t + c) lim hc2 hl16 hm
      (fun j => sliceG (LookG.look ix G Rs (j * (Rs.size / (Rs.size / 25))) (Rs.size - j * (Rs.size / (Rs.size / 25)))
        (prepG ix Rs (Rs.size / 25) (Rs.size / (Rs.size / 25)))[j]!) (Rs.size - j * (Rs.size / (Rs.size / 25)))
        offs[c]! (gbs ++ gbs)[t + c]!.size)
      (fun j hj => by
        rw [prepG_get ix Rs _ _ j hj, hgc]
        exact sliceG_ok G gbs[c]! Rs _ _ _ _ (hlk _ _ (seed_fits Rs.size j hm hj)) hcatc.1 hcatc.2)
      _ (hsub.nodup nd) (fun j hj => lt j (hsub.subset hj)) (by rw [List.length_take, len]; omega)
      w hwc (by omega)
    rw [hcw'] at H
    unfold slicesAt
    rw [List.map_map]
    exact H

end strand3

set_option maxHeartbeats 1000000 in
theorem mem_hitsAtB3 (lim : Nat) (hl16 : lim ≤ 16) (read : List Char) (g : Genome) (gbs : Array ByteArray)
    (R : ByteArray) (hg : GenomeBytes gbs g) (hr : Encodes R read) {L Pp : Type} [LookG L Pp] [Inhabited Pp]
    (ix : L) (G : ByteArray) (offs : Array Nat) (hcat : catOk G offs gbs = true)
    (hlk : ∀ (R' : ByteArray) s base, s + q ≤ R'.size →
      LookOkS G R' s base 0 (LookG.look ix G R' s base (LookG.prep ix (seedHashAt R' s))))
    (l : List (Placement × Int)) (hl : hitsAtB3 lim ix G offs gbs R = some l) (x : Placement × Int) :
    x ∈ l ↔ x ∈ hitsBoth sc0 (-(lim : Int)) g read := by
  unfold hitsAtB3 at hl
  split at hl
  · next hok =>
    unfold fastT at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hm, hsb⟩ := hok
    simp only [Option.some.injEq] at hl
    subst hl
    have hn : gbs.size = g.length := hg.1
    have hrr := revCompB_encodes R read hr
    have hsz := revCompB_size R
    have hcw1 : ∀ c, c < gbs.size → ∀ st len,
        cwB lim read g ⟨0 + c, st, len⟩ = cwT lim read (g ++ g) ⟨0 + c, st, len⟩ := by
      intro c hc st len
      rw [Nat.zero_add, cwT_app_left lim read g _ (by simp only; omega)]
      unfold cwB; rw [if_pos (by simp only; omega)]
    have hcw2 : ∀ c, c < gbs.size → ∀ st len,
        cwB lim read g ⟨gbs.size + c, st, len⟩ = cwT lim (revComp read) (g ++ g) ⟨gbs.size + c, st, len⟩ := by
      intro c hc st len
      rw [hn, cwT_app_right]
      unfold cwB; rw [if_neg (by simp only; omega)]
      simp
    have key : ∀ w k, (w, k) ∈ hitsS3 ix G offs (gbs ++ gbs) gbs.size 0 lim R ++
        hitsS3 ix G offs (gbs ++ gbs) gbs.size gbs.size lim (revCompB2 R) ↔ k ≤ lim ∧ cwB lim read g w = k := by
      intro w k
      rw [List.mem_append, revCompB2_eq,
        hitsS3_mem lim read g gbs hg ix G offs hcat R read hr 0 (Or.inl rfl) hcw1 hm hsb hl16 (hlk R),
        hitsS3_mem lim read g gbs hg ix G offs hcat (revCompB R) (revComp read) hrr gbs.size (Or.inr rfl) hcw2
          (by rw [hsz]; exact hm) (by rw [hsz]; exact hsb) hl16 (hlk _)]
      constructor
      · rintro (⟨-, h⟩ | ⟨-, h⟩) <;> exact h
      · rintro ⟨hk, hcw⟩
        have := cwB_chr_lt lim read g w (by omega)
        by_cases hc : w.chr < gbs.size
        · left; exact ⟨⟨w.chr, hc, by omega⟩, hk, hcw⟩
        · right; exact ⟨⟨w.chr - gbs.size, by omega, by omega⟩, hk, hcw⟩
    obtain ⟨p, s⟩ := x
    rw [List.mem_map, mem_hitsBoth_T]
    have hS : ∀ st w, (strandScore g read st w = some s ∧ -(lim : Int) ≤ s) ↔
        (cwS lim read g st w ≤ lim ∧ s = -(cwS lim read g st w : Int)) := by
      intro st w; cases st
      · exact cwT_iff lim read g w s
      · exact cwT_iff lim (revComp read) g w s
    constructor
    · rintro ⟨⟨w, k⟩, hmem, he⟩
      rw [key] at hmem
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have h3 : cwS lim read g (decB gbs.size w).2 (decB gbs.size w).1 = k := by
        rw [hn, cwS_decB]; exact hmem.2
      have h4 := (hS (decB gbs.size w).2 (decB gbs.size w).1).2 ⟨by omega, by rw [h3]⟩
      exact ⟨strandScore_allWindows g read _ _ _ h4.1, h4.1, h4.2⟩
    · rintro ⟨-, h1, h2⟩
      have h4 := (hS p.2 p.1).1 ⟨h1, h2⟩
      refine ⟨(encB gbs.size p, cwS lim read g p.2 p.1), (key _ _).2 ⟨h4.1, ?_⟩, ?_⟩
      · rw [hn]; exact cwB_encB lim read g p h4.1
      · simp only [Prod.mk.injEq]
        rw [hn, decB_encB g.length p (cwS_chr_lt lim read g p h4.1), h4.2]
        exact ⟨rfl, rfl⟩
  · cases hl

/-- `hitsSK` (packed chromosomes, word filter and kernels) with one more seed. -/
def hitsSK3 {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G : ByteArray) (offs : Array Nat)
    (pgs2 : Array PGen) (n t lim : Nat) (Rs : ByteArray) : List (Window × Nat) :=
  let m := Rs.size / 25
  let Ls := Rs.size / m
  let K := packRP Rs
  let ps := prepG ix Rs m Ls
  let J := (ordG (ps.map (LookG.size ix)) m).take (sbound lim + 2)
  let lk := J.map fun j => (j, LookG.look ix G Rs (j * Ls) (Rs.size - j * Ls) ps[j]!)
  let us := unseen m J
  (List.range n).flatMap fun c =>
    hitsCK K Rs pgs2 (t + c) lim (slicesAt lk Rs.size Ls offs[c]! (GRead.size pgs2[t + c]!)) us Ls

/-- Every placement of a read within `lim ≤ 16`, from `sbound lim + 2` seeds, packed genome. -/
def hitsAtKP3 {L Pp : Type} [LookG L Pp] [Inhabited Pp] (lim : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (pgs : Array PGen) (R : ByteArray) : Option (List (Placement × Int)) :=
  if fastT lim R then
    let n := pgs.size
    let pgs2 := pgs ++ pgs
    some ((hitsSK3 ix G offs pgs2 n 0 lim R ++ hitsSK3 ix G offs pgs2 n n lim (revCompK R)).map
      fun x => (decB n x.1, -(x.2 : Int)))
  else none

theorem hitsSK3_eq {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G : ByteArray) (offs : Array Nat)
    (pgs : Array PGen) (n t lim : Nat) (Rs : ByteArray) :
    hitsSK3 ix G offs (pgs ++ pgs) n t lim Rs = hitsS3 ix G offs (pgs.map Mz.unpack ++ pgs.map Mz.unpack) n t lim Rs := by
  have hs := sameA_append (sameA_unpack pgs) sameG_default
  have hz : ∀ c, GRead.size (pgs ++ pgs)[c]! = ByteArray.size ((pgs.map Mz.unpack ++ pgs.map Mz.unpack)[c]!) :=
    fun c => (hs.2 c).1
  unfold hitsSK3 hitsS3
  simp only [hitsCK_eq, hz]

theorem hitsAtKP3_eq {L Pp : Type} [LookG L Pp] [Inhabited Pp] (lim : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (pgs : Array PGen) (R : ByteArray) :
    hitsAtKP3 lim ix G offs pgs R = hitsAtB3 lim ix G offs (pgs.map Mz.unpack) R := by
  unfold hitsAtKP3 hitsAtB3
  simp only [hitsSK3_eq, revCompK_eq, revCompB2_eq, Array.size_map]

theorem hitsAtB3_congrG {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G G' : ByteArray)
    (hG : ∀ R s base p, LookG.look ix G R s base p = LookG.look ix G' R s base p) (lim : Nat)
    (offs : Array Nat) (gbs : Array ByteArray) (R : ByteArray) :
    hitsAtB3 lim ix G offs gbs R = hitsAtB3 lim ix G' offs gbs R := by
  simp only [hitsAtB3, hitsS3, hG]

/-- **The enumerated mate's hits, packed whole genome.** -/
theorem mem_hitsAtKP3_mz (lim : Nat) (hl16 : lim ≤ 16) (g : Genome) (read : List Char) (ix : Mz.MzIdx)
    (G : PGen) (offs ns : Array Nat) (R : ByteArray) (hcut : cutOk G offs ns = true)
    (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) g) (hr : Encodes R read)
    (hchk : Mz.check2P ix G = true) (l : List (Placement × Int))
    (hl : hitsAtKP3 lim ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) R = some l)
    (x : Placement × Int) : x ∈ l ↔ x ∈ hitsBoth sc0 (-(lim : Int)) g read := by
  rw [hitsAtKP3_eq, hitsAtB3_congrG ((ix, G) : PkMz) ByteArray.empty (Mz.unpack G) (fun _ _ _ _ => rfl)] at hl
  exact mem_hitsAtB3 lim hl16 read g _ R hg hr _ _ offs (catOk_cut G offs ns hcut) (lookOk_pk ix G hchk) l hl x

theorem hitsAtKP3_some {L Pp : Type} [LookG L Pp] [Inhabited Pp] (lim : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (pgs : Array PGen) (R : ByteArray) (h : fastT lim R = true) :
    ∃ l, hitsAtKP3 lim ix G offs pgs R = some l := by
  unfold hitsAtKP3
  rw [if_pos h]
  exact ⟨_, rfl⟩

/-! ## Part B: the partner, by a window scan -/

/-- Positions `a, a + 1, …, a + k − 1` through `f`, the `some`s kept (onto `acc`). -/
def scanW {α : Type} (f : Nat → Option α) : Nat → Nat → List α → List α
  | _, 0, acc => acc
  | a, k + 1, acc => scanW f (a + 1) k (match f a with | some v => v :: acc | none => acc)

theorem mem_scanW {α : Type} (f : Nat → Option α) : ∀ (a k : Nat) (acc : List α) (v : α),
    v ∈ scanW f a k acc ↔ v ∈ acc ∨ ∃ i, a ≤ i ∧ i < a + k ∧ f i = some v
  | a, 0, acc, v => by
    simp only [scanW]
    constructor
    · exact Or.inl
    · rintro (h | ⟨i, h1, h2, -⟩)
      · exact h
      · omega
  | a, k + 1, acc, v => by
    rw [scanW, mem_scanW f (a + 1) k]
    constructor
    · rintro (h | ⟨i, h1, h2, h3⟩)
      · cases hf : f a with
        | none => rw [hf] at h; exact Or.inl h
        | some u =>
          rw [hf] at h
          rcases List.mem_cons.mp h with rfl | h
          · exact Or.inr ⟨a, Nat.le_refl _, by omega, hf⟩
          · exact Or.inl h
      · exact Or.inr ⟨i, by omega, by omega, h3⟩
    · rintro (h | ⟨i, h1, h2, h3⟩)
      · left
        cases f a with
        | none => exact h
        | some u => exact List.mem_cons_of_mem _ h
      · by_cases hi : i = a
        · subst hi; left; rw [h3]; exact List.mem_cons_self
        · right; exact ⟨i, by omega, by omega, h3⟩

/-- The partner's hits within `lim` forming a proper pair with `x`: the windows of the partner's
length at every start a proper pair allows (opposite strand, same chromosome), each through the
word kernel. `RYr`, `KYr`: the reverse complement and the packed reads. -/
def partnerK (pgs2 : Array PGen) (RY RYr : ByteArray) (KY KYr : RP) (sl lo hi lim : Nat)
    (x : Placement) : List (Placement × Int) :=
  let ny := RY.size
  let a := if x.2 = Strand.fwd then x.1.start + lo - ny else x.1.start + x.1.len - hi
  let b := if x.2 = Strand.fwd then x.1.start + hi - ny else x.1.start + x.1.len - lo
  scanW (fun s =>
    let k := if x.2 = Strand.fwd then kerHKG RYr KYr pgs2 pgs2 x.1.chr s ny lim
      else kerHKG RY KY pgs2 pgs2 x.1.chr s ny lim
    let y : Placement := (⟨x.1.chr, s, ny⟩, if x.2 = Strand.fwd then Strand.rev else Strand.fwd)
    if k ≤ lim ∧ properPairU sl lo hi x y = true then some (y, -(k : Int)) else none) a (b + 1 - a) []

/-- Above `−8` a window is gapless: it has the read's length. -/
theorem len_of_score (read : List Char) (g : Genome) (w : Window) (s : Int)
    (hs : windowScore sc0 read g w = some s) (h8 : -8 < s) : w.len = read.length := by
  unfold windowScore at hs
  cases hseq : windowSeq g w with
  | none => rw [hseq] at hs; cases hs
  | some ys =>
    rw [hseq] at hs
    simp only at hs
    cases hbest : getBestAlignment sc0 read ys with
    | none => rw [hbest] at hs; cases hs
    | some best =>
      rw [hbest] at hs
      obtain ⟨path, bs⟩ := best
      have hsb : bs = s := by simpa using hs
      subst hsb
      obtain ⟨hlen, -, -⟩ := best_gapless sc0 valid_sc0 read ys path bs hbest
        (by unfold gapCost1 sc0; simp only; omega)
      unfold windowSeq at hseq
      cases hc : g[w.chr]? with
      | none => rw [hc] at hseq; cases hseq
      | some ch =>
        rw [hc] at hseq
        simp only at hseq
        split at hseq
        · have hys : ys = (ch.seq.drop w.start).take w.len := by simpa using hseq.symm
          rw [hlen, hys, List.length_take, List.length_drop]; omega
        · cases hseq

theorem properPairU_comm (sl lo hi : Nat) (a b : Placement) :
    properPairU sl lo hi a b = properPairU sl lo hi b a := by
  rcases a with ⟨wa, sa⟩
  rcases b with ⟨wb, sb⟩
  cases sa <;> cases sb <;> simp [properPairU, properPair, fwdRev]

/-- A proper partner of `x` lies on the other strand of `x`'s chromosome, at a start of
`partnerK`'s range. -/
theorem properPairU_range (sl lo hi : Nat) (x y : Placement) (h : properPairU sl lo hi x y = true) :
    y.1.chr = x.1.chr ∧ y.2 = (if x.2 = Strand.fwd then Strand.rev else Strand.fwd) ∧
      (if x.2 = Strand.fwd then x.1.start + lo - y.1.len else x.1.start + x.1.len - hi) ≤ y.1.start ∧
      y.1.start ≤ (if x.2 = Strand.fwd then x.1.start + hi - y.1.len else x.1.start + x.1.len - lo) := by
  rcases x with ⟨⟨xc, xs, xl⟩, sx⟩
  rcases y with ⟨⟨yc, ys, yl⟩, sy⟩
  cases sx <;> cases sy <;> simp only [properPairU, properPair, fwdRev, if_true, if_false, reduceCtorEq,
    Bool.and_eq_true, decide_eq_true_eq, and_true, decide_false, Bool.false_and, Bool.and_false,
    Bool.false_eq_true] at h
  all_goals simp only [reduceCtorEq, if_true, if_false, true_and]
  · exact ⟨by omega, by omega, by omega⟩
  · exact ⟨by omega, by omega, by omega⟩

/-- The word kernel on the doubled packed genome is the byte kernel. -/
theorem kerHKG_unpack (R : ByteArray) (pgs : Array PGen) (c st len l : Nat) :
    kerHKG R (packRP R) (pgs ++ pgs) (pgs ++ pgs) c st len l =
      kerH R (pgs.map Mz.unpack ++ pgs.map Mz.unpack) c st len l := by
  have hs := sameA_append (sameA_unpack pgs) sameG_default
  rw [kerHKG_same hs, kerHKG_bytes, kerHK_eq R _ _ (repAllK_unpack pgs)]

/-- The kernel on a chromosome of `g` is the spec's capped penalty. -/
theorem kerHKG_cwT (g : Genome) (pgs : Array PGen) (hg : GenomeBytes (pgs.map Mz.unpack) g)
    (R : ByteArray) (read : List Char) (hr : Encodes R read) (c st len lim : Nat) (hc : c < pgs.size)
    (hl : lim ≤ 16) :
    kerHKG R (packRP R) (pgs ++ pgs) (pgs ++ pgs) c st len lim = min (cwT lim read g ⟨c, st, len⟩) (lim + 1) := by
  have hg2 := genomeBytes_app _ g hg
  have hn : pgs.size = g.length := by have := hg.1; simpa using this
  rw [kerHKG_unpack, ← cwT_kerH lim read (g ++ g) _ R hg2 hr c st len lim (by simp; omega) (Nat.le_refl _) hl,
    cwT_app_left lim read g _ (by simp only; omega)]

section partner
variable (g : Genome) (pgs : Array PGen) (hg : GenomeBytes (pgs.map Mz.unpack) g)
  (RY : ByteArray) (rY : List Char) (hr : Encodes RY rY) (sl lo hi lim : Nat) (hl : lim ≤ 7)

include hg hr hl in
/-- **The partner scan is exact**: the partner's hits within `lim < 8` that form a proper pair with `x`. -/
theorem mem_partnerK (x : Placement) (hx : x.1.chr < g.length) (y : Placement × Int) :
    y ∈ partnerK (pgs ++ pgs) RY (revCompK RY) (packRP RY) (packRP (revCompK RY)) sl lo hi lim x ↔
      y ∈ hitsBoth sc0 (-(lim : Int)) g rY ∧ properPairU sl lo hi x y.1 = true := by
  have hn : pgs.size = g.length := by have := hg.1; simpa using this
  have hrr : Encodes (revCompK RY) (revComp rY) := by rw [revCompK_eq]; exact revCompB_encodes RY rY hr
  have hny : RY.size = rY.length := hr.1
  have hlr : (revComp rY).length = rY.length := by simp [revComp]
  -- the kernel at a start, as the spec's penalty of the placement
  have hk : ∀ s, (if x.2 = Strand.fwd then kerHKG (revCompK RY) (packRP (revCompK RY)) (pgs ++ pgs) (pgs ++ pgs) x.1.chr s RY.size lim
      else kerHKG RY (packRP RY) (pgs ++ pgs) (pgs ++ pgs) x.1.chr s RY.size lim) =
      min (cwS lim rY g (if x.2 = Strand.fwd then Strand.rev else Strand.fwd) ⟨x.1.chr, s, RY.size⟩) (lim + 1) := by
    intro s
    split
    · rw [kerHKG_cwT g pgs hg _ _ hrr _ _ _ _ (by omega) (by omega)]; rfl
    · rw [kerHKG_cwT g pgs hg _ _ hr _ _ _ _ (by omega) (by omega)]; rfl
  have hS : ∀ st w s, (strandScore g rY st w = some s ∧ -(lim : Int) ≤ s) ↔
      (cwS lim rY g st w ≤ lim ∧ s = -(cwS lim rY g st w : Int)) := by
    intro st w s; cases st
    · exact cwT_iff lim rY g w s
    · exact cwT_iff lim (revComp rY) g w s
  unfold partnerK
  rw [mem_scanW]
  simp only [List.not_mem_nil, false_or]
  obtain ⟨p, sc⟩ := y
  constructor
  · rintro ⟨i, -, -, hfi⟩
    rw [hk] at hfi
    generalize hst : (if x.2 = Strand.fwd then Strand.rev else Strand.fwd) = st at hfi
    by_cases hc : min (cwS lim rY g st ⟨x.1.chr, i, RY.size⟩) (lim + 1) ≤ lim ∧
        properPairU sl lo hi x (⟨x.1.chr, i, RY.size⟩, st) = true
    · rw [if_pos hc] at hfi
      simp only [Option.some.injEq, Prod.mk.injEq] at hfi
      obtain ⟨rfl, rfl⟩ := hfi
      have hle : cwS lim rY g st ⟨x.1.chr, i, RY.size⟩ ≤ lim := by have := hc.1; omega
      rw [Nat.min_eq_left (by omega)]
      refine ⟨?_, hc.2⟩
      have h4 := (hS _ _ _).2 ⟨hle, rfl⟩
      rw [mem_hitsBoth_T]
      exact ⟨strandScore_allWindows g rY _ _ _ h4.1, h4.1, h4.2⟩
    · rw [if_neg hc] at hfi; cases hfi
  · rintro ⟨hm, hpp⟩
    rw [mem_hitsBoth_T] at hm
    obtain ⟨-, hss, hsl⟩ := hm
    obtain ⟨hcw, hsc⟩ := (hS _ _ _).1 ⟨hss, hsl⟩
    obtain ⟨hch, hst, hlo, hhi⟩ := properPairU_range sl lo hi x p hpp
    -- the partner is gapless: the partner's length
    have hlen : p.1.len = RY.size := by
      rw [hny]
      have h8 : -8 < sc := by omega
      rcases p with ⟨w, st⟩
      cases st
      · exact len_of_score rY g w sc hss h8
      · rw [← hlr]; exact len_of_score (revComp rY) g w sc hss h8
    rcases p with ⟨⟨pc, ps, pl⟩, pst⟩
    simp only at hch hst hlen hlo hhi hcw hsc hpp
    subst hch hst hlen hsc
    refine ⟨ps, hlo, by omega, ?_⟩
    rw [hk, Nat.min_eq_left (Nat.le_succ_of_le hcw), if_pos ⟨hcw, hpp⟩]

end partner

/-! ## Part C: the pairs and the answer -/

/-- The pairs: each hit `x` of the enumerated mate with its partners within `Gc − pen x`, kept at
pair score `≥ −Gc`; `swap`: the enumerated mate is mate 2. -/
def pairsGF (dc : Nat → Nat) (sl lo hi Gc : Nat) (pgs2 : Array PGen) (RY RYr : ByteArray) (KY KYr : RP)
    (swap : Bool) (lX : List (Placement × Int)) : List PairHit :=
  lX.flatMap fun x =>
    (partnerK pgs2 RY RYr KY KYr sl lo hi (Gc - (-x.2).toNat) x.1).filterMap fun y =>
      let p : PairHit := if swap then (y, x) else (x, y)
      if -(Gc : Int) ≤ pairScoreD dc p then some p else none

theorem hitsBoth_chr {T : Int} {g : Genome} {r : List Char} {x : Placement × Int}
    (hx : x ∈ hitsBoth sc0 T g r) : x.1.1.chr < g.length := by
  obtain ⟨p, s⟩ := x
  rw [mem_hitsBoth_T] at hx
  obtain ⟨hw, -, -⟩ := hx
  show p.1.chr < g.length
  rw [mem_allWindows] at hw
  unfold windowSeq at hw
  apply Classical.byContradiction
  intro hc
  rw [List.getElem?_eq_none (by omega)] at hw
  cases hw

section pairs
variable (g : Genome) (pgs : Array PGen) (hg : GenomeBytes (pgs.map Mz.unpack) g)
  (dc : Nat → Nat) (sl lo hi Gc : Nat) (hG : Gc ≤ 7) (m1 m2 : List Char) (swap : Bool)
  (RY : ByteArray) (hr : Encodes RY (if swap then m1 else m2))
  (lX : List (Placement × Int)) (hX : ∀ x, x ∈ lX ↔ x ∈ hitsBoth sc0 (-(Gc : Int)) g (if swap then m2 else m1))
  (P1 P2 : Nat) (hP1 : Gc ≤ P1) (hP2 : Gc ≤ P2)

include hg hG hr hX hP1 hP2 in
/-- **The pairs found are exactly the proper pairs at pair score `≥ −Gc`** (any caps `≥ Gc`). -/
theorem mem_pairsGF (p : PairHit) :
    p ∈ pairsGF dc sl lo hi Gc (pgs ++ pgs) RY (revCompK RY) (packRP RY) (packRP (revCompK RY)) swap lX ↔
      p ∈ properPairs sl lo hi (hitsBoth sc0 (-(P1 : Int)) g m1) (hitsBoth sc0 (-(P2 : Int)) g m2) ∧
        -(Gc : Int) ≤ pairScoreD dc p := by
  have hd : ∀ f : Nat, (0 : Int) ≤ (dc f : Int) := fun f => Int.natCast_nonneg _
  -- the partner of `x` within `Gc − pen x`, at any cap of the partner's mate; `S`: the pair-score test
  have key : ∀ (mX mY : List Char) (PX PY : Nat), Gc ≤ PX → Gc ≤ PY → Encodes RY mY →
      (∀ x, x ∈ lX ↔ x ∈ hitsBoth sc0 (-(Gc : Int)) g mX) →
      ∀ (S : Prop) (x y : Placement × Int), (S → -(Gc : Int) ≤ x.2 + y.2) →
      ((x ∈ lX ∧ y ∈ partnerK (pgs ++ pgs) RY (revCompK RY) (packRP RY) (packRP (revCompK RY)) sl lo hi
          (Gc - (-x.2).toNat) x.1 ∧ S) ↔
        (x ∈ hitsBoth sc0 (-(PX : Int)) g mX ∧ y ∈ hitsBoth sc0 (-(PY : Int)) g mY ∧
          properPairU sl lo hi x.1 y.1 = true ∧ S)) := by
    intro mX mY PX PY hPX hPY hrY hXX S x y hSS
    constructor
    · rintro ⟨hx, hy, hs⟩
      have hx' := (hXX x).1 hx
      rw [mem_partnerK g pgs hg RY mY hrY sl lo hi _ (by omega) x.1 (hitsBoth_chr hx')] at hy
      exact ⟨hitsBoth_mono (by omega) hx', hitsBoth_mono (by omega) hy.1, hy.2, hs⟩
    · rintro ⟨hx, hy, hpp, hs⟩
      have nx := hitsBoth_nonpos _ _ _ x hx
      have ny := hitsBoth_nonpos _ _ _ y hy
      have hxy := hSS hs
      have hx' : x ∈ hitsBoth sc0 (-(Gc : Int)) g mX := hitsBoth_lower hx (by omega) (by omega)
      refine ⟨(hXX x).2 hx', ?_, hs⟩
      rw [mem_partnerK g pgs hg RY mY hrY sl lo hi _ (by omega) x.1 (hitsBoth_chr hx')]
      exact ⟨hitsBoth_lower hy (by omega) (by omega), hpp⟩
  unfold pairsGF
  rw [List.mem_flatMap, mem_properPairs]
  simp only [List.mem_filterMap]
  obtain ⟨a, b⟩ := p
  cases swap
  · simp only [Bool.false_eq_true, if_false] at hr hX ⊢
    have K := key m1 m2 P1 P2 hP1 hP2 hr hX
    constructor
    · rintro ⟨x, hx, y, hy, he⟩
      split at he
      · next hs =>
        simp only [Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        have hS : -(Gc : Int) ≤ pairScoreD dc (x, y) → -(Gc : Int) ≤ x.2 + y.2 := by
          have := hd (fragLen x.1 y.1); unfold pairScoreD; simp only; omega
        obtain ⟨h1, h2, h3, h4⟩ := (K _ x y hS).1 ⟨hx, hy, hs⟩
        exact ⟨⟨h1, h2, h3⟩, h4⟩
      · cases he
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      have hS : -(Gc : Int) ≤ pairScoreD dc (a, b) → -(Gc : Int) ≤ a.2 + b.2 := by
        have := hd (fragLen a.1 b.1); unfold pairScoreD; simp only; omega
      obtain ⟨hx, hy, hs⟩ := (K _ a b hS).2 ⟨h1, h2, h3, h4⟩
      exact ⟨a, hx, b, hy, by rw [if_pos hs]⟩
  · simp only [if_true] at hr hX ⊢
    have K := key m2 m1 P2 P1 hP2 hP1 hr hX
    constructor
    · rintro ⟨x, hx, y, hy, he⟩
      split at he
      · next hs =>
        simp only [Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        have hS : -(Gc : Int) ≤ pairScoreD dc (y, x) → -(Gc : Int) ≤ x.2 + y.2 := by
          have := hd (fragLen y.1 x.1); unfold pairScoreD; simp only; omega
        obtain ⟨h1, h2, h3, h4⟩ := (K _ x y hS).1 ⟨hx, hy, hs⟩
        exact ⟨⟨h2, h1, by rw [properPairU_comm]; exact h3⟩, h4⟩
      · cases he
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      have hS : -(Gc : Int) ≤ pairScoreD dc (a, b) → -(Gc : Int) ≤ b.2 + a.2 := by
        have := hd (fragLen a.1 b.1); unfold pairScoreD; simp only; omega
      obtain ⟨hx, hy, hs⟩ := (K _ b a hS).2 ⟨h2, h1, by rw [properPairU_comm]; exact h3, h4⟩
      exact ⟨b, hx, a, hy, by rw [if_pos hs]⟩

end pairs

/-- **The answer from the pairs above a bound**: when the pairs at score `≥ W` are listed (some
exist), their unique best is `bestPairD`'s. -/
theorem bestOfPairs_restrict (dc : Nat → Nat) (sl lo hi : Nat) (h1 h2 : List (Placement × Int))
    (f1 : ScoreFun h1) (f2 : ScoreFun h2) (W : Int) (ps : List PairHit)
    (hps : ∀ p, p ∈ ps ↔ p ∈ properPairs sl lo hi h1 h2 ∧ W ≤ pairScoreD dc p) (hne : ps ≠ []) :
    bestOfPairs dc ps = bestPairD dc sl lo hi h1 h2 := by
  have hfun : ∀ x ∈ properPairs sl lo hi h1 h2, ∀ y ∈ properPairs sl lo hi h1 h2,
      (x.1.1 = y.1.1 ∧ x.2.1 = y.2.1) → x = y := by
    rintro ⟨⟨a, sa⟩, ⟨b, sb⟩⟩ hx ⟨⟨a', sa'⟩, ⟨b', sb'⟩⟩ hy ⟨e1, e2⟩
    simp only at e1 e2
    subst e1 e2
    rw [mem_properPairs] at hx hy
    have ea : sa = sa' := f1 _ hx.1 _ hy.1 rfl
    have eb : sb = sb' := f2 _ hx.2.1 _ hy.2.1 rfl
    rw [ea, eb]
  have hA := fun q => Fast.findU_iff (pairScoreD dc) (fun p' p => decide (p'.1.1 = p.1.1 ∧ p'.2.1 = p.2.1)) ps
    (fun x hx y hy he => hfun x ((hps x).1 hx).1 y ((hps y).1 hy).1 (by simpa using he)) q
  simp only [decide_eq_true_eq] at hA
  rw [bestOfPairs_eq]
  apply Option.ext
  intro q
  rw [hA, bestPairD_iff dc sl lo hi h1 h2 f1 f2]
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil ps hne
  constructor
  · rintro ⟨hq, hall⟩
    obtain ⟨hqp, hqs⟩ := (hps q).1 hq
    refine ⟨hqp, fun x hx => ?_⟩
    by_cases hxs : W ≤ pairScoreD dc x
    · exact hall x ((hps x).2 ⟨hx, hxs⟩)
    · exact Or.inl (by omega)
  · rintro ⟨hq, hall⟩
    obtain ⟨hwp, hws⟩ := (hps w).1 hw
    have hqs : W ≤ pairScoreD dc q := by
      rcases hall w hwp with h | h
      · omega
      · rw [← hfun w hwp q hq h]; exact hws
    exact ⟨(hps q).2 ⟨hq, hqs⟩, fun x hx => hall x ((hps x).1 hx).1⟩

/-! ## Part D: the kernel and its theorem -/

/-- **The fast pair-level guarantee at `Gc`**: the enumerated mate's hits within `Gc` (`swap`: mate 2),
each hit's partners by the window scan, the pairs at pair score `≥ −Gc`, their unique best.
Answer: `(best, a pair seen, the enumerated mate's hits)`; `none` when the enumerated mate is too
short (`fastT Gc`). -/
def pairGF (dc : Nat → Nat) (sl lo hi Gc : Nat) (swap : Bool) (ix : PkMz) (offs : Array Nat)
    (pgs : Array PGen) (R1 R2 : ByteArray) : Option (Option PairHit × Bool × List (Placement × Int)) :=
  match hitsAtKP3 Gc ix ByteArray.empty offs pgs (if swap then R2 else R1) with
  | none => none
  | some lX =>
    let RY := if swap then R1 else R2
    let RYr := revCompK RY
    let ps := pairsGF dc sl lo hi Gc (pgs ++ pgs) RY RYr (packRP RY) (packRP RYr) swap lX
    some (bestOfPairs dc ps, !ps.isEmpty, lX)

theorem pairGF_some (dc : Nat → Nat) (sl lo hi Gc : Nat) (swap : Bool) (ix : PkMz) (offs : Array Nat)
    (pgs : Array PGen) (R1 R2 : ByteArray) (h : fastT Gc (if swap then R2 else R1) = true) :
    ∃ v, pairGF dc sl lo hi Gc swap ix offs pgs R1 R2 = some v := by
  obtain ⟨l, hl⟩ := hitsAtKP3_some Gc ix ByteArray.empty offs pgs _ h
  unfold pairGF
  simp only [hl]
  exact ⟨_, rfl⟩

section top
variable (dc : Nat → Nat) (sl lo hi Gc : Nat) (g : Genome) (m1 m2 : List Char) (ix : Mz.MzIdx) (G : PGen)
  (offs ns : Array Nat) (R1 R2 : ByteArray)
  (hcut : cutOk G offs ns = true) (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) g)
  (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hchk : Mz.check2P ix G = true)

include hcut hg h1 h2 hchk in
/-- **The fast guarantee is the specification.**  At any caps `P1, P2 ≥ Gc` (`Gc ≤ 7`):
the enumerated mate's hits are exactly its hits within `Gc`; a pair is seen iff some proper pair
has pair score `≥ −Gc`; then the answer is `pairSpecUT`, and `none` is a pair-level tie. -/
theorem pairGF_sound (hG : Gc ≤ 7) (swap : Bool) (P1 P2 : Nat) (hP1 : Gc ≤ P1) (hP2 : Gc ≤ P2)
    (r : Option PairHit) (seen : Bool) (lX : List (Placement × Int))
    (h : pairGF dc sl lo hi Gc swap ((ix, G) : PkMz) offs (cutAll G offs ns) R1 R2 = some (r, seen, lX)) :
    (∀ x, x ∈ lX ↔ x ∈ hitsBoth sc0 (-(Gc : Int)) g (if swap then m2 else m1)) ∧
    (seen = true ↔ ∃ w ∈ properPairs sl lo hi (hitsBoth sc0 (-(P1 : Int)) g m1) (hitsBoth sc0 (-(P2 : Int)) g m2),
      -(Gc : Int) ≤ pairScoreD dc w) ∧
    (seen = true → r = pairSpecUT sc0 dc sl lo hi (-(P1 : Int)) (-(P2 : Int)) g m1 m2) ∧
    (seen = true → r = none → PairTieOk dc sl lo hi (-(P1 : Int)) (-(P2 : Int)) g m1 m2) := by
  cases hl : hitsAtKP3 Gc ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) (if swap then R2 else R1) with
  | none => simp only [pairGF, hl, reduceCtorEq] at h
  | some lX' =>
    simp only [pairGF, hl, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hrX : Encodes (if swap then R2 else R1) (if swap then m2 else m1) := by cases swap <;> simpa
    have hrY : Encodes (if swap then R1 else R2) (if swap then m1 else m2) := by cases swap <;> simpa
    have hX := mem_hitsAtKP3_mz Gc (by omega) g _ ix G offs ns _ hcut hg hrX hchk lX' hl
    have HP := mem_pairsGF g (cutAll G offs ns) hg dc sl lo hi Gc hG m1 m2 swap _ hrY lX' hX P1 P2 hP1 hP2
    have hseen : (!(pairsGF dc sl lo hi Gc (cutAll G offs ns ++ cutAll G offs ns) (if swap then R1 else R2)
        (revCompK (if swap then R1 else R2)) (packRP (if swap then R1 else R2))
        (packRP (revCompK (if swap then R1 else R2))) swap lX').isEmpty) = true ↔
        ∃ w ∈ properPairs sl lo hi (hitsBoth sc0 (-(P1 : Int)) g m1) (hitsBoth sc0 (-(P2 : Int)) g m2),
          -(Gc : Int) ≤ pairScoreD dc w := by
      rw [Bool.not_eq_true', List.isEmpty_eq_false_iff_exists_mem]
      constructor
      · rintro ⟨w, hw⟩; exact ⟨w, ((HP w).1 hw).1, ((HP w).1 hw).2⟩
      · rintro ⟨w, hw, hs⟩; exact ⟨w, (HP w).2 ⟨hw, hs⟩⟩
    have hbest : (!(pairsGF dc sl lo hi Gc (cutAll G offs ns ++ cutAll G offs ns) (if swap then R1 else R2)
        (revCompK (if swap then R1 else R2)) (packRP (if swap then R1 else R2))
        (packRP (revCompK (if swap then R1 else R2))) swap lX').isEmpty) = true →
        bestOfPairs dc (pairsGF dc sl lo hi Gc (cutAll G offs ns ++ cutAll G offs ns) (if swap then R1 else R2)
          (revCompK (if swap then R1 else R2)) (packRP (if swap then R1 else R2))
          (packRP (revCompK (if swap then R1 else R2))) swap lX') =
          pairSpecUT sc0 dc sl lo hi (-(P1 : Int)) (-(P2 : Int)) g m1 m2 := by
      intro hs
      rw [Bool.not_eq_true', List.isEmpty_eq_false_iff_exists_mem] at hs
      obtain ⟨w, hw⟩ := hs
      exact bestOfPairs_restrict dc sl lo hi _ _ (hitsBoth_scoreFun _ _ _ _) (hitsBoth_scoreFun _ _ _ _) _ _ HP
        (List.ne_nil_of_mem hw)
    refine ⟨hX, hseen, hbest, fun hs hn => ⟨?_, ?_⟩⟩
    · rw [← hbest hs]; exact hn
    · obtain ⟨w, hw, -⟩ := hseen.1 hs; exact ⟨w, hw⟩

end top

end MapSpec.Fast

#print axioms MapSpec.Fast.pairGF_sound
