import PairGuarFast
import MapperK250Loops
import MapperK250Words

/-!
# The fast pair-level guarantee at `pairGX`'s speed (`pairGQ`), proved

`pairGF` (codecs/PairGuarFast.lean) with three changes, each proved to keep its answer:

* **Raw bucket lookups** (`rawLookP`): the enumerated mate's seed places are the bucket slots
  whose key and stored context match (`Mz.okAt` without the genome letters it reads), a superset
  of the exact places (`rawScan_sup`), kept when increasing (else the exact lookup).  The hit
  enumeration only needs a sorted superset (`hitsC_complete`); every candidate goes through the kernel.
* **A word reject in the partner scan** (`rejW`): a start whose first 32 letters already differ
  from the partner in more than `lim / 4` places is skipped (there the kernel answers `lim + 1`:
  `rejW_ker`), so the scan lists the same partners (`pscanQ_eq`).
* **An early stop** (`goP`): the enumerated mate's perfect hits first; the pairs are folded into
  (best, tie) and the scan stops once no remaining pair can change the answer: the best beats the
  bound on the remaining pairs, or ties at it (`goP_spec`, `ansOk`).

    pairGQ … = some (r, seen, lX) → the same four conclusions as `pairGF_sound`   (pairGQ_sound)
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec MapSpec.Packed

/-! ## Part A: raw bucket lookups -/

/-- Entry `t` passes the key and the stored context of the seed (`Mz.okAt` without the letters). -/
@[inline] def rawOk (ix : Mz.MzIdx) (o key bw aw pmo o2 t : Nat) : Bool :=
  let e := ix.slot t
  (e &&& ix.kbM) == key &&
    (let pos := ix.posOf e
     let tg := ix.tagOf e
     decide (o ≤ pos) && (ix.flagF tg != 0 || ((ix.befF tg &&& pmo) == bw && (ix.aftF tg >>> o2) == aw)))

/-- Anchors of the entries `[t, hi)` passing `rawOk`. -/
def rawScan (ix : Mz.MzIdx) (o key bw aw pmo o2 hi base : Nat) (t : Nat) (acc : Array Nat) : Array Nat :=
  if t < hi then
    rawScan ix o key bw aw pmo o2 hi base (t + 1)
      (if rawOk ix o key bw aw pmo o2 t then acc.push (anc base 0 (ix.posOf (ix.slot t) - o)) else acc)
  else acc
termination_by hi - t

/-- A seed's anchors: the raw bucket scan when increasing, else the exact lookup. -/
def rawLookP (ix : Mz.MzIdx) (G : PGen) (R : ByteArray) (s base : Nat) (p : MzP) : Array Nat :=
  if p.ok then
    let o := p.o
    let v := p.v
    let m1 := min o ix.c
    let m2 := min (ix.w - 1 - o) ix.c
    let a := rawScan ix o (p.h &&& ix.kbM) ((v >>> (2 * (Mz.q - o))) &&& ix.pm[m1]!)
      ((v >>> (2 * (Mz.q - o - ix.k - m2))) &&& ix.pm[m2]!) ix.pm[m1]! (2 * (ix.c - m2))
      (ix.hiB p.b) base (ix.loB p.b) #[]
    if incA a a.size 0 then a else mzLookSP ix G R s base p
  else mzLookSP ix G R s base p

/-- A minimizer index and its packed genome, looked up raw. -/
def PkMzR := Mz.MzIdx × PGen

/-- The index `ix` of the packed genome `G`, looked up raw. -/
def PkMzR.mk (ix : Mz.MzIdx) (G : PGen) : PkMzR := (ix, G)

instance : LookG PkMzR MzP :=
  ⟨fun ix => mzPrep ix.1, fun ix => mzSize ix.1, fun ix _ R s base p => rawLookP ix.1 ix.2 R s base p⟩

/-! ## Part B: the partner scan with a word reject -/

/-- The first 32 letters of the partner at `st` differ in more than `lim / 4` places (by words, where
their genome blocks are flagged). -/
@[inline] def rejW (R : ByteArray) (K : RP) (P : PGen) (st lim : Nat) : Bool :=
  let A := P.o + st
  K.ok && decide (32 ≤ R.size) && decide (st + 32 ≤ P.n) && P.w.get! (17 * (A / 64)) == 1 &&
    P.w.get! (17 * ((A + 31) / 64)) == 1 &&
    decide (lim / 4 < cnt64 (fold (K.w[0]! ^^^ comb (gword P.w (A / 32)) (gword P.w (A / 32 + 1)) (A % 32)
      (2 * (A % 32)).toUInt64 (64 - 2 * (A % 32)).toUInt64)))

/-- `partnerK` with the word reject before the kernel. -/
def pscanQ (pgs2 : Array PGen) (RY RYr : ByteArray) (KY KYr : RP) (sl lo hi lim : Nat)
    (x : Placement) : List (Placement × Int) :=
  let ny := RY.size
  let fw := decide (x.2 = Strand.fwd)
  let a := if fw then x.1.start + lo - ny else x.1.start + x.1.len - hi
  let b := if fw then x.1.start + hi - ny else x.1.start + x.1.len - lo
  let P := pgs2[x.1.chr]!
  scanW (fun s =>
    if (if fw then rejW RYr KYr P s lim else rejW RY KY P s lim) then none else
    let k := if x.2 = Strand.fwd then kerHKG RYr KYr pgs2 pgs2 x.1.chr s ny lim
      else kerHKG RY KY pgs2 pgs2 x.1.chr s ny lim
    let y : Placement := (⟨x.1.chr, s, ny⟩, if x.2 = Strand.fwd then Strand.rev else Strand.fwd)
    if k ≤ lim ∧ properPairU sl lo hi x y = true then some (y, -(k : Int)) else none) a (b + 1 - a) []

/-! ## Part C: the early stop -/

/-- Same placements. -/
@[inline] def samePlP (p q : PairHit) : Bool := decide (p.1.1 = q.1.1 ∧ p.2.1 = q.2.1)

/-- One pair into (best, tie at the best with another placement). -/
@[inline] def stepP (dc : Nat → Nat) (s : Option PairHit × Bool) (p : PairHit) : Option PairHit × Bool :=
  match s.1 with
  | none => (some p, false)
  | some b =>
    if pairScoreD dc b < pairScoreD dc p then (some p, false)
    else if pairScoreD dc p = pairScoreD dc b ∧ samePlP p b = false then (some b, true)
    else s

/-- Nothing at most `U` can change the answer any more. -/
@[inline] def stopP (dc : Nat → Nat) (U : Int) (s : Option PairHit × Bool) : Bool :=
  match s.1 with
  | none => false
  | some b => decide (U < pairScoreD dc b) || (s.2 && decide (U ≤ pairScoreD dc b))

/-- Hits `xs` in order, each one's pairs `f x` folded in, until `stopP U`. -/
def goP (dc : Nat → Nat) (f : Placement × Int → List PairHit) (U : Int) :
    List (Placement × Int) → Option PairHit × Bool → Option PairHit × Bool
  | [], s => s
  | x :: xs, s => if stopP dc U s then s else goP dc f U xs ((f x).foldl (stepP dc) s)

/-- The fold's invariant over the pairs `D` folded so far: `best` is a best of `D` (none iff `D` is
empty), `tie` iff another placement of `D` has the best's score. -/
def InvQ (dc : Nat → Nat) (D : List PairHit) (s : Option PairHit × Bool) : Prop :=
  (s.1 = none → D = []) ∧
    ∀ b, s.1 = some b → b ∈ D ∧ (∀ q ∈ D, pairScoreD dc q ≤ pairScoreD dc b) ∧
      (s.2 = true ↔ ∃ q ∈ D, pairScoreD dc q = pairScoreD dc b ∧ samePlP q b = false)

/-! ## Part D: the kernel -/

/-- The pairs of one hit `x` of the enumerated mate (partners within `Gc − pen x`, pair score `≥ −Gc`). -/
def pairsQ (dc : Nat → Nat) (sl lo hi Gc : Nat) (pgs2 : Array PGen) (RY RYr : ByteArray) (KY KYr : RP)
    (swap : Bool) (x : Placement × Int) : List PairHit :=
  (pscanQ pgs2 RY RYr KY KYr sl lo hi (Gc - (-x.2).toNat) x.1).filterMap fun y =>
    let p : PairHit := if swap then (y, x) else (x, y)
    if -(Gc : Int) ≤ pairScoreD dc p then some p else none

/-- **The fast pair-level guarantee at `Gc`, early stop**: the enumerated mate's hits within `Gc`
(raw lookups), the perfect ones' pairs first, then the others' (bound: their best score), stopping
when the answer is settled.  Answer as `pairGF`'s. -/
def pairGQ (dc : Nat → Nat) (sl lo hi Gc : Nat) (swap : Bool) (ix : PkMzR) (offs : Array Nat)
    (pgs : Array PGen) (R1 R2 : ByteArray) : Option (Option PairHit × Bool × List (Placement × Int)) :=
  match hitsAtKP3 Gc ix ByteArray.empty offs pgs (if swap then R2 else R1) with
  | none => none
  | some lX =>
    let RY := if swap then R1 else R2
    let RYr := revCompK RY
    let f := pairsQ dc sl lo hi Gc (pgs ++ pgs) RY RYr (packRP RY) (packRP RYr) swap
    let l0 := lX.filter fun x => decide (x.2 = 0)
    let l1 := lX.filter fun x => !decide (x.2 = 0)
    let U1 := l1.foldl (fun m x => max m x.2) (-(Gc : Int))
    let s := goP dc f U1 l1 (goP dc f 0 l0 (none, false))
    some (if s.2 then none else s.1, s.1.isSome, lX)

/-! ## Proofs, part A: the raw lookups are sorted supersets -/

/-- A sorted superset of a seed's places (what the hit enumeration needs). -/
def LookSupS (G R : ByteArray) (s base : Nat) (a : Array Nat) : Prop :=
  a.toList.Pairwise (· < ·) ∧ ∀ p, MatchAt G p R s → (p + base) * 16 + 0 ∈ a.toList

theorem rawOk_of_okAt (ix : Mz.MzIdx) (G R : ByteArray) (s o key bw aw pmo o2 n1 a2 n2 t : Nat)
    (h : Mz.okAt ix G R s o key bw aw pmo o2 n1 a2 n2 t = true) : rawOk ix o key bw aw pmo o2 t = true := by
  unfold Mz.okAt at h
  unfold rawOk
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq]
  refine ⟨h1, h2, ?_⟩
  split at h3
  · next hf =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h3
    exact Or.inr ⟨h3.1.1.1.1.1, h3.1.1.1.1.2⟩
  · next hf => exact Or.inl hf

theorem scanA_sub (ix : Mz.MzIdx) (G R : ByteArray) (s o key bw aw pmo o2 n1 a2 n2 hi base : Nat) :
    ∀ d t (acc acc' : Array Nat), hi - t = d → (∀ x ∈ acc.toList, x ∈ acc'.toList) →
      ∀ x ∈ (scanA ix G R s o key bw aw pmo o2 n1 a2 n2 hi base 0 t acc).toList,
        x ∈ (rawScan ix o key bw aw pmo o2 hi base t acc').toList := by
  intro d
  induction d with
  | zero =>
    intro t acc acc' h hs
    have hlt : ¬ t < hi := by omega
    unfold scanA rawScan
    simp only [hlt, if_false]
    exact hs
  | succ d ih =>
    intro t acc acc' h hs
    have hlt : t < hi := by omega
    unfold scanA rawScan
    simp only [hlt, if_true]
    apply ih _ _ _ (by omega)
    intro x hx
    by_cases ho : Mz.okAt ix G R s o key bw aw pmo o2 n1 a2 n2 t = true
    · rw [if_pos ho] at hx
      rw [if_pos (rawOk_of_okAt ix G R s o key bw aw pmo o2 n1 a2 n2 t ho)]
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (hs x hx)
      · exact Or.inr hx
    · rw [if_neg ho] at hx
      have := hs x hx
      split
      · simp only [Array.toList_push, List.mem_append]; exact Or.inl this
      · exact this

/-- **The raw lookup is a sorted superset of the exact one.** -/
theorem rawLookP_sup (ix : Mz.MzIdx) (G : PGen) (R : ByteArray) (s base : Nat) (p : MzP)
    (hE : LookOkS (Mz.unpack G) R s base 0 (mzLookSP ix G R s base p)) :
    LookSupS (Mz.unpack G) R s base (rawLookP ix G R s base p) := by
  have hE' : LookSupS (Mz.unpack G) R s base (mzLookSP ix G R s base p) :=
    ⟨hE.1, fun q hq => (hE.2 _).2 ⟨q, hq, rfl⟩⟩
  unfold rawLookP
  split
  · next hok =>
    simp only []
    split
    · next hinc =>
      refine ⟨incA_pw _ hinc, fun q hq => ?_⟩
      have hm := hE'.2 q hq
      rw [mzLookSP_eq (Mz.rep_unpack G)] at hm
      unfold mzLookS lookupP at hm
      rw [if_pos hok] at hm
      exact scanA_sub ix _ R s _ _ _ _ _ _ _ _ _ _ base _ _ #[] #[] rfl (by simp) _ hm
    · exact hE'
  · exact hE'

/-- Raw lookups through `PkMzR`, at a seed's own prepared values. -/
theorem lookSup_pkR (ix : Mz.MzIdx) (G : PGen) (hchk : Mz.check2P ix G = true) :
    ∀ (R' : ByteArray) s base, s + q ≤ R'.size →
      LookSupS (Mz.unpack G) R' s base
        (LookG.look (PkMzR.mk ix G) (Mz.unpack G) R' s base (LookG.prep (PkMzR.mk ix G) (seedHashAt R' s))) := by
  intro R' s base hs
  exact rawLookP_sup ix G R' s base _ (lookOk_pk ix G hchk R' s base hs)

/-- `sliceG_ok` for a sorted superset. -/
theorem sliceG_sup (G Gc R : ByteArray) (s base o : Nat) (a : Array Nat) (hl : LookSupS G R s base a)
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
    refine ⟨(o + p + base) * 16 + 0, (mem _).mpr ⟨hl.2 _ hm, ?_, ?_⟩, by omega⟩
    · omega
    · have := hp.1; have hq : q = 25 := rfl; omega

section strand3S
variable (lim : Nat) (read : List Char) (g : Genome) (gbs : Array ByteArray) (hg : GenomeBytes gbs g)
  {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G : ByteArray) (offs : Array Nat)
  (hcat : catOk G offs gbs = true)
  (Rs : ByteArray) (reads : List Char) (hrs : Encodes Rs reads) (t : Nat) (ht : t = 0 ∨ t = gbs.size)
  (hcwc : ∀ c, c < gbs.size → ∀ st len,
    cwB lim read g ⟨t + c, st, len⟩ = cwT lim reads (g ++ g) ⟨t + c, st, len⟩)
  (hm : 0 < Rs.size / 25) (hsb : sbound lim < Rs.size / 25) (hl16 : lim ≤ 16)
  (hlk : ∀ s base, s + q ≤ Rs.size →
    LookSupS G Rs s base (LookG.look ix G Rs s base (LookG.prep ix (seedHashAt Rs s))))

include hg hcat hrs ht hcwc hm hsb hl16 hlk in
set_option maxHeartbeats 1000000 in
theorem hitsS3_memS (w : Window) (k : Nat) :
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
        exact sliceG_sup G gbs[c]! Rs _ _ _ _ (hlk _ _ (seed_fits Rs.size j hm hj)) hcatc.1 hcatc.2)
      _ (hsub.nodup nd) (fun j hj => lt j (hsub.subset hj)) (by rw [List.length_take, len]; omega)
      w hwc (by omega)
    rw [hcw'] at H
    unfold slicesAt
    rw [List.map_map]
    exact H

end strand3S

set_option maxHeartbeats 1000000 in
theorem mem_hitsAtB3S (lim : Nat) (hl16 : lim ≤ 16) (read : List Char) (g : Genome) (gbs : Array ByteArray)
    (R : ByteArray) (hg : GenomeBytes gbs g) (hr : Encodes R read) {L Pp : Type} [LookG L Pp] [Inhabited Pp]
    (ix : L) (G : ByteArray) (offs : Array Nat) (hcat : catOk G offs gbs = true)
    (hlk : ∀ (R' : ByteArray) s base, s + q ≤ R'.size →
      LookSupS G R' s base (LookG.look ix G R' s base (LookG.prep ix (seedHashAt R' s))))
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
        hitsS3_memS lim read g gbs hg ix G offs hcat R read hr 0 (Or.inl rfl) hcw1 hm hsb hl16 (hlk R),
        hitsS3_memS lim read g gbs hg ix G offs hcat (revCompB R) (revComp read) hrr gbs.size (Or.inr rfl) hcw2
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


/-- **The enumerated mate's hits, raw lookups, packed whole genome.** -/
theorem mem_hitsAtKP3_mzR (lim : Nat) (hl16 : lim ≤ 16) (g : Genome) (read : List Char) (ix : Mz.MzIdx)
    (G : PGen) (offs ns : Array Nat) (R : ByteArray) (hcut : cutOk G offs ns = true)
    (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) g) (hr : Encodes R read)
    (hchk : Mz.check2P ix G = true) (l : List (Placement × Int))
    (hl : hitsAtKP3 lim (PkMzR.mk ix G) ByteArray.empty offs (cutAll G offs ns) R = some l)
    (x : Placement × Int) : x ∈ l ↔ x ∈ hitsBoth sc0 (-(lim : Int)) g read := by
  rw [hitsAtKP3_eq, hitsAtB3_congrG (PkMzR.mk ix G) ByteArray.empty (Mz.unpack G) (fun _ _ _ _ => rfl)] at hl
  exact mem_hitsAtB3S lim hl16 read g _ R hg hr _ _ offs (catOk_cut G offs ns hcut) (lookSup_pkR ix G hchk) l hl x

end MapSpec.Fast
