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

/-- `rdSlot` before its `toNat`. -/
@[inline] def rdSlotU (B : ByteArray) (sw t : Nat) : UInt64 :=
  let j := sw * t
  if sw = 4 then Mz.rd4 B j
  else if sw = 5 then Mz.rd4 B j ||| Mz.byteAt B (j + 4) 32
  else if sw = 6 then Mz.rd4 B j ||| Mz.byteAt B (j + 4) 32 ||| Mz.byteAt B (j + 5) 40
  else Mz.rd4 B j ||| (Mz.rd4 B (j + 4) <<< 32)

theorem rdSlot_eqU (B : ByteArray) (sw t : Nat) : Mz.rdSlot B sw t = (rdSlotU B sw t).toNat := rfl

/-- `rawScan` on `UInt64` slots: the masks, shifts and fields of `rawOk` as `UInt64`s
(`rawScan_eqU`, when they are below `2^64` and the shifts below 64). -/
def rawScanU (sl : ByteArray) (sw o : Nat) (kb tm fm T bs as fs o2 key bw aw pmo : UInt64) (hi base : Nat) (t : Nat)
    (acc : Array Nat) : Array Nat :=
  if t < hi then
    let e := rdSlotU sl sw t
    let pos := e >>> T
    let tg := e &&& tm
    let ok := (e &&& kb) == key && (decide (o ≤ pos.toNat) &&
      ((tg >>> fs) != 0 || (((tg >>> bs) &&& fm) &&& pmo) == bw && ((tg >>> as) &&& fm) >>> o2 == aw))
    rawScanU sl sw o kb tm fm T bs as fs o2 key bw aw pmo hi base (t + 1)
      (if ok then acc.push (anc base 0 (pos.toNat - o)) else acc)
  else acc
termination_by hi - t

theorem u_and (x : UInt64) (m : Nat) (hm : m < 2 ^ 64) : (x &&& m.toUInt64).toNat = x.toNat &&& m := by
  rw [UInt64.toNat_and]; congr 1; simp; omega

theorem u_shr (x : UInt64) (n : Nat) (hn : n < 64) : (x >>> n.toUInt64).toNat = x.toNat >>> n := by
  rw [UInt64.toNat_shiftRight]; congr 1; simp; omega

theorem u_beq (x : UInt64) (m : Nat) (hm : m < 2 ^ 64) : (x == m.toUInt64) = (x.toNat == m) := by
  have : (m.toUInt64).toNat = m := by simp; omega
  apply Bool.eq_iff_iff.2
  simp only [beq_iff_eq]
  constructor
  · intro h; rw [h, this]
  · intro h; apply UInt64.toNat_inj.1; rw [h, this]

theorem u_bne0 (x : UInt64) : (x != 0) = (x.toNat != 0) := by
  apply Bool.eq_iff_iff.2
  simp only [bne_iff_ne, ne_eq]
  constructor
  · intro h h0; exact h (UInt64.toNat_inj.1 (by rw [h0]; rfl))
  · intro h h0; exact h (by rw [h0]; rfl)

/-- The condition under which `rawScanU` runs in place of `rawScan`. -/
def rawSmall (ix : Mz.MzIdx) (key bw aw pmo o2 : Nat) : Bool :=
  decide (ix.kbM < 2 ^ 64) && decide (ix.tM < 2 ^ 64) && decide (ix.fM < 2 ^ 64) && decide (ix.T < 64) &&
  decide (ix.bsh < 64) && decide (ix.ash < 64) && decide (ix.fsh < 64) && decide (o2 < 64) &&
  decide (key < 2 ^ 64) && decide (bw < 2 ^ 64) && decide (aw < 2 ^ 64) && decide (pmo < 2 ^ 64)

theorem rawScan_eqU (ix : Mz.MzIdx) (o key bw aw pmo o2 hi base : Nat) (h : rawSmall ix key bw aw pmo o2 = true) :
    ∀ (t : Nat) (acc : Array Nat), rawScan ix o key bw aw pmo o2 hi base t acc =
      rawScanU ix.sl ix.sw o ix.kbM.toUInt64 ix.tM.toUInt64 ix.fM.toUInt64 ix.T.toUInt64 ix.bsh.toUInt64
        ix.ash.toUInt64 ix.fsh.toUInt64 o2.toUInt64 key.toUInt64 bw.toUInt64 aw.toUInt64 pmo.toUInt64 hi base t acc := by
  simp only [rawSmall, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hkb, htm⟩, hfm⟩, hT⟩, hbs⟩, has⟩, hfs⟩, ho2⟩, hkey⟩, hbw⟩, haw⟩, hpmo⟩ := h
  have e1 : ∀ x : UInt64, ((x >>> ix.T.toUInt64).toNat) = x.toNat >>> ix.T := fun x => u_shr x _ hT
  have hand : ∀ (x : UInt64) (m : Nat), m < 2 ^ 64 → (x &&& m.toUInt64).toNat = x.toNat &&& m := u_and
  have ok : ∀ t, rawOk ix o key bw aw pmo o2 t =
      ((rdSlotU ix.sl ix.sw t &&& ix.kbM.toUInt64) == key.toUInt64 &&
        (decide (o ≤ (rdSlotU ix.sl ix.sw t >>> ix.T.toUInt64).toNat) &&
          (((rdSlotU ix.sl ix.sw t &&& ix.tM.toUInt64) >>> ix.fsh.toUInt64) != 0 ||
            ((((rdSlotU ix.sl ix.sw t &&& ix.tM.toUInt64) >>> ix.bsh.toUInt64) &&& ix.fM.toUInt64) &&&
              pmo.toUInt64) == bw.toUInt64 &&
            (((rdSlotU ix.sl ix.sw t &&& ix.tM.toUInt64) >>> ix.ash.toUInt64) &&& ix.fM.toUInt64) >>>
              o2.toUInt64 == aw.toUInt64))) := by
    intro t
    simp only [rawOk, Mz.MzIdx.slot, rdSlot_eqU, Mz.MzIdx.posOf, Mz.MzIdx.tagOf, Mz.MzIdx.flagF,
      Mz.MzIdx.befF, Mz.MzIdx.aftF]
    rw [u_beq _ _ hkey, u_beq _ _ hbw, u_beq _ _ haw, u_bne0, hand _ _ hkb, e1,
      u_shr _ _ hfs, hand _ _ htm, hand _ _ hpmo, hand _ _ hfm, u_shr _ _ hbs,
      u_shr _ _ ho2, hand _ _ hfm, u_shr _ _ has, hand _ _ htm]
    exact rfl
  have hp : ∀ t, ix.posOf (ix.slot t) = (rdSlotU ix.sl ix.sw t >>> ix.T.toUInt64).toNat := by
    intro t; simp only [Mz.MzIdx.slot, rdSlot_eqU, Mz.MzIdx.posOf, e1]
  have main : ∀ n t acc, hi - t = n → rawScan ix o key bw aw pmo o2 hi base t acc =
      rawScanU ix.sl ix.sw o ix.kbM.toUInt64 ix.tM.toUInt64 ix.fM.toUInt64 ix.T.toUInt64 ix.bsh.toUInt64
        ix.ash.toUInt64 ix.fsh.toUInt64 o2.toUInt64 key.toUInt64 bw.toUInt64 aw.toUInt64 pmo.toUInt64 hi base t acc := by
    intro n
    induction n with
    | zero =>
      intro t acc hn
      have h' : ¬ t < hi := by omega
      rw [rawScan, rawScanU, if_neg h', if_neg h']
    | succ n ih =>
      intro t acc hn
      have h' : t < hi := by omega
      rw [rawScan, rawScanU, if_pos h', if_pos h']
      simp only []
      rw [← ok t, ← hp t]
      exact ih (t + 1) _ (by omega)
  intro t acc
  exact main _ t acc rfl

/-- `rawScan` through `rawScanU` when the fields fit. -/
@[inline] def rawScanD (ix : Mz.MzIdx) (o key bw aw pmo o2 hi base : Nat) (t : Nat) (acc : Array Nat) : Array Nat :=
  if rawSmall ix key bw aw pmo o2 then
    rawScanU ix.sl ix.sw o ix.kbM.toUInt64 ix.tM.toUInt64 ix.fM.toUInt64 ix.T.toUInt64 ix.bsh.toUInt64
      ix.ash.toUInt64 ix.fsh.toUInt64 o2.toUInt64 key.toUInt64 bw.toUInt64 aw.toUInt64 pmo.toUInt64 hi base t acc
  else rawScan ix o key bw aw pmo o2 hi base t acc

theorem rawScanD_eq (ix : Mz.MzIdx) (o key bw aw pmo o2 hi base t : Nat) (acc : Array Nat) :
    rawScanD ix o key bw aw pmo o2 hi base t acc = rawScan ix o key bw aw pmo o2 hi base t acc := by
  unfold rawScanD
  split
  · next h => rw [rawScan_eqU _ _ _ _ _ _ _ _ _ h]
  · rfl

/-- `rawLookP` with the bucket scan `rawScanD` (`rawLookP_eqD`). -/
def rawLookPD (ix : Mz.MzIdx) (G : PGen) (R : ByteArray) (s base : Nat) (p : MzP) : Array Nat :=
  if p.ok then
    let o := p.o
    let v := p.v
    let m1 := min o ix.c
    let m2 := min (ix.w - 1 - o) ix.c
    let a := rawScanD ix o (p.h &&& ix.kbM) ((v >>> (2 * (Mz.q - o))) &&& ix.pm[m1]!)
      ((v >>> (2 * (Mz.q - o - ix.k - m2))) &&& ix.pm[m2]!) ix.pm[m1]! (2 * (ix.c - m2))
      (ix.hiB p.b) base (ix.loB p.b) #[]
    if incA a a.size 0 then a else mzLookSP ix G R s base p
  else mzLookSP ix G R s base p

/-- Compiled code runs `rawLookPD`. -/
@[csimp] theorem rawLookP_eqD : @rawLookP = @rawLookPD := by
  funext ix G R s base p
  unfold rawLookP rawLookPD
  simp only [rawScanD_eq]

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

/-- `rejW` with the two genome words given. -/
@[inline] def rejC (R : ByteArray) (K : RP) (P : PGen) (st lim : Nat) (cur nxt : UInt64) : Bool :=
  let A := P.o + st
  K.ok && decide (32 ≤ R.size) && decide (st + 32 ≤ P.n) && P.w.get! (17 * (A / 64)) == 1 &&
    P.w.get! (17 * ((A + 31) / 64)) == 1 &&
    decide (lim / 4 < cnt64 (fold (K.w[0]! ^^^ comb cur nxt (A % 32) (2 * (A % 32)).toUInt64 (64 - 2 * (A % 32)).toUInt64)))

/-- `scanW` of `f` with the starts rejected by `rejC` skipped; the genome words of the current
32-letter block (`u`) carried along. -/
def scanWC {α : Type} (R : ByteArray) (K : RP) (P : PGen) (lim : Nat) (f : Nat → Option α) :
    Nat → Nat → Nat → UInt64 → UInt64 → List α → List α
  | _, 0, _, _, _, acc => acc
  | a, k + 1, u, cur, nxt, acc =>
    let u' := (P.o + a) / 32
    let cur' := if u' = u then cur else if u' = u + 1 then nxt else gword P.w u'
    let nxt' := if u' = u then nxt else gword P.w (u' + 1)
    scanWC R K P lim f (a + 1) k u' cur' nxt'
      (if rejC R K P a lim cur' nxt' then acc else match f a with | some v => v :: acc | none => acc)

/-- `pscanQ` with the genome words carried (the scan the kernel runs). -/
def pscanC (pgs2 : Array PGen) (RY RYr : ByteArray) (KY KYr : RP) (sl lo hi lim : Nat)
    (x : Placement) : List (Placement × Int) :=
  let ny := RY.size
  let fw := decide (x.2 = Strand.fwd)
  let a := if fw then x.1.start + lo - ny else x.1.start + x.1.len - hi
  let b := if fw then x.1.start + hi - ny else x.1.start + x.1.len - lo
  let P := pgs2[x.1.chr]!
  let u := (P.o + a) / 32
  let f := fun s =>
    let k := if x.2 = Strand.fwd then kerHKG RYr KYr pgs2 pgs2 x.1.chr s ny lim
      else kerHKG RY KY pgs2 pgs2 x.1.chr s ny lim
    let y : Placement := (⟨x.1.chr, s, ny⟩, if x.2 = Strand.fwd then Strand.rev else Strand.fwd)
    if k ≤ lim ∧ properPairU sl lo hi x y = true then some (y, -(k : Int)) else none
  if fw then scanWC RYr KYr P lim f a (b + 1 - a) u (gword P.w u) (gword P.w (u + 1)) []
  else scanWC RY KY P lim f a (b + 1 - a) u (gword P.w u) (gword P.w (u + 1)) []

/-! ### The partner scan on `UInt64` positions (compiled in place of `pscanC`: `pscanC_eq_pscanD`) -/

/-- `scanWC` with the read's first word `w0`, `lim / 4` (`l4`) and the chromosome end `top = P.o + P.n`
hoisted, the absolute position `A = P.o + st` a `UInt64`, and the genome words `cur` / `nxt` of
`A / 32`, `A / 32 + 1` advanced when `A` leaves its 32-letter block. -/
def scanWE {α : Type} (w : ByteArray) (w0 : UInt64) (l4 : Nat) (top : UInt64) (f : Nat → Option α) :
    Nat → Nat → UInt64 → UInt64 → UInt64 → List α → List α
  | 0, _, _, _, _, acc => acc
  | k + 1, st, A, cur, nxt, acc =>
    let s := (A &&& 31).toNat
    let rej := decide (A + 32 ≤ top) && w.get! (17 * (A >>> 6).toNat) == 1 &&
      w.get! (17 * ((A + 31) >>> 6).toNat) == 1 &&
      decide (l4 < cnt64 (fold (w0 ^^^ comb cur nxt s (2 * s).toUInt64 (64 - 2 * s).toUInt64)))
    let acc' := if rej then acc else match f st with | some v => v :: acc | none => acc
    if s = 31 then scanWE w w0 l4 top f k (st + 1) (A + 1) nxt (gword w ((A >>> 5).toNat + 2)) acc'
    else scanWE w w0 l4 top f k (st + 1) (A + 1) cur nxt acc'

/-- The two block flags `scanWE` reads at position `A`. -/
@[inline] def flgW (w : ByteArray) (A : UInt64) : Bool :=
  w.get! (17 * (A >>> 6).toNat) == 1 && w.get! (17 * ((A + 31) >>> 6).toNat) == 1

/-- `scanWE` with the block flags `fl = flgW w A` carried (re-read only where `A`'s blocks can change)
and the shift `A % 32` kept a `UInt64`. -/
def scanWF {α : Type} (w : ByteArray) (w0 : UInt64) (l4 : Nat) (top : UInt64) (f : Nat → Option α) :
    Nat → Nat → UInt64 → UInt64 → UInt64 → Bool → List α → List α
  | 0, _, _, _, _, _, acc => acc
  | k + 1, st, A, cur, nxt, fl, acc =>
    let s := A &&& 31
    let rej := decide (A + 32 ≤ top) && fl &&
      decide (l4 < cnt64 (fold (w0 ^^^ comb cur nxt s.toNat (2 * s) (64 - 2 * s))))
    let acc' := if rej then acc else match f st with | some v => v :: acc | none => acc
    if s = 31 then scanWF w w0 l4 top f k (st + 1) (A + 1) nxt (gword w ((A >>> 5).toNat + 2)) (flgW w (A + 1)) acc'
    else if s = 0 then scanWF w w0 l4 top f k (st + 1) (A + 1) cur nxt (flgW w (A + 1)) acc'
    else scanWF w w0 l4 top f k (st + 1) (A + 1) cur nxt fl acc'

theorem flgW_succ (w : ByteArray) (A : UInt64) (h31 : A &&& 31 ≠ 31) (h0 : A &&& 31 ≠ 0)
    (hb : A.toNat + 64 < 2 ^ 64) : flgW w (A + 1) = flgW w A := by
  have hs : (A &&& 31).toNat = A.toNat % 32 := by
    rw [UInt64.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod A.toNat 5
  have n31 : A.toNat % 32 ≠ 31 := by
    intro h; apply h31; apply UInt64.toNat_inj.1; rw [hs, h]; rfl
  have n0 : A.toNat % 32 ≠ 0 := by
    intro h; apply h0; apply UInt64.toNat_inj.1; rw [hs, h]; rfl
  have e1 : ((A + 1) >>> 6).toNat = (A >>> 6).toNat := by
    rw [UInt64.toNat_shiftRight, UInt64.toNat_shiftRight, UInt64.toNat_add]
    simp [Nat.shiftRight_eq_div_pow]; omega
  have e2 : ((A + 1 + 31) >>> 6).toNat = ((A + 31) >>> 6).toNat := by
    rw [UInt64.toNat_shiftRight, UInt64.toNat_shiftRight, UInt64.toNat_add, UInt64.toNat_add,
      UInt64.toNat_add]
    simp [Nat.shiftRight_eq_div_pow]; omega
  simp only [flgW, e1, e2]

theorem scanWF_eq {α : Type} (w : ByteArray) (w0 : UInt64) (l4 : Nat) (top : UInt64) (f : Nat → Option α) :
    ∀ (k st : Nat) (A cur nxt : UInt64) (fl : Bool) (acc : List α), fl = flgW w A →
      A.toNat + k + 64 < 2 ^ 64 →
      scanWF w w0 l4 top f k st A cur nxt fl acc = scanWE w w0 l4 top f k st A cur nxt acc
  | 0, st, A, cur, nxt, fl, acc, _, _ => by simp only [scanWF, scanWE]
  | k + 1, st, A, cur, nxt, fl, acc, hfl, hb => by
    have hs : (A &&& 31).toNat = A.toNat % 32 := by
      rw [UInt64.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod A.toNat 5
    have h2 : 2 * (A &&& 31) = (2 * (A &&& 31).toNat).toUInt64 := by
      apply UInt64.toNat_inj.1; rw [UInt64.toNat_mul, hs]; simp; try omega
    have h64 : 64 - 2 * (A &&& 31) = (64 - 2 * (A &&& 31).toNat).toUInt64 := by
      apply UInt64.toNat_inj.1; rw [UInt64.toNat_sub_of_le, UInt64.toNat_mul, hs]
      · simp; try omega
      · rw [UInt64.le_iff_toNat_le, UInt64.toNat_mul, hs]; simp; omega
    have h31 : (A &&& 31 = 31) ↔ ((A &&& 31).toNat = 31) := by
      constructor
      · intro h; rw [h]; rfl
      · intro h; apply UInt64.toNat_inj.1; rw [h]; rfl
    have hrej : (decide (A + 32 ≤ top) && fl &&
        decide (l4 < cnt64 (fold (w0 ^^^ comb cur nxt (A &&& 31).toNat (2 * (A &&& 31)) (64 - 2 * (A &&& 31)))))) =
        (decide (A + 32 ≤ top) && w.get! (17 * (A >>> 6).toNat) == 1 &&
          w.get! (17 * ((A + 31) >>> 6).toNat) == 1 &&
          decide (l4 < cnt64 (fold (w0 ^^^ comb cur nxt (A &&& 31).toNat (2 * (A &&& 31).toNat).toUInt64
            (64 - 2 * (A &&& 31).toNat).toUInt64)))) := by
      rw [hfl, h64, h2, flgW]; simp only [Bool.and_assoc]
    simp only [scanWF, scanWE]
    rw [hrej]
    by_cases e31 : A &&& 31 = 31
    · have e31' : (A &&& 31).toNat = 31 := h31.1 e31
      simp only [e31, if_true]
      exact scanWF_eq w w0 l4 top f k (st + 1) (A + 1) _ _ _ _ rfl
        (by rw [UInt64.toNat_add]; simp; omega)
    · have e31' : ¬ (A &&& 31).toNat = 31 := fun h => e31 (h31.2 h)
      simp only [e31, e31', if_false]
      have hA1 : (A + 1).toNat = A.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      by_cases e0 : A &&& 31 = 0
      · simp only [e0, if_true]
        exact scanWF_eq w w0 l4 top f k (st + 1) (A + 1) _ _ _ _ rfl (by rw [hA1]; omega)
      · simp only [e0, if_false]
        exact scanWF_eq w w0 l4 top f k (st + 1) (A + 1) _ _ _ _
          (by rw [hfl, flgW_succ w A e31 e0 (by omega)]) (by rw [hA1]; omega)

/-- `pscanC` with the scan `scanWF` (`scanWE` with the flags carried) when the read word path applies and all positions are below `2^62`. -/
def pscanD (pgs2 : Array PGen) (RY RYr : ByteArray) (KY KYr : RP) (sl lo hi lim : Nat)
    (x : Placement) : List (Placement × Int) :=
  let ny := RY.size
  let fw := decide (x.2 = Strand.fwd)
  let a := if fw then x.1.start + lo - ny else x.1.start + x.1.len - hi
  let b := if fw then x.1.start + hi - ny else x.1.start + x.1.len - lo
  let P := pgs2[x.1.chr]!
  let f := fun s =>
    let k := if x.2 = Strand.fwd then kerHKG RYr KYr pgs2 pgs2 x.1.chr s ny lim
      else kerHKG RY KY pgs2 pgs2 x.1.chr s ny lim
    let y : Placement := (⟨x.1.chr, s, ny⟩, if x.2 = Strand.fwd then Strand.rev else Strand.fwd)
    if k ≤ lim ∧ properPairU sl lo hi x y = true then some (y, -(k : Int)) else none
  let R := if fw then RYr else RY
  let K := if fw then KYr else KY
  if K.ok && decide (32 ≤ R.size) && decide (P.o + P.n + a + (b + 1 - a) + 64 < 4611686018427387904) then
    scanWF P.w K.w[0]! (lim / 4) (P.o + P.n).toUInt64 f (b + 1 - a) a (P.o + a).toUInt64
      (gword P.w ((P.o + a) / 32)) (gword P.w ((P.o + a) / 32 + 1)) (flgW P.w (P.o + a).toUInt64) []
  else pscanC pgs2 RY RYr KY KYr sl lo hi lim x

theorem scanWC_eqW {α : Type} (R : ByteArray) (K : RP) (P : PGen) (lim : Nat) (f : Nat → Option α) :
    ∀ (k a u : Nat) (acc : List α),
      scanWC R K P lim f a k u (gword P.w u) (gword P.w (u + 1)) acc =
        scanW (fun s => if rejW R K P s lim then none else f s) a k acc
  | 0, a, u, acc => by simp only [scanWC, scanW]
  | k + 1, a, u, acc => by
    simp only [scanWC, scanW]
    have hc : (if (P.o + a) / 32 = u then gword P.w u else if (P.o + a) / 32 = u + 1 then gword P.w (u + 1)
        else gword P.w ((P.o + a) / 32)) = gword P.w ((P.o + a) / 32) := by
      split
      · next h => rw [h]
      · split
        · next h => rw [h]
        · rfl
    have hn : (if (P.o + a) / 32 = u then gword P.w (u + 1) else gword P.w ((P.o + a) / 32 + 1)) =
        gword P.w ((P.o + a) / 32 + 1) := by
      split
      · next h => rw [h]
      · rfl
    rw [hc, hn, scanWC_eqW R K P lim f k (a + 1) ((P.o + a) / 32)]
    congr 1
    have hr : rejC R K P a lim (gword P.w ((P.o + a) / 32)) (gword P.w ((P.o + a) / 32 + 1)) =
        rejW R K P a lim := rfl
    rw [hr]
    cases rejW R K P a lim <;> rfl

theorem scanWE_eq {α : Type} (R : ByteArray) (K : RP) (P : PGen) (lim : Nat) (f : Nat → Option α)
    (hK : K.ok = true) (hR : 32 ≤ R.size) (htop : P.o + P.n < 4611686018427387904) :
    ∀ (k st : Nat) (A : UInt64) (acc : List α), A.toNat = P.o + st → P.o + st + k + 64 < 4611686018427387904 →
      scanWE P.w K.w[0]! (lim / 4) (P.o + P.n).toUInt64 f k st A
        (gword P.w ((P.o + st) / 32)) (gword P.w ((P.o + st) / 32 + 1)) acc =
        scanW (fun s => if rejW R K P s lim then none else f s) st k acc
  | 0, st, A, acc, _, _ => by simp only [scanWE, scanW]
  | k + 1, st, A, acc, hA, hb => by
    have hs : (A &&& 31).toNat = (P.o + st) % 32 := by
      rw [UInt64.toNat_and, ← hA]; exact Nat.and_two_pow_sub_one_eq_mod A.toNat 5
    have h6 : (A >>> 6).toNat = (P.o + st) / 64 := by
      rw [UInt64.toNat_shiftRight, ← hA]; simp [Nat.shiftRight_eq_div_pow]
    have h5 : (A >>> 5).toNat = (P.o + st) / 32 := by
      rw [UInt64.toNat_shiftRight, ← hA]; simp [Nat.shiftRight_eq_div_pow]
    have h31 : (A + 31).toNat = P.o + st + 31 := by
      rw [UInt64.toNat_add]; simp; omega
    have h31' : ((A + 31) >>> 6).toNat = (P.o + st + 31) / 64 := by
      rw [UInt64.toNat_shiftRight, h31]; simp [Nat.shiftRight_eq_div_pow]
    have h1 : (A + 1).toNat = P.o + (st + 1) := by
      rw [UInt64.toNat_add]; simp; omega
    have htopN : ((P.o + P.n).toUInt64).toNat = P.o + P.n := by simp; omega
    have hle : decide (A + 32 ≤ (P.o + P.n).toUInt64) = decide (st + 32 ≤ P.n) := by
      have h32 : (A + 32).toNat = P.o + st + 32 := by rw [UInt64.toNat_add]; simp; omega
      rw [decide_eq_decide, UInt64.le_iff_toNat_le, h32, htopN]; omega
    have hrej : (decide (A + 32 ≤ (P.o + P.n).toUInt64) && P.w.get! (17 * (A >>> 6).toNat) == 1 &&
        P.w.get! (17 * ((A + 31) >>> 6).toNat) == 1 &&
        decide (lim / 4 < cnt64 (fold (K.w[0]! ^^^ comb (gword P.w ((P.o + st) / 32)) (gword P.w ((P.o + st) / 32 + 1))
          (A &&& 31).toNat (2 * (A &&& 31).toNat).toUInt64 (64 - 2 * (A &&& 31).toNat).toUInt64)))) =
        rejW R K P st lim := by
      rw [hle, h6, h31', hs]
      simp only [rejW, hK, hR, Bool.true_and, decide_true]
    simp only [scanWE, scanW]
    rw [hrej]
    have hacc : (if rejW R K P st lim = true then acc else match f st with | some v => v :: acc | none => acc) =
        (match (if rejW R K P st lim = true then none else f st) with | some v => v :: acc | none => acc) := by
      cases rejW R K P st lim <;> rfl
    rw [hacc, hs]
    split
    · next h =>
      have e1 : (P.o + (st + 1)) / 32 = (P.o + st) / 32 + 1 := by omega
      have e2 := scanWE_eq R K P lim f hK hR htop k (st + 1) (A + 1)
        (match (if rejW R K P st lim = true then none else f st) with | some v => v :: acc | none => acc) h1 (by omega)
      have e3 : (P.o + st) / 32 + 1 + 1 = (P.o + st) / 32 + 2 := by omega
      rw [e1, e3] at e2
      rw [h5]; exact e2
    · next h =>
      have e1 : (P.o + (st + 1)) / 32 = (P.o + st) / 32 := by omega
      have e2 := scanWE_eq R K P lim f hK hR htop k (st + 1) (A + 1)
        (match (if rejW R K P st lim = true then none else f st) with | some v => v :: acc | none => acc) h1 (by omega)
      rw [e1] at e2
      exact e2

theorem pscanD_eq (pgs2 : Array PGen) (RY RYr : ByteArray) (KY KYr : RP) (sl lo hi lim : Nat) (x : Placement) :
    pscanD pgs2 RY RYr KY KYr sl lo hi lim x = pscanC pgs2 RY RYr KY KYr sl lo hi lim x := by
  unfold pscanD
  by_cases hfw : x.2 = Strand.fwd
  · simp only [hfw, decide_true, if_true]
    split
    · next hg =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
      obtain ⟨⟨hK, hR⟩, hb⟩ := hg
      unfold pscanC
      simp only [hfw, decide_true, if_true]
      rw [scanWF_eq _ _ _ _ _ _ _ _ _ _ _ _ rfl (by simp; omega),
        scanWE_eq _ _ _ _ _ hK hR (by omega) _ _ _ _ (by simp; omega) (by omega), scanWC_eqW]
    · rfl
  · simp only [hfw, decide_false, Bool.false_eq_true, if_false]
    split
    · next hg =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
      obtain ⟨⟨hK, hR⟩, hb⟩ := hg
      unfold pscanC
      simp only [hfw, decide_false, Bool.false_eq_true, if_false]
      rw [scanWF_eq _ _ _ _ _ _ _ _ _ _ _ _ rfl (by simp; omega),
        scanWE_eq _ _ _ _ _ hK hR (by omega) _ _ _ _ (by simp; omega) (by omega), scanWC_eqW]
    · rfl

/-- Compiled code runs `pscanD`. -/
@[csimp] theorem pscanC_eq_pscanD : @pscanC = @pscanD := by
  funext pgs2 RY RYr KY KYr sl lo hi lim x
  exact (pscanD_eq pgs2 RY RYr KY KYr sl lo hi lim x).symm

/-! ## Part A': the enumerated mate's hits by global diagonals -/

/-- The last `c ∈ [lo, hi)` with `offs[c] ≤ x` (binary search; `lo` when none). -/
def chromOf (offs : Array Nat) (x : Nat) (lo hi : Nat) : Nat :=
  if lo + 1 < hi then
    let mid := (lo + hi) / 2
    if offs[mid]! ≤ x then chromOf offs x mid hi else chromOf offs x lo mid
  else lo
termination_by hi - lo

/-- The chromosomes are laid out in order, without overlap. -/
def offsOk (offs : Array Nat) (pgs : Array PGen) : Bool :=
  (List.range pgs.size).all fun c => decide (pgs.size ≤ c + 1) || decide (offs[c]! + pgs[c]!.n ≤ offs[c + 1]!)

/-- The diagonals held by at least `need` of the arrays `all`, from the first `k` arrays of `l`
(each diagonal once: skipped when an earlier array `prev` holds it). -/
def candsB (need : Nat) (all prev : List (Array Nat)) : List (Array Nat) → Nat → List Nat
  | [], _ => []
  | _, 0 => []
  | arr :: rest, k + 1 =>
    (arr.toList.filterMap fun e =>
      if need ≤ suppA all (e / 16) 0 && prev.all (fun a => !anyNear a (e / 16) (e / 16)) then some (e / 16) else none) ++
    candsB need all (arr :: prev) rest k

/-- `need ≤ suppA l D 0`, stopping at the `need`-th array holding `D` (`atLeastD_eq`). -/
def atLeastD (D : Nat) : Nat → List (Array Nat) → Bool
  | 0, _ => true
  | _ + 1, [] => false
  | n + 1, a :: as => if anyNear a D D then atLeastD D n as else atLeastD D (n + 1) as

/-- `candsB` as run: the earlier arrays checked first (a diagonal one of them holds is skipped
without counting), then the support counted over the current and later arrays only, stopping at
`need` (`candsC_eq`: the same list). -/
def candsC (need : Nat) (prev : List (Array Nat)) : List (Array Nat) → Nat → List Nat
  | [], _ => []
  | _, 0 => []
  | arr :: rest, k + 1 =>
    (arr.toList.filterMap fun e =>
      if prev.all (fun a => !anyNear a (e / 16) (e / 16)) && atLeastD (e / 16) need (arr :: rest)
      then some (e / 16) else none) ++
    candsC need (arr :: prev) rest k

theorem suppA0_cons (a : Array Nat) (as : List (Array Nat)) (D : Nat) :
    suppA (a :: as) D 0 = if anyNear a D D = true then suppA as D 0 + 1 else suppA as D 0 := by
  unfold suppA
  simp only [Nat.sub_zero, Nat.add_zero, List.filter_cons]
  split <;> simp

theorem atLeastD_eq (D : Nat) : ∀ (n : Nat) (l : List (Array Nat)), atLeastD D n l = decide (n ≤ suppA l D 0)
  | 0, _ => by simp [atLeastD]
  | n + 1, [] => by simp [atLeastD, suppA]
  | n + 1, a :: as => by
    have ih1 := atLeastD_eq D n as
    have ih2 := atLeastD_eq D (n + 1) as
    rw [show atLeastD D (n + 1) (a :: as) = (if anyNear a D D then atLeastD D n as else atLeastD D (n + 1) as)
      from rfl, suppA0_cons]
    cases h : anyNear a D D
    · simp only [Bool.false_eq_true, if_false, ih2]
    · simp only [if_true, ih1]
      simp

theorem suppA_append_none (p l : List (Array Nat)) (D : Nat) (hp : (p.all fun a => !anyNear a D D) = true) :
    suppA (p ++ l) D 0 = suppA l D 0 := by
  unfold suppA
  rw [List.filter_append, List.length_append]
  have : (p.filter fun arr => anyNear arr (D - 0) (D + 0)) = [] := by
    rw [List.filter_eq_nil_iff]; intro a ha
    have := List.all_eq_true.1 hp a ha
    simpa using this
  rw [this, List.length_nil, Nat.zero_add]

/-- **`candsC` is `candsB`.** -/
theorem candsC_eq (need : Nat) : ∀ (prev l : List (Array Nat)) (k : Nat),
    candsB need (prev.reverse ++ l) prev l k = candsC need prev l k
  | _, [], _ => by simp [candsB, candsC]
  | _, _ :: _, 0 => by simp [candsB, candsC]
  | prev, arr :: rest, k + 1 => by
    unfold candsB candsC
    have ih := candsC_eq need (arr :: prev) rest k
    rw [List.reverse_cons, List.append_assoc, List.singleton_append] at ih
    rw [ih]
    congr 1
    congr 1
    funext e
    cases hp : (prev.all fun a => !anyNear a (e / 16) (e / 16))
    · simp
    · have hp' : (prev.reverse.all fun a => !anyNear a (e / 16) (e / 16)) = true := by
        rw [List.all_reverse]; exact hp
      rw [suppA_append_none _ _ _ hp', atLeastD_eq]
      simp

theorem candsC_nil (need : Nat) (l : List (Array Nat)) (k : Nat) :
    candsC need [] l k = candsB need l [] l k := by
  rw [← candsC_eq]; rfl

/-- One strand's windows within `lim` (gapless, `lim ≤ 7`): the anchor diagonals of the
`sbound lim + 2` rarest seeds held by all but `sbound lim` of them, each placed in its chromosome
(`chromOf`), through the kernel `ker c st` (virtual chromosome `t + c`). -/
def hitsGS {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G : ByteArray) (offs : Array Nat) (n : Nat)
    (gsz : Nat → Nat) (ker : Nat → Nat → Nat) (t lim : Nat) (Rs : ByteArray) : List (Window × Nat) :=
  let m := Rs.size / 25
  let Ls := Rs.size / m
  let ps := prepG ix Rs m Ls
  let J := (ordG (ps.map (LookG.size ix)) m).take (sbound lim + 2)
  let acc := J.map fun j => LookG.look ix G Rs (j * Ls) (Rs.size - j * Ls) ps[j]!
  (candsC (J.length - sbound lim) [] acc (sbound lim + 1)).filterMap fun D =>
    let x := D - Rs.size
    let c := chromOf offs x 0 n
    if Rs.size ≤ D ∧ c < n ∧ offs[c]! ≤ x ∧ x - offs[c]! + Rs.size ≤ gsz c then
      let k := ker c (x - offs[c]!)
      if k ≤ lim then some (⟨t + c, x - offs[c]!, Rs.size⟩, k) else none
    else none

/-- Every placement of a read within `lim ≤ 7`: by global diagonals when the chromosomes are in
order (`offsOk`), else `hitsAtKP3`. -/
def hitsAtQ (lim : Nat) (ix : PkMzR) (offs : Array Nat) (pgs : Array PGen) (R : ByteArray) :
    Option (List (Placement × Int)) :=
  if fastT lim R then
    if offsOk offs pgs then
      let n := pgs.size
      let pgs2 := pgs ++ pgs
      let Rr := revCompK R
      let K := packRP R
      let Kr := packRP Rr
      some ((hitsGS ix ByteArray.empty offs n (fun c => pgs[c]!.n)
          (fun c st => kerHKG R K pgs2 pgs2 c st R.size lim) 0 lim R ++
        hitsGS ix ByteArray.empty offs n (fun c => pgs[c]!.n)
          (fun c st => kerHKG Rr Kr pgs2 pgs2 (n + c) st Rr.size lim) n lim Rr).map
        fun x => (decB n x.1, -(x.2 : Int)))
    else hitsAtKP3 lim ix ByteArray.empty offs pgs R
  else none

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

/-- As `pairsQ`, with cached words (`pscanC`).  The pairs of one hit `x` of the enumerated mate (partners within `Gc − pen x`, pair score `≥ −Gc`). -/
def pairsQC (dc : Nat → Nat) (sl lo hi Gc : Nat) (pgs2 : Array PGen) (RY RYr : ByteArray) (KY KYr : RP)
    (swap : Bool) (x : Placement × Int) : List PairHit :=
  (pscanC pgs2 RY RYr KY KYr sl lo hi (Gc - (-x.2).toNat) x.1).filterMap fun y =>
    let p : PairHit := if swap then (y, x) else (x, y)
    if -(Gc : Int) ≤ pairScoreD dc p then some p else none

/-- As `pairGQ`, with global diagonal X hits (`hitsAtQ`) and `pairsQC` (meets `pairGF_sound`'s statement: `pairGQC_sound`, PairGuarQE).  **The fast pair-level guarantee at `Gc`, early stop**: the enumerated mate's hits within `Gc`
(raw lookups), the perfect ones' pairs first, then the others' (bound: their best score), stopping
when the answer is settled.  Answer as `pairGF`'s. -/
def pairGQC (dc : Nat → Nat) (sl lo hi Gc : Nat) (swap : Bool) (ix : PkMzR) (offs : Array Nat)
    (pgs : Array PGen) (R1 R2 : ByteArray) : Option (Option PairHit × Bool × List (Placement × Int)) :=
  match hitsAtQ Gc ix offs pgs (if swap then R2 else R1) with
  | none => none
  | some lX =>
    let RY := if swap then R1 else R2
    let RYr := revCompK RY
    let f := pairsQC dc sl lo hi Gc (pgs ++ pgs) RY RYr (packRP RY) (packRP RYr) swap
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
