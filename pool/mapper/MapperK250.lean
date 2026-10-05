import MapperPGen
import MapperPacked
import MapperGenScore

/-!
# Word kernels for short reads (≤ 256 letters) over the packed genome

The read is packed once (`packRP`: 32 letters per `UInt64`, A0 C1 G2 T3, letter
`i` in bits `2·(i % 32)` of word `i / 32`).  The genome is a `PGen` (64-letter
blocks: a flag byte, then 16 code bytes); the aligned word `u` (absolute letters
`[32u, 32u + 32)`) is 8 consecutive code bytes (`gword`).  A window whose blocks are
all flagged (pure ACGT) is compared 32 letters at a time: XOR, fold each 2-bit
field to its low bit (`fold`), SWAR count (`cnt64`), lowest/highest set field by
`cnt64 (m ^^^ (m - 1))` / `cnt64 (smear m)`.  Anything else (non-ACGT read or
blocks, read longer than 256, a window off the chromosome) takes the byte loops.

Kernels, each equal to the byte version under `Rep P G` (`P` spells `G`):
`hamK` (= `hamming`), `fwdK` (= `fwdMis`), `bwdK` (= `bwdMis`),
`gappedK` (= `gappedPen2`), `kerGK` (= `kerG`).
-/

namespace MapSpec.Fast

open MapSpec

/-! ## Algorithm -/

/-- Packed read: words, and whether the word path applies (`≤ 256` letters, all ACGT). -/
structure RP where
  w : Array UInt64
  ok : Bool
deriving Inhabited

/-- Pack `R[i ..]`: `w` is the word being filled (next field at bit `sh`), `acc` the
full words, `ok` all ACGT so far. -/
def packLoop (R : ByteArray) (i : Nat) (sh : UInt64) (w : UInt64) (acc : Array UInt64) (ok : Bool) : RP :=
  if i < R.size then
    let t := codeTab.get! (R.get! i).toNat
    let w := w ||| (t &&& 3).toUInt64 <<< sh
    if sh == 62 then packLoop R (i + 1) 0 0 (acc.push w) (ok && decide (t < 4))
    else packLoop R (i + 1) (sh + 2) w acc (ok && decide (t < 4))
  else ⟨acc.push w, ok⟩
termination_by R.size - i

def packRP (R : ByteArray) : RP :=
  if R.size ≤ 256 then packLoop R 0 0 0 (Array.emptyWithCapacity 9) true else ⟨#[], false⟩

/-- Aligned genome word `u` of the blocks `w`. -/
@[inline] def gword (w : ByteArray) (u : Nat) : UInt64 :=
  let b := 17 * (u / 2) + 1 + 8 * (u % 2)
  (w.get! b).toUInt64 ||| (w.get! (b + 1)).toUInt64 <<< 8 ||| (w.get! (b + 2)).toUInt64 <<< 16 |||
  (w.get! (b + 3)).toUInt64 <<< 24 ||| (w.get! (b + 4)).toUInt64 <<< 32 ||| (w.get! (b + 5)).toUInt64 <<< 40 |||
  (w.get! (b + 6)).toUInt64 <<< 48 ||| (w.get! (b + 7)).toUInt64 <<< 56

theorem usz_toNat (b k : Nat) (h : b + k < USize.size) : (b.toUSize + k.toUSize).toNat = b + k := by
  have hs : USize.size = 2 ^ System.Platform.numBits := rfl
  rw [hs] at h
  rw [USize.toNat_add, Nat.toUSize_eq, Nat.toUSize_eq, USize.toNat_ofNat', USize.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (show b < 2 ^ System.Platform.numBits by omega),
    Nat.mod_eq_of_lt (show k < 2 ^ System.Platform.numBits by omega), Nat.mod_eq_of_lt h]

/-- A round trip through `USize` that keeps `b + 8` bounds it below `USize.size` (a
small-number test, unlike comparing with the big constant `USize.size`). -/
theorem usz_lt (b : Nat) (h : (b.toUSize + (8 : Nat).toUSize).toNat = b + 8) : b + 8 < USize.size :=
  h ▸ USize.toNat_lt_size _

/-- `gword` with machine-word indices and one bounds check (`gword_eq_gwordF`, used by
the compiler in place of `gword`). -/
@[inline] def gwordF (w : ByteArray) (u : Nat) : UInt64 :=
  let b := 17 * (u / 2) + 1 + 8 * (u % 2)
  if h : b + 8 ≤ w.size ∧ (b.toUSize + (8 : Nat).toUSize).toNat = b + 8 then
    let i := b.toUSize
    (w.uget (i + (0 : Nat).toUSize) (by have := usz_lt b h.2; rw [usz_toNat _ _ (by omega)]; omega)).toUInt64 |||
    (w.uget (i + (1 : Nat).toUSize) (by have := usz_lt b h.2; rw [usz_toNat _ _ (by omega)]; omega)).toUInt64 <<< 8 |||
    (w.uget (i + (2 : Nat).toUSize) (by have := usz_lt b h.2; rw [usz_toNat _ _ (by omega)]; omega)).toUInt64 <<< 16 |||
    (w.uget (i + (3 : Nat).toUSize) (by have := usz_lt b h.2; rw [usz_toNat _ _ (by omega)]; omega)).toUInt64 <<< 24 |||
    (w.uget (i + (4 : Nat).toUSize) (by have := usz_lt b h.2; rw [usz_toNat _ _ (by omega)]; omega)).toUInt64 <<< 32 |||
    (w.uget (i + (5 : Nat).toUSize) (by have := usz_lt b h.2; rw [usz_toNat _ _ (by omega)]; omega)).toUInt64 <<< 40 |||
    (w.uget (i + (6 : Nat).toUSize) (by have := usz_lt b h.2; rw [usz_toNat _ _ (by omega)]; omega)).toUInt64 <<< 48 |||
    (w.uget (i + (7 : Nat).toUSize) (by have := usz_lt b h.2; rw [usz_toNat _ _ (by omega)]; omega)).toUInt64 <<< 56
  else gwordS w u
where
  /-- The same as `gword` (its slow path; not rewritten by `csimp`). -/
  gwordS (w : ByteArray) (u : Nat) : UInt64 :=
    let b := 17 * (u / 2) + 1 + 8 * (u % 2)
    (w.get! b).toUInt64 ||| (w.get! (b + 1)).toUInt64 <<< 8 ||| (w.get! (b + 2)).toUInt64 <<< 16 |||
    (w.get! (b + 3)).toUInt64 <<< 24 ||| (w.get! (b + 4)).toUInt64 <<< 32 ||| (w.get! (b + 5)).toUInt64 <<< 40 |||
    (w.get! (b + 6)).toUInt64 <<< 48 ||| (w.get! (b + 7)).toUInt64 <<< 56

theorem uget_get! (w : ByteArray) (i : USize) (h : i.toNat < w.size) : w.uget i h = w.get! i.toNat := by
  cases w with
  | mk bs =>
    simp only [ByteArray.uget, ByteArray.get!]
    simp only [ByteArray.size] at h
    rw [getElem!_pos bs i.toNat h]
    rfl

@[csimp] theorem gword_eq_gwordF : @gword = @gwordF := by
  funext w u
  unfold gwordF gwordF.gwordS gword
  simp only []
  split
  · rename_i h
    have e : ∀ k, k < 9 → ((17 * (u / 2) + 1 + 8 * (u % 2)).toUSize + k.toUSize).toNat =
        17 * (u / 2) + 1 + 8 * (u % 2) + k := fun k hk =>
      usz_toNat _ _ (by have := usz_lt _ h.2; omega)
    rw [uget_get!, uget_get!, uget_get!, uget_get!, uget_get!, uget_get!, uget_get!, uget_get!,
      e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega), e 5 (by omega),
      e 6 (by omega), e 7 (by omega)]
    rfl
  · rfl

/-- Each 2-bit field folded to its low bit. -/
@[inline] def fold (x : UInt64) : UInt64 := (x ||| x >>> 1) &&& 0x5555555555555555

/-- Fields `[0, c)` kept (`c ≥ 32`: all). -/
@[inline] def lowF (x : UInt64) (c : Nat) : UInt64 :=
  if c < 32 then x &&& ((1 <<< (2 * c).toUInt64) - 1) else x

/-- Fields `[c, 32)` kept. -/
@[inline] def highF (x : UInt64) (c : Nat) : UInt64 :=
  if c = 0 then x else if c < 32 then x &&& ~~~((1 <<< (2 * c).toUInt64) - 1) else 0

/-- Index of the lowest set field (`m ≠ 0`, folded). -/
@[inline] def lowIdx (m : UInt64) : Nat := Packed.cnt64 (m ^^^ (m - 1)) - 1

/-- Index of the highest set field (`m ≠ 0`, folded). -/
@[inline] def highIdx (m : UInt64) : Nat :=
  let m := m ||| m >>> 1
  let m := m ||| m >>> 2
  let m := m ||| m >>> 4
  let m := m ||| m >>> 8
  let m := m ||| m >>> 16
  let m := m ||| m >>> 32
  Packed.cnt64 m - 1

/-- Index of the `k+1`-th lowest set field. -/
def selLow (m : UInt64) : Nat → Nat
  | 0 => lowIdx m
  | k + 1 => selLow (m &&& (m - 1)) k

/-- Index of the `k+1`-th highest set field. -/
def selHigh (m : UInt64) : Nat → Nat
  | 0 => highIdx m
  | k + 1 => selHigh (m ^^^ (1 <<< (2 * highIdx m).toUInt64)) k

/-- Genome letters of read chunk `j`: the aligned words `cur`, `nxt` shifted by `s`
fields (`sh = 2s`, `sh' = 64 − 2s`). -/
@[inline] def comb (cur nxt : UInt64) (s : Nat) (sh sh' : UInt64) : UInt64 :=
  if s = 0 then cur else (cur >>> sh) ||| (nxt <<< sh')

/-- Mismatches of `R[32j, stop)` against the genome added to `acc`, stopping once
above `lim`; the genome at read letter `x` is absolute letter `32·u0 + s + x`, `cur`
is the aligned word `u0 + j`. -/
def hamW (rw : Array UInt64) (gw : ByteArray) (u0 s : Nat) (sh sh' : UInt64) (lim stop : Nat)
    (j acc : Nat) (cur : UInt64) : Nat :=
  if 32 * j < stop then
    let nxt := gword gw (u0 + j + 1)
    let acc := acc + Packed.cnt64 (lowF (fold (rw[j]! ^^^ comb cur nxt s sh sh')) (stop - 32 * j))
    if lim < acc then lim + 1 else hamW rw gw u0 s sh sh' lim stop (j + 1) acc nxt
  else acc
termination_by stop - 32 * j

/-- Position of the `k`-th mismatch (`k ≥ 1`) in `R[32j, stop)`, or `stop`. -/
def fwdW (rw : Array UInt64) (gw : ByteArray) (u0 s : Nat) (sh sh' : UInt64) (stop : Nat)
    (j k : Nat) (cur : UInt64) : Nat :=
  if 32 * j < stop then
    let nxt := gword gw (u0 + j + 1)
    let m := lowF (fold (rw[j]! ^^^ comb cur nxt s sh sh')) (stop - 32 * j)
    let c := Packed.cnt64 m
    if c < k then fwdW rw gw u0 s sh sh' stop (j + 1) (k - c) nxt else 32 * j + selLow m (k - 1)
  else stop
termination_by stop - 32 * j

/-- One past the `k`-th mismatch from the right (`k ≥ 1`) in `R[lo, e)`, chunk `j`
and below, or `lo`; `nxt` is the aligned word `u0 + j + 1`. -/
def bwdW (rw : Array UInt64) (gw : ByteArray) (u0 s : Nat) (sh sh' : UInt64) (lo e : Nat) :
    (j k : Nat) → UInt64 → Nat
  | j, k, nxt =>
    let cur := gword gw (u0 + j)
    let m := highF (lowF (fold (rw[j]! ^^^ comb cur nxt s sh sh')) (e - 32 * j)) (lo - 32 * j)
    let c := Packed.cnt64 m
    if k ≤ c then 32 * j + selHigh m (k - 1) + 1
    else if 32 * j ≤ lo then lo
    else match j with
      | 0 => lo
      | j + 1 => bwdW rw gw u0 s sh sh' lo e j (k - c) cur

/-- Blocks `[b, stop)` all flagged. -/
def flagsOk (w : ByteArray) (b stop : Nat) : Bool :=
  if b < stop then w.get! (17 * b) == 1 && flagsOk w (b + 1) stop else true
termination_by stop - b

/-- The window `[st, st + len)` of `P` lies in flagged blocks (`len ≥ 1`). -/
@[inline] def winOk (P : PGen) (st len : Nat) : Bool :=
  decide (st + len ≤ P.n) && flagsOk P.w ((P.o + st) / 64) ((P.o + st + len - 1) / 64 + 1)

/-- Word scans at absolute genome start `a` (read letter `x` ↦ `a + x`). -/
@[inline] def hamA (rw : Array UInt64) (gw : ByteArray) (a lim stop : Nat) : Nat :=
  let s := a % 32
  hamW rw gw (a / 32) s (2 * s).toUInt64 (64 - 2 * s).toUInt64 lim stop 0 0 (gword gw (a / 32))

@[inline] def fwdA (rw : Array UInt64) (gw : ByteArray) (a stop k : Nat) : Nat :=
  let s := a % 32
  fwdW rw gw (a / 32) s (2 * s).toUInt64 (64 - 2 * s).toUInt64 stop 0 k (gword gw (a / 32))

@[inline] def bwdA (rw : Array UInt64) (gw : ByteArray) (a lo e k : Nat) : Nat :=
  let s := a % 32
  let j := (e - 1) / 32
  bwdW rw gw (a / 32) s (2 * s).toUInt64 (64 - 2 * s).toUInt64 lo e j k (gword gw (a / 32 + j + 1))

/-- Number of letters scanned with bytes before the word path. -/
def pre : Nat := 8

/-- `fwdMis R G st stop 0 k` (`stop ≤ R.size`; words at absolute `a`). -/
@[inline] def fwdK (R G : ByteArray) (rw : Array UInt64) (gw : ByteArray) (a st stop k : Nat) : Nat :=
  let f := fwdMis R G st (min stop pre) 0 k
  if f < min stop pre then f else fwdA rw gw a stop k

/-- `bwdMis R G st len lo R.size k` (words at absolute `a` for the end diagonal). -/
@[inline] def bwdK (R G : ByteArray) (rw : Array UInt64) (gw : ByteArray) (a st len lo k : Nat) : Nat :=
  let b := bwdMis R G st len (max lo (R.size - pre)) R.size k
  if max lo (R.size - pre) < b then b else bwdA rw gw a lo R.size k

/-- `gappedPen2` with a third level (one gap, at most two mismatches): exact up to
`lim ≤ 17` (`gappedPen3_spec`); `= gappedPen2` for `lim ≤ 15`. -/
def gappedPen3 (r g : ByteArray) (st len lim : Nat) : Nat :=
  let n := r.size
  let L := if len > n then len - n else n - len
  if lim < 6 + 2 * L then lim + 1 else
  let skip := if len < n then L else 0
  let F1 := fwdMis r g st (n - skip) 0 1
  let E1 := bwdMis r g st len skip n 1
  if E1 - skip ≤ F1 then 6 + 2 * L else
  if lim < 10 + 2 * L then lim + 1 else
  let F2 := fwdMis r g st (n - skip) 0 2
  let E2 := bwdMis r g st len skip n 2
  if E1 - skip ≤ F2 || E2 - skip ≤ F1 then 10 + 2 * L else
  if lim < 14 + 2 * L then lim + 1 else
  let F3 := fwdMis r g st (n - skip) 0 3
  let E3 := bwdMis r g st len skip n 3
  if E1 - skip ≤ F3 || E2 - skip ≤ F2 || E3 - skip ≤ F1 then 14 + 2 * L else lim + 1

/-- `kerG` with `gappedPen3`: exact up to `lim ≤ 17`. -/
def kerG3 (R G : ByteArray) (st len lim : Nat) : Nat :=
  if st + len ≤ G.size then
    if len = R.size then
      let h := hamming R G st (lim / 4) 0 R.size 0
      if 4 * h ≤ lim then 4 * h else lim + 1
    else gappedPen3 R G st len lim
  else lim + 1

/-- `fwdMis R G st stop 0 k`: the byte pre-scan, then the word scan when the range is
flagged (checked only then), else the byte loop. -/
@[inline] def fwdL (R G : ByteArray) (K : RP) (P : PGen) (st stop k : Nat) : Nat :=
  let f := fwdMis R G st (min stop pre) 0 k
  if f < min stop pre then f
  else if K.ok && decide (stop ≤ R.size) && winOk P st stop then fwdA K.w P.w (P.o + st) stop k
  else fwdMis R G st stop 0 k

/-- `bwdMis R G st len lo R.size k` likewise (end diagonal `st + len − n`). -/
@[inline] def bwdL (R G : ByteArray) (K : RP) (P : PGen) (st len lo k : Nat) : Nat :=
  let n := R.size
  let b := bwdMis R G st len (max lo (n - pre)) n k
  if max lo (n - pre) < b then b
  else if K.ok && decide (n ≤ st + len) && decide (lo < n) && winOk P (st + len - n + lo) (n - lo) then
    bwdA K.w P.w (P.o + (st + len - n)) lo n k
  else bwdMis R G st len lo n k

/-- `gappedPen3` with the scans `fwdL` / `bwdL`. -/
@[inline] def gappedL (R G : ByteArray) (K : RP) (P : PGen) (st len lim : Nat) : Nat :=
  let n := R.size
  let L := if len > n then len - n else n - len
  if lim < 6 + 2 * L then lim + 1 else
  let skip := if len < n then L else 0
  let F1 := fwdL R G K P st (n - skip) 1
  let E1 := bwdL R G K P st len skip 1
  if E1 - skip ≤ F1 then 6 + 2 * L else
  if lim < 10 + 2 * L then lim + 1 else
  let F2 := fwdL R G K P st (n - skip) 2
  let E2 := bwdL R G K P st len skip 2
  if E1 - skip ≤ F2 || E2 - skip ≤ F1 then 10 + 2 * L else
  if lim < 14 + 2 * L then lim + 1 else
  let F3 := fwdL R G K P st (n - skip) 3
  let E3 := bwdL R G K P st len skip 3
  if E1 - skip ≤ F3 || E2 - skip ≤ F2 || E3 - skip ≤ F1 then 14 + 2 * L else lim + 1

/-- Word path applies to window `(st, len)`. -/
@[inline] def wordOk (R : ByteArray) (K : RP) (P : PGen) (st len : Nat) : Bool :=
  K.ok && decide (0 < R.size) && decide (0 < len) && decide (R.size ≤ st + len) && winOk P st len

/-- The word kernel: `kerG3` (so `kerG` for `lim ≤ 15`). -/
def kerGK (R : ByteArray) (K : RP) (G : ByteArray) (P : PGen) (st len lim : Nat) : Nat :=
  if len = R.size then
    if wordOk R K P st len then
      let h := hamA K.w P.w (P.o + st) (lim / 4) R.size
      if 4 * h ≤ lim then 4 * h else lim + 1
    else if lim / 4 < hamming R G st (lim / 4) 0 (min R.size pre) 0 then lim + 1
    else kerG3 R G st len lim
  else if st + len ≤ P.n then gappedL R G K P st len lim
  else lim + 1

end MapSpec.Fast
