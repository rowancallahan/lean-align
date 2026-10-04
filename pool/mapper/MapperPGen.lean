import MapperFastAlgo
import MapperMzWords

/-!
# Compact genome: 2 bits per letter plus the exact non-ACGT runs

`PGen`: blocks of 64 letters, 17 bytes each (one cache line holds a block): a
flag byte, 1 when the block lies inside the genome and is all ACGT, then the 2-bit
codes (A0 C1 G2 T3), letter `i` in bits `2·(i % 4)` of byte `i % 64 / 4`.
Outside flagged blocks the byte comes from the run list `ex` (LE `UInt32`
triples `start, stop, byte`, increasing).  `PGen.get P i` is the byte at `i`, and
0 past the end (as `ByteArray.get!`) when no flag 1 reaches past the end (`tailOk`).

The builder `pack` is not trusted: `checkPG P G = true → Rep P G` (same size,
same byte at every index).  Under `Rep`, the genome-reading loops (`hammingP`,
`fwdMisP`, `bwdMisP`, `eqRunP`) equal the byte versions they copy.
-/

namespace MapSpec.Fast

structure PGen where
  n : Nat
  w : ByteArray
  ex : ByteArray
deriving Inhabited

/-- A0 C1 G2 T3 ↦ the ASCII letter. -/
@[inline] def letter (c : UInt8) : UInt8 := ((0x54474341 : UInt32) >>> (c.toUInt32 <<< 3)).toUInt8

/-- Last run with start `≤ i` among runs `[lo, hi)` (binary search; `f` bounds the steps). -/
def exFind (ex : ByteArray) (i : Nat) : (f lo hi : Nat) → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo < hi then
      let m := (lo + hi) / 2
      if u32 ex (3 * m) ≤ i then exFind ex i f (m + 1) hi else exFind ex i f lo m
    else lo

/-- 2-bit code of letter `i`. -/
@[inline] def PGen.code (P : PGen) (i : Nat) : UInt8 :=
  (P.w.get! (17 * (i >>> 6) + 1 + ((i >>> 2) &&& 15)) >>> ((i.toUInt8 &&& 3) <<< 1)) &&& 3

/-- Byte at `i` outside the all-ACGT blocks. -/
def PGen.slow (P : PGen) (i : Nat) : UInt8 :=
  if i < P.n then
    let t := exFind P.ex i 64 0 (len32 P.ex / 3)
    if 0 < t && i < u32 P.ex (3 * (t - 1) + 1) then (u32 P.ex (3 * (t - 1) + 2)).toUInt8 else letter (P.code i)
  else 0

/-- Flag 1: block `i / 64` lies inside the genome and is all ACGT (a missing flag
reads 0, so no separate bounds test). -/
@[inline] def PGen.get (P : PGen) (i : Nat) : UInt8 :=
  if P.w.get! (17 * (i >>> 6)) == 1 then letter (P.code i) else P.slow i

/-- Builder state (not trusted; see `checkPG`): letters so far, blocks, the byte
being filled, the current block's flag and its place, runs, previous byte. -/
structure PB where
  n : Nat := 0
  w : ByteArray
  cur : UInt8 := 0
  f : UInt8 := 1
  fpos : Nat := 0
  ex : Array UInt32 := #[]
  prev : UInt8 := 65

/-- Empty builder with room for `cap` letters (untouched capacity is not resident). -/
def PB.init (cap : Nat) : PB := { w := .emptyWithCapacity (17 * (cap / 64 + 1)) }

/-- Append letter `v` (fields taken apart so the arrays are updated in place). -/
def PB.push : PB → UInt8 → PB
  | ⟨n, w, cur, f, fpos, ex, prev⟩, v =>
    let fpos := if n % 64 == 0 then w.size else fpos
    let w := if n % 64 == 0 then w.push 0 else w
    let cur := cur ||| ((c2 v).toUInt8 <<< (2 * (n % 4)).toUInt8)
    let odd := !acgt v
    let ex := if !odd then ex else if n > 0 && prev == v then ex.set! (ex.size - 2) (n + 1).toUInt32
      else ((ex.push n.toUInt32).push (n + 1).toUInt32).push v.toUInt32
    let f := if odd then 0 else f
    let (w, cur) := if n % 4 == 3 then (w.push cur, 0) else (w, cur)
    let (w, f) := if n % 64 == 63 then (w.set! fpos f, 1) else (w, f)
    ⟨n + 1, w, cur, f, fpos, ex, v⟩

/-- A partial last block keeps flag 0 (slow path). -/
def PB.finish (s : PB) : PGen := ⟨s.n, if s.n % 4 == 0 then s.w else s.w.push s.cur, pack32 s.ex⟩

def pack (G : ByteArray) : PGen := (G.foldl PB.push (PB.init G.size)).finish

/-- `P` spells `G`: same size, same byte everywhere. -/
def Rep (P : PGen) (G : ByteArray) : Prop := P.n = G.size ∧ ∀ i, P.get i = G.get! i

theorem get!_out (G : ByteArray) (i : Nat) (h : G.size ≤ i) : G.get! i = 0 := by
  cases G with
  | mk a => simp only [ByteArray.get!, ByteArray.size] at *; rw [getElem!_neg a i (by omega)]; rfl

/-- No block flag 1 covers a place `≥ n`. -/
def tailOk (P : PGen) : Bool :=
  decide (P.w.size ≤ 17 * (P.n / 64)) ||
    (decide (P.w.size ≤ 17 * (P.n / 64) + 17) && P.w.get! (17 * (P.n / 64)) != 1)

theorem get_out (P : PGen) (h : tailOk P = true) (i : Nat) (hi : P.n ≤ i) : P.get i = 0 := by
  have hs : i >>> 6 = i / 64 := by rw [Nat.shiftRight_eq_div_pow]
  have hb : P.w.get! (17 * (i >>> 6)) ≠ 1 := by
    rw [hs]
    simp only [tailOk, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    by_cases e : i / 64 = P.n / 64
    · rcases h with h | h
      · rw [get!_out _ _ (by omega)]; decide
      · rw [e]; exact h.2
    · have : P.n / 64 < i / 64 := by
        have := Nat.div_le_div_right (c := 64) hi; omega
      rcases h with h | h <;> (rw [get!_out _ _ (by omega)]; decide)
  unfold PGen.get PGen.slow
  rw [if_neg (by simpa using hb), if_neg (by omega)]

def eqAll (P : PGen) (G : ByteArray) : (k i : Nat) → Bool
  | 0, _ => true
  | k + 1, i => P.get i == G.get! i && eqAll P G k (i + 1)

/-- The runtime check of a packed genome. -/
def checkPG (P : PGen) (G : ByteArray) : Bool := P.n == G.size && tailOk P && eqAll P G G.size 0

theorem eqAll_ok (P : PGen) (G : ByteArray) : ∀ k i, eqAll P G k i = true → ∀ j, i ≤ j → j < i + k →
    P.get j = G.get! j := by
  intro k
  induction k with
  | zero => intro i _ j _ _; omega
  | succ k ih =>
    intro i h j h1 h2
    simp only [eqAll, Bool.and_eq_true, beq_iff_eq] at h
    by_cases e : j = i
    · subst e; exact h.1
    · exact ih (i + 1) h.2 j (by omega) (by omega)

theorem checkPG_ok (P : PGen) (G : ByteArray) (h : checkPG P G = true) : Rep P G := by
  simp only [checkPG, Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1.1, fun i => ?_⟩
  by_cases hi : i < G.size
  · exact eqAll_ok P G _ 0 h.2 i (by omega) (by omega)
  · rw [get!_out G i (by omega)]; exact get_out P h.1.2 i (by omega)

/-! ## Genome-reading loops over `PGen` (copies of the byte versions) -/

def hammingP (r : ByteArray) (g : PGen) (a lim : Nat) (i stop m : Nat) : Nat :=
  if i < stop then
    if r.get! i != g.get (a + i) then
      if lim < m + 1 then m + 1 else hammingP r g a lim (i + 1) stop (m + 1)
    else hammingP r g a lim (i + 1) stop m
  else m
termination_by stop - i

def fwdMisP (r : ByteArray) (g : PGen) (st stop : Nat) (i k : Nat) : Nat :=
  if i < stop then
    if r.get! i != g.get (st + i) then (if k ≤ 1 then i else fwdMisP r g st stop (i + 1) (k - 1))
    else fwdMisP r g st stop (i + 1) k
  else stop
termination_by stop - i

def bwdMisP (r : ByteArray) (g : PGen) (st len lo : Nat) (e k : Nat) : Nat :=
  if lo < e then
    if r.get! (e - 1) != g.get (st + len + (e - 1) - r.size) then
      (if k ≤ 1 then e else bwdMisP r g st len lo (e - 1) (k - 1))
    else bwdMisP r g st len lo (e - 1) k
  else lo
termination_by e - lo

/-- `G[i, i+k) = R[j, j+k)`. -/
def eqRunP (a : PGen) (b : ByteArray) (i j : Nat) : (k : Nat) → Bool
  | 0 => true
  | k + 1 => a.get i == b.get! j && eqRunP a b (i + 1) (j + 1) k

section
variable {P : PGen} {G : ByteArray} (h : Rep P G)
include h

theorem hammingP_eq (r : ByteArray) (a lim stop : Nat) : ∀ d i m, stop - i = d →
    hammingP r P a lim i stop m = hamming r G a lim i stop m := by
  intro d
  induction d with
  | zero => intro i m hd; unfold hammingP hamming; rw [if_neg (by omega), if_neg (by omega)]
  | succ d ih =>
    intro i m hd
    unfold hammingP hamming
    have e : stop - (i + 1) = d := by omega
    have ih' := fun m => ih (i + 1) m e
    simp only [h.2, ih']

theorem fwdMisP_eq (r : ByteArray) (st stop : Nat) : ∀ d i k, stop - i = d →
    fwdMisP r P st stop i k = fwdMis r G st stop i k := by
  intro d
  induction d with
  | zero => intro i k hd; unfold fwdMisP fwdMis; rw [if_neg (by omega), if_neg (by omega)]
  | succ d ih =>
    intro i k hd
    unfold fwdMisP fwdMis
    have e : stop - (i + 1) = d := by omega
    have ih' := fun k => ih (i + 1) k e
    simp only [h.2, ih']

theorem bwdMisP_eq (r : ByteArray) (st len lo : Nat) : ∀ d e k, e - lo = d →
    bwdMisP r P st len lo e k = bwdMis r G st len lo e k := by
  intro d
  induction d with
  | zero => intro e k hd; unfold bwdMisP bwdMis; rw [if_neg (by omega), if_neg (by omega)]
  | succ d ih =>
    intro e k hd
    unfold bwdMisP bwdMis
    by_cases he : lo < e
    · have e' : e - 1 - lo = d := by omega
      have ih' := fun k => ih (e - 1) k e'
      simp only [h.2, ih']
    · rw [if_neg he, if_neg he]

theorem hammingP_eq' (r : ByteArray) (a lim i stop m : Nat) :
    hammingP r P a lim i stop m = hamming r G a lim i stop m := hammingP_eq h r a lim stop _ i m rfl

theorem fwdMisP_eq' (r : ByteArray) (st stop i k : Nat) : fwdMisP r P st stop i k = fwdMis r G st stop i k :=
  fwdMisP_eq h r st stop _ i k rfl

theorem bwdMisP_eq' (r : ByteArray) (st len lo e k : Nat) : bwdMisP r P st len lo e k = bwdMis r G st len lo e k :=
  bwdMisP_eq h r st len lo _ e k rfl

theorem eqRunP_eq (b : ByteArray) : ∀ k i j, eqRunP P b i j k = eqRun G b i j k := by
  intro k
  induction k with
  | zero => intro i j; rfl
  | succ k ih => intro i j; simp only [eqRunP, eqRun, h.2, ih]

theorem eqRunP_eqMz (b : ByteArray) : ∀ k i j, eqRunP P b i j k = Mz.eqRun G b i j k := by
  intro k
  induction k with
  | zero => intro i j; rfl
  | succ k ih => intro i j; simp only [eqRunP, Mz.eqRun, h.2, ih]

end

end MapSpec.Fast
