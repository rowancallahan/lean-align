import MapperFastAlgo
import MapperMzWords

/-!
# Compact genome: 2 bits per letter plus the exact non-ACGT runs

`PGen`: blocks of 64 letters, 17 bytes each (one cache line holds a block): a
flag byte, 1 when the block lies inside the genome and is all ACGT, then the 2-bit
codes (A0 C1 G2 T3), letter `i` in bits `2·(i % 4)` of byte `i % 64 / 4`.
Outside flagged blocks the byte comes from the run list `ex` (LE `UInt32`
triples `start, stop, byte`, increasing).  A `PGen` is the window `[o, o + n)` of
these blocks, so chromosomes are views into one packed concatenated genome
(`view`, no copies).  `PGen.get P i` is the byte at `o + i` for `i < n`, else 0
(as `ByteArray.get!`).

The builder `pack` is not trusted: `checkPG P G = true → Rep P G` (same size,
same byte at every index).  Under `Rep`, the genome-reading loops (`hammingP`,
`fwdMisP`, `bwdMisP`, `eqRunP`) equal the byte versions they copy.
-/

namespace MapSpec.Fast

structure PGen where
  n : Nat
  o : Nat
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

/-- Byte at place `i` of the blocks (no window) outside the all-ACGT blocks. -/
def PGen.slow (P : PGen) (i : Nat) : UInt8 :=
  let t := exFind P.ex i 64 0 (len32 P.ex / 3)
  if 0 < t && i < u32 P.ex (3 * (t - 1) + 1) then (u32 P.ex (3 * (t - 1) + 2)).toUInt8 else letter (P.code i)

/-- Byte at place `i` of the blocks. -/
@[inline] def PGen.raw (P : PGen) (i : Nat) : UInt8 :=
  if i < USize.size then
    -- machine-word arithmetic; the block offset is computed once (`raw_eq`)
    let u : USize := i.toUSize
    let b : USize := (u >>> (6 : USize)) * (17 : USize)
    let k : USize := b + (1 : USize) + ((u >>> (2 : USize)) &&& (15 : USize))
    if P.w.get! b.toNat == 1 then
      letter ((P.w.get! k.toNat >>> ((u.toUInt8 &&& 3) <<< 1)) &&& 3)
    else P.slow i
  else if P.w.get! (17 * (i >>> 6)) == 1 then letter (P.code i) else P.slow i

@[inline] def PGen.get (P : PGen) (i : Nat) : UInt8 := if i < P.n then P.raw (P.o + i) else 0

/-- Letters `[o, o + n)` of `P` (shares its arrays). -/
def view (P : PGen) (o n : Nat) : PGen := { P with o := P.o + o, n }

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
def PB.finish (s : PB) : PGen := ⟨s.n, 0, if s.n % 4 == 0 then s.w else s.w.push s.cur, pack32 s.ex⟩

def pack (G : ByteArray) : PGen := (G.foldl PB.push (PB.init G.size)).finish

/-- `P` spells `G`: same size, same byte everywhere. -/
def Rep (P : PGen) (G : ByteArray) : Prop := P.n = G.size ∧ ∀ i, P.get i = G.get! i

theorem usizeLit (n : Nat) (h : n < 4294967296) : (OfNat.ofNat n : USize).toNat = n := by
  have : 4294967296 ≤ USize.size := by rcases USize.size_eq with e | e <;> omega
  exact USize.toNat_ofNat_of_lt' (by omega)

/-- The machine-word form of `raw` is the plain one. -/
theorem raw_eq (P : PGen) (i : Nat) :
    P.raw i = if P.w.get! (17 * (i >>> 6)) == 1 then letter (P.code i) else P.slow i := by
  unfold PGen.raw; split
  · next h =>
    have hs := USize.size_eq_two_pow
    have hb : (i.toUSize >>> (6 : USize) * (17 : USize)).toNat = 17 * (i >>> 6) := by
      rw [USize.toNat_mul, USize.toNat_shiftRight, USize.toNat_ofNat_of_lt' h, usizeLit 6 (by omega),
        usizeLit 17 (by omega), Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
      rw [hs] at h
      rcases System.Platform.numBits_eq with e | e <;> rw [e] at h ⊢ <;>
        simp only [Nat.reduceMod, Nat.reducePow] at h ⊢ <;> omega
    have hk : (i.toUSize >>> (6 : USize) * (17 : USize) + (1 : USize) +
        ((i.toUSize >>> (2 : USize)) &&& (15 : USize))).toNat = 17 * (i >>> 6) + 1 + ((i >>> 2) &&& 15) := by
      have e15 : ((i >>> 2) &&& 15) ≤ 15 := Nat.and_le_right
      rw [USize.toNat_add, USize.toNat_add, USize.toNat_mul, USize.toNat_and, USize.toNat_shiftRight,
        USize.toNat_shiftRight, USize.toNat_ofNat_of_lt' h, usizeLit 6 (by omega), usizeLit 17 (by omega),
        usizeLit 1 (by omega), usizeLit 2 (by omega), usizeLit 15 (by omega)]
      rw [Nat.shiftRight_eq_div_pow] at e15 ⊢
      rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
      rw [hs] at h
      rcases System.Platform.numBits_eq with e | e <;> rw [e] at h ⊢ <;>
        simp only [Nat.reduceMod, Nat.reducePow] at h e15 ⊢ <;> omega
    have h8 : i.toUSize.toUInt8 = i.toUInt8 := by
      apply UInt8.toNat_inj.1
      rw [USize.toNat_toUInt8, USize.toNat_ofNat_of_lt' h, UInt8.toNat_ofNat']
    simp only [hb, hk, h8]; rfl
  · rfl

theorem get!_out (G : ByteArray) (i : Nat) (h : G.size ≤ i) : G.get! i = 0 := by
  cases G with
  | mk a => simp only [ByteArray.get!, ByteArray.size] at *; rw [getElem!_neg a i (by omega)]; rfl

theorem get_out (P : PGen) (i : Nat) (hi : P.n ≤ i) : P.get i = 0 := by
  unfold PGen.get; rw [if_neg (by omega)]

def eqAll (P : PGen) (G : ByteArray) : (k i : Nat) → Bool
  | 0, _ => true
  | k + 1, i => P.get i == G.get! i && eqAll P G k (i + 1)

/-- The runtime check of a packed genome. -/
def checkPG (P : PGen) (G : ByteArray) : Bool := P.n == G.size && eqAll P G G.size 0

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
  refine ⟨h.1, fun i => ?_⟩
  by_cases hi : i < G.size
  · exact eqAll_ok P G _ 0 h.2 i (by omega) (by omega)
  · rw [get!_out G i (by omega)]; exact get_out P i (by omega)

/-! ## Genome-reading loops over `PGen`

The kernels are generic over `GRead` (pool/mapper/MapperGRead.lean); `PGen` is an
instance.  `SameG x y`: two genomes of any representations with the same size and
bytes; every kernel gives the same answer on both (`hamming_same`, …).  `Rep P G`
is `SameG P G`. -/

instance : GRead PGen := ⟨PGen.get, PGen.n⟩

/-- Same length, same byte at every index. -/
def SameG {G1 G2 : Type} [GRead G1] [GRead G2] (x : G1) (y : G2) : Prop :=
  GRead.size x = GRead.size y ∧ ∀ i, GRead.get x i = GRead.get y i

theorem Rep.same {P : PGen} {G : ByteArray} (h : Rep P G) : SameG P G := ⟨h.1, h.2⟩

section
variable {G1 G2 : Type} [GRead G1] [GRead G2] {x : G1} {y : G2} (h : SameG x y)
include h

theorem hamming_same (r : ByteArray) (a lim stop : Nat) : ∀ d i m, stop - i = d →
    hamming r x a lim i stop m = hamming r y a lim i stop m := by
  intro d
  induction d with
  | zero => intro i m hd; unfold hamming; rw [if_neg (by omega), if_neg (by omega)]
  | succ d ih =>
    intro i m hd
    unfold hamming
    have ih' := fun m => ih (i + 1) m (by omega)
    simp only [h.2, ih']

theorem fwdMis_same (r : ByteArray) (st stop : Nat) : ∀ d i k, stop - i = d →
    fwdMis r x st stop i k = fwdMis r y st stop i k := by
  intro d
  induction d with
  | zero => intro i k hd; unfold fwdMis; rw [if_neg (by omega), if_neg (by omega)]
  | succ d ih =>
    intro i k hd
    unfold fwdMis
    have ih' := fun k => ih (i + 1) k (by omega)
    simp only [h.2, ih']

theorem bwdMis_same (r : ByteArray) (st len lo : Nat) : ∀ d e k, e - lo = d →
    bwdMis r x st len lo e k = bwdMis r y st len lo e k := by
  intro d
  induction d with
  | zero => intro e k hd; unfold bwdMis; rw [if_neg (by omega), if_neg (by omega)]
  | succ d ih =>
    intro e k hd
    unfold bwdMis
    by_cases he : lo < e
    · have ih' := fun k => ih (e - 1) k (by omega)
      simp only [h.2, ih']
    · rw [if_neg he, if_neg he]

theorem eqRun_same (b : ByteArray) : ∀ k i j, eqRun x b i j k = eqRun y b i j k := by
  intro k
  induction k with
  | zero => intro i j; rfl
  | succ k ih => intro i j; simp only [eqRun, h.2, ih]

theorem hamming_same' (r : ByteArray) (a lim i stop m : Nat) :
    hamming r x a lim i stop m = hamming r y a lim i stop m := hamming_same h r a lim stop _ i m rfl

theorem fwdMis_same' (r : ByteArray) (st stop i k : Nat) : fwdMis r x st stop i k = fwdMis r y st stop i k :=
  fwdMis_same h r st stop _ i k rfl

theorem bwdMis_same' (r : ByteArray) (st len lo e k : Nat) : bwdMis r x st len lo e k = bwdMis r y st len lo e k :=
  bwdMis_same h r st len lo _ e k rfl

end

/-! The names used by codecs/PairPacked.lean (the kernels at `PGen`). -/

abbrev hammingP (r : ByteArray) (g : PGen) (a lim i stop m : Nat) : Nat := hamming r g a lim i stop m
abbrev fwdMisP (r : ByteArray) (g : PGen) (st stop i k : Nat) : Nat := fwdMis r g st stop i k
abbrev bwdMisP (r : ByteArray) (g : PGen) (st len lo e k : Nat) : Nat := bwdMis r g st len lo e k
abbrev eqRunP (a : PGen) (b : ByteArray) (i j k : Nat) : Bool := eqRun a b i j k

section
variable {P : PGen} {G : ByteArray} (h : Rep P G)
include h

theorem hammingP_eq' (r : ByteArray) (a lim i stop m : Nat) :
    hammingP r P a lim i stop m = hamming r G a lim i stop m := hamming_same' h.same r a lim i stop m

theorem fwdMisP_eq' (r : ByteArray) (st stop i k : Nat) : fwdMisP r P st stop i k = fwdMis r G st stop i k :=
  fwdMis_same' h.same r st stop i k

theorem bwdMisP_eq' (r : ByteArray) (st len lo e k : Nat) : bwdMisP r P st len lo e k = bwdMis r G st len lo e k :=
  bwdMis_same' h.same r st len lo e k

theorem eqRunP_eq (b : ByteArray) (k i j : Nat) : eqRunP P b i j k = eqRun G b i j k := eqRun_same h.same b k i j

theorem eqRunP_eqMz (b : ByteArray) : ∀ k i j, eqRunP P b i j k = Mz.eqRun G b i j k := by
  intro k
  induction k with
  | zero => intro i j; rfl
  | succ k ih => intro i j; simp only [eqRunP, eqRun, Mz.eqRun, ih] at *; rw [show GRead.get P i = G.get! i from h.2 i]

end

end MapSpec.Fast
