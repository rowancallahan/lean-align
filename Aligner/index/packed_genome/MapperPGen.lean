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

/-! `exFind` on machine words (compiled code only): `exFind_eq_exFindF` (`@[csimp]`). The run starts are read by
`pgGet` at a `USize` offset and compared as `UInt32`; taken when the letter index is below `2^32` and the run
count below `2^28` (the guard uses `2^32 − 1`: a literal ≥ `2^32` would be rebuilt by GMP at every call). -/

theorem exLit (n : Nat) (h : n < 4294967296) : (OfNat.ofNat n : USize).toNat = n := by
  have : 4294967296 ≤ USize.size := by rcases USize.size_eq with e | e <;> omega
  exact USize.toNat_ofNat_of_lt' (by omega)

/-- `u32 B k` at a machine-word index (`u32W_eq`). -/
@[inline] def u32W (B : ByteArray) (k : USize) : UInt32 :=
  let j := 4 * k
  (pgGet B j).toUInt32 ||| ((pgGet B (j + 1)).toUInt32 <<< 8) ||| ((pgGet B (j + 2)).toUInt32 <<< 16) |||
    ((pgGet B (j + 3)).toUInt32 <<< 24)

theorem u32W_eq (B : ByteArray) (k : USize) (hk : k.toNat < 2 ^ 30) : (u32W B k).toNat = u32 B k.toNat := by
  have h4 : (4 * k).toNat = 4 * k.toNat := by
    rw [USize.toNat_mul, show (4 : USize).toNat = 4 from exLit 4 (by omega),
      Nat.mod_eq_of_lt (by have := pgu_pow; omega)]
  have e : ∀ c : Nat, c < 4 → (4 * k + (OfNat.ofNat c : USize)).toNat = 4 * k.toNat + c := fun c hc => by
    rw [pgu_add _ _ (by rw [h4, exLit c (by omega)]; omega), h4, exLit c (by omega)]
  unfold u32W u32
  simp only [pgGet_eq, h4, e 1 (by omega), e 2 (by omega), e 3 (by omega)]

/-- `exFind` with `lo`, `hi` in `USize` and the letter index in `UInt32` (`exFindU_eq`). -/
def exFindU (ex : ByteArray) (i : UInt32) : (f : Nat) → (lo hi : USize) → USize
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo < hi then
      let m := (lo + hi) / 2
      if u32W ex (3 * m) ≤ i then exFindU ex i f (m + 1) hi else exFindU ex i f lo m
    else lo

theorem exFindU_eq (ex : ByteArray) (iU : UInt32) (i : Nat) (hi : iU.toNat = i) :
    ∀ f (loU hiU : USize), hiU.toNat < 2 ^ 28 → loU.toNat ≤ hiU.toNat →
      (exFindU ex iU f loU hiU).toNat = exFind ex i f loU.toNat hiU.toNat
  | 0, _, _, _, _ => rfl
  | f + 1, loU, hiU, hh, hl => by
    have hN := pgu_pow
    rw [exFindU, exFind]
    by_cases hlt : loU.toNat < hiU.toNat
    · have hlt' : loU < hiU := hlt
      rw [if_pos hlt', if_pos hlt]
      simp only []
      have em : ((loU + hiU) / 2).toNat = (loU.toNat + hiU.toNat) / 2 := by
        rw [USize.toNat_div, pgu_add _ _ (by omega), show (2 : USize).toNat = 2 from exLit 2 (by omega)]
      have e3 : (3 * ((loU + hiU) / 2)).toNat = 3 * ((loU.toNat + hiU.toNat) / 2) := by
        rw [USize.toNat_mul, em, show (3 : USize).toNat = 3 from exLit 3 (by omega),
          Nat.mod_eq_of_lt (by omega)]
      have ec : (u32W ex (3 * ((loU + hiU) / 2)) ≤ iU) = (u32 ex (3 * ((loU.toNat + hiU.toNat) / 2)) ≤ i) := by
        rw [← e3, ← u32W_eq ex _ (by rw [e3]; omega), ← hi]
        exact propext UInt32.le_iff_toNat_le
      by_cases hc : u32 ex (3 * ((loU.toNat + hiU.toNat) / 2)) ≤ i
      · have hc' : u32W ex (3 * ((loU + hiU) / 2)) ≤ iU := by rw [ec]; exact hc
        rw [if_pos hc', if_pos hc]
        have e1 : ((loU + hiU) / 2 + 1).toNat = (loU.toNat + hiU.toNat) / 2 + 1 := by
          rw [pgu_add _ _ (by rw [em, pgu_one]; omega), em, pgu_one]
        rw [exFindU_eq ex iU i hi f _ _ hh (by rw [e1]; omega), e1]
      · have hc' : ¬ u32W ex (3 * ((loU + hiU) / 2)) ≤ iU := by rw [ec]; exact hc
        rw [if_neg hc', if_neg hc, exFindU_eq ex iU i hi f _ _ (by rw [em]; omega) (by rw [em]; omega), em]
    · have hlt' : ¬ loU < hiU := hlt
      rw [if_neg hlt', if_neg hlt]

/-- `exFind` for the compiled code (`exFind_eq_exFindF`). -/
@[inline] def exFindF (ex : ByteArray) (i f lo hi : Nat) : Nat :=
  if i < 4294967295 ∧ hi < 268435456 ∧ lo ≤ hi then
    (exFindU ex i.toUInt32 f lo.toUSize hi.toUSize).toNat
  else exFindS ex i f lo hi
where
  /-- `exFind` (its slow path; not rewritten by `csimp`). -/
  exFindS (ex : ByteArray) (i : Nat) : (f lo hi : Nat) → Nat
    | 0, lo, _ => lo
    | f + 1, lo, hi =>
      if lo < hi then
        let m := (lo + hi) / 2
        if u32 ex (3 * m) ≤ i then exFindS ex i f (m + 1) hi else exFindS ex i f lo m
      else lo

theorem exFindS_eq (ex : ByteArray) (i : Nat) : ∀ f lo hi, exFindF.exFindS ex i f lo hi = exFind ex i f lo hi
  | 0, _, _ => rfl
  | f + 1, lo, hi => by
    rw [exFindF.exFindS, exFind]
    simp only []
    split
    · split
      · exact exFindS_eq ex i f _ _
      · exact exFindS_eq ex i f _ _
    · rfl

@[csimp] theorem exFind_eq_exFindF : @exFind = @exFindF := by
  funext ex i f lo hi
  unfold exFindF
  split
  · rename_i h
    rw [exFindU_eq ex i.toUInt32 i (UInt32.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le h.1 (by decide))) f _ _ (by rw [pgu_n _ (by omega)]; omega)
      (by rw [pgu_n _ (by omega), pgu_n _ (by omega)]; omega), pgu_n _ (by omega), pgu_n _ (by omega)]
  · exact (exFindS_eq ex i f lo hi).symm

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

/-! `PGen.raw` on machine words (compiled code only): `raw_eq_rawF` (`@[csimp]`) replaces the
`i < USize.size` test (a big-number comparison per letter) by `i < 2^32 - 1` and reads the two
bytes with `uget` (`rawU`); placed before every reader of `PGen.raw`. -/

/-- `PGen.raw` at a machine-word place. -/
@[inline] def rawU (P : PGen) (u : USize) : UInt8 :=
  let b : USize := (u >>> (6 : USize)) * (17 : USize)
  let k : USize := b + (1 : USize) + ((u >>> (2 : USize)) &&& (15 : USize))
  if pgGet P.w b == 1 then letter ((pgGet P.w k >>> ((u.toUInt8 &&& 3) <<< 1)) &&& 3) else P.slow u.toNat

theorem rawU_eq (P : PGen) (u : USize) : rawU P u = P.raw u.toNat := by
  unfold rawU PGen.raw
  have e : u.toNat.toUSize = u := USize.ofNat_toNat
  rw [if_pos (USize.toNat_lt_size u)]
  simp only [e, pgGet_eq]

/-- `PGen.raw` (its slow path; not rewritten by `csimp`). -/
def rawS (P : PGen) (i : Nat) : UInt8 :=
  if i < USize.size then
    let u : USize := i.toUSize
    let b : USize := (u >>> (6 : USize)) * (17 : USize)
    let k : USize := b + (1 : USize) + ((u >>> (2 : USize)) &&& (15 : USize))
    if P.w.get! b.toNat == 1 then
      letter ((P.w.get! k.toNat >>> ((u.toUInt8 &&& 3) <<< 1)) &&& 3)
    else P.slow i
  else if P.w.get! (17 * (i >>> 6)) == 1 then letter (P.code i) else P.slow i

/-- `PGen.raw` for the compiled code (`raw_eq_rawF`). -/
@[inline] def rawF (P : PGen) (i : Nat) : UInt8 :=
  if i < 4294967295 then rawU P i.toUSize else rawS P i

@[csimp] theorem raw_eq_rawF : @PGen.raw = @rawF := by
  funext P i
  unfold rawF; split
  · rw [rawU_eq, pgu_n i (by omega)]
  · rfl

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

/-- `PGen.get` at a machine-word index (`PGen.getW_eq`, when `o + n < 2^32 − 1`). -/
@[inline] def PGen.getW (P : PGen) (u : USize) : UInt8 :=
  if u < P.n.toUSize then rawU P (P.o.toUSize + u) else 0

theorem PGen.getW_eq (P : PGen) (u : USize) (h : decide (P.o + P.n < 4294967295) = true) :
    P.getW u = P.get u.toNat := by
  simp only [decide_eq_true_eq] at h
  have en : P.n.toUSize.toNat = P.n := pgu_n _ (by omega)
  have eo : P.o.toUSize.toNat = P.o := pgu_n _ (by omega)
  have hlt : (u < P.n.toUSize) ↔ (u.toNat < P.n) := by
    rw [show (u < P.n.toUSize) = (u.toNat < P.n.toUSize.toNat) from rfl, en]
  unfold PGen.getW PGen.get
  by_cases hu : u.toNat < P.n
  · have ea : (P.o.toUSize + u).toNat = P.o + u.toNat := by rw [pgu_add _ _ (by rw [eo]; omega), eo]
    rw [if_pos (hlt.mpr hu), if_pos hu, rawU_eq, ea]
  · rw [if_neg (fun h => hu (hlt.mp h)), if_neg hu]

instance : GRead PGen where
  get := PGen.get
  size := PGen.n
  ok P := decide (P.o + P.n < 4294967295)
  getW := PGen.getW
  getW_eq P u h := PGen.getW_eq P u h

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

theorem hamming_same' (r : ByteArray) (a lim i stop m : Nat) :
    hamming r x a lim i stop m = hamming r y a lim i stop m := hamming_same h r a lim stop _ i m rfl

theorem fwdMis_same' (r : ByteArray) (st stop i k : Nat) : fwdMis r x st stop i k = fwdMis r y st stop i k :=
  fwdMis_same h r st stop _ i k rfl

theorem bwdMis_same' (r : ByteArray) (st len lo e k : Nat) : bwdMis r x st len lo e k = bwdMis r y st len lo e k :=
  bwdMis_same h r st len lo _ e k rfl

end

/-! The names used by codecs/PairPacked.lean (the kernels at `PGen`). -/

abbrev eqRunP (a : PGen) (b : ByteArray) (i j k : Nat) : Bool := eqRun a b i j k

section
variable {P : PGen} {G : ByteArray} (h : Rep P G)
include h

theorem eqRunP_eqMz (b : ByteArray) : ∀ k i j, eqRunP P b i j k = Mz.eqRun G b i j k := by
  intro k
  induction k with
  | zero => intro i j; rfl
  | succ k ih => intro i j; simp only [eqRunP, eqRun, Mz.eqRun, ih] at *; rw [show GRead.get P i = G.get! i from h.2 i]

end

end MapSpec.Fast
