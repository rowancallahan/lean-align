import ReadTrim

/-!
# Adapter trimming

A read whose fragment is shorter than the read runs on into the sequencing adapter. `cutAdapter`
cuts the read (letters and qualities together) at the FIRST position where the adapter starts.

`matchesAt adapter minLen maxErr read i` (the spec): compare the read from `i` on with the adapter,
over `len = min |adapter| (|read| - i)` letters (the whole adapter, or the part of it that fits
before the read's end). It matches when `i` is in the read, `len ≥ minLen`, and the number of
mismatches is at most `maxErr` when the whole adapter fits, 0 when only a prefix of it fits.

Theorems (`cut_*` below), for `cutPos adapter minLen maxErr read`:
  1. the kept letters and qualities are prefixes of the input;
  2. if it cuts (`cutPos < |read|`), the adapter matches at `cutPos`;
  3. no position before `cutPos` matches;
  4. if it does not cut (`cutPos = |read|`), no position matches.

`cutPos` is a scan over the bytes with no allocation; `fastMatchesAt_eq` proves its per-position
test equal to `matchesAt`. The compiled code runs `cutPosF` instead (`@[csimp] cutPos_eq_cutPosF`): the same
scan with machine-word (`USize`) counters and one-compare byte reads, proved equal for reads and adapters
shorter than 2^30.
-/

namespace AdapterTrim

/-- Illumina TruSeq adapter (both mates), first 13 letters. -/
def truSeq : ByteArray := "AGATCGGAAGAGC".toUTF8

/-! ## Spec -/

/-- Number of `j < len` with `read[i + j] ≠ adapter[j]`. -/
def mismatches (adapter read : ByteArray) (i len : Nat) : Nat :=
  ((List.range len).filter fun j => read[i + j]! != adapter[j]!).length

/-- The adapter (or, near the read's end, a prefix of it at least `minLen` long) starts at `i`. -/
def matchesAt (adapter : ByteArray) (minLen maxErr : Nat) (read : ByteArray) (i : Nat) : Bool :=
  let len := min adapter.size (read.size - i)
  i < read.size && minLen ≤ len &&
    mismatches adapter read i len ≤ (if len = adapter.size then maxErr else 0)

/-! ## Fast scan -/

/-- `c` + mismatches over adapter positions `j, …, j + k - 1` is at most `lim`; stops at the first
mismatch over the limit. -/
def mmLoop (adapter read : ByteArray) (i lim : Nat) : (k j c : Nat) → Bool
  | 0, _, c => c ≤ lim
  | k + 1, j, c =>
    let c' := if read[i + j]! != adapter[j]! then c + 1 else c
    if lim < c' then false else mmLoop adapter read i lim k (j + 1) c'

def fastMatchesAt (adapter : ByteArray) (minLen maxErr : Nat) (read : ByteArray) (i : Nat) : Bool :=
  let len := min adapter.size (read.size - i)
  i < read.size && minLen ≤ len &&
    mmLoop adapter read i (if len = adapter.size then maxErr else 0) len 0 0

/-- First `j` in `[i, i + k)` where the adapter matches, else `i + k`. -/
def scan (adapter : ByteArray) (minLen maxErr : Nat) (read : ByteArray) : (k i : Nat) → Nat
  | 0, i => i
  | k + 1, i => if fastMatchesAt adapter minLen maxErr read i then i else scan adapter minLen maxErr read k (i + 1)

/-- Where the read is cut: the first matching position, or `read.size` (no cut). -/
def cutPos (adapter : ByteArray) (minLen maxErr : Nat) (read : ByteArray) : Nat :=
  scan adapter minLen maxErr read read.size 0

/-! ## Machine-word scan (compiled code only, `cutPos_eq_cutPosF`) -/

open ReadTrim (rtGet rtGet_eq rt_n rt_add rt_one rt_sub1)

theorem u_ne0 (k : USize) (h : k ≠ 0) : k.toNat ≠ 0 := fun e => h (USize.toNat_inj.mp (by rw [e]; rfl))

/-- `mmLoop` with `USize` counters. -/
def mmU (adapter read : ByteArray) (i lim k j c : USize) : Bool :=
  if h : k = 0 then c ≤ lim
  else
    let c' := if rtGet read (i + j) != rtGet adapter j then c + 1 else c
    if lim < c' then false else mmU adapter read i lim (k - 1) (j + 1) c'
termination_by k.toNat
decreasing_by have := u_ne0 k h; rw [rt_sub1 k h]; omega

/-- `fastMatchesAt` with `USize` counters (`aSize` = adapter size, `n` = read size). -/
@[inline] def matchU (adapter read : ByteArray) (minLen maxErr aSize n i : USize) : Bool :=
  let len := if aSize ≤ n - i then aSize else n - i
  let lim := if len = aSize then maxErr else 0
  -- skip: with at most 1 mismatch allowed, one of the first two letters must match (`mmLoop_two`)
  i < n && minLen ≤ len &&
    !(lim ≤ 1 && 2 ≤ len && rtGet read i != rtGet adapter 0 && rtGet read (i + 1) != rtGet adapter 1) &&
    mmU adapter read i lim len 0 0

/-- `scan` with `USize` counters. -/
def scanU (adapter read : ByteArray) (minLen maxErr aSize n k i : USize) : USize :=
  if h : k = 0 then i
  else if matchU adapter read minLen maxErr aSize n i then i
  else scanU adapter read minLen maxErr aSize n (k - 1) (i + 1)
termination_by k.toNat
decreasing_by have := u_ne0 k h; rw [rt_sub1 k h]; omega

theorem mmLoop_two (adapter read : ByteArray) (i lim k : Nat) (hl : lim ≤ 1)
    (h0 : (read[i]! != adapter[0]!) = true) (h1 : (read[i + 1]! != adapter[1]!) = true) :
    mmLoop adapter read i lim (k + 2) 0 0 = false := by
  simp only [mmLoop, Nat.add_zero, Nat.zero_add, h0, h1, ↓reduceIte]
  split
  · rfl
  · split
    · rfl
    · omega

theorem mmU_eq (adapter read : ByteArray) : ∀ (k : Nat) (kU i lim j c : USize), kU.toNat = k →
    i.toNat + j.toNat + k < 2 ^ 30 → c.toNat + k < 2 ^ 30 → lim.toNat < 2 ^ 30 →
    mmU adapter read i lim kU j c = mmLoop adapter read i.toNat lim.toNat k j.toNat c.toNat
  | 0, kU, i, lim, j, c, hk, _, _, _ => by
    have : kU = 0 := USize.toNat_inj.mp (by rw [hk]; rfl)
    rw [mmU]; simp [this, mmLoop, USize.le_iff_toNat_le]
  | k + 1, kU, i, lim, j, c, hk, hij, hc, hl => by
    have h0 : kU ≠ 0 := fun e => by rw [e] at hk; simp at hk
    have ek : (kU - 1).toNat = k := by rw [rt_sub1 kU h0, hk]; rfl
    have eij : (i + j).toNat = i.toNat + j.toNat := rt_add _ _ (by omega)
    have ej : (j + 1).toNat = j.toNat + 1 := by rw [rt_add _ _ (by rw [rt_one]; omega), rt_one]
    have ec : (c + 1).toNat = c.toNat + 1 := by rw [rt_add _ _ (by rw [rt_one]; omega), rt_one]
    rw [mmU]; simp only [h0, ↓reduceDIte]
    simp only [mmLoop, rtGet_eq, eij]
    by_cases hm : (read[i.toNat + j.toNat]! != adapter[j.toNat]!) = true
    · simp only [hm, ↓reduceIte, USize.lt_iff_toNat_lt, ec]
      split
      · rfl
      · rw [mmU_eq adapter read k _ i lim _ _ ek (by rw [ej]; omega) (by rw [ec]; omega) hl, ej, ec]
    · simp only [hm, Bool.false_eq_true, ↓reduceIte, USize.lt_iff_toNat_lt]
      split
      · rfl
      · rw [mmU_eq adapter read k _ i lim _ _ ek (by rw [ej]; omega) (by omega) hl, ej]

theorem matchU_eq (adapter read : ByteArray) (minLen maxErr aSize n i : USize) (ha : aSize.toNat = adapter.size)
    (hn : n.toNat = read.size) (hnb : read.size < 2 ^ 30) (hab : adapter.size < 2 ^ 30) (hm : maxErr.toNat < 2 ^ 30) :
    matchU adapter read minLen maxErr aSize n i = fastMatchesAt adapter minLen.toNat maxErr.toNat read i.toNat := by
  unfold matchU fastMatchesAt
  by_cases hi : i < n
  · have hi' : i.toNat < read.size := by rw [← hn]; exact USize.lt_iff_toNat_lt.mp hi
    have esub : (n - i).toNat = read.size - i.toNat := by
      rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by omega)), hn]
    have elen : (if aSize ≤ n - i then aSize else n - i).toNat = min adapter.size (read.size - i.toNat) := by
      split
      · rename_i h; rw [USize.le_iff_toNat_le, esub, ha] at h; rw [ha]; omega
      · rename_i h; rw [USize.le_iff_toNat_le, esub, ha] at h; rw [esub]; omega
    have eeq : ((if aSize ≤ n - i then aSize else n - i) = aSize) ↔ (min adapter.size (read.size - i.toNat) = adapter.size) := by
      rw [← USize.toNat_inj, elen, ha]
    have elim : (if (if aSize ≤ n - i then aSize else n - i) = aSize then maxErr else 0).toNat =
        (if min adapter.size (read.size - i.toNat) = adapter.size then maxErr.toNat else 0) := by
      by_cases h : min adapter.size (read.size - i.toNat) = adapter.size
      · simp only [eeq.mpr h, h, ↓reduceIte]
      · simp only [show ¬ _ from fun e => h (eeq.mp e), h, ↓reduceIte]; rfl
    dsimp only
    generalize hL : (if aSize ≤ n - i then aSize else n - i) = L at elen eeq elim
    have e0 : (0 : USize).toNat = 0 := rfl
    have hmm := mmU_eq adapter read _ L i _ 0 0 elen (by rw [e0]; omega) (by rw [e0]; omega)
      (by rw [elim]; split <;> omega)
    rw [hmm, elim, e0]
    have e1 : (i + 1).toNat = i.toNat + 1 := by rw [rt_add _ _ (by rw [rt_one]; omega), rt_one]
    simp only [rtGet_eq, e1, e0, hi, hi', USize.le_iff_toNat_le, elen, elim, decide_true, Bool.true_and]
    rw [show (1 : USize).toNat = 1 from rt_one, show (2 : USize).toNat = 2 from rt_n 2 (by decide)]
    generalize hM : min adapter.size (read.size - i.toNat) = M at *
    generalize hLim : (if M = adapter.size then maxErr.toNat else 0) = lim at *
    by_cases hpre : (lim ≤ 1 ∧ 2 ≤ M ∧ (read[i.toNat]! != adapter[0]!) = true ∧
        (read[i.toNat + 1]! != adapter[1]!) = true)
    · obtain ⟨p1, p2, p3, p4⟩ := hpre
      obtain ⟨k, rfl⟩ : ∃ k, M = k + 2 := ⟨M - 2, by omega⟩
      rw [mmLoop_two adapter read i.toNat lim k p1 p3 p4]
      simp [p1, p2, p3, p4]
    · have : (decide (lim ≤ 1) && decide (2 ≤ M) && (read[i.toNat]! != adapter[0]!) &&
          (read[i.toNat + 1]! != adapter[1]!)) = false := by
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
        by_cases a : lim ≤ 1 <;> by_cases b : 2 ≤ M <;> simp_all
        exact Classical.or_iff_not_imp_left.mpr hpre
      rw [this]; simp
  · have hi' : ¬ i.toNat < read.size := by rw [← hn]; exact fun h => hi (USize.lt_iff_toNat_lt.mpr h)
    simp [hi, hi']

theorem scanU_eq (adapter read : ByteArray) (minLen maxErr aSize n : USize) (ha : aSize.toNat = adapter.size)
    (hn : n.toNat = read.size) (hnb : read.size < 2 ^ 30) (hab : adapter.size < 2 ^ 30) (hm : maxErr.toNat < 2 ^ 30) :
    ∀ (k : Nat) (kU i : USize), kU.toNat = k → i.toNat + k < 2 ^ 30 →
    (scanU adapter read minLen maxErr aSize n kU i).toNat = scan adapter minLen.toNat maxErr.toNat read k i.toNat
  | 0, kU, i, hk, _ => by
    have : kU = 0 := USize.toNat_inj.mp (by rw [hk]; rfl)
    rw [scanU]; simp [this, scan]
  | k + 1, kU, i, hk, hi => by
    have h0 : kU ≠ 0 := fun e => by rw [e] at hk; simp at hk
    have ek : (kU - 1).toNat = k := by rw [rt_sub1 kU h0, hk]; rfl
    have ei : (i + 1).toNat = i.toNat + 1 := by rw [rt_add _ _ (by rw [rt_one]; omega), rt_one]
    rw [scanU]; simp only [h0, ↓reduceDIte]; rw [scan, matchU_eq adapter read minLen maxErr aSize n i ha hn hnb hab hm]
    split
    · rfl
    · rw [scanU_eq adapter read minLen maxErr aSize n ha hn hnb hab hm k _ _ ek (by rw [ei]; omega), ei]

theorem count_cons (p : Nat → Bool) (j k : Nat) :
    ((List.range' j (k + 1)).filter p).length = (if p j then 1 else 0) + ((List.range' (j + 1) k).filter p).length := by
  rw [List.range'_succ, List.filter_cons]
  split <;> simp_all <;> omega

theorem mmLoop_eq (adapter read : ByteArray) (i lim : Nat) : ∀ k j c,
    mmLoop adapter read i lim k j c =
      decide (c + ((List.range' j k).filter fun t => read[i + t]! != adapter[t]!).length ≤ lim)
  | 0, j, c => by simp [mmLoop]
  | k + 1, j, c => by
    rw [count_cons]
    simp only [mmLoop]
    rw [mmLoop_eq adapter read i lim k (j + 1)]
    split <;> split <;> simp_all <;> omega

theorem fastMatchesAt_eq (adapter : ByteArray) (minLen maxErr : Nat) (read : ByteArray) (i : Nat) :
    fastMatchesAt adapter minLen maxErr read i = matchesAt adapter minLen maxErr read i := by
  simp only [fastMatchesAt, matchesAt, mmLoop_eq, mismatches, List.range_eq_range', Nat.zero_add]

theorem scan_spec (adapter : ByteArray) (minLen maxErr : Nat) (read : ByteArray) : ∀ k i,
    i ≤ scan adapter minLen maxErr read k i ∧ scan adapter minLen maxErr read k i ≤ i + k ∧
    (scan adapter minLen maxErr read k i < i + k → matchesAt adapter minLen maxErr read (scan adapter minLen maxErr read k i) = true) ∧
    (∀ j, i ≤ j → j < scan adapter minLen maxErr read k i → matchesAt adapter minLen maxErr read j = false)
  | 0, i => by simp only [scan]; refine ⟨Nat.le_refl _, by omega, by omega, fun j h1 h2 => by omega⟩
  | k + 1, i => by
    simp only [scan]
    by_cases h : fastMatchesAt adapter minLen maxErr read i = true
    · simp only [h, ↓reduceIte]; rw [← fastMatchesAt_eq]
      exact ⟨Nat.le_refl _, by omega, fun _ => h, fun j h1 h2 => by omega⟩
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨a, b, c, d⟩ := scan_spec adapter minLen maxErr read k (i + 1)
      refine ⟨by omega, by omega, fun hl => c (by omega), fun j h1 h2 => ?_⟩
      by_cases hj : j = i
      · subst hj; rw [← fastMatchesAt_eq]; simpa using h
      · exact d j (by omega) h2

/-! ## Bit-parallel scan (shift-and; compiled code only, through `cutPosF`)

Bit `t` of `st0 p` (`st1 p`): the `t + 1` read letters ending at letter `p − 1` are the adapter's first `t + 1`
letters with no mismatch (at most one) (`st0_bit`, `st1_bit`). A start `s` with the whole adapter before the read's
end matches iff bit `m − 1` is set after `s + m` letters; a start nearer the end iff bit `n − s − 1` of the final
exact state is (`fastMatchesAt_saT`). `saLoop` keeps both states letter by letter and tests each start once
(`saLoop_eq`: `scan` with that test). -/

/-- Bits `t ∈ [j, j + k)` with `adapter[t] = c`. -/
def bmask (adapter : ByteArray) (c : UInt8) : (k j : Nat) → Nat
  | 0, _ => 0
  | k + 1, j => (if adapter[j]! == c then 2 ^ j else 0) ||| bmask adapter c k (j + 1)

theorem bmask_bit (adapter : ByteArray) (c : UInt8) : ∀ k j t,
    (bmask adapter c k j).testBit t = (decide (j ≤ t) && decide (t < j + k) && (adapter[t]! == c))
  | 0, j, t => by simp [bmask]; omega
  | k + 1, j, t => by
    rw [bmask, Nat.testBit_or, bmask_bit adapter c k (j + 1) t]
    by_cases hj : t = j
    · subst hj
      by_cases ha : (adapter[t]! == c) = true
      · simp [ha, Nat.testBit_two_pow]
      · simp only [ha, Bool.false_eq_true, ↓reduceIte, Nat.zero_testBit, Bool.and_false, Bool.or_false]
    · have e1 : (if adapter[j]! == c then 2 ^ j else 0 : Nat).testBit t = false := by
        split
        · rw [Nat.testBit_two_pow]; simp; omega
        · exact Nat.zero_testBit t
      rw [e1, Bool.false_or]
      by_cases h1 : j ≤ t <;> by_cases h2 : t < j + (k + 1) <;> simp [h1, h2] <;> omega

theorem mismatches_succ (adapter read : ByteArray) (s len : Nat) :
    mismatches adapter read s (len + 1) =
      mismatches adapter read s len + (if read[s + len]! != adapter[len]! then 1 else 0) := by
  unfold mismatches
  rw [List.range_succ, List.filter_append, List.length_append]
  split <;> simp_all

section sa
variable (adapter read : ByteArray)

/-- The exact state after `p` read letters. -/
def st0 : Nat → Nat
  | 0 => 0
  | p + 1 => ((st0 p <<< 1) ||| 1) &&& bmask adapter read[p]! adapter.size 0

/-- The one-mismatch state after `p` read letters. -/
def st1 : Nat → Nat
  | 0 => 0
  | p + 1 => (((st1 p <<< 1) ||| 1) &&& bmask adapter read[p]! adapter.size 0) |||
      (((st0 adapter read p <<< 1) ||| 1) &&& (2 ^ adapter.size - 1))

theorem shl1_bit (x t : Nat) : ((x <<< 1) ||| 1).testBit t = (decide (t = 0) || (decide (1 ≤ t) && x.testBit (t - 1))) := by
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  rcases t with _ | t
  · simp
  · have : (1 : Nat).testBit (t + 1) = false := by
      rw [Nat.testBit_succ]; simp
    rw [this]; simp

theorem mism_zero (s : Nat) : mismatches adapter read s 0 = 0 := by simp [mismatches]

theorem mism_one (s : Nat) : mismatches adapter read s 1 = if read[s]! != adapter[0]! then 1 else 0 := by
  rw [mismatches_succ, mism_zero, Nat.add_zero, Nat.zero_add]

theorem bne_iff' (x y : UInt8) : (x != y) = true ↔ x ≠ y := bne_iff_ne

theorem st0_bit : ∀ p t, (st0 adapter read p).testBit t = true ↔
    (t < adapter.size ∧ t < p ∧ mismatches adapter read (p - 1 - t) (t + 1) = 0)
  | 0, t => by simp [st0]
  | p + 1, t => by
    rw [st0, Nat.testBit_and, shl1_bit, bmask_bit]
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
    rcases t with _ | u
    · rw [mism_one, show p + 1 - 1 - 0 = p by omega]
      by_cases hm : read[p]! = adapter[0]!
      · have : (read[p]! != adapter[0]!) = false := by simp [hm]
        simp only [this]; simp [hm]
      · have : (read[p]! != adapter[0]!) = true := (bne_iff' _ _).mpr hm
        simp only [this]; simp; intro _ h; exact hm h.symm
    · rw [show u + 1 - 1 = u by omega, st0_bit p u, show p + 1 - 1 - (u + 1) = p - 1 - u by omega,
        mismatches_succ adapter read (p - 1 - u) (u + 1)]
      by_cases hp : u < p
      · rw [show p - 1 - u + (u + 1) = p by omega]
        by_cases hm : read[p]! = adapter[u + 1]!
        · have : (read[p]! != adapter[u + 1]!) = false := by simp [hm]
          simp only [this, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; simp only [hm, and_true]; constructor
          · intro h; omega
          · intro h; omega
        · have : (read[p]! != adapter[u + 1]!) = true := (bne_iff' _ _).mpr hm
          simp only [this, ↓reduceIte]; constructor
          · intro h; exact absurd h.2.2.symm hm
          · intro h; omega
      · constructor
        · intro h; omega
        · intro h; omega

theorem st1_bit : ∀ p t, (st1 adapter read p).testBit t = true ↔
    (t < adapter.size ∧ t < p ∧ mismatches adapter read (p - 1 - t) (t + 1) ≤ 1)
  | 0, t => by simp [st1]
  | p + 1, t => by
    rw [st1, Nat.testBit_or, Nat.testBit_and, Nat.testBit_and, shl1_bit, shl1_bit, bmask_bit,
      Nat.testBit_two_pow_sub_one]
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
    rcases t with _ | u
    · rw [mism_one, show p + 1 - 1 - 0 = p by omega]
      constructor
      · intro h; rcases h with h | h
        · exact ⟨by omega, by omega, by split <;> omega⟩
        · exact ⟨h.2, by omega, by split <;> omega⟩
      · intro h; exact Or.inr ⟨Or.inl rfl, h.1⟩
    · rw [show u + 1 - 1 = u by omega, st1_bit p u, st0_bit adapter read p u,
        show p + 1 - 1 - (u + 1) = p - 1 - u by omega, mismatches_succ adapter read (p - 1 - u) (u + 1)]
      by_cases hp : u < p
      · rw [show p - 1 - u + (u + 1) = p by omega]
        by_cases hm : read[p]! = adapter[u + 1]!
        · have : (read[p]! != adapter[u + 1]!) = false := by simp [hm]
          simp only [this, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; simp only [hm, and_true]; constructor
          · intro h; omega
          · intro h; omega
        · have : (read[p]! != adapter[u + 1]!) = true := (bne_iff' _ _).mpr hm
          simp only [this, ↓reduceIte]; constructor
          · intro h; rcases h with h | h
            · exact absurd h.2.2.symm hm
            · omega
          · intro h; omega
      · constructor
        · intro h; omega
        · intro h; omega

/-- `scan` with any per-start test. -/
def scanP (T : Nat → Bool) : (k i : Nat) → Nat
  | 0, i => i
  | k + 1, i => if T i then i else scanP T k (i + 1)

theorem scanP_congr (T T' : Nat → Bool) : ∀ k i, (∀ j, i ≤ j → j < i + k → T j = T' j) → scanP T k i = scanP T' k i
  | 0, _, _ => rfl
  | k + 1, i, h => by
    simp only [scanP, h i (Nat.le_refl _) (by omega), scanP_congr T T' k (i + 1) (fun j h1 h2 => h j (by omega) (by omega))]

theorem scan_eq_scanP (minLen maxErr : Nat) (T : Nat → Bool) : ∀ k i,
    (∀ j, i ≤ j → j < i + k → fastMatchesAt adapter minLen maxErr read j = T j) →
      scan adapter minLen maxErr read k i = scanP T k i
  | 0, _, _ => rfl
  | k + 1, i, h => by
    simp only [scan, scanP, h i (Nat.le_refl _) (by omega),
      scan_eq_scanP minLen maxErr T k (i + 1) (fun j h1 h2 => h j (by omega) (by omega))]

/-- The test of start `s` by the states: bit `m − 1` after `s + m` letters (whole adapter), else bit `n − s − 1`
of the final exact state. -/
def saT (minLen maxErr s : Nat) : Bool :=
  if s + adapter.size ≤ read.size then
    decide (minLen ≤ adapter.size) &&
      (if maxErr = 0 then st0 adapter read (s + adapter.size) else st1 adapter read (s + adapter.size)).testBit
        (adapter.size - 1)
  else decide (minLen ≤ read.size - s) && (st0 adapter read read.size).testBit (read.size - s - 1)

theorem fastMatchesAt_saT (minLen maxErr : Nat) (hm : 0 < adapter.size) (he : maxErr ≤ 1) (s : Nat)
    (hs : s < read.size) : fastMatchesAt adapter minLen maxErr read s = saT adapter read minLen maxErr s := by
  rw [fastMatchesAt_eq]
  unfold matchesAt saT
  apply Bool.eq_iff_iff.mpr
  by_cases hf : s + adapter.size ≤ read.size
  · rw [if_pos hf, show min adapter.size (read.size - s) = adapter.size by omega]
    simp only [↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, hs, true_and]
    by_cases h0 : maxErr = 0
    · rw [if_pos h0, st0_bit, show s + adapter.size - 1 - (adapter.size - 1) = s by omega,
        show adapter.size - 1 + 1 = adapter.size by omega, h0]
      constructor
      · intro h; exact ⟨h.1, by omega, by omega, by omega⟩
      · intro h; exact ⟨h.1, by omega⟩
    · rw [if_neg h0, st1_bit, show s + adapter.size - 1 - (adapter.size - 1) = s by omega,
        show adapter.size - 1 + 1 = adapter.size by omega]
      constructor
      · intro h; exact ⟨h.1, by omega, by omega, by omega⟩
      · intro h; exact ⟨h.1, by omega⟩
  · rw [if_neg hf, show min adapter.size (read.size - s) = read.size - s by omega]
    simp only []
    rw [if_neg (show ¬ read.size - s = adapter.size by omega)]
    simp only [Bool.and_eq_true, decide_eq_true_eq, hs, true_and]
    rw [st0_bit, show read.size - 1 - (read.size - s - 1) = s by omega, show read.size - s - 1 + 1 = read.size - s by omega]
    constructor
    · intro h; exact ⟨h.1, by omega, by omega, by omega⟩
    · intro h; exact ⟨h.1, by omega⟩

/-- The scan by the two states, letter by letter (`k` letters left from `p`): start `p + 1 − m` is tested once the
state for `p + 1` letters is known; at the read's end the starts nearer the end are tested on the exact state. -/
def saLoop (minLen maxErr : Nat) : (k p e0 e1 : Nat) → Nat
  | 0, p, e0, _ =>
    scanP (fun s => decide (minLen ≤ read.size - s) && e0.testBit (read.size - s - 1))
      (read.size - (p + 1 - adapter.size)) (p + 1 - adapter.size)
  | k + 1, p, e0, e1 =>
    let b := bmask adapter read[p]! adapter.size 0
    let e0' := ((e0 <<< 1) ||| 1) &&& b
    let e1' := (((e1 <<< 1) ||| 1) &&& b) ||| (((e0 <<< 1) ||| 1) &&& (2 ^ adapter.size - 1))
    if decide (adapter.size ≤ p + 1) && decide (minLen ≤ adapter.size) &&
        (if maxErr = 0 then e0' else e1').testBit (adapter.size - 1) then p + 1 - adapter.size
    else saLoop minLen maxErr k (p + 1) e0' e1'

theorem saLoop_eq (minLen maxErr : Nat) (hm : 0 < adapter.size) : ∀ k p, p + k = read.size →
    saLoop adapter read minLen maxErr k p (st0 adapter read p) (st1 adapter read p) =
      scanP (saT adapter read minLen maxErr) (read.size - (p + 1 - adapter.size)) (p + 1 - adapter.size)
  | 0, p, hp => by
    rw [saLoop, show p = read.size by omega]
    apply scanP_congr
    intro j h1 h2
    unfold saT
    rw [if_neg (by omega)]
  | k + 1, p, hp => by
    simp only [saLoop]
    rw [show ((st0 adapter read p <<< 1) ||| 1) &&& bmask adapter read[p]! adapter.size 0 = st0 adapter read (p + 1) from rfl,
      show (((st1 adapter read p <<< 1) ||| 1) &&& bmask adapter read[p]! adapter.size 0) |||
        (((st0 adapter read p <<< 1) ||| 1) &&& (2 ^ adapter.size - 1)) = st1 adapter read (p + 1) from rfl,
      saLoop_eq minLen maxErr hm k (p + 1) (by omega)]
    by_cases hs : adapter.size ≤ p + 1
    · rw [show read.size - (p + 1 - adapter.size) = (read.size - (p + 1 + 1 - adapter.size)) + 1 by omega, scanP,
        show p + 1 + 1 - adapter.size = p + 1 - adapter.size + 1 by omega]
      have eT : saT adapter read minLen maxErr (p + 1 - adapter.size) =
          (decide (minLen ≤ adapter.size) &&
            (if maxErr = 0 then st0 adapter read (p + 1) else st1 adapter read (p + 1)).testBit (adapter.size - 1)) := by
        unfold saT
        rw [if_pos (by omega), show p + 1 - adapter.size + adapter.size = p + 1 by omega]
      rw [eT]
      simp only [hs, decide_true, Bool.true_and]
    · rw [show p + 1 + 1 - adapter.size = p + 1 - adapter.size by omega]
      simp [hs]

/-- `cutPos` by the states (`cutPos_eq_sa`, for an adapter of at least one letter and at most one mismatch). -/
theorem cutPos_eq_sa (minLen maxErr : Nat) (hm : 0 < adapter.size) (he : maxErr ≤ 1) :
    cutPos adapter minLen maxErr read = saLoop adapter read minLen maxErr read.size 0 0 0 := by
  unfold cutPos
  rw [scan_eq_scanP adapter read minLen maxErr (saT adapter read minLen maxErr) read.size 0
    (fun j _ h2 => fastMatchesAt_saT adapter read minLen maxErr hm he j (by omega))]
  have := saLoop_eq adapter read minLen maxErr hm read.size 0 (by omega)
  rw [show (0 : Nat) + 1 - adapter.size = 0 by omega] at this
  rw [show read.size - 0 = read.size by omega] at this
  exact this.symm

/-! ### The states on machine words -/

theorem bmask_lt (c : UInt8) : bmask adapter c adapter.size 0 < 2 ^ adapter.size := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [bmask_bit]; simp; omega

theorem bmask_other (c : UInt8) (hc : ∀ j, j < adapter.size → adapter[j]! ≠ c) : bmask adapter c adapter.size 0 = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [bmask_bit, Nat.zero_testBit]
  by_cases h : i < adapter.size
  · have := hc i h; simp [this]
  · simp; omega

theorem step_lt (x b m : Nat) (hb : b < 2 ^ m) : ((x <<< 1) ||| 1) &&& b < 2 ^ m := Nat.and_lt_two_pow _ hb

theorem st0_lt : ∀ p, st0 adapter read p < 2 ^ adapter.size
  | 0 => Nat.two_pow_pos _
  | p + 1 => step_lt _ _ _ (bmask_lt adapter _)

theorem st1_lt : ∀ p, st1 adapter read p < 2 ^ adapter.size
  | 0 => Nat.two_pow_pos _
  | p + 1 => Nat.or_lt_two_pow (step_lt _ _ _ (bmask_lt adapter _))
      (step_lt _ _ _ (Nat.sub_lt (Nat.two_pow_pos _) (by decide)))

theorem u64_step (x b : UInt64) (hx : x.toNat < 2 ^ 63) :
    (((x <<< (1 : UInt64)) ||| (1 : UInt64)) &&& b).toNat = ((x.toNat <<< 1) ||| 1) &&& b.toNat := by
  have hU : UInt64.size = 18446744073709551616 := rfl
  rw [UInt64.toNat_and, UInt64.toNat_or, UInt64.toNat_shiftLeft]
  rw [show (1 : UInt64).toNat = 1 from rfl, show (1 : Nat) % 64 = 1 from rfl, Nat.shiftLeft_eq,
    Nat.pow_one, Nat.mod_eq_of_lt (by omega)]

theorem u64_bit (x : UInt64) (k : Nat) (hk : k < 64) :
    (((x >>> k.toUInt64) &&& 1) != 0) = x.toNat.testBit k := by
  have hU : UInt64.size = 18446744073709551616 := rfl
  have ek : k.toUInt64.toNat % 64 = k := by rw [UInt64.toNat_ofNat_of_lt' (by omega)]; omega
  have e : ((x >>> k.toUInt64) &&& 1).toNat = x.toNat / 2 ^ k % 2 := by
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight, ek, show (1 : UInt64).toNat = 1 from rfl, Nat.and_one_is_mod,
      Nat.shiftRight_eq_div_pow]
  rw [Nat.testBit_eq_decide_div_mod_eq]
  apply Bool.eq_iff_iff.mpr
  rw [bne_iff_ne, ne_eq, ← UInt64.toNat_inj, e, show (0 : UInt64).toNat = 0 from rfl, decide_eq_true_eq]
  omega

/-- The machine-word letter mask: `A C G T` from the four masks, any other byte `0`. -/
@[inline] def bOf (bA bC bG bT : UInt64) (c : UInt8) : UInt64 :=
  if c == 65 then bA else if c == 67 then bC else if c == 71 then bG else if c == 84 then bT else 0

/-- `saLoop` on machine words (`saLoopU_eq`): states in `UInt64`, the letter index in `USize`. -/
def saLoopU (bA bC bG bT msk sh : UInt64) (m : USize) (ok1 e1q : Bool) (minLen : Nat) :
    (k : Nat) → (p : USize) → (e0 e1 : UInt64) → Nat
  | 0, p, e0, _ =>
    scanP (fun s => decide (minLen ≤ read.size - s) && e0.toNat.testBit (read.size - s - 1))
      (read.size - (p.toNat + 1 - adapter.size)) (p.toNat + 1 - adapter.size)
  | k + 1, p, e0, e1 =>
    let b := bOf bA bC bG bT (ReadTrim.rtGet read p)
    let e0' := ((e0 <<< (1 : UInt64)) ||| (1 : UInt64)) &&& b
    let e1' := (((e1 <<< (1 : UInt64)) ||| (1 : UInt64)) &&& b) ||| (((e0 <<< (1 : UInt64)) ||| (1 : UInt64)) &&& msk)
    if m ≤ p + 1 && ok1 && ((((if e1q then e1' else e0') >>> sh) &&& (1 : UInt64)) != 0) then (p + 1 - m).toNat
    else saLoopU bA bC bG bT msk sh m ok1 e1q minLen k (p + 1) e0' e1'

theorem saLoopU_eq (minLen maxErr : Nat) (bA bC bG bT msk sh : UInt64) (mU : USize)
    (hm0 : 0 < adapter.size) (hm : adapter.size < 64) (hn : read.size < 2 ^ 30)
    (hb : ∀ c, (bOf bA bC bG bT c).toNat = bmask adapter c adapter.size 0)
    (hmsk : msk.toNat = 2 ^ adapter.size - 1) (hsh : sh = (adapter.size - 1).toUInt64) (hmU : mU.toNat = adapter.size) :
    ∀ k (p : USize), p.toNat + k = read.size →
      saLoopU adapter read bA bC bG bT msk sh mU (decide (minLen ≤ adapter.size)) (decide (maxErr ≠ 0)) minLen k p
          (st0 adapter read p.toNat).toUInt64 (st1 adapter read p.toNat).toUInt64 =
        saLoop adapter read minLen maxErr k p.toNat (st0 adapter read p.toNat) (st1 adapter read p.toNat)
  | 0, p, _ => by
    have := st0_lt adapter read p.toNat
    have hU : UInt64.size = 18446744073709551616 := rfl
    have h2 : 2 ^ adapter.size ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
    rw [saLoopU, saLoop, UInt64.toNat_ofNat_of_lt' (by omega)]
  | k + 1, p, hp => by
    have hU : UInt64.size = 18446744073709551616 := rfl
    have h2 : 2 ^ adapter.size ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
    have l0 := st0_lt adapter read p.toNat
    have l1 := st1_lt adapter read p.toNat
    have e0 : (st0 adapter read p.toNat).toUInt64.toNat = st0 adapter read p.toNat :=
      UInt64.toNat_ofNat_of_lt' (by omega)
    have e1 : (st1 adapter read p.toNat).toUInt64.toNat = st1 adapter read p.toNat :=
      UInt64.toNat_ofNat_of_lt' (by omega)
    have ep : (p + 1).toNat = p.toNat + 1 := by
      rw [ReadTrim.rt_add _ _ (by rw [ReadTrim.rt_one]; omega), ReadTrim.rt_one]
    have eb := hb (ReadTrim.rtGet read p)
    rw [ReadTrim.rtGet_eq] at eb
    -- the new states as machine words
    have n0 : (((st0 adapter read p.toNat).toUInt64 <<< (1 : UInt64) ||| (1 : UInt64)) &&& bOf bA bC bG bT (ReadTrim.rtGet read p)) =
        (st0 adapter read (p.toNat + 1)).toUInt64 := by
      apply UInt64.toNat_inj.mp
      rw [u64_step _ _ (by omega), e0, ReadTrim.rtGet_eq, eb,
        UInt64.toNat_ofNat_of_lt' (by have := st0_lt adapter read (p.toNat + 1); omega)]; rfl
    have n1 : ((((st1 adapter read p.toNat).toUInt64 <<< (1 : UInt64) ||| (1 : UInt64)) &&& bOf bA bC bG bT (ReadTrim.rtGet read p)) |||
        (((st0 adapter read p.toNat).toUInt64 <<< (1 : UInt64) ||| (1 : UInt64)) &&& msk)) = (st1 adapter read (p.toNat + 1)).toUInt64 := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_or, u64_step _ _ (by omega), u64_step _ _ (by omega), e0, e1, ReadTrim.rtGet_eq, eb, hmsk,
        UInt64.toNat_ofNat_of_lt' (by have := st1_lt adapter read (p.toNat + 1); omega)]; rfl
    simp only [saLoopU, saLoop]
    rw [n0, n1, show ((st0 adapter read p.toNat <<< 1) ||| 1) &&& bmask adapter read[p.toNat]! adapter.size 0 =
        st0 adapter read (p.toNat + 1) from rfl,
      show (((st1 adapter read p.toNat <<< 1) ||| 1) &&& bmask adapter read[p.toNat]! adapter.size 0) |||
        (((st0 adapter read p.toNat <<< 1) ||| 1) &&& (2 ^ adapter.size - 1)) = st1 adapter read (p.toNat + 1) from rfl]
    have et : ∀ x : Nat, x < 2 ^ adapter.size →
        (((x.toUInt64 >>> sh) &&& 1) != 0) = x.testBit (adapter.size - 1) := fun x hx => by
      rw [hsh, u64_bit _ _ (by omega), UInt64.toNat_ofNat_of_lt' (by omega)]
    have eq1 : ((if decide (maxErr ≠ 0) then (st1 adapter read (p.toNat + 1)).toUInt64
        else (st0 adapter read (p.toNat + 1)).toUInt64) >>> sh &&& 1 != 0) =
        (if maxErr = 0 then st0 adapter read (p.toNat + 1) else st1 adapter read (p.toNat + 1)).testBit (adapter.size - 1) := by
      by_cases h : maxErr = 0
      · simp only [h, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
        exact et _ (st0_lt adapter read _)
      · simp only [h, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
        exact et _ (st1_lt adapter read _)
    have em : decide (mU ≤ p + 1) = decide (adapter.size ≤ p.toNat + 1) :=
      decide_eq_decide.mpr (by rw [USize.le_iff_toNat_le, ep, hmU])
    rw [eq1, em]
    have ih := saLoopU_eq minLen maxErr bA bC bG bT msk sh mU hm0 hm hn hb hmsk hsh hmU k (p + 1) (by rw [ep]; omega)
    rw [ep] at ih
    generalize (if maxErr = 0 then st0 adapter read (p.toNat + 1) else st1 adapter read (p.toNat + 1)).testBit
      (adapter.size - 1) = tb
    by_cases hc : (decide (adapter.size ≤ p.toNat + 1) && decide (minLen ≤ adapter.size) && tb) = true
    · rw [if_pos hc, if_pos hc]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by rw [ep, hmU]; exact hc.1.1)), ep, hmU]
    · rw [if_neg hc, if_neg hc]; exact ih

/-- `saLoopU` without the `Nat` fuel: the loop runs while `p < nU` (`nU = read.size`; `saLoopV_eq`). -/
def saLoopV (bA bC bG bT msk sh : UInt64) (m nU : USize) (ok1 e1q : Bool) (minLen : Nat) (p : USize) (e0 e1 : UInt64) : Nat :=
  if h : p < nU then
    let b := bOf bA bC bG bT (ReadTrim.rtGet read p)
    let e0' := ((e0 <<< (1 : UInt64)) ||| (1 : UInt64)) &&& b
    let e1' := (((e1 <<< (1 : UInt64)) ||| (1 : UInt64)) &&& b) ||| (((e0 <<< (1 : UInt64)) ||| (1 : UInt64)) &&& msk)
    if m ≤ p + 1 && ok1 && ((((if e1q then e1' else e0') >>> sh) &&& (1 : UInt64)) != 0) then (p + 1 - m).toNat
    else saLoopV bA bC bG bT msk sh m nU ok1 e1q minLen (p + 1) e0' e1'
  else
    scanP (fun s => decide (minLen ≤ read.size - s) && e0.toNat.testBit (read.size - s - 1))
      (read.size - (p.toNat + 1 - adapter.size)) (p.toNat + 1 - adapter.size)
termination_by nU.toNat - p.toNat
decreasing_by
  have hl : p.toNat < nU.toNat := h
  have hs := USize.toNat_lt_size nU
  rw [USize.size_eq_two_pow] at hs
  rw [USize.toNat_add, show (1 : USize).toNat = 1 from ReadTrim.rt_one, Nat.mod_eq_of_lt (by omega)]
  omega

theorem saLoopV_eq (bA bC bG bT msk sh : UInt64) (m nU : USize) (ok1 e1q : Bool) (minLen : Nat)
    (hnU : nU.toNat = read.size) (hn : read.size < 2 ^ 30) :
    ∀ k (p : USize) (e0 e1 : UInt64), p.toNat + k = read.size →
      saLoopV adapter read bA bC bG bT msk sh m nU ok1 e1q minLen p e0 e1 =
        saLoopU adapter read bA bC bG bT msk sh m ok1 e1q minLen k p e0 e1
  | 0, p, e0, e1, hp => by
    rw [saLoopV, dif_neg (show ¬ p < nU from fun h => by have : p.toNat < nU.toNat := h; omega), saLoopU]
  | k + 1, p, e0, e1, hp => by
    have ih := fun e0' e1' => saLoopV_eq bA bC bG bT msk sh m nU ok1 e1q minLen hnU hn k (p + 1) e0' e1'
      (by rw [ReadTrim.rt_add _ _ (by rw [ReadTrim.rt_one]; omega), ReadTrim.rt_one]; omega)
    rw [saLoopV, dif_pos (show p < nU from show p.toNat < nU.toNat by omega), saLoopU]
    simp only [ih]

end sa

/-- `bmask` on machine words (`bmaskU_eq`, for masks below `2^64`). -/
def bmaskU (adapter : ByteArray) (c : UInt8) : (k j : Nat) → UInt64
  | 0, _ => 0
  | k + 1, j => (if adapter[j]! == c then (1 : UInt64) <<< j.toUInt64 else 0) ||| bmaskU adapter c k (j + 1)

theorem bmaskU_eq (adapter : ByteArray) (c : UInt8) : ∀ k j, j + k ≤ 63 →
    (bmaskU adapter c k j).toNat = bmask adapter c k j
  | 0, _, _ => rfl
  | k + 1, j, h => by
    have hU : UInt64.size = 18446744073709551616 := rfl
    rw [bmaskU, bmask, UInt64.toNat_or, bmaskU_eq adapter c k (j + 1) (by omega)]
    congr 1
    split
    · rw [UInt64.toNat_shiftLeft, show (1 : UInt64).toNat = 1 from rfl, UInt64.toNat_ofNat_of_lt' (by omega),
        Nat.mod_eq_of_lt (show j < 64 by omega), Nat.one_shiftLeft, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))]
    · rfl

theorem pow_sub_one_u64 (m : Nat) (hm : m < 64) : ((1 : UInt64) <<< m.toUInt64) - 1 = (2 ^ m - 1).toUInt64 := by
  have hU : UInt64.size = 18446744073709551616 := rfl
  have hp : 2 ^ m < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hm
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  apply UInt64.toNat_inj.mp
  have e : ((1 : UInt64) <<< m.toUInt64).toNat = 2 ^ m := by
    rw [UInt64.toNat_shiftLeft, show (1 : UInt64).toNat = 1 from rfl, UInt64.toNat_ofNat_of_lt' (by omega),
      Nat.mod_eq_of_lt hm, Nat.one_shiftLeft, Nat.mod_eq_of_lt hp]
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, e]; exact h1), e, show (1 : UInt64).toNat = 1 from rfl,
    UInt64.toNat_ofNat_of_lt' (by omega)]

/-- Every adapter letter is `A`, `C`, `G` or `T`. -/
def acgtAll (adapter : ByteArray) : Bool :=
  (List.range adapter.size).all fun j => adapter[j]! == 65 || adapter[j]! == 67 || adapter[j]! == 71 || adapter[j]! == 84

/-- The bit-parallel cut (`saCutU_eq`): the four letter masks once, then `saLoopU`. -/
@[inline] def saCutU (adapter : ByteArray) (minLen maxErr : Nat) (read : ByteArray) : Nat :=
  let m := adapter.size
  saLoopV adapter read (bmaskU adapter 65 m 0) (bmaskU adapter 67 m 0) (bmaskU adapter 71 m 0)
    (bmaskU adapter 84 m 0) (((1 : UInt64) <<< m.toUInt64) - 1) (m - 1).toUInt64 m.toUSize read.size.toUSize (decide (minLen ≤ m))
    (decide (maxErr ≠ 0)) minLen 0 0 0

theorem saCutU_eq (adapter : ByteArray) (minLen maxErr : Nat) (read : ByteArray) (hm0 : 0 < adapter.size)
    (hm : adapter.size < 64) (he : maxErr ≤ 1) (hn : read.size < 2 ^ 30) (ha : acgtAll adapter = true) :
    saCutU adapter minLen maxErr read = cutPos adapter minLen maxErr read := by
  have hU : UInt64.size = 18446744073709551616 := rfl
  have h2 : 2 ^ adapter.size ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
  have lt64 : ∀ c, (bmask adapter c adapter.size 0).toUInt64.toNat = bmask adapter c adapter.size 0 := fun c => by
    have := bmask_lt adapter c; exact UInt64.toNat_ofNat_of_lt' (by omega)
  have hacgt : ∀ j, j < adapter.size → adapter[j]! = 65 ∨ adapter[j]! = 67 ∨ adapter[j]! = 71 ∨ adapter[j]! = 84 := by
    intro j hj
    have := List.all_eq_true.mp ha j (List.mem_range.mpr hj)
    simp only [Bool.or_eq_true, beq_iff_eq] at this
    rcases this with ((h | h) | h) | h <;> simp [h]
  have hb : ∀ c, (bOf (bmask adapter 65 adapter.size 0).toUInt64 (bmask adapter 67 adapter.size 0).toUInt64
      (bmask adapter 71 adapter.size 0).toUInt64 (bmask adapter 84 adapter.size 0).toUInt64 c).toNat =
      bmask adapter c adapter.size 0 := by
    intro c
    unfold bOf
    by_cases c1 : c = 65
    · subst c1; simp [lt64]
    · by_cases c2 : c = 67
      · subst c2; simp [lt64]
      · by_cases c3 : c = 71
        · subst c3; simp [lt64]
        · by_cases c4 : c = 84
          · subst c4; simp [lt64]
          · simp only [beq_iff_eq, c1, c2, c3, c4, ↓reduceIte]
            rw [bmask_other adapter c (fun j hj e => by rcases hacgt j hj with h | h | h | h <;> simp_all)]
            rfl
  unfold saCutU
  rw [saLoopV_eq adapter read _ _ _ _ _ _ _ _ _ _ _ (rt_n _ (by omega)) hn read.size 0 _ _ (by simp)]
  simp only [pow_sub_one_u64 _ hm]
  have em : ∀ c, bmaskU adapter c adapter.size 0 = (bmask adapter c adapter.size 0).toUInt64 := fun c => by
    apply UInt64.toNat_inj.mp; rw [bmaskU_eq _ _ _ _ (by omega), lt64]
  simp only [em]
  have hl := saLoopU_eq adapter read minLen maxErr _ _ _ _ (2 ^ adapter.size - 1).toUInt64 (adapter.size - 1).toUInt64
    adapter.size.toUSize hm0 hm hn hb (UInt64.toNat_ofNat_of_lt' (by omega)) rfl (rt_n _ (by omega)) read.size 0 (by simp)
  simp only [show (0 : USize).toNat = 0 from rfl, show st0 adapter read 0 = 0 from rfl,
    show st1 adapter read 0 = 0 from rfl] at hl
  rw [show ((0 : Nat).toUInt64) = 0 from rfl] at hl
  rw [hl, cutPos_eq_sa adapter read minLen maxErr hm0 he]

/-- The `USize` scan (`cutPosW_eq`): every adapter and error bound below `2^30`. -/
def cutPosW (adapter : ByteArray) (minLen maxErr : Nat) (read : ByteArray) : Nat :=
  if read.size < 2 ^ 30 ∧ adapter.size < 2 ^ 30 ∧ minLen < 2 ^ 30 ∧ maxErr < 2 ^ 30 then
    (scanU adapter read minLen.toUSize maxErr.toUSize adapter.size.toUSize read.size.toUSize
      read.size.toUSize 0).toNat
  else scan adapter minLen maxErr read read.size 0

theorem cutPosW_eq (adapter : ByteArray) (minLen maxErr : Nat) (read : ByteArray) :
    cutPosW adapter minLen maxErr read = cutPos adapter minLen maxErr read := by
  unfold cutPos cutPosW
  split
  · rename_i h
    obtain ⟨hn, ha, hl, hm⟩ := h
    have := scanU_eq adapter read minLen.toUSize maxErr.toUSize adapter.size.toUSize read.size.toUSize
      (rt_n _ (by omega)) (rt_n _ (by omega)) hn ha (by rw [rt_n _ (by omega)]; omega) read.size
      read.size.toUSize 0 (rt_n _ (by omega)) (by show 0 + _ < _; omega)
    rw [this, rt_n _ (by omega), rt_n _ (by omega)]; rfl
  · rfl

/-- What the compiled code runs for `cutPos`: the bit-parallel scan for an `A C G T` adapter of 1–63 letters with
at most one mismatch, else the `USize` scan. -/
@[inline] def cutPosF (adapter : ByteArray) (minLen maxErr : Nat) (read : ByteArray) : Nat :=
  if 0 < adapter.size ∧ adapter.size < 64 ∧ maxErr ≤ 1 ∧ read.size < 2 ^ 30 ∧ acgtAll adapter = true then
    saCutU adapter minLen maxErr read
  else cutPosW adapter minLen maxErr read

@[csimp] theorem cutPos_eq_cutPosF : @cutPos = @cutPosF := by
  funext adapter minLen maxErr read
  unfold cutPosF
  split
  · rename_i h
    exact (saCutU_eq adapter minLen maxErr read h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2).symm
  · exact (cutPosW_eq adapter minLen maxErr read).symm

/-- Letters and qualities `[0, cutPos)`. -/
@[inline] def cutAdapter (adapter : ByteArray) (minLen maxErr : Nat) (letters qual : ByteArray) : ByteArray × ByteArray :=
  let c := cutPos adapter minLen maxErr letters
  (letters.extract 0 c, qual.extract 0 c)

/-- The setting used by the FASTQ reader: TruSeq, tail prefixes of at least 6 letters, 1 mismatch
over the whole adapter. -/
def cutTruSeq (letters qual : ByteArray) : ByteArray × ByteArray := cutAdapter truSeq 6 1 letters qual

/-! `cutTruSeq` for the compiled code (`cutTruSeq_eqF`): the adapter's letter masks and constants computed once
(top-level values), not per read, and the conditions of `cutPosF` decided once for `truSeq`. -/

def tsA : UInt64 := bmaskU truSeq 65 truSeq.size 0
def tsC : UInt64 := bmaskU truSeq 67 truSeq.size 0
def tsG : UInt64 := bmaskU truSeq 71 truSeq.size 0
def tsT : UInt64 := bmaskU truSeq 84 truSeq.size 0
def tsMsk : UInt64 := ((1 : UInt64) <<< truSeq.size.toUInt64) - 1
def tsSh : UInt64 := (truSeq.size - 1).toUInt64
def tsM : USize := truSeq.size.toUSize

/-- `scanP` with `saLoopTS`'s end test inlined (no closure): `scanTS_eq`. -/
def scanTS (read : ByteArray) (e0 : UInt64) : (k i : Nat) → Nat
  | 0, i => i
  | k + 1, i => if decide (6 ≤ read.size - i) && e0.toNat.testBit (read.size - i - 1) then i else scanTS read e0 k (i + 1)

theorem scanTS_eq (read : ByteArray) (e0 : UInt64) : ∀ k i,
    scanTS read e0 k i = scanP (fun s => decide (6 ≤ read.size - s) && e0.toNat.testBit (read.size - s - 1)) k i
  | 0, _ => rfl
  | k + 1, i => by rw [scanTS, scanP, scanTS_eq read e0 k (i + 1)]

/-- `saLoopV` for TruSeq with its constants as literals (`saLoopTS_eq`; the masks `tsConst`). -/
def saLoopTS (read : ByteArray) (nU p : USize) (e0 e1 : UInt64) : Nat :=
  if h : p < nU then
    let b := bOf 1413 4112 2658 8 (ReadTrim.rtGet read p)
    let e0' := ((e0 <<< (1 : UInt64)) ||| (1 : UInt64)) &&& b
    let e1' := (((e1 <<< (1 : UInt64)) ||| (1 : UInt64)) &&& b) ||| (((e0 <<< (1 : UInt64)) ||| (1 : UInt64)) &&& 8191)
    if 13 ≤ p + 1 && (((e1' >>> (12 : UInt64)) &&& (1 : UInt64)) != 0) then (p + 1 - 13).toNat
    else saLoopTS read nU (p + 1) e0' e1'
  else scanTS read e0 (read.size - (p.toNat + 1 - 13)) (p.toNat + 1 - 13)
termination_by nU.toNat - p.toNat
decreasing_by
  have hl : p.toNat < nU.toNat := h
  have hs := USize.toNat_lt_size nU
  rw [USize.size_eq_two_pow] at hs
  rw [USize.toNat_add, show (1 : USize).toNat = 1 from ReadTrim.rt_one, Nat.mod_eq_of_lt (by omega)]
  omega

/-- `saLoopTS` with no bounds check: `hn` carries `nU ≤ read.size`, so `uget` needs no test (`saLoopTSc_eq`). -/
def saLoopTSc (read : ByteArray) (nU p : USize) (e0 e1 : UInt64) (hn : nU.toNat ≤ read.size) : Nat :=
  if h : p < nU then
    let b := bOf 1413 4112 2658 8 (read.uget p (Nat.lt_of_lt_of_le h hn))
    let e0' := ((e0 <<< (1 : UInt64)) ||| (1 : UInt64)) &&& b
    let e1' := (((e1 <<< (1 : UInt64)) ||| (1 : UInt64)) &&& b) ||| (((e0 <<< (1 : UInt64)) ||| (1 : UInt64)) &&& 8191)
    if 13 ≤ p + 1 && (((e1' >>> (12 : UInt64)) &&& (1 : UInt64)) != 0) then (p + 1 - 13).toNat
    else saLoopTSc read nU (p + 1) e0' e1' hn
  else scanTS read e0 (read.size - (p.toNat + 1 - 13)) (p.toNat + 1 - 13)
termination_by nU.toNat - p.toNat
decreasing_by
  have hl : p.toNat < nU.toNat := h
  have hs := USize.toNat_lt_size nU
  rw [USize.size_eq_two_pow] at hs
  rw [USize.toNat_add, show (1 : USize).toNat = 1 from ReadTrim.rt_one, Nat.mod_eq_of_lt (by omega)]
  omega

theorem saLoopTSc_eq (read : ByteArray) (nU : USize) (hn : nU.toNat ≤ read.size) : ∀ k (p : USize) (e0 e1 : UInt64),
    nU.toNat - p.toNat = k → saLoopTSc read nU p e0 e1 hn = saLoopTS read nU p e0 e1 := by
  intro k
  induction k with
  | zero =>
    intro p e0 e1 hk
    rw [saLoopTSc, saLoopTS, dif_neg (fun h => by have : p.toNat < nU.toNat := h; omega),
      dif_neg (fun h => by have : p.toNat < nU.toNat := h; omega)]
  | succ k ih =>
    intro p e0 e1 hk
    have hp : p < nU := show p.toNat < nU.toNat by omega
    have hs := USize.toNat_lt_size nU
    rw [USize.size_eq_two_pow] at hs
    have h1 : (p + 1).toNat = p.toNat + 1 := by
      rw [USize.toNat_add, show (1 : USize).toNat = 1 from ReadTrim.rt_one, Nat.mod_eq_of_lt (by omega)]
    rw [saLoopTSc, saLoopTS, dif_pos hp, dif_pos hp,
      ReadTrim.rtGet_of read p (Nat.lt_of_lt_of_le hp hn)]
    simp only [ih (p + 1) _ _ (by omega)]

theorem tsConst : tsA = 1413 ∧ tsC = 4112 ∧ tsG = 2658 ∧ tsT = 8 ∧ tsMsk = 8191 ∧ tsSh = 12 ∧ tsM = 13 ∧
    truSeq.size = 13 := by
  have hz : truSeq.size = 13 := by decide
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_, hz⟩
  show truSeq.size.toUSize = 13
  rw [hz]; rfl

theorem saLoopTS_eq (read : ByteArray) (nU : USize) (hnU : nU.toNat = read.size) (hn : read.size < 2 ^ 30) :
    ∀ k (p : USize) (e0 e1 : UInt64), p.toNat + k = read.size →
      saLoopTS read nU p e0 e1 = saLoopV truSeq read tsA tsC tsG tsT tsMsk tsSh tsM nU true true 6 p e0 e1
  | 0, p, e0, e1, hp => by
    obtain ⟨_, _, _, _, _, _, _, hz⟩ := tsConst
    rw [saLoopTS, saLoopV, dif_neg (show ¬ p < nU from fun h => by have : p.toNat < nU.toNat := h; omega),
      dif_neg (show ¬ p < nU from fun h => by have : p.toNat < nU.toNat := h; omega), hz, scanTS_eq]
  | k + 1, p, e0, e1, hp => by
    obtain ⟨hA, hC, hG, hT, hM, hS, hm, _⟩ := tsConst
    have ih := fun e0' e1' => saLoopTS_eq read nU hnU hn k (p + 1) e0' e1'
      (by rw [ReadTrim.rt_add _ _ (by rw [ReadTrim.rt_one]; omega), ReadTrim.rt_one]; omega)
    rw [saLoopTS, saLoopV, dif_pos (show p < nU from show p.toNat < nU.toNat by omega),
      dif_pos (show p < nU from show p.toNat < nU.toNat by omega)]
    simp only [ih, hA, hC, hG, hT, hM, hS, hm, Bool.and_true, if_true]

/-- `cutPos truSeq 6 1` with the precomputed masks (`cutPosTS_eq`). -/
@[inline] def cutPosTS (read : ByteArray) : Nat :=
  if hn : read.size < 2 ^ 30 then saLoopTSc read read.size.toUSize 0 0 0 (by rw [rt_n _ (by omega)]; exact Nat.le_refl _)
  else cutPosW truSeq 6 1 read

theorem cutPosTS_eq (read : ByteArray) : cutPosTS read = cutPos truSeq 6 1 read := by
  unfold cutPosTS
  split
  · rename_i hn
    rw [saLoopTSc_eq read _ _ _ _ _ _ rfl, saLoopTS_eq read _ (rt_n _ (by omega)) hn read.size 0 0 0 (by simp),
      ← saCutU_eq truSeq 6 1 read (by decide) (by decide) (by decide) hn (by decide)]
    rfl
  · exact cutPosW_eq truSeq 6 1 read

/-- `cutTruSeq` for the compiled code. -/
@[inline] def cutTruSeqF (letters qual : ByteArray) : ByteArray × ByteArray :=
  let c := cutPosTS letters
  (letters.extract 0 c, qual.extract 0 c)

@[csimp] theorem cutTruSeq_eqF : @cutTruSeq = @cutTruSeqF := by
  funext letters qual
  unfold cutTruSeq cutTruSeqF cutAdapter
  rw [cutPosTS_eq]

/-- Minimum length: a mate with fewer than `minLength` letters becomes empty (trimmed away). -/
def dropShort (minLength : Nat) (letters qual : ByteArray) : ByteArray × ByteArray :=
  if letters.size < minLength then (ByteArray.empty, ByteArray.empty) else (letters, qual)

/-! ## Proofs -/

/-- (0) The cut is inside the read. -/
theorem cut_le (adapter : ByteArray) (minLen maxErr : Nat) (read : ByteArray) :
    cutPos adapter minLen maxErr read ≤ read.size := by
  have := (scan_spec adapter minLen maxErr read read.size 0).2.1; unfold cutPos; omega

/-- (1) The kept letters and qualities are prefixes of the input. -/
theorem cut_prefix (adapter : ByteArray) (minLen maxErr : Nat) (letters qual : ByteArray) :
    (cutAdapter adapter minLen maxErr letters qual).1.data.toList <+: letters.data.toList ∧
    (cutAdapter adapter minLen maxErr letters qual).2.data.toList <+: qual.data.toList := by
  simp only [cutAdapter, ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop,
    List.drop_zero, Nat.sub_zero]
  exact ⟨List.take_prefix _ _, List.take_prefix _ _⟩

/-- (2) If it cuts at `i`, the adapter (or its allowed prefix) matches at `i`. -/
theorem cut_matches (adapter : ByteArray) (minLen maxErr : Nat) (read : ByteArray) :
    cutPos adapter minLen maxErr read < read.size →
    matchesAt adapter minLen maxErr read (cutPos adapter minLen maxErr read) = true := by
  have := (scan_spec adapter minLen maxErr read read.size 0).2.2.1
  unfold cutPos; intro h; exact this (by omega)

/-- (3) No position before the cut matches (it cuts at the first match). -/
theorem cut_first (adapter : ByteArray) (minLen maxErr : Nat) (read : ByteArray) :
    ∀ j, j < cutPos adapter minLen maxErr read → matchesAt adapter minLen maxErr read j = false :=
  fun j h => (scan_spec adapter minLen maxErr read read.size 0).2.2.2 j (Nat.zero_le _) h

/-- (4) If it does not cut, no position matches. -/
theorem cut_none (adapter : ByteArray) (minLen maxErr : Nat) (read : ByteArray) :
    cutPos adapter minLen maxErr read = read.size → ∀ j, matchesAt adapter minLen maxErr read j = false := by
  intro h j
  by_cases hj : j < read.size
  · exact cut_first adapter minLen maxErr read j (by omega)
  · simp [matchesAt, hj]

/-- (5) After `dropShort`, a mate is empty or has at least `minLength` letters. -/
theorem dropShort_size (minLength : Nat) (letters qual : ByteArray) :
    (dropShort minLength letters qual).1.size = 0 ∨ minLength ≤ (dropShort minLength letters qual).1.size := by
  unfold dropShort; split
  · exact Or.inl rfl
  · exact Or.inr (Nat.le_of_not_lt ‹_›)


-- examples: full adapter with 1 mismatch mid-read; a 6-letter tail; a 5-letter tail is too short
#guard cutPos truSeq 6 1 "ACGTACGTAGATCGGTAGAGCTTTT".toUTF8 = 8
#guard cutPos truSeq 6 1 "ACGTACGTACGTAGATCG".toUTF8 = 12
#guard cutPos truSeq 6 1 "ACGTACGTACGTAGATC".toUTF8 = 17

#print axioms cut_le
#print axioms cut_prefix
#print axioms cut_matches
#print axioms cut_first
#print axioms cut_none
#print axioms fastMatchesAt_eq
#print axioms dropShort_size
#print axioms cutPos_eq_cutPosF

end AdapterTrim
