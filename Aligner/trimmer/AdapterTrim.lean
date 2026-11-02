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

/-- What the compiled code runs for `cutPos`. -/
def cutPosF (adapter : ByteArray) (minLen maxErr : Nat) (read : ByteArray) : Nat :=
  if read.size < 2 ^ 30 ∧ adapter.size < 2 ^ 30 ∧ minLen < 2 ^ 30 ∧ maxErr < 2 ^ 30 then
    (scanU adapter read minLen.toUSize maxErr.toUSize adapter.size.toUSize read.size.toUSize
      read.size.toUSize 0).toNat
  else scan adapter minLen maxErr read read.size 0

@[csimp] theorem cutPos_eq_cutPosF : @cutPos = @cutPosF := by
  funext adapter minLen maxErr read
  unfold cutPos cutPosF
  split
  · rename_i h
    obtain ⟨hn, ha, hl, hm⟩ := h
    have := scanU_eq adapter read minLen.toUSize maxErr.toUSize adapter.size.toUSize read.size.toUSize
      (rt_n _ (by omega)) (rt_n _ (by omega)) hn ha (by rw [rt_n _ (by omega)]; omega) read.size
      read.size.toUSize 0 (rt_n _ (by omega)) (by show 0 + _ < _; omega)
    rw [this, rt_n _ (by omega), rt_n _ (by omega)]; rfl
  · rfl

/-- Letters and qualities `[0, cutPos)`. -/
def cutAdapter (adapter : ByteArray) (minLen maxErr : Nat) (letters qual : ByteArray) : ByteArray × ByteArray :=
  let c := cutPos adapter minLen maxErr letters
  (letters.extract 0 c, qual.extract 0 c)

/-- The setting used by the FASTQ reader: TruSeq, tail prefixes of at least 6 letters, 1 mismatch
over the whole adapter. -/
def cutTruSeq (letters qual : ByteArray) : ByteArray × ByteArray := cutAdapter truSeq 6 1 letters qual

/-- Minimum length: a mate with fewer than `minLength` letters becomes empty (trimmed away). -/
def dropShort (minLength : Nat) (letters qual : ByteArray) : ByteArray × ByteArray :=
  if letters.size < minLength then (ByteArray.empty, ByteArray.empty) else (letters, qual)

/-! ## Proofs -/

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
