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
test equal to `matchesAt`.
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

end AdapterTrim
