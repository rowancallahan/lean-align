import MapperBandSpec

/-!
The capped banded score-only kernel and its proof.

One pass per window END `e`: Gotoh's three-state recurrence over suffixes
(the specification's own recursion, `sv`), rows `i = n, n-1, …, 0` of the
read, `2B+1` cells per row.  Cell `k` of row `i` is the read suffix from `i`
against the genome segment `[p, e)` with `p = e + i + B - n - k`; row 0 gives
the score of every window ending at `e` with length `n + k - B`.

Read and chromosome are `ByteArray`s, one byte per letter (`Encodes`: the
byte is the letter's code, so letters must be `< 256`).  Three `Array Int`
rows are updated in place (each uniquely referenced).  A row whose every cell
is below its threshold stops the pass (`none`: every window ending at `e`
scores below `T`).
-/

namespace MapSpec

open AlignmentSpec

/-- Bytes spell the letters, one byte per letter. -/
def Encodes (bs : ByteArray) (cs : List Char) : Prop :=
  bs.size = cs.length ∧ ∀ i (h : i < cs.length), (bs.get! i).toNat = (cs[i]).toNat

theorem Encodes.beq_iff {b1 b2 : ByteArray} {c1 c2 : List Char} (h1 : Encodes b1 c1)
    (h2 : Encodes b2 c2) (i j : Nat) (hi : i < c1.length) (hj : j < c2.length) :
    (b1.get! i == b2.get! j) = decide (c1[i] = c2[j]) := by
  have e1 := h1.2 i hi
  have e2 := h2.2 j hj
  by_cases h : c1[i] = c2[j]
  · have : b1.get! i = b2.get! j := UInt8.toNat_inj.mp (by rw [e1, e2, h])
    simp [this, h]
  · have : b1.get! i ≠ b2.get! j := by
      intro hb
      apply h
      apply Char.toNat_inj.mp
      rw [← e1, ← e2, hb]
    simp [this, h]

/-! ## The grid of true values -/

def seg (gs : List Char) (p e : Nat) : List Char := (gs.drop p).take (e - p)

theorem seg_length (gs : List Char) (p e : Nat) (he : e ≤ gs.length) :
    (seg gs p e).length = e - p := by
  simp [seg]; omega

theorem seg_self (gs : List Char) (e : Nat) : seg gs e e = [] := by simp [seg]

theorem seg_cons (gs : List Char) (p e : Nat) (hp : p < e) (he : e ≤ gs.length) :
    seg gs p e = gs[p] :: seg gs (p + 1) e := by
  unfold seg
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [show e - p = (e - (p + 1)) + 1 by omega, List.take_succ_cons]

/-- True value of cell `(i, p)` in state `st`. -/
def cv (sc : Scoring) (xs gs : List Char) (e : Nat) (st : Option Step) (i p : Nat) : Int :=
  sv sc (xs.drop i) (seg gs p e) st

theorem drop_cons_get (xs : List Char) (i : Nat) (h : i < xs.length) :
    xs.drop i = xs[i] :: xs.drop (i + 1) := List.drop_eq_getElem_cons h

theorem cv_last_end (sc : Scoring) (xs gs : List Char) (e : Nat) (st : Option Step) :
    cv sc xs gs e st xs.length e = 0 := by
  simp [cv, seg_self, sv_nil_nil]

theorem cv_last (sc : Scoring) (xs gs : List Char) (e : Nat) (he : e ≤ gs.length)
    (st : Option Step) (p : Nat) (hp : p < e) :
    cv sc xs gs e st xs.length p = gapXCost sc st + cv sc xs gs e (some .gapX) xs.length (p + 1) := by
  simp only [cv, seg_cons gs p e hp he, List.drop_length, sv_nil_cons]

theorem cv_end (sc : Scoring) (xs gs : List Char) (e : Nat) (st : Option Step) (i : Nat)
    (hi : i < xs.length) :
    cv sc xs gs e st i e = gapYCost sc st + cv sc xs gs e (some .gapY) (i + 1) e := by
  simp only [cv, seg_self, drop_cons_get xs i hi, sv_cons_nil]

theorem cv_main (sc : Scoring) (xs gs : List Char) (e : Nat) (he : e ≤ gs.length)
    (st : Option Step) (i p : Nat) (hi : i < xs.length) (hp : p < e) :
    cv sc xs gs e st i p =
      max (max (diagCost sc xs[i] (gs[p]'(by omega)) + cv sc xs gs e none (i + 1) (p + 1))
               (gapXCost sc st + cv sc xs gs e (some .gapX) i (p + 1)))
          (gapYCost sc st + cv sc xs gs e (some .gapY) (i + 1) p) := by
  unfold cv
  rw [seg_cons gs p e hp he, drop_cons_get xs i hi, sv_cons_cons]

/-- Off-band cells are below their thresholds. -/
theorem cv_off_band (sc : Scoring) (hv : ValidScoring sc) (T : Int) (B : Nat)
    (hb : BandOK sc T B) (xs gs : List Char) (e : Nat) (he : e ≤ gs.length)
    (st : Option Step) (i p : Nat)
    (hoff : (B : Int) + 1 ≤ (((e - p : Nat) : Int) - ((xs.length - i : Nat) : Int)).natAbs) :
    cv sc xs gs e st i p < thr sc T st := by
  apply sv_lt_thr sc hv T B hb
  rw [List.length_drop, seg_length gs p e he]
  exact hoff

/-! ## Dead rows -/

/-- Every cell of row `i` is below its threshold. -/
def DeadRow (sc : Scoring) (T : Int) (xs gs : List Char) (e i : Nat) : Prop :=
  ∀ p, p ≤ e → cv sc xs gs e none i p < T ∧
    cv sc xs gs e (some .gapX) i p < T - sc.gapOpen ∧ cv sc xs gs e (some .gapY) i p < T - sc.gapOpen

theorem deadRow_step (sc : Scoring) (hv : ValidScoring sc) (T : Int) (xs gs : List Char) (e : Nat)
    (he : e ≤ gs.length) (i : Nat) (hi : i < xs.length) (hd : DeadRow sc T xs gs e (i + 1)) :
    DeadRow sc T xs gs e i := by
  obtain ⟨hM, hX, hO, hE⟩ := hv
  have key : ∀ m p, e - p = m → p ≤ e → cv sc xs gs e none i p < T ∧
      cv sc xs gs e (some .gapX) i p < T - sc.gapOpen ∧
      cv sc xs gs e (some .gapY) i p < T - sc.gapOpen := by
    intro m
    induction m with
    | zero =>
      intro p hm hp
      have hpe : p = e := by omega
      subst hpe
      obtain ⟨-, -, hy⟩ := hd p (Nat.le_refl _)
      simp only [cv_end sc xs gs p _ i hi, gapYCost]
      simp
      omega
    | succ m ih =>
      intro p hm hp
      obtain ⟨hn1, -, -⟩ := hd (p + 1) (by omega)
      obtain ⟨-, -, hy⟩ := hd p hp
      obtain ⟨-, hx, -⟩ := ih (p + 1) (by omega) (by omega)
      have hD : diagCost sc xs[i] (gs[p]'(by omega)) ≤ 0 := by
        unfold diagCost; split <;> omega
      simp only [cv_main sc xs gs e he _ i p hi (by omega), gapXCost, gapYCost]
      simp
      omega
  intro p hp
  exact key (e - p) p rfl hp

theorem deadRow_down (sc : Scoring) (hv : ValidScoring sc) (T : Int) (xs gs : List Char) (e : Nat)
    (he : e ≤ gs.length) : ∀ i, i ≤ xs.length → DeadRow sc T xs gs e i → DeadRow sc T xs gs e 0
  | 0, _, h => h
  | i + 1, hi, h => deadRow_down sc hv T xs gs e he i (by omega)
      (deadRow_step sc hv T xs gs e he i (by omega) h)

/-! ## The kernel -/

/-- New (none, gapX, gapY) values of one cell from its diagonal neighbour's
none value, its right neighbour's gapX value and its lower neighbour's gapY
value. -/
@[inline] def cellVals (sc : Scoring) (rb gb : ByteArray) (i p : Nat) (lastRow atEnd : Bool)
    (dN xX yY : Int) : Int × Int × Int :=
  let oe := sc.gapOpen + sc.gapExtend
  let ext := sc.gapExtend
  if lastRow then
    if atEnd then (0, 0, 0) else (oe + xX, ext + xX, oe + xX)
  else if atEnd then (oe + yY, oe + yY, ext + yY)
  else
    let d := (if rb.get! i == gb.get! p then sc.matchScore else sc.mismatchScore) + dN
    (max (max d (oe + xX)) (oe + yY), max (max d (ext + xX)) (oe + yY),
     max (max d (oe + xX)) (ext + yY))

/-- One row: cells `k, k+1, …, 2B`, in place. -/
def bandRow (sc : Scoring) (T : Int) (B : Nat) (rb gb : ByteArray) (e i : Nat) :
    Nat → Array Int → Array Int → Array Int → Bool → Array Int × Array Int × Array Int × Bool
  | k, N, X, Y, alive =>
    if k < 2 * B + 1 then
      if rb.size + k ≤ e + i + B ∧ i + B ≤ rb.size + k then
        let p := e + i + B - rb.size - k
        let xX := if k = 0 then T - 1 else X[k - 1]!
        let yY := if k + 1 < 2 * B + 1 then Y[k + 1]! else T - 1
        let v := cellVals sc rb gb i p (i == rb.size) (p == e) N[k]! xX yY
        bandRow sc T B rb gb e i (k + 1) (N.set! k v.1) (X.set! k v.2.1) (Y.set! k v.2.2)
          (alive || decide (T ≤ v.1) || decide (T - sc.gapOpen ≤ v.2.1) ||
            decide (T - sc.gapOpen ≤ v.2.2))
      else bandRow sc T B rb gb e i (k + 1) N X Y alive
    else (N, X, Y, alive)
  termination_by k => 2 * B + 1 - k

/-- Rows `i, i-1, …, 0`; `none` as soon as a row is dead. -/
def bandRows (sc : Scoring) (T : Int) (B : Nat) (rb gb : ByteArray) (e : Nat) :
    Nat → Array Int → Array Int → Array Int → Option (Array Int)
  | i, N, X, Y =>
    match bandRow sc T B rb gb e i 0 N X Y false with
    | (N, X, Y, alive) =>
      if alive then
        match i with
        | 0 => some N
        | i + 1 => bandRows sc T B rb gb e i N X Y
      else none

/-- All windows ending at `e`: entry `k` is the capped score of the window of
length `n + k - B`; `none` = every one of them scores below `T`. -/
def bandEnd (sc : Scoring) (T : Int) (B : Nat) (rb gb : ByteArray) (e : Nat) : Option (Array Int) :=
  bandRows sc T B rb gb e rb.size (Array.replicate (2 * B + 1) (T - 1))
    (Array.replicate (2 * B + 1) (T - 1)) (Array.replicate (2 * B + 1) (T - 1))

end MapSpec
