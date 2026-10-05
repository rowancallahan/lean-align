import MapperBandPrune

/-! The pruned banded pass on bytes (default scoring `sc0`).

Cells hold penalties (`−score`) saturated at `M` (`satP`), three `ByteArray`
rows, `min` of small sums instead of `max` of `Int`s.  Saturation commutes with
the recurrence (`cellB_eq`), and every threshold the pass tests is below `M`,
so the byte pass makes the same alive decisions and its row is the saturated
`Int` row (`bandRowsCB_rel`). -/

namespace MapSpec

open AlignmentSpec

/-- Saturated penalty of a score. -/
def satP (M : Nat) (v : Int) : Nat := min (-v).toNat M

/-- `cellVals sc0` on saturated penalties. -/
@[inline] def cellB (M : Nat) {Gt : Type} [GRead Gt] (rb : ByteArray) (gb : Gt) (i p : Nat) (lastRow atEnd : Bool)
    (dN xX yY : Nat) : Nat × Nat × Nat :=
  if lastRow then
    if atEnd then (0, 0, 0) else (min (8 + xX) M, min (2 + xX) M, min (8 + xX) M)
  else if atEnd then (min (8 + yY) M, min (8 + yY) M, min (2 + yY) M)
  else
    let d := (if rb.get! i == GRead.get gb p then 0 else 4) + dN
    (min (min (min d (8 + xX)) (8 + yY)) M, min (min (min d (2 + xX)) (8 + yY)) M,
     min (min (min d (8 + xX)) (2 + yY)) M)

theorem satP_k3 (M : Nat) (a b c : Int) (ka kb kc : Nat) (ha : a ≤ 0) (hb : b ≤ 0) (hc : c ≤ 0) :
    satP M (max (max (-(ka : Int) + a) (-(kb : Int) + b)) (-(kc : Int) + c)) =
      min (min (min (ka + satP M a) (kb + satP M b)) (kc + satP M c)) M := by
  unfold satP; omega

theorem satP_k1 (M : Nat) (a : Int) (ka : Nat) (ha : a ≤ 0) :
    satP M (-(ka : Int) + a) = min (ka + satP M a) M := by
  unfold satP; omega

theorem cellB_eq (M : Nat) {Gt : Type} [GRead Gt] (rb : ByteArray) (gb : Gt) (i p : Nat) (lastRow atEnd : Bool)
    (dN xX yY : Int) (h1 : dN ≤ 0) (h2 : xX ≤ 0) (h3 : yY ≤ 0) :
    cellB M rb gb i p lastRow atEnd (satP M dN) (satP M xX) (satP M yY) =
      (satP M (cellVals sc0 rb gb i p lastRow atEnd dN xX yY).1,
       satP M (cellVals sc0 rb gb i p lastRow atEnd dN xX yY).2.1,
       satP M (cellVals sc0 rb gb i p lastRow atEnd dN xX yY).2.2) ∧
    (cellVals sc0 rb gb i p lastRow atEnd dN xX yY).1 ≤ 0 ∧
    (cellVals sc0 rb gb i p lastRow atEnd dN xX yY).2.1 ≤ 0 ∧
    (cellVals sc0 rb gb i p lastRow atEnd dN xX yY).2.2 ≤ 0 := by
  have e8 : ∀ x : Int, sc0.gapOpen + sc0.gapExtend + x = -((8 : Nat) : Int) + x := fun x => by simp [sc0]
  have e2 : ∀ x : Int, sc0.gapExtend + x = -((2 : Nat) : Int) + x := fun x => by simp [sc0]
  have z0 : satP M 0 = 0 := by unfold satP; omega
  unfold cellB cellVals
  cases lastRow <;> cases atEnd <;> simp only [Bool.false_eq_true, if_false, if_true, e8, e2]
  · generalize hk : (if (rb.get! i == GRead.get gb p) = true then sc0.matchScore else sc0.mismatchScore) = cd
    have hcd : cd = -(((if (rb.get! i == GRead.get gb p) = true then 0 else 4 : Nat)) : Int) := by
      rw [← hk]; split <;> simp [sc0]
    have hn : (if (rb.get! i == GRead.get gb p) = true then 0 else 4) + satP M dN =
        (if (rb.get! i == GRead.get gb p) = true then 0 else 4 : Nat) + satP M dN := rfl
    rw [hcd, satP_k3 M _ _ _ _ _ _ h1 h2 h3, satP_k3 M _ _ _ _ _ _ h1 h2 h3, satP_k3 M _ _ _ _ _ _ h1 h2 h3]
    refine ⟨rfl, by omega, by omega, by omega⟩
  · rw [satP_k1 M _ _ h3, satP_k1 M _ _ h3]
    exact ⟨rfl, by omega, by omega, by omega⟩
  · rw [satP_k1 M _ _ h2, satP_k1 M _ _ h2]
    exact ⟨rfl, by omega, by omega, by omega⟩
  · rw [z0]
    exact ⟨rfl, by omega, by omega, by omega⟩

/-- Cells `k … hi` of row `i` on bytes; alive tests `pen ≤ uN` / `pen ≤ uG`. -/
@[specialize] def bandLoopB (M : Nat) (uN uG : Int) {Gt : Type} [GRead Gt] (rb : ByteArray) (gb : Gt) (e i : Nat)
    (lastRow : Bool) (hi : Nat) :
    Nat → Nat → ByteArray → ByteArray → ByteArray → Bool → ByteArray × ByteArray × ByteArray × Bool
  | k, p, N, X, Y, alive =>
    if k ≤ hi then
      let v := cellB M rb gb i p lastRow (p == e) (N.get! (k + 1)).toNat (X.get! k).toNat (Y.get! (k + 2)).toNat
      bandLoopB M uN uG rb gb e i lastRow hi (k + 1) (p - 1) (N.set! (k + 1) v.1.toUInt8)
        (X.set! (k + 1) v.2.1.toUInt8) (Y.set! (k + 1) v.2.2.toUInt8)
        (alive || decide ((v.1 : Int) ≤ uN) || decide ((v.2.1 : Int) ≤ uG) || decide ((v.2.2 : Int) ≤ uG))
    else (N, X, Y, alive)
  termination_by k => hi + 1 - k

/-- Byte rows that are the saturated `Int` rows (all `Int` cells `≤ 0`). -/
def RelRow (M : Nat) (A : Array Int) (Bb : ByteArray) : Prop :=
  A.size = Bb.size ∧ ∀ j, j < A.size → A[j]! ≤ 0 ∧ (Bb.get! j).toNat = satP M A[j]!

theorem satP_le (M : Nat) (v : Int) : satP M v ≤ M := by unfold satP; omega

theorem byte_get_set (Bb : ByteArray) (j : Nat) (x : UInt8) (k : Nat) (hj : j < Bb.size) :
    (Bb.set! j x).get! k = if k = j then x else Bb.get! k := by
  cases Bb with
  | mk a =>
    simp only [ByteArray.set!, ByteArray.get!, ByteArray.size] at *
    split
    · next h => subst h; rw [getElem!_pos _ _ (by simpa using hj)]; simp
    · next h => rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm h)]

theorem relRow_set (M : Nat) (hM : M < 256) (A : Array Int) (Bb : ByteArray) (h : RelRow M A Bb) (j : Nat)
    (hj : j < A.size) (v : Int) (hv : v ≤ 0) :
    RelRow M (A.set! j v) (Bb.set! j (satP M v).toUInt8) := by
  obtain ⟨hs, hr⟩ := h
  refine ⟨by simp [hs], fun k hk => ?_⟩
  simp only [Array.size_set!] at hk
  rw [byte_get_set _ _ _ _ (by omega)]
  by_cases hkj : k = j
  · subst hkj
    rw [Array.getElem!_set!_self _ _ _ hk, if_pos rfl]
    refine ⟨hv, ?_⟩
    have := satP_le M v
    simp only [UInt8.toNat_ofNat', Nat.toUInt8]
    exact Nat.mod_eq_of_lt (by omega)
  · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hkj), if_neg hkj]
    exact hr k hk

theorem decide_satP (M : Nat) (v t : Int) (hv : v ≤ 0) (ht : -t < M) :
    decide ((satP M v : Int) ≤ -t) = decide (t ≤ v) := by
  unfold satP
  by_cases h : t ≤ v
  · rw [decide_eq_true h]; apply decide_eq_true; omega
  · rw [decide_eq_false h]; apply decide_eq_false; omega

/-- **The byte loop is the saturated `Int` loop**, with the same alive flag. -/
theorem bandLoopB_rel (M : Nat) (hM : M < 256) (T To : Int) (hT : -T < M) (hTo : -To < M) {Gt : Type} [GRead Gt]
    (rb : ByteArray) (gb : Gt) (e i : Nat) (lastRow : Bool) (hi : Nat) :
    ∀ m k p (N X Y : Array Int) (Nb Xb Yb : ByteArray) (alive : Bool), hi + 1 - k = m →
      hi + 2 < N.size → hi + 2 < X.size → hi + 2 < Y.size →
      RelRow M N Nb → RelRow M X Xb → RelRow M Y Yb →
      RelRow M (bandLoop sc0 T To rb gb e i lastRow hi k p N X Y alive).1
          (bandLoopB M (-T) (-To) rb gb e i lastRow hi k p Nb Xb Yb alive).1 ∧
      RelRow M (bandLoop sc0 T To rb gb e i lastRow hi k p N X Y alive).2.1
          (bandLoopB M (-T) (-To) rb gb e i lastRow hi k p Nb Xb Yb alive).2.1 ∧
      RelRow M (bandLoop sc0 T To rb gb e i lastRow hi k p N X Y alive).2.2.1
          (bandLoopB M (-T) (-To) rb gb e i lastRow hi k p Nb Xb Yb alive).2.2.1 ∧
      (bandLoop sc0 T To rb gb e i lastRow hi k p N X Y alive).2.2.2 =
          (bandLoopB M (-T) (-To) rb gb e i lastRow hi k p Nb Xb Yb alive).2.2.2 := by
  intro m
  induction m with
  | zero =>
    intro k p N X Y Nb Xb Yb alive hm _ _ _ hN hX hY
    rw [bandLoop, bandLoopB, if_neg (by omega), if_neg (by omega)]
    exact ⟨hN, hX, hY, rfl⟩
  | succ m ih =>
    intro k p N X Y Nb Xb Yb alive hm hNs hXs hYs hN hX hY
    rw [bandLoop, bandLoopB, if_pos (by omega), if_pos (by omega)]
    have n1 := hN.2 (k + 1) (by omega)
    have x1 := hX.2 k (by omega)
    have y1 := hY.2 (k + 2) (by omega)
    have hc := cellB_eq M rb gb i p lastRow (p == e) N[k + 1]! X[k]! Y[k + 2]! n1.1 x1.1 y1.1
    rw [n1.2, x1.2, y1.2, hc.1]
    obtain ⟨-, c1, c2, c3⟩ := hc
    generalize cellVals sc0 rb gb i p lastRow (p == e) N[k + 1]! X[k]! Y[k + 2]! = v at c1 c2 c3 ⊢
    simp only []
    rw [decide_satP M _ _ c1 hT, decide_satP M _ _ c2 hTo, decide_satP M _ _ c3 hTo]
    exact ih (k + 1) (p - 1) _ _ _ _ _ _ _ (by omega) (by simp; omega) (by simp; omega) (by simp; omega)
      (relRow_set M hM N Nb hN (k + 1) (by omega) v.1 c1)
      (relRow_set M hM X Xb hX (k + 1) (by omega) v.2.1 c2)
      (relRow_set M hM Y Yb hY (k + 1) (by omega) v.2.2 c3)

/-- `bandRowsC` on bytes (`M = −T + 1`, thresholds as penalties). -/
@[specialize] def bandRowsCB (T : Int) (B : Nat) (cnt : Array Nat) (M : Nat) {Gt : Type} [GRead Gt] (rb : ByteArray)
    (gb : Gt) (e : Nat) : Nat → ByteArray → ByteArray → ByteArray → Option ByteArray
  | i, N, X, Y =>
    if rb.size ≤ e + i + B then
      let h := cnt[i / 25]!
      let tN := T + 4 * (h : Int)
      match bandLoopB M (-tN) (-(tN + (if h = 0 then 6 else 4))) rb gb e i (i == rb.size)
          (min (2 * B) (e + i + B - rb.size)) (i + B - rb.size) (e + i + B - rb.size - (i + B - rb.size)) N X Y false with
      | (N, X, Y, alive) =>
        if alive then
          match i with
          | 0 => some N
          | i + 1 => bandRowsCB T B cnt M rb gb e i N X Y
        else none
    else none

theorem bandLoop_size (sc : Scoring) (T To : Int) {Gt : Type} [GRead Gt] (rb : ByteArray) (gb : Gt) (e i : Nat)
    (lastRow : Bool) (hi : Nat) :
    ∀ m k p (N X Y : Array Int) (alive : Bool), hi + 1 - k = m →
      (bandLoop sc T To rb gb e i lastRow hi k p N X Y alive).1.size = N.size ∧
      (bandLoop sc T To rb gb e i lastRow hi k p N X Y alive).2.1.size = X.size ∧
      (bandLoop sc T To rb gb e i lastRow hi k p N X Y alive).2.2.1.size = Y.size := by
  intro m
  induction m with
  | zero => intro k p N X Y alive hm; rw [bandLoop, if_neg (by omega)]; exact ⟨rfl, rfl, rfl⟩
  | succ m ih =>
    intro k p N X Y alive hm
    rw [bandLoop, if_pos (by omega)]
    generalize cellVals sc rb gb i p lastRow (p == e) N[k + 1]! X[k]! Y[k + 2]! = v
    obtain ⟨a1, a2, a3⟩ := ih (k + 1) (p - 1) (N.set! (k + 1) v.1) (X.set! (k + 1) v.2.1) (Y.set! (k + 1) v.2.2)
      (alive || decide (T ≤ v.1) || decide (To ≤ v.2.1) || decide (To ≤ v.2.2)) (by omega)
    simp only [Array.size_set!] at a1 a2 a3
    exact ⟨a1, a2, a3⟩

theorem bandRowsCB_rel (T : Int) (hT0 : T ≤ 0) (B : Nat) (cnt : Array Nat) (M : Nat) (hM : M < 256)
    (hTM : -T < M) {Gt : Type} [GRead Gt] (rb : ByteArray) (gb : Gt) (e : Nat) :
    ∀ i (N X Y : Array Int) (Nb Xb Yb : ByteArray), N.size = 2 * B + 3 → X.size = 2 * B + 3 →
      Y.size = 2 * B + 3 → RelRow M N Nb → RelRow M X Xb → RelRow M Y Yb →
      match bandRowsC T B cnt rb gb e i N X Y, bandRowsCB T B cnt M rb gb e i Nb Xb Yb with
      | some A, some Ab => RelRow M A Ab
      | none, none => True
      | _, _ => False := by
  intro i
  induction i with
  | zero =>
    intro N X Y Nb Xb Yb hNs hXs hYs hN hX hY
    rw [bandRowsC, bandRowsCB]
    by_cases hin : rb.size ≤ e + 0 + B
    · simp only [hin, if_true]
      have hr := bandLoopB_rel M hM (T + 4 * (cnt[0 / 25]! : Int))
        (T + 4 * (cnt[0 / 25]! : Int) + (if cnt[0 / 25]! = 0 then 6 else 4)) (by omega) (by split <;> omega)
        rb gb e 0 (0 == rb.size) (min (2 * B) (e + 0 + B - rb.size)) _ (0 + B - rb.size)
        (e + 0 + B - rb.size - (0 + B - rb.size)) N X Y Nb Xb Yb false rfl (by omega) (by omega) (by omega) hN hX hY
      revert hr
      generalize bandLoop sc0 (T + 4 * (cnt[0 / 25]! : Int))
        (T + 4 * (cnt[0 / 25]! : Int) + (if cnt[0 / 25]! = 0 then 6 else 4)) rb gb e 0 (0 == rb.size)
        (min (2 * B) (e + 0 + B - rb.size)) (0 + B - rb.size) (e + 0 + B - rb.size - (0 + B - rb.size)) N X Y false = r
      generalize bandLoopB M (-(T + 4 * (cnt[0 / 25]! : Int)))
        (-(T + 4 * (cnt[0 / 25]! : Int) + (if cnt[0 / 25]! = 0 then 6 else 4))) rb gb e 0 (0 == rb.size)
        (min (2 * B) (e + 0 + B - rb.size)) (0 + B - rb.size) (e + 0 + B - rb.size - (0 + B - rb.size)) Nb Xb Yb false = rb'
      obtain ⟨N', X', Y', a⟩ := r
      obtain ⟨Nb', Xb', Yb', a'⟩ := rb'
      rintro ⟨h1, -, -, h4⟩
      simp only at h1 h4
      subst h4
      cases a <;> simp [h1]
    · simp only [hin, if_false]
  | succ i ih =>
    intro N X Y Nb Xb Yb hNs hXs hYs hN hX hY
    rw [bandRowsC, bandRowsCB]
    by_cases hin : rb.size ≤ e + (i + 1) + B
    · simp only [hin, if_true]
      have hr := bandLoopB_rel M hM (T + 4 * (cnt[(i + 1) / 25]! : Int))
        (T + 4 * (cnt[(i + 1) / 25]! : Int) + (if cnt[(i + 1) / 25]! = 0 then 6 else 4)) (by omega) (by split <;> omega)
        rb gb e (i + 1) (i + 1 == rb.size) (min (2 * B) (e + (i + 1) + B - rb.size)) _ (i + 1 + B - rb.size)
        (e + (i + 1) + B - rb.size - (i + 1 + B - rb.size)) N X Y Nb Xb Yb false rfl (by omega) (by omega) (by omega)
        hN hX hY
      have hsz := bandLoop_size sc0 (T + 4 * (cnt[(i + 1) / 25]! : Int))
        (T + 4 * (cnt[(i + 1) / 25]! : Int) + (if cnt[(i + 1) / 25]! = 0 then 6 else 4))
        rb gb e (i + 1) (i + 1 == rb.size) (min (2 * B) (e + (i + 1) + B - rb.size)) _ (i + 1 + B - rb.size)
        (e + (i + 1) + B - rb.size - (i + 1 + B - rb.size)) N X Y false rfl
      revert hr hsz
      generalize bandLoop sc0 (T + 4 * (cnt[(i + 1) / 25]! : Int))
        (T + 4 * (cnt[(i + 1) / 25]! : Int) + (if cnt[(i + 1) / 25]! = 0 then 6 else 4)) rb gb e (i + 1)
        (i + 1 == rb.size) (min (2 * B) (e + (i + 1) + B - rb.size)) (i + 1 + B - rb.size)
        (e + (i + 1) + B - rb.size - (i + 1 + B - rb.size)) N X Y false = r
      generalize bandLoopB M (-(T + 4 * (cnt[(i + 1) / 25]! : Int)))
        (-(T + 4 * (cnt[(i + 1) / 25]! : Int) + (if cnt[(i + 1) / 25]! = 0 then 6 else 4))) rb gb e (i + 1)
        (i + 1 == rb.size) (min (2 * B) (e + (i + 1) + B - rb.size)) (i + 1 + B - rb.size)
        (e + (i + 1) + B - rb.size - (i + 1 + B - rb.size)) Nb Xb Yb false = rb'
      obtain ⟨N', X', Y', a⟩ := r
      obtain ⟨Nb', Xb', Yb', a'⟩ := rb'
      rintro ⟨h1, h2, h3, h4⟩ ⟨s1, s2, s3⟩
      simp only at h1 h2 h3 h4 s1 s2 s3
      subst h4
      cases a
      · simp
      · simp only [if_true]
        exact ih N' X' Y' Nb' Xb' Yb' (by omega) (by omega) (by omega) h1 h2 h3
    · simp only [hin, if_false]

/-- All windows ending at `e`, byte pass, penalties saturated at `M`. -/
@[specialize] def bandEndCB (T : Int) (B : Nat) (cnt : Array Nat) (M : Nat) {Gt : Type} [GRead Gt] (rb : ByteArray)
    (gb : Gt) (e : Nat) : Option ByteArray :=
  let z : ByteArray := ⟨Array.replicate (2 * B + 3) (satP M (T - 1)).toUInt8⟩
  bandRowsCB T B cnt M rb gb e rb.size z z z

/-- A byte row back as scores. -/
def toIntRow (Bb : ByteArray) : Array Int := (Array.range Bb.size).map fun j => -((Bb.get! j).toNat : Int)

theorem relRow_init (M : Nat) (hM : M < 256) (T : Int) (hT : T ≤ 0) (n : Nat) :
    RelRow M (Array.replicate n (T - 1)) ⟨Array.replicate n (satP M (T - 1)).toUInt8⟩ := by
  refine ⟨by simp [ByteArray.size], fun j hj => ?_⟩
  simp only [Array.size_replicate] at hj
  rw [getElem!_pos _ _ (by simpa using hj)]
  simp only [Array.getElem_replicate, ByteArray.get!]
  rw [getElem!_pos _ _ (by simpa using hj)]
  simp only [Array.getElem_replicate]
  refine ⟨by omega, ?_⟩
  have := satP_le M (T - 1)
  simp only [UInt8.toNat_ofNat', Nat.toUInt8]
  exact Nat.mod_eq_of_lt (by omega)

/-- The byte pass and the `Int` pass: both `none`, or rows related. -/
theorem bandEndCB_rel (T : Int) (hT0 : T ≤ 0) (B : Nat) (cnt : Array Nat) (M : Nat) (hM : M < 256) (hTM : -T < M)
    {Gt : Type} [GRead Gt] (rb : ByteArray) (gb : Gt) (e : Nat) :
    match bandEndC T B cnt rb gb e, bandEndCB T B cnt M rb gb e with
    | some A, some Ab => RelRow M A Ab
    | none, none => True
    | _, _ => False := by
  unfold bandEndC bandEndCB
  exact bandRowsCB_rel T hT0 B cnt M hM hTM rb gb e rb.size _ _ _ _ _ _ (by simp) (by simp) (by simp)
    (relRow_init M hM T hT0 _) (relRow_init M hM T hT0 _) (relRow_init M hM T hT0 _)

/-- Reading a related row: exact at scores `≥ −P`, below `−P` otherwise (`M = P + 1`). -/
theorem relRow_read (P : Nat) (A : Array Int) (Bb : ByteArray) (h : RelRow (P + 1) A Bb) (j : Nat) (hj : j < A.size) :
    ((-(P : Int) ≤ A[j]!) → (toIntRow Bb)[j]! = A[j]!) ∧ (A[j]! < -(P : Int) → (toIntRow Bb)[j]! < -(P : Int)) := by
  obtain ⟨hs, hr⟩ := h
  have hj' : j < Bb.size := by omega
  have e1 : (toIntRow Bb)[j]! = -((Bb.get! j).toNat : Int) := by
    unfold toIntRow
    rw [getElem!_pos _ _ (by simpa using hj')]
    simp
  obtain ⟨h0, h1⟩ := hr j hj
  rw [e1, h1]
  unfold satP
  constructor <;> intro hh <;> omega

end MapSpec
