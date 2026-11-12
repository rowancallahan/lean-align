import ReadWindowTrimmer
import ParStream

/-!
# Codec `trimRead`: the proved read-window trimmer on FASTQ bytes

Per base: Phred quality `q` (FASTQ byte − 33, at most 93) for A/C/G/T, scored
`q − Q` for a neutral quality `Q ≤ 93` (`trimReadQ Q`; below `Q` costs); any other
letter (N) scores `−1 000 000`.  `trimRead` is `trimReadQ defQ` (defQ = 25).  The kept window is the best-scoring window of the frozen
contract (`get_best_window`, trimmer/ReadWindowTrimmer/Contract.lean), computed
by the packed trimmer (`getBestWindowPacked`).

    trimReadQ Q seq qual = get_best_window [] (scoresOf seq qual) (·.map (perBase Q))
      for every Q ≤ 93 and read with an A/C/G/T letter    (trimRead_eq_contract)
    trimReadQ Q seq qual = some (s, e) → e ≤ seq.size ∧ s < e ∧
      ∀ i, s ≤ i → i < e → isACGT seq[i]! = true          (trimRead_acgt)

Reads with no A/C/G/T or longer than 10 000 letters give `none`.

Chunked output: the texts of the chunks, in order, are the text of the whole
input mapped (`chunks_text`), however the input is cut.
-/

namespace ReadTrim

open ReadWindow

def isACGT (b : UInt8) : Bool := b == 65 || b == 67 || b == 71 || b == 84

/-- Encoded per-base value: quality for A/C/G/T, −1 otherwise. -/
@[inline] def enc (b qc : UInt8) : Int := if isACGT b then ((min (qc.toNat - 33) 93 : Nat) : Int) else -1

@[inline] def perBase (Q : Nat) (v : Int) : Int := if v < 0 then -1000000 else v - Q

def scoresOf (seq qual : ByteArray) : List Int := (List.range seq.size).map fun i => enc seq[i]! qual[i]!

/-- The packed trimmer's fold over `scoresOf`, run on the bytes from the end
(no list; `winLoop_eq`). -/
def winLoop (Q : Nat) (seq qual : ByteArray) : Nat → PackedFoldState → PackedFoldState
  | 0, st => st
  | i + 1, st => winLoop Q seq qual i (packedFoldStep (perBase Q) (enc seq[i]! qual[i]!) st)

/-- `winLoop` with the state's fields as arguments (no state allocated per base; `wl_eq`). -/
def wl (Q : Nat) (seq qual : ByteArray) : Nat → Nat → Bool → Nat → Int → Nat → Nat → Int → PackedFoldState
  | 0, ns, hr, pl, ps, bs, be, bsc => ⟨ns, hr, pl, ps, bs, be, bsc⟩
  | i + 1, ns, hr, pl, ps, bs, be, bsc =>
    let cs := ns - 1
    let f := perBase Q (enc seq[i]! qual[i]!)
    if hr then
      if 0 < ps then
        if bsc ≤ f + ps then wl Q seq qual i cs true (pl + 1) (f + ps) cs (cs + (pl + 1)) (f + ps)
        else wl Q seq qual i cs true (pl + 1) (f + ps) bs be bsc
      else if bsc ≤ f then wl Q seq qual i cs true 1 f cs (cs + 1) f
      else wl Q seq qual i cs true 1 f bs be bsc
    else wl Q seq qual i cs true 1 f cs (cs + 1) f

/-! `wl` with the scores in `Int64` (compiled code only): `wl_eq_wlF` (`@[csimp]`). For reads of at
most 10 000 letters every prefix score is within ±2·10^6 per letter, far inside 64 bits. -/

/-- `perBase Q (enc b qc)` in `Int64` (`fI_eq`). -/
@[inline] def fI (Q : Int64) (b qc : UInt8) : Int64 :=
  if isACGT b then Int64.ofNat (min (qc.toNat - 33) 93) - Q else -1000000

theorem i64_ofNat (n : Nat) (h : n < 2 ^ 62) : (Int64.ofNat n).toInt = n := by
  have e : Int64.size = 18446744073709551616 := rfl
  rw [Int64.toInt_ofNat', e, Int.bmod_eq_of_le (by omega) (by omega)]

theorem i64_add (a b : Int64) (ha : -2 ^ 61 ≤ a.toInt ∧ a.toInt ≤ 2 ^ 61) (hb : -2 ^ 61 ≤ b.toInt ∧ b.toInt ≤ 2 ^ 61) :
    (a + b).toInt = a.toInt + b.toInt := by
  rw [Int64.toInt_add]; exact Int.bmod_eq_of_le (by omega) (by omega)

theorem fI_eq (Q : Nat) (hQ : Q ≤ 1000) (b qc : UInt8) :
    (fI (Int64.ofNat Q) b qc).toInt = perBase Q (enc b qc) := by
  have eQ := i64_ofNat Q (by omega)
  unfold fI perBase enc
  by_cases h : isACGT b = true
  · simp only [h, if_true]
    have hm : min (qc.toNat - 33) 93 ≤ 93 := Nat.min_le_right _ _
    have em := i64_ofNat (min (qc.toNat - 33) 93) (by omega)
    rw [if_neg (by omega), Int64.toInt_sub, em, eQ, Int.bmod_eq_of_le (by omega) (by omega)]
  · simp only [h, Bool.false_eq_true, if_false]
    rw [if_pos (by omega)]; rfl

theorem fI_bd (Q : Nat) (hQ : Q ≤ 1000) (b qc : UInt8) :
    -1000000 ≤ (fI (Int64.ofNat Q) b qc).toInt ∧ (fI (Int64.ofNat Q) b qc).toInt ≤ 1000000 := by
  rw [fI_eq Q hQ]; unfold perBase enc
  split
  · omega
  · split
    · have : min (qc.toNat - 33) 93 ≤ 93 := Nat.min_le_right _ _
      omega
    · omega

/-- `wl` with `Int64` scores (`wlI_eq`). -/
def wlI (Q : Int64) (seq qual : ByteArray) : Nat → Nat → Bool → Nat → Int64 → Nat → Nat → Int64 → PackedFoldState
  | 0, ns, hr, pl, ps, bs, be, bsc => ⟨ns, hr, pl, ps.toInt, bs, be, bsc.toInt⟩
  | i + 1, ns, hr, pl, ps, bs, be, bsc =>
    let cs := ns - 1
    let f := fI Q seq[i]! qual[i]!
    if hr then
      if 0 < ps then
        if bsc ≤ f + ps then wlI Q seq qual i cs true (pl + 1) (f + ps) cs (cs + (pl + 1)) (f + ps)
        else wlI Q seq qual i cs true (pl + 1) (f + ps) bs be bsc
      else if bsc ≤ f then wlI Q seq qual i cs true 1 f cs (cs + 1) f
      else wlI Q seq qual i cs true 1 f bs be bsc
    else wlI Q seq qual i cs true 1 f cs (cs + 1) f

theorem wlI_eq (Q : Nat) (hQ : Q ≤ 1000) (seq qual : ByteArray) : ∀ (i ns : Nat) (hr : Bool) (pl : Nat)
    (ps : Int64) (bs be : Nat) (bsc : Int64), i ≤ 20000 →
    -(2000000 * ((20000 - i : Nat) : Int)) ≤ ps.toInt ∧ ps.toInt ≤ 2000000 * ((20000 - i : Nat) : Int) →
    -(2000000 * ((20000 - i : Nat) : Int)) ≤ bsc.toInt ∧ bsc.toInt ≤ 2000000 * ((20000 - i : Nat) : Int) →
    wlI (Int64.ofNat Q) seq qual i ns hr pl ps bs be bsc = wl Q seq qual i ns hr pl ps.toInt bs be bsc.toInt
  | 0, ns, hr, pl, ps, bs, be, bsc, _, _, _ => rfl
  | i + 1, ns, hr, pl, ps, bs, be, bsc, hi, hp, hb => by
    have hf := fI_bd Q hQ seq[i]! qual[i]!
    have ef := fI_eq Q hQ seq[i]! qual[i]!
    have e2 : ((20000 - i : Nat) : Int) = ((20000 - (i + 1) : Nat) : Int) + 1 := by omega
    have hsum : (fI (Int64.ofNat Q) seq[i]! qual[i]! + ps).toInt = (fI (Int64.ofNat Q) seq[i]! qual[i]!).toInt + ps.toInt :=
      i64_add _ _ (by omega) (by omega)
    have bF : -(2000000 * ((20000 - i : Nat) : Int)) ≤ (fI (Int64.ofNat Q) seq[i]! qual[i]!).toInt ∧
        (fI (Int64.ofNat Q) seq[i]! qual[i]!).toInt ≤ 2000000 * ((20000 - i : Nat) : Int) := by omega
    have bS : -(2000000 * ((20000 - i : Nat) : Int)) ≤ (fI (Int64.ofNat Q) seq[i]! qual[i]! + ps).toInt ∧
        (fI (Int64.ofNat Q) seq[i]! qual[i]! + ps).toInt ≤ 2000000 * ((20000 - i : Nat) : Int) := by omega
    have bB : -(2000000 * ((20000 - i : Nat) : Int)) ≤ bsc.toInt ∧ bsc.toInt ≤ 2000000 * ((20000 - i : Nat) : Int) := by omega
    have bP : -(2000000 * ((20000 - i : Nat) : Int)) ≤ ps.toInt ∧ ps.toInt ≤ 2000000 * ((20000 - i : Nat) : Int) := by omega
    have c1 : (0 < ps) ↔ (0 < ps.toInt) := by rw [Int64.lt_iff_toInt_lt]; simp
    have c2 : (bsc ≤ fI (Int64.ofNat Q) seq[i]! qual[i]! + ps) ↔
        (bsc.toInt ≤ (fI (Int64.ofNat Q) seq[i]! qual[i]!).toInt + ps.toInt) := by rw [Int64.le_iff_toInt_le, hsum]
    have c3 : (bsc ≤ fI (Int64.ofNat Q) seq[i]! qual[i]!) ↔ (bsc.toInt ≤ (fI (Int64.ofNat Q) seq[i]! qual[i]!).toInt) :=
      Int64.le_iff_toInt_le
    simp only [wlI, wl]
    rw [← ef]
    cases hr
    · simp only [Bool.false_eq_true, if_false]
      exact wlI_eq Q hQ seq qual i _ _ _ _ _ _ _ (by omega) bF bF
    · simp only [if_true]
      by_cases h0 : 0 < ps.toInt
      · rw [if_pos (c1.mpr h0), if_pos h0]
        by_cases h1 : bsc.toInt ≤ (fI (Int64.ofNat Q) seq[i]! qual[i]!).toInt + ps.toInt
        · rw [if_pos (c2.mpr h1), if_pos h1, wlI_eq Q hQ seq qual i _ _ _ _ _ _ _ (by omega) bS bS, hsum]
        · rw [if_neg (fun c => h1 (c2.mp c)), if_neg h1, wlI_eq Q hQ seq qual i _ _ _ _ _ _ _ (by omega) bS bB, hsum]
      · rw [if_neg (fun c => h0 (c1.mp c)), if_neg h0]
        by_cases h1 : bsc.toInt ≤ (fI (Int64.ofNat Q) seq[i]! qual[i]!).toInt
        · rw [if_pos (c3.mpr h1), if_pos h1, wlI_eq Q hQ seq qual i _ _ _ _ _ _ _ (by omega) bF bF]
        · rw [if_neg (fun c => h1 (c3.mp c)), if_neg h1, wlI_eq Q hQ seq qual i _ _ _ _ _ _ _ (by omega) bF bB]

/-! `wlI` with the counters in `USize` and the bytes read by `uget` (`wlU_eq`; all counters stay below 2^31). -/

theorem rt_usize_le (B : ByteArray) : B.usize.toNat ≤ B.size := by
  show B.size.toUSize.toNat ≤ B.size
  rw [Nat.toUSize_eq, USize.toNat_ofNat']; exact Nat.mod_le _ _

theorem rt_n (n : Nat) (h : n < 2 ^ 32) : n.toUSize.toNat = n := by
  rw [Nat.toUSize_eq, USize.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h USize.le_size)]

theorem rt_add (a b : USize) (h : a.toNat + b.toNat < 2 ^ 32) : (a + b).toNat = a.toNat + b.toNat := by
  rw [USize.toNat_add, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h USize.le_size)]

theorem rt_one : (1 : USize).toNat = 1 := rt_n 1 (by decide)

theorem rt_sub1 (a : USize) (h : a ≠ 0) : (a - 1).toNat = a.toNat - 1 := by
  have : a.toNat ≠ 0 := fun e => h (USize.toNat_inj.mp (by rw [e]; rfl))
  rw [USize.toNat_sub_of_le _ _ (by show (1 : USize).toNat ≤ a.toNat; rw [rt_one]; omega), rt_one]

/-- `B[p.toNat]!` with one machine-word bounds check. -/
@[inline] def rtGet (B : ByteArray) (p : USize) : UInt8 :=
  if h : p < B.usize then B.uget p (Nat.lt_of_lt_of_le h (rt_usize_le B)) else B[p.toNat]!

theorem rtGet_eq (B : ByteArray) (p : USize) : rtGet B p = B[p.toNat]! := by
  unfold rtGet; split
  · rename_i h
    have h' : p.toNat < B.size := Nat.lt_of_lt_of_le h (rt_usize_le B)
    rw [getElem!_pos B p.toNat h']; rfl
  · rfl

def wlU (Q : Int64) (seq qual : ByteArray) (i ns : USize) (hr : Bool) (pl : USize) (ps : Int64) (bs be : USize)
    (bsc : Int64) : PackedFoldState :=
  if h : i = 0 then ⟨ns.toNat, hr, pl.toNat, ps.toInt, bs.toNat, be.toNat, bsc.toInt⟩
  else
    let j := i - 1
    let cs := if ns = 0 then 0 else ns - 1
    let f := fI Q (rtGet seq j) (rtGet qual j)
    if hr then
      if 0 < ps then
        if bsc ≤ f + ps then wlU Q seq qual j cs true (pl + 1) (f + ps) cs (cs + (pl + 1)) (f + ps)
        else wlU Q seq qual j cs true (pl + 1) (f + ps) bs be bsc
      else if bsc ≤ f then wlU Q seq qual j cs true 1 f cs (cs + 1) f
      else wlU Q seq qual j cs true 1 f bs be bsc
    else wlU Q seq qual j cs true 1 f cs (cs + 1) f
termination_by i.toNat
decreasing_by
  all_goals
    have : i.toNat ≠ 0 := fun e => h (USize.toNat_inj.mp (by rw [e]; rfl))
    rw [rt_sub1 i h]; omega

theorem wlU_eq (Q : Int64) (seq qual : ByteArray) : ∀ (i : Nat) (iU nsU plU bsU beU : USize) (hr : Bool)
    (ps bsc : Int64), iU.toNat = i → nsU.toNat < 2 ^ 30 → plU.toNat + i < 2 ^ 30 → bsU.toNat < 2 ^ 31 →
    beU.toNat < 2 ^ 31 →
    wlU Q seq qual iU nsU hr plU ps bsU beU bsc =
      wlI Q seq qual i nsU.toNat hr plU.toNat ps bsU.toNat beU.toNat bsc
  | 0, iU, nsU, plU, bsU, beU, hr, ps, bsc, hi, _, _, _, _ => by
    have : iU = 0 := USize.toNat_inj.mp (by rw [hi]; rfl)
    rw [wlU, dif_pos this]; rfl
  | i + 1, iU, nsU, plU, bsU, beU, hr, ps, bsc, hi, hn, hp, hb, he => by
    have h0 : iU ≠ 0 := fun e => by rw [e] at hi; simp at hi
    have ej : (iU - 1).toNat = i := by rw [rt_sub1 iU h0, hi]; rfl
    have ecs : (if nsU = 0 then 0 else nsU - 1 : USize).toNat = nsU.toNat - 1 := by
      split
      · rename_i e; rw [e]; rfl
      · rename_i e; exact rt_sub1 nsU e
    have epl : (plU + 1).toNat = plU.toNat + 1 := by rw [rt_add _ _ (by rw [rt_one]; omega), rt_one]
    have ecp : ((if nsU = 0 then 0 else nsU - 1 : USize) + (plU + 1)).toNat = (nsU.toNat - 1) + (plU.toNat + 1) := by
      rw [rt_add _ _ (by rw [ecs, epl]; omega), ecs, epl]
    have ec1 : ((if nsU = 0 then 0 else nsU - 1 : USize) + 1).toNat = (nsU.toNat - 1) + 1 := by
      rw [rt_add _ _ (by rw [ecs, rt_one]; omega), ecs, rt_one]
    have eo : (1 : USize).toNat = 1 := rt_one
    rw [wlU, dif_neg h0]
    simp only [wlI, rtGet_eq, ej]
    have ih := fun (plU' bsU' beU' : USize) (hr' : Bool) (ps' bsc' : Int64) (hp' : plU'.toNat + i < 2 ^ 30)
      (hb' : bsU'.toNat < 2 ^ 31) (he' : beU'.toNat < 2 ^ 31) =>
      wlU_eq Q seq qual i (iU - 1) (if nsU = 0 then 0 else nsU - 1) plU' bsU' beU' hr' ps' bsc' ej
        (by rw [ecs]; omega) hp' hb' he'
    split
    · split
      · split
        · rw [ih _ _ _ _ _ _ (by rw [epl]; omega) (by rw [ecs]; omega) (by rw [ecp]; omega), epl, ecs, ecp]
        · rw [ih _ _ _ _ _ _ (by rw [epl]; omega) hb he, epl, ecs]
      · split
        · rw [ih _ _ _ _ _ _ (by rw [eo]; omega) (by rw [ecs]; omega) (by rw [ec1]; omega), eo, ecs, ec1]
        · rw [ih _ _ _ _ _ _ (by rw [eo]; omega) hb he, eo, ecs]
    · rw [ih _ _ _ _ _ _ (by rw [eo]; omega) (by rw [ecs]; omega) (by rw [ec1]; omega), eo, ecs, ec1]

/-- `fI` with the quality in `UInt8` arithmetic (`fIU_eq`). -/
@[inline] def fIU (Q : Int64) (b qc : UInt8) : Int64 :=
  if isACGT b then (if qc < 33 then (0 : UInt8) else min (qc - 33) 93).toUInt64.toInt64 - Q else -1000000

/-- `wlU` with `fIU` and the literal `0` passed in as `z` (a literal `Int64` in the loop is fetched through
`lean_uint64_once` every step): `wlU2_eq`. -/
def wlU2 (Q z : Int64) (seq qual : ByteArray) (i ns : USize) (hr : Bool) (pl : USize) (ps : Int64) (bs be : USize)
    (bsc : Int64) : PackedFoldState :=
  if h : i = 0 then ⟨ns.toNat, hr, pl.toNat, ps.toInt, bs.toNat, be.toNat, bsc.toInt⟩
  else
    let j := i - 1
    let cs := if ns = 0 then 0 else ns - 1
    let f := fIU Q (rtGet seq j) (rtGet qual j)
    if hr then
      if z < ps then
        if bsc ≤ f + ps then wlU2 Q z seq qual j cs true (pl + 1) (f + ps) cs (cs + (pl + 1)) (f + ps)
        else wlU2 Q z seq qual j cs true (pl + 1) (f + ps) bs be bsc
      else if bsc ≤ f then wlU2 Q z seq qual j cs true 1 f cs (cs + 1) f
      else wlU2 Q z seq qual j cs true 1 f bs be bsc
    else wlU2 Q z seq qual j cs true 1 f cs (cs + 1) f
termination_by i.toNat
decreasing_by
  all_goals
    have : i.toNat ≠ 0 := fun e => h (USize.toNat_inj.mp (by rw [e]; rfl))
    rw [rt_sub1 i h]; omega

set_option maxRecDepth 8000 in
theorem qcU_all : ∀ n, n < 256 → (if (UInt8.ofNat n) < 33 then (0 : UInt8) else min (UInt8.ofNat n - 33) 93).toUInt64.toInt64 =
    Int64.ofNat (min ((UInt8.ofNat n).toNat - 33) 93) := by
  decide

theorem qcU_eq (qc : UInt8) :
    (if qc < 33 then (0 : UInt8) else min (qc - 33) 93).toUInt64.toInt64 = Int64.ofNat (min (qc.toNat - 33) 93) := by
  have := qcU_all qc.toNat qc.toNat_lt
  rwa [UInt8.ofNat_toNat] at this

theorem fIU_eq (Q : Int64) (b qc : UInt8) : fIU Q b qc = fI Q b qc := by
  unfold fIU fI; rw [qcU_eq]

theorem wlU2_eq (Q : Int64) (seq qual : ByteArray) : ∀ (n : Nat) (iU : USize), iU.toNat = n →
    ∀ ns hr pl ps bs be bsc, wlU2 Q 0 seq qual iU ns hr pl ps bs be bsc = wlU Q seq qual iU ns hr pl ps bs be bsc := by
  intro n
  induction n with
  | zero =>
    intro iU hi ns hr pl ps bs be bsc
    have : iU = 0 := USize.toNat_inj.mp (by rw [hi]; rfl)
    rw [wlU2, wlU, dif_pos this, dif_pos this]
  | succ n ih =>
    intro iU hi ns hr pl ps bs be bsc
    have h0 : iU ≠ 0 := fun e => by rw [e] at hi; simp at hi
    have ej : (iU - 1).toNat = n := by rw [rt_sub1 iU h0, hi]; rfl
    rw [wlU2, wlU, dif_neg h0, dif_neg h0]
    simp only [fIU_eq, ih _ ej]

/-- `wlU2` from the full read (`trimReadQ`'s call: `ns = i`, and `hr` is true after the first letter), the current
run kept as its right end `re` instead of its length (`pl = re − i`): `wlR_eq`. -/
def wlR (Q z : Int64) (seq qual : ByteArray) (i re : USize) (ps : Int64) (bs be : USize) (bsc : Int64) : PackedFoldState :=
  if h : i = 0 then ⟨0, true, re.toNat, ps.toInt, bs.toNat, be.toNat, bsc.toInt⟩
  else
    let j := i - 1
    let f := fIU Q (rtGet seq j) (rtGet qual j)
    if z < ps then
      let ps' := f + ps
      if bsc ≤ ps' then wlR Q z seq qual j re ps' j re ps' else wlR Q z seq qual j re ps' bs be bsc
    else if bsc ≤ f then wlR Q z seq qual j (j + 1) f j (j + 1) f
    else wlR Q z seq qual j (j + 1) f bs be bsc
termination_by i.toNat
decreasing_by
  all_goals
    have : i.toNat ≠ 0 := fun e => h (USize.toNat_inj.mp (by rw [e]; rfl))
    rw [rt_sub1 i h]; omega

theorem wlR_eq (Q : Int64) (seq qual : ByteArray) : ∀ (n : Nat) (iU reU : USize), iU.toNat = n → n ≤ reU.toNat →
    reU.toNat < 2 ^ 30 → ∀ ps bs be bsc,
      wlR Q 0 seq qual iU reU ps bs be bsc = wlU2 Q 0 seq qual iU iU true (reU - iU) ps bs be bsc := by
  intro n
  induction n with
  | zero =>
    intro iU reU hi _ _ ps bs be bsc
    have h0 : iU = 0 := USize.toNat_inj.mp (by rw [hi]; rfl)
    rw [wlR, wlU2, dif_pos h0, dif_pos h0]
    subst h0
    simp only [USize.toNat_zero, USize.sub_zero]
  | succ n ih =>
    intro iU reU hi hle hre ps bs be bsc
    have h0 : iU ≠ 0 := fun e => by rw [e] at hi; simp at hi
    have ej : (iU - 1).toNat = n := by rw [rt_sub1 iU h0, hi]; rfl
    have hns : (if iU = 0 then 0 else iU - 1 : USize) = iU - 1 := by rw [if_neg h0]
    -- the run length after a step, as the run end
    have s0 : (reU - iU).toNat = reU.toNat - (n + 1) := by
      rw [USize.toNat_sub_of_le reU iU (show iU.toNat ≤ reU.toNat by omega), hi]
    have s1 : (reU - (iU - 1)).toNat = reU.toNat - n := by
      rw [USize.toNat_sub_of_le reU (iU - 1) (show (iU - 1).toNat ≤ reU.toNat by omega), ej]
    have s2 : ((iU - 1) + 1).toNat = n + 1 := by rw [rt_add _ _ (by rw [ej, rt_one]; omega), ej, rt_one]
    have hpl : (reU - iU) + 1 = reU - (iU - 1) := by
      apply USize.toNat_inj.mp
      rw [rt_add _ _ (by rw [s0, rt_one]; omega), s0, rt_one, s1]; omega
    have hbe : (iU - 1) + (reU - (iU - 1)) = reU := by
      apply USize.toNat_inj.mp
      rw [rt_add _ _ (by rw [ej, s1]; omega), ej, s1]; omega
    have hone : ((iU - 1) + 1) - (iU - 1) = (1 : USize) := by
      apply USize.toNat_inj.mp
      rw [USize.toNat_sub_of_le ((iU - 1) + 1) (iU - 1) (show (iU - 1).toNat ≤ ((iU - 1) + 1).toNat by omega), s2, ej, rt_one]
      omega
    have ih1 := fun reU' ps' bs' be' bsc' (h1 : n ≤ reU'.toNat) (h2 : reU'.toNat < 2 ^ 30) =>
      ih (iU - 1) reU' ej h1 h2 ps' bs' be' bsc'
    have hj1 : n ≤ ((iU - 1) + 1).toNat := by rw [s2]; omega
    have hj2 : ((iU - 1) + 1).toNat < 2 ^ 30 := by rw [s2]; omega
    rw [wlR, wlU2, dif_neg h0, dif_neg h0]
    simp only [hns, if_true]
    split
    · split
      · rw [ih1 _ _ _ _ _ (by omega) hre, hpl, hbe]
      · rw [ih1 _ _ _ _ _ (by omega) hre, hpl]
    · split
      · rw [ih1 _ _ _ _ _ hj1 hj2, hone]
      · rw [ih1 _ _ _ _ _ hj1 hj2, hone]

theorem rtGet_uget (B : ByteArray) (p : USize) (h : p.toNat < B.size) : rtGet B p = B.uget p h := by
  rw [rtGet_eq, getElem!_pos B p.toNat h]; rfl

/-- `wlR` with the bounds of `seq` and `qual` as hypotheses: the letter and quality loads are plain `uget`s (`wlRH_eq`). -/
def wlRH (Q z : Int64) (seq qual : ByteArray) (i re : USize) (ps : Int64) (bs be : USize) (bsc : Int64)
    (hs : i.toNat ≤ seq.size) (hq : i.toNat ≤ qual.size) : PackedFoldState :=
  if h : i = 0 then ⟨0, true, re.toNat, ps.toInt, bs.toNat, be.toNat, bsc.toInt⟩
  else
    have hi : i.toNat ≠ 0 := fun e => h (USize.toNat_inj.mp (by rw [e]; rfl))
    have hj : (i - 1).toNat = i.toNat - 1 := rt_sub1 i h
    let f := fIU Q (seq.uget (i - 1) (by omega)) (qual.uget (i - 1) (by omega))
    if z < ps then
      let ps' := f + ps
      if bsc ≤ ps' then wlRH Q z seq qual (i - 1) re ps' (i - 1) re ps' (by omega) (by omega)
      else wlRH Q z seq qual (i - 1) re ps' bs be bsc (by omega) (by omega)
    else if bsc ≤ f then wlRH Q z seq qual (i - 1) ((i - 1) + 1) f (i - 1) ((i - 1) + 1) f (by omega) (by omega)
    else wlRH Q z seq qual (i - 1) ((i - 1) + 1) f bs be bsc (by omega) (by omega)
termination_by i.toNat
decreasing_by
  all_goals
    simp_wf
    omega

theorem wlRH_eq (Q z : Int64) (seq qual : ByteArray) : ∀ (n : Nat) (i re : USize) ps bs be bsc hs hq, i.toNat = n →
    wlRH Q z seq qual i re ps bs be bsc hs hq = wlR Q z seq qual i re ps bs be bsc
  | 0, i, re, ps, bs, be, bsc, hs, hq, hn => by
    have h : i = 0 := USize.toNat_inj.mp (by rw [hn]; rfl)
    rw [wlRH, wlR, dif_pos h, dif_pos h]
  | n + 1, i, re, ps, bs, be, bsc, hs, hq, hn => by
    have h : i ≠ 0 := fun e => by rw [e] at hn; simp at hn
    have hj : (i - 1).toNat = n := by rw [rt_sub1 i h, hn]; rfl
    rw [wlRH, wlR, dif_neg h, dif_neg h]
    dsimp only
    rw [← rtGet_uget seq (i - 1) (by omega), ← rtGet_uget qual (i - 1) (by omega)]
    split
    · split
      · rw [wlRH_eq Q z seq qual n (i - 1) _ _ _ _ _ (by omega) (by omega) hj]
      · rw [wlRH_eq Q z seq qual n (i - 1) _ _ _ _ _ (by omega) (by omega) hj]
    · split
      · rw [wlRH_eq Q z seq qual n (i - 1) _ _ _ _ _ (by omega) (by omega) hj]
      · rw [wlRH_eq Q z seq qual n (i - 1) _ _ _ _ _ (by omega) (by omega) hj]

/-- `wlR`, with the unchecked loop when the bounds hold (`wlRG_eq`). -/
@[inline] def wlRG (Q z : Int64) (seq qual : ByteArray) (i re : USize) (ps : Int64) (bs be : USize) (bsc : Int64) :
    PackedFoldState :=
  if h : i.toNat ≤ seq.size ∧ i.toNat ≤ qual.size then wlRH Q z seq qual i re ps bs be bsc h.1 h.2
  else wlR Q z seq qual i re ps bs be bsc

theorem wlRG_eq (Q z : Int64) (seq qual : ByteArray) (i re : USize) (ps : Int64) (bs be : USize) (bsc : Int64) :
    wlRG Q z seq qual i re ps bs be bsc = wlR Q z seq qual i re ps bs be bsc := by
  unfold wlRG; split
  · exact wlRH_eq Q z seq qual i.toNat i re ps bs be bsc _ _ rfl
  · rfl

/-- `wl` for the compiled code (`wl_eq_wlF`): `wlI` from the start state (scores 0). -/
@[inline] def wlF (Q : Nat) (seq qual : ByteArray) (i ns : Nat) (hr : Bool) (pl : Nat) (ps : Int) (bs be : Nat)
    (bsc : Int) : PackedFoldState :=
  if Q ≤ 1000 ∧ i ≤ 10000 ∧ ps = 0 ∧ bsc = 0 then
    if ns = i ∧ hr = false ∧ pl = 0 ∧ bs = 0 ∧ be = 0 ∧ 0 < i then
      let j := (i - 1).toUSize
      let f := fIU (Int64.ofNat Q) (rtGet seq j) (rtGet qual j)
      wlRG (Int64.ofNat Q) 0 seq qual j i.toUSize f j i.toUSize f
    else if ns < 1073741824 ∧ pl + i < 1073741824 ∧ bs < 2147483648 ∧ be < 2147483648 then
      wlU2 (Int64.ofNat Q) 0 seq qual i.toUSize ns.toUSize hr pl.toUSize 0 bs.toUSize be.toUSize 0
    else wlI (Int64.ofNat Q) seq qual i ns hr pl 0 bs be 0
  else wl Q seq qual i ns hr pl ps bs be bsc

@[csimp] theorem wl_eq_wlF : @wl = @wlF := by
  funext Q seq qual i ns hr pl ps bs be bsc
  unfold wlF; split
  · rename_i h
    obtain ⟨hQ, hi, rfl, rfl⟩ := h
    have e0 : (0 : Int64).toInt = 0 := rfl
    have hI := wlI_eq Q hQ seq qual i ns hr pl 0 bs be 0 (by omega) (by rw [e0]; omega) (by rw [e0]; omega)
    rw [e0] at hI
    -- `wl` = `wlU2` within the bounds
    have hU : ns < 1073741824 → pl + i < 1073741824 → bs < 2147483648 → be < 2147483648 →
        wl Q seq qual i ns hr pl 0 bs be 0 =
          wlU2 (Int64.ofNat Q) 0 seq qual i.toUSize ns.toUSize hr pl.toUSize 0 bs.toUSize be.toUSize 0 := by
      intro h1 h2 h3 h4
      rw [wlU2_eq _ seq qual i _ (rt_n i (by omega)), wlU_eq _ seq qual i _ _ _ _ _ hr 0 0 (rt_n i (by omega))
        (by rw [rt_n ns (by omega)]; omega) (by rw [rt_n pl (by omega)]; omega) (by rw [rt_n bs (by omega)]; omega)
        (by rw [rt_n be (by omega)]; omega), rt_n ns (by omega), rt_n pl (by omega), rt_n bs (by omega),
        rt_n be (by omega), hI]
    split
    · rename_i hf
      obtain ⟨hns, rfl, rfl, rfl, rfl, hpos⟩ := hf
      rw [hU (by omega) (by omega) (by omega) (by omega), hns]
      have hi0 : i.toUSize ≠ 0 := fun e => by
        have := congrArg USize.toNat e; rw [rt_n i (by omega)] at this; simp at this; omega
      have hj : i.toUSize - 1 = (i - 1).toUSize := by
        apply USize.toNat_inj.mp; rw [rt_sub1 _ hi0, rt_n i (by omega), rt_n (i - 1) (by omega)]
      have hjn : ((i - 1).toUSize).toNat = i - 1 := rt_n (i - 1) (by omega)
      have hre : i.toUSize = (i - 1).toUSize + 1 := by
        apply USize.toNat_inj.mp; rw [rt_add _ _ (by rw [hjn, rt_one]; omega), hjn, rt_one, rt_n i (by omega)]; omega
      have h1 : i.toUSize - (i - 1).toUSize = (1 : USize) := by
        apply USize.toNat_inj.mp
        rw [USize.toNat_sub_of_le _ _ (show ((i - 1).toUSize).toNat ≤ (i.toUSize).toNat by rw [hjn, rt_n i (by omega)]; omega),
          hjn, rt_n i (by omega), rt_one]; omega
      rw [wlU2, dif_neg hi0]
      simp only [if_neg hi0, hj, Bool.false_eq_true, ↓reduceIte]
      rw [wlRG_eq, wlR_eq _ seq qual (i - 1) _ _ hjn (by rw [rt_n i (by omega)]; omega) (by rw [rt_n i (by omega)]; omega), h1,
        ← hre]
    · split
      · rename_i _ hb
        exact hU hb.1 hb.2.1 hb.2.2.1 hb.2.2.2
      · exact hI.symm
  · rfl

/-- The kept window `[s, e)`, or `none` (nothing worth keeping: the best window
starts with a non-A/C/G/T letter only when the read has no A/C/G/T at all). -/
def trimReadQ (Q : Nat) (seq qual : ByteArray) : Option (Nat × Nat) :=
  if seq.size ≤ 10000 then
    match (wl Q seq qual seq.size seq.size false 0 0 0 0 0).result.map
        (fun r => (r.bestStart, r.bestEnd)) with
    | some (s, e) => if isACGT seq[s]! then some (s, e) else none
    | none => none
  else none

/-! ## Proof -/

theorem enc_le (b qc : UInt8) : enc b qc ≤ 93 := by
  unfold enc; split <;> omega

theorem enc_nonneg (b qc : UInt8) : 0 ≤ enc b qc ↔ isACGT b = true := by
  unfold enc; split <;> simp_all

theorem perBase_neg (Q : Nat) (v : Int) (h : v < 0) : perBase Q v = -1000000 := by simp [perBase, h]
theorem perBase_pos (Q : Nat) (v : Int) (h : ¬ v < 0) : perBase Q v = v - Q := by simp [perBase, h]

theorem sum_le (Q : Nat) (hQ : Q ≤ 93) (l : List Int) (h : ∀ x ∈ l, x ≤ 93) :
    (l.map (perBase Q)).sum ≤ (93 - Q : Int) * l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x List.mem_cons_self
    rw [show ((xs.length + 1 : Nat) : Int) = (xs.length : Int) + 1 by omega, Int.mul_add, Int.mul_one]
    by_cases hx0 : x < 0
    · rw [perBase_neg Q x hx0]; omega
    · rw [perBase_pos Q x hx0]; omega

theorem sum_le_neg (Q : Nat) (hQ : Q ≤ 93) (l : List Int) (h : ∀ x ∈ l, x ≤ 93) (hn : ∃ x ∈ l, x < 0) :
    (l.map (perBase Q)).sum ≤ -1000000 + (93 - Q : Int) * l.length := by
  induction l with
  | nil => simp at hn
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [show ((xs.length + 1 : Nat) : Int) = (xs.length : Int) + 1 by omega, Int.mul_add, Int.mul_one]
    have hx := h x List.mem_cons_self
    have h2 := sum_le Q hQ xs (fun y hy => h y (List.mem_cons_of_mem _ hy))
    by_cases hx0 : x < 0
    · rw [perBase_neg Q x hx0]; omega
    · obtain ⟨y, hy, hy0⟩ := hn
      rcases List.mem_cons.mp hy with rfl | hy
      · omega
      · have := ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) ⟨y, hy, hy0⟩
        rw [perBase_pos Q x hx0]; omega

theorem winLoop_eq (Q : Nat) (seq qual : ByteArray) (k : Nat) (st : PackedFoldState) :
    winLoop Q seq qual k st =
      ((List.range k).map (fun i => enc seq[i]! qual[i]!)).foldr (packedFoldStep (perBase Q)) st := by
  induction k generalizing st with
  | zero => rfl
  | succ k ih => rw [winLoop, ih, List.range_succ]; simp

theorem wl_eq (Q : Nat) (seq qual : ByteArray) (i ns : Nat) (hr : Bool) (pl : Nat) (ps : Int) (bs be : Nat)
    (bsc : Int) : wl Q seq qual i ns hr pl ps bs be bsc = winLoop Q seq qual i ⟨ns, hr, pl, ps, bs, be, bsc⟩ := by
  induction i generalizing ns hr pl ps bs be bsc with
  | zero => rfl
  | succ i ih =>
    simp only [wl, winLoop, packedFoldStep]
    cases hr <;> simp only [Bool.false_eq_true, if_false, if_true] <;> (try split) <;> (try split) <;> rw [ih]

theorem winLoop_packed (Q : Nat) (seq qual : ByteArray) :
    (winLoop Q seq qual seq.size (initialPackedFoldState seq.size)).result.map (fun r => (r.bestStart, r.bestEnd)) =
      getBestWindowPacked (scoresOf seq qual) (perBase Q) := by
  rw [winLoop_eq]; unfold getBestWindowPacked scoresOf; simp

/-- The contract's best window, when the read has an A/C/G/T letter: inside the
read, non-empty, A/C/G/T only. -/
theorem best_acgt (Q : Nat) (hQ : Q ≤ 93) (seq qual : ByteArray) (s e : Nat) (hsz : seq.size ≤ 10000) (j : Nat)
    (hj : j < seq.size) (hjA : isACGT seq[j]! = true)
    (ht : get_best_window [] (scoresOf seq qual) (fun ws => ws.map (perBase Q)) = some (s, e)) :
    e ≤ seq.size ∧ s < e ∧ ∀ i, s ≤ i → i < e → isACGT seq[i]! = true := by
    have hlen : (scoresOf seq qual).length = seq.size := by simp [scoresOf]
    have hget : ∀ i (hi : i < (scoresOf seq qual).length), (scoresOf seq qual)[i] = enc seq[i]! qual[i]! := by
      intro i hi; simp [scoresOf]
    have hv := get_best_window_returns_a_valid_window [] _ _ _ ht
    simp only at hv
    refine ⟨by omega, hv.1, fun i hsi hie => ?_⟩
    apply Classical.byContradiction; intro hnA
    have hmax := get_best_window_returns_a_maximum_score [] _ _ _ (j, j + 1) ht (by simp) (by simp; omega)
    unfold window_score at hmax
    simp only at hmax
    -- the single A/C/G/T base scores ≥ −Q ≥ −93
    have h1 : (List.take (j + 1 - j) (List.drop j (scoresOf seq qual))) = [enc seq[j]! qual[j]!] := by
      rw [show j + 1 - j = 1 by omega, List.take_one, List.head?_drop, List.getElem?_eq_getElem (by omega),
        hget j (by omega)]
      rfl
    rw [h1] at hmax
    have h0 := (enc_nonneg seq[j]! qual[j]!).2 hjA
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hmax
    -- the best window holds the non-A/C/G/T base: ≤ −1 000 000 + (93 − Q) · 10 000
    generalize hw : List.take (e - s) (List.drop s (scoresOf seq qual)) = w at hmax
    have hwl : w.length ≤ 10000 := by rw [← hw]; simp; omega
    have hw93 : ∀ x ∈ w, x ≤ 93 := by
      intro x hx
      rw [← hw] at hx
      have := List.mem_of_mem_take hx
      have := List.mem_of_mem_drop this
      simp only [scoresOf, List.mem_map] at this
      obtain ⟨k, -, rfl⟩ := this
      exact enc_le _ _
    have hneg : ∃ x ∈ w, x < 0 := by
      refine ⟨enc seq[i]! qual[i]!, ?_, ?_⟩
      · rw [← hw, List.mem_iff_getElem]
        refine ⟨i - s, by simp; omega, ?_⟩
        simp only [List.getElem_take, List.getElem_drop]
        rw [hget _ (by omega), show s + (i - s) = i by omega]
      · apply Classical.byContradiction; intro h0'
        exact hnA ((enc_nonneg seq[i]! qual[i]!).1 (by omega))
    have := sum_le_neg Q hQ w hw93 hneg
    have hwl' : (w.length : Int) ≤ 10000 := by omega
    have hprod : (93 - Q : Int) * w.length ≤ 93 * 10000 :=
      Int.mul_le_mul (by omega) hwl' (by omega) (by omega)
    rw [perBase_pos Q _ (by omega)] at hmax
    omega

theorem trimRead_packed (Q : Nat) (seq qual : ByteArray) (s e : Nat) (ht : trimReadQ Q seq qual = some (s, e)) :
    seq.size ≤ 10000 ∧ isACGT seq[s]! = true ∧
      get_best_window [] (scoresOf seq qual) (fun ws => ws.map (perBase Q)) = some (s, e) := by
  unfold trimReadQ at ht
  split at ht
  · next hsz =>
    split at ht
    · next s' e' hw =>
      split at ht
      · next hA =>
        cases ht
        rw [wl_eq, ← initialPackedFoldState, winLoop_packed, getBestWindowPacked_equals_frozen_get_best_window []] at hw
        exact ⟨hsz, hA, hw⟩
      · cases ht
    · cases ht
  · cases ht

/-- **The kept window is inside the read, non-empty, and A/C/G/T only** (any `Q ≤ 93`). -/
theorem trimRead_acgt (Q : Nat) (hQ : Q ≤ 93) (seq qual : ByteArray) (s e : Nat)
    (ht : trimReadQ Q seq qual = some (s, e)) :
    e ≤ seq.size ∧ s < e ∧ ∀ i, s ≤ i → i < e → isACGT seq[i]! = true := by
  obtain ⟨hsz, hA, hw⟩ := trimRead_packed Q seq qual s e ht
  have hv := get_best_window_returns_a_valid_window [] _ _ _ hw
  simp only [scoresOf, List.length_map, List.length_range] at hv
  exact best_acgt Q hQ seq qual s e hsz s (by omega) hA hw

/-- **The trimmer is the frozen contract** for every neutral quality `Q ≤ 93` and
every read with an A/C/G/T letter (at most 10 000 letters). -/
theorem trimRead_eq_contract (Q : Nat) (hQ : Q ≤ 93) (seq qual : ByteArray) (h : seq.size ≤ 10000) (j : Nat)
    (hj : j < seq.size) (hjA : isACGT seq[j]! = true) :
    trimReadQ Q seq qual = get_best_window [] (scoresOf seq qual) (fun ws => ws.map (perBase Q)) := by
  have hc := (winLoop_packed Q seq qual).trans (getBestWindowPacked_equals_frozen_get_best_window [] _ _)
  rw [initialPackedFoldState, ← wl_eq] at hc
  unfold trimReadQ
  rw [if_pos h, hc]
  cases hw : get_best_window [] (scoresOf seq qual) (fun ws => ws.map (perBase Q)) with
  | none => rfl
  | some w =>
    obtain ⟨s, e⟩ := w
    have := best_acgt Q hQ seq qual s e h j hj hjA hw
    simp [this.2.2 s (Nat.le_refl _) this.2.1]

/-- The default neutral quality. -/
def defQ : Nat := 25

/-- The trimmer at the default neutral quality. -/
def trimRead (seq qual : ByteArray) : Option (Nat × Nat) := trimReadQ defQ seq qual

theorem trimRead_def_eq_contract (seq qual : ByteArray) (h : seq.size ≤ 10000) (j : Nat) (hj : j < seq.size)
    (hjA : isACGT seq[j]! = true) :
    trimRead seq qual = get_best_window [] (scoresOf seq qual) (fun ws => ws.map (perBase defQ)) :=
  trimRead_eq_contract defQ (by decide) seq qual h j hj hjA

theorem trimRead_def_acgt (seq qual : ByteArray) (s e : Nat) (ht : trimRead seq qual = some (s, e)) :
    e ≤ seq.size ∧ s < e ∧ ∀ i, s ≤ i → i < e → isACGT seq[i]! = true :=
  trimRead_acgt defQ (by decide) seq qual s e ht

end ReadTrim

namespace ParMap

/-- **Chunked output is the whole output**: for any cut of the input into
chunks, the chunks' texts in order are the text of the whole input mapped. -/
theorem chunks_text {α β : Type} (f : α → β) (fmt : β → String) (cs : List (Array α)) :
    String.join (cs.map fun c => formatAll fmt (c.map f)) = formatAll fmt ((cs.foldl (· ++ ·) #[]).map f) := by
  suffices h : ∀ acc, formatAll fmt (acc.map f) ++ String.join (cs.map fun c => formatAll fmt (c.map f)) =
      formatAll fmt ((cs.foldl (· ++ ·) acc).map f) by
    have := h #[]; simpa [formatAll] using this
  induction cs with
  | nil => intro acc; simp
  | cons c cs ih =>
    intro acc
    rw [List.map_cons, String.join_cons, ← String.append_assoc, ← formatAll_append, ← Array.map_append, ih]
    rfl

/-- Two stages (prep, then map) are their composition. -/
theorem stages_text {α β γ : Type} (p : α → β) (m : β → γ) (fmt : γ → String) (c : Array α) :
    formatAll fmt ((c.map p).map m) = formatAll fmt (c.map (m ∘ p)) := by
  rw [Array.map_map]

end ParMap

#print axioms ReadTrim.trimRead_eq_contract
#print axioms ReadTrim.trimRead_acgt
#print axioms ReadTrim.trimRead_def_eq_contract
#print axioms ReadTrim.trimRead_def_acgt
#print axioms ParMap.chunks_text
#print axioms ParMap.stages_text
