import FastGenPairPacked
import FastGenK250

/-!
# The diagonal filter by words (`kfiltV = kfilt`)

`kfilt` (codecs/FastGenAlgo.lean) checks, for a diagonal `D`, the 25-letter seeds not
looked up (`unlook`) and the 8-letter pieces (`fineOk`) at each of the `2r + 1` read
starts `s ∈ [D − n − r, D − n + r]`, letter by letter.  When the genome is a packed
`PGen` (`GPk`), the read is ACGT and packed (`packRP`), and the whole window lies in
all-ACGT blocks away from the chromosome start, `kfiltV` does the same tests on
2-bit words: the genome words of the window are loaded once (`loadW`); a seed is 25
fields compared at once (`eq25`); the pieces of a read word are four 16-bit lanes
of its folded mismatch word, all tested at once (`laneZ`).  Elsewhere it is `kfilt`.

    kfiltV (packRP R) R G acc us Ls lim b D = kfilt R G acc us Ls lim b D      (kfiltV_eq)
-/

namespace MapSpec.Fast

open MapSpec MapSpec.Packed

/-- A genome representation that may carry its packed form (same letters). -/
class GPk (Gt : Type) [GRead Gt] where
  pk : Gt → Option PGen
  pk_same : ∀ (G : Gt) (P : PGen), pk G = some P → SameG G P

instance : GPk ByteArray := ⟨fun _ => none, fun _ _ h => by cases h⟩

instance : GPk PGen := ⟨some, fun G P h => by cases h; exact ⟨rfl, fun _ => rfl⟩⟩

/-- Words `u0, u0 + 1, …` (`k` more) of the blocks pushed onto `a`. -/
def loadW (w : ByteArray) (u0 : Nat) : Nat → Array UInt64 → Array UInt64
  | 0, a => a
  | k + 1, a => loadW w (u0 + 1) k (a.push (gword w u0))

/-- The 32 fields starting at field `t` of the words `gs`. -/
@[inline] def gAt (gs : Array UInt64) (t : Nat) : UInt64 :=
  let s := t % 32
  comb (gs.getD (t / 32) 0) (gs.getD (t / 32 + 1) 0) s (2 * s).toUInt64 (64 - 2 * s).toUInt64

/-- The low 25 fields agree. -/
@[inline] def eq25 (x y : UInt64) : Bool := lowF (x ^^^ y) 25 == 0

/-- The seed `sv` is at some field offset `t, t + 1, …` (`k` of them) of `gs`. -/
def svAny (gs : Array UInt64) (sv : UInt64) (t : Nat) : Nat → Bool
  | 0 => false
  | k + 1 => eq25 (gAt gs t) sv || svAny gs sv (t + 1) k

/-- `unlook` by words: read start `s` ↦ field `o + (s − s0)` of `gs` (`s0 = D − n − r`). -/
def unlookV (K : RP) (gs : Array UInt64) (R : ByteArray) {Gt : Type} [GRead Gt] (G : Gt)
    (o Ls r D sb : Nat) : List Nat → Nat → Bool
  | [], _ => true
  | j :: us, f =>
    let A := j * Ls
    let ok := if A + q ≤ R.size then
        let sv := gAt K.w A
        eq25 (gAt gs (o + A + r)) sv || svAny gs sv (o + A) (2 * r + 1)
      else seedNear R G Ls r D j
    if ok then unlookV K gs R G o Ls r D sb us f
    else if sb < f + 1 then false else unlookV K gs R G o Ls r D sb us (f + 1)

/-- Folded mismatches of read word `j` against the genome at field offset `t`. -/
@[inline] def mAt (K : RP) (gs : Array UInt64) (t j : Nat) : UInt64 :=
  fold (K.w.getD j 0 ^^^ gAt gs (t + 32 * j))

/-- Bit `16i` set iff the 16-bit lane `i` of `m` is zero (nothing else set). -/
@[inline] def laneZ (m : UInt64) : UInt64 :=
  let x := m ||| m >>> 2
  let x := x ||| x >>> 4
  let x := x ||| x >>> 8
  ~~~x &&& 0x0001000100010001

/-- The low `np` lanes (`np ≤ 4`). -/
@[inline] def fullL (np : Nat) : UInt64 :=
  if np = 0 then 0 else if np = 1 then 1 else if np = 2 then 0x10001 else if np = 3 then 0x100010001
  else 0x1000100010001

/-- Lanes of read word `j` found zero at field offsets `t, t + 1, …` (`k`), or-ed into `F`;
stops once all of `full` are found. -/
def lanesAny (K : RP) (gs : Array UInt64) (n j : Nat) (full F : UInt64) (t : Nat) : Nat → UInt64
  | 0 => F
  | k + 1 =>
    let F := F ||| laneZ (lowF (mAt K gs t j) (n - 32 * j))
    if F &&& full == full then F else lanesAny K gs n j full F (t + 1) k

/-- Number of lanes `0 … 3` flagged (bit `16i`). -/
@[inline] def lc (F : UInt64) : Nat :=
  (F &&& 1).toNat + (F >>> 16 &&& 1).toNat + (F >>> 32 &&& 1).toNat + (F >>> 48 &&& 1).toNat

/-- Pieces found (of `m`), read words `j, j + 1, …` (`k` of them), added to `acc`. -/
def fineV (K : RP) (gs : Array UInt64) (o n r m : Nat) : Nat → Nat → Nat → Nat
  | _, 0, acc => acc
  | j, k + 1, acc =>
    let full := fullL (min 4 (m - 4 * j))
    let F := laneZ (lowF (mAt K gs (o + r) j) (n - 32 * j)) &&& full
    let F := if F == full then F else lanesAny K gs n j full F o (2 * r + 1) &&& full
    fineV K gs o n r m (j + 1) k (acc + lc F)

/-- The word path applies: packed read, the window `[D − n − r, D + r)` inside the
chromosome and in all-ACGT blocks, pieces of 8 letters 8 apart. -/
@[inline] def wordWin (K : RP) (n r D : Nat) (P : PGen) : Bool :=
  K.ok && decide (n + r ≤ D) && n / (n / pl) == 8 && winOk P (D - n - r) (n + 2 * r)

/-- `kfilt` with the word path where it applies. -/
@[inline] def kfiltV {Gt : Type} [GRead Gt] [GPk Gt] (K : RP) (R : ByteArray) (G : Gt) (acc : List (Array Nat))
    (us : List Nat) (Ls lim : Nat) (b : Best) (D : Nat) : Bool :=
  let Q := min lim b.pen
  let r := 2 * gapBound sc0 (-(Q : Int))
  let n := R.size
  let fJ := acc.length - suppA acc D r
  let sb := sbound Q
  if fJ ≤ sb then
    match GPk.pk G with
    | some P =>
      if wordWin K n r D P then
        let a := P.o + (D - n - r)
        let o := a % 32
        let gs := loadW P.w (a / 32) ((o + 2 * r + n) / 32 + 2) (Array.emptyWithCapacity 12)
        unlookV K gs R G o Ls r D sb us fJ &&
          decide (n / pl ≤ sb + fineV K gs o n r (n / pl) 0 ((n + 31) / 32) 0)
      else kfilt R G acc us Ls lim b D
    | none => kfilt R G acc us Ls lim b D
  else false

/-- `stageKS` with `kfiltV`. -/
@[specialize] def stageKSV {Gt : Type} [GRead Gt] [GPk Gt] (body : Nat → Best → Best) (K : RP) (R : ByteArray)
    (G : Gt) (acc : List (Array Nat)) (us : List Nat) (Ls lim : Nat) (ds : List Nat) (b : Best) : Best :=
  ds.foldl (fun b D => if kfiltV K R G acc us Ls lim b D then body D b else b) b

/-! ## Proofs -/

/-! ### Bits -/

theorem w0_iff (w : UInt64) : w = 0 ↔ ∀ t, t < 32 → dig w.toNat t = 0 := by
  constructor
  · intro h t _; subst h; simp [dig]
  · intro h
    apply UInt64.toNat_inj.mp
    show w.toNat = (0 : UInt64).toNat
    apply Nat.eq_of_testBit_eq
    intro b
    simp only [UInt64.toNat_zero, Nat.zero_testBit]
    by_cases hb : b < 64
    · have := h (b / 2) (by omega)
      rw [dig_eq] at this
      rcases Nat.mod_two_eq_zero_or_one b with e | e
      · have : w.toNat.testBit (2 * (b / 2)) = false := by
          cases hh : w.toNat.testBit (2 * (b / 2)) <;> simp_all
        rwa [show 2 * (b / 2) = b by omega] at this
      · have : w.toNat.testBit (2 * (b / 2) + 1) = false := by
          cases hh : w.toNat.testBit (2 * (b / 2) + 1) <;> simp_all
        rwa [show 2 * (b / 2) + 1 = b by omega] at this
    · exact tb_hi w b (by omega)

theorem beq0_iff (w : UInt64) : (w == 0) = true ↔ ∀ t, t < 32 → dig w.toNat t = 0 := by
  rw [beq_iff_eq]; exact w0_iff w

theorem bit1 (x : UInt64) (k : Nat) (hk : k < 64) :
    (x >>> k.toUInt64 &&& 1).toNat = if x.toNat.testBit k then 1 else 0 := by
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight, UInt64.toNat_one]
  have e : k.toUInt64.toNat % 64 = k := by simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
  rw [e, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (x.toNat / 2 ^ k) with h | h <;> simp [h]

theorem lc_eq (F : UInt64) : lc F = (if F.toNat.testBit 0 then 1 else 0) + (if F.toNat.testBit 16 then 1 else 0) +
    (if F.toNat.testBit 32 then 1 else 0) + (if F.toNat.testBit 48 then 1 else 0) := by
  unfold lc
  rw [show F &&& 1 = F >>> (0 : Nat).toUInt64 &&& 1 by simp, bit1 F 0 (by omega),
    show (16 : UInt64) = (16 : Nat).toUInt64 from rfl, bit1 F 16 (by omega),
    show (32 : UInt64) = (32 : Nat).toUInt64 from rfl, bit1 F 32 (by omega),
    show (48 : UInt64) = (48 : Nat).toUInt64 from rfl, bit1 F 48 (by omega)]

theorem tb_shr (x : UInt64) (k b : Nat) (hk : k < 64) :
    (x >>> k.toUInt64).toNat.testBit b = x.toNat.testBit (b + k) := by
  rw [UInt64.toNat_shiftRight]
  have e : k.toUInt64.toNat % 64 = k := by simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
  rw [e, Nat.testBit_shiftRight, Nat.add_comm]

theorem laneZ_bit (m : UInt64) (i : Nat) (hi : i < 4) :
    (laneZ m).toNat.testBit (16 * i) = true ↔ ∀ b, b < 8 → m.toNat.testBit (16 * i + 2 * b) = false := by
  unfold laneZ
  simp only [UInt64.toNat_and, Nat.testBit_and, tb_not, UInt64.toNat_or, Nat.testBit_or]
  rw [show (2 : UInt64) = (2 : Nat).toUInt64 from rfl, show (4 : UInt64) = (4 : Nat).toUInt64 from rfl,
    show (8 : UInt64) = (8 : Nat).toUInt64 from rfl]
  simp only [tb_shr _ _ _ (show 2 < 64 by omega), tb_shr _ _ _ (show 4 < 64 by omega),
    tb_shr _ _ _ (show 8 < 64 by omega), UInt64.toNat_or, Nat.testBit_or]
  have hmask : (0x0001000100010001 : UInt64).toNat.testBit (16 * i) = true := by
    obtain _ | _ | _ | _ | i := i <;> first | omega | decide
  rw [hmask, decide_eq_true (show 16 * i < 64 by omega)]
  simp only [Bool.true_and, Bool.and_true, Bool.not_eq_true', Bool.or_eq_false_iff]
  constructor
  · intro h b hb
    obtain _ | _ | _ | _ | _ | _ | _ | _ | b := b
    all_goals first | omega | (simp only [Nat.add_assoc] at h ⊢; simp_all)
  · intro h
    have h0 := h 0 (by omega); have h1 := h 1 (by omega); have h2 := h 2 (by omega); have h3 := h 3 (by omega)
    have h4 := h 4 (by omega); have h5 := h 5 (by omega); have h6 := h 6 (by omega); have h7 := h 7 (by omega)
    simp only [Nat.add_assoc] at h0 h1 h2 h3 h4 h5 h6 h7 ⊢
    simp_all


theorem dig_le1 (x : UInt64) (t : Nat) (h : dig x.toNat t ≤ 1) :
    dig x.toNat t = if x.toNat.testBit (2 * t) then 1 else 0 := by
  rw [dig_eq] at h ⊢
  cases h1 : x.toNat.testBit (2 * t + 1) <;> cases h2 : x.toNat.testBit (2 * t) <;> simp_all

theorem fullL_bit (np i : Nat) (hnp : np ≤ 4) (hi : i < 4) :
    (fullL np).toNat.testBit (16 * i) = decide (i < np) := by
  unfold fullL
  obtain _ | _ | _ | _ | _ | np := np <;> obtain _ | _ | _ | _ | i := i <;> first | omega | decide

/-! ### Loaded words, digits, letters -/

theorem getD_push (a : Array UInt64) (x : UInt64) (i : Nat) :
    (a.push x).getD i 0 = if i < a.size then a.getD i 0 else if i = a.size then x else 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  by_cases h2 : i = a.size
  · subst h2; simp
  · rw [if_neg h2]
    by_cases h1 : i < a.size
    · simp [h1]
    · rw [Array.getElem?_eq_none (by omega)]; simp [h1, h2]

theorem loadW_getD (w : ByteArray) : ∀ (k u0 : Nat) (a : Array UInt64) (i : Nat),
    (loadW w u0 k a).getD i 0 =
      if i < a.size then a.getD i 0 else if i < a.size + k then gword w (u0 + (i - a.size)) else 0 := by
  intro k
  induction k with
  | zero =>
    intro u0 a i
    simp only [loadW, Nat.add_zero]
    by_cases h : i < a.size
    · simp [h]
    · simp [h, Array.getD_eq_getD_getElem?]
  | succ k ih =>
    intro u0 a i
    rw [loadW, ih, Array.size_push, getD_push]
    by_cases h1 : i < a.size
    · simp [h1, show i < a.size + 1 by omega]
    by_cases h2 : i = a.size
    · subst h2; simp
    · simp only [show ¬ i < a.size + 1 by omega, h1, h2, if_false]
      by_cases h3 : i < a.size + (k + 1)
      · rw [if_pos (by omega), if_pos h3, show u0 + 1 + (i - (a.size + 1)) = u0 + (i - a.size) by omega]
      · rw [if_neg (by omega), if_neg h3]

theorem loadW_get (w : ByteArray) (u0 k i : Nat) (hi : i < k) :
    (loadW w u0 k (Array.emptyWithCapacity 12)).getD i 0 = gword w (u0 + i) := by
  rw [loadW_getD]; simp [hi]

/-- Genome fields of the loaded words. -/
theorem gAt_dig (P : PGen) (u0 k t i : Nat) (hk : t / 32 + 1 < k) (hi : i < 32) :
    dig (gAt (loadW P.w u0 k (Array.emptyWithCapacity 12)) t).toNat i = (P.code (32 * u0 + t + i)).toNat := by
  unfold gAt
  simp only []
  rw [comb_dig _ _ _ _ (Nat.mod_lt _ (by omega)) hi, loadW_get _ _ _ _ (by omega), loadW_get _ _ _ _ hk]
  split
  · rw [code_dig _ _ _ (by omega)]; congr 2; omega
  · rw [code_dig _ _ _ (by omega)]; congr 2; omega

/-- Read fields of the packed read. -/
theorem rAt_dig (R : ByteArray) (hok : (packRP R).ok = true) (A i : Nat) (hi : i < 32) (hA : A + i < R.size) :
    dig (gAt (packRP R).w A).toNat i = c2N (R.get! (A + i)) := by
  have hR := (packRP_ok R hok).2 (A + i) hA
  unfold gAt
  simp only []
  rw [comb_dig _ _ _ _ (Nat.mod_lt _ (by omega)) hi, getD_get!, getD_get!]
  split
  · rw [← hR.2, show (A + i) / 32 = A / 32 by omega, show (A + i) % 32 = A % 32 + i by omega]
  · rw [← hR.2, show (A + i) / 32 = A / 32 + 1 by omega, show (A + i) % 32 = A % 32 + i - 32 by omega]

theorem kw_dig (R : ByteArray) (hok : (packRP R).ok = true) (j i : Nat) (hi : i < 32) (hA : 32 * j + i < R.size) :
    dig ((packRP R).w.getD j 0).toNat i = c2N (R.get! (32 * j + i)) := by
  have hR := (packRP_ok R hok).2 (32 * j + i) hA
  rw [getD_get!, ← hR.2, show (32 * j + i) / 32 = j by omega, show (32 * j + i) % 32 = i by omega]

/-- A genome letter in flagged blocks, by its code. -/
theorem gb_letter (P : PGen) (Gb : ByteArray) (hP : Rep P Gb) (y : Nat) (hin : y < P.n)
    (hfl : P.w.get! (17 * ((P.o + y) / 64)) = 1) : Gb.get! y = letter (P.code (P.o + y)) := by
  rw [← hP.2, PGen.get, if_pos hin, raw_eq, Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 6 = 64 from rfl, hfl]
  rfl

theorem code_lt (P : PGen) (i : Nat) : (P.code i).toNat < 4 := by
  unfold PGen.code
  rw [UInt8.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

/-- Read letter `x` against genome place `y` (flagged), by digits. -/
theorem letter_dig (R : ByteArray) (hok : (packRP R).ok = true) (P : PGen) (Gb : ByteArray) (hP : Rep P Gb)
    (x y : Nat) (hx : x < R.size) (hin : y < P.n) (hfl : P.w.get! (17 * ((P.o + y) / 64)) = 1) :
    c2N (R.get! x) = (P.code (P.o + y)).toNat ↔ Gb.get! y = R.get! x := by
  rw [gb_letter P Gb hP y hin hfl, show (letter (P.code (P.o + y)) = R.get! x) ↔ (R.get! x = letter (P.code (P.o + y)))
    from eq_comm, letter_iff _ _ ((packRP_ok R hok).2 x hx).1 (code_lt P _)]

/-- The word-path setting: `P` spells `Gb`, the read is packed, the window
`[s0, s0 + L)` lies in the chromosome, in flagged blocks. -/
structure WS (R : ByteArray) (P : PGen) (Gb : ByteArray) (s0 L : Nat) : Prop where
  rep : Rep P Gb
  ok : (packRP R).ok = true
  win : ∀ y, s0 ≤ y → y < s0 + L → y < P.n ∧ P.w.get! (17 * ((P.o + y) / 64)) = 1

/-- Field `t` of the words loaded from `P.o + s0` is genome place `s0 + (t − o)`. -/
theorem fieldW {R : ByteArray} {P : PGen} {Gb : ByteArray} {s0 L : Nat} (h : WS R P Gb s0 L) (k t x : Nat)
    (hk : t / 32 + 1 < k) (ht : (P.o + s0) % 32 ≤ t) (i : Nat) (hi : i < 32) (hx : x < R.size)
    (hy : t + i - (P.o + s0) % 32 < L) :
    dig (gAt (loadW P.w ((P.o + s0) / 32) k (Array.emptyWithCapacity 12)) t).toNat i = c2N (R.get! x) ↔
      Gb.get! (s0 + (t + i - (P.o + s0) % 32)) = R.get! x := by
  rw [gAt_dig P _ k t i hk hi]
  have hw := h.win (s0 + (t + i - (P.o + s0) % 32)) (by omega) (by omega)
  rw [← letter_dig R h.ok P Gb h.rep x _ hx hw.1 hw.2, eq_comm]
  have : 32 * ((P.o + s0) / 32) + t + i = P.o + (s0 + (t + i - (P.o + s0) % 32)) := by omega
  rw [this]

/-! ### Seeds -/

theorem matchQ_iff (R G : ByteArray) (s p : Nat) : ∀ k, k ≤ q →
    (matchQ R G s p k = true ↔ ∀ i, q - k ≤ i → i < q → G.get! (p + i) = R.get! (s + i)) := by
  intro k
  induction k with
  | zero => intro _; simp only [matchQ, true_iff]; intro i h1 h2; omega
  | succ k ih =>
    intro hk
    simp only [matchQ, Bool.and_eq_true, beq_iff_eq, GRead.get_bytes, ih (by omega)]
    constructor
    · rintro ⟨h1, h2⟩ i hi1 hi2
      by_cases e : i = q - (k + 1)
      · subst e; exact h1
      · exact h2 i (by omega) hi2
    · intro h
      exact ⟨h _ (Nat.le_refl _) (by omega), fun i h1 h2 => h i (by omega) h2⟩

theorem nearS_iff (R G : ByteArray) (s : Nat) : ∀ w lo, nearS R G s lo w = true ↔
    ∃ p, lo ≤ p ∧ p < lo + w ∧ p + q ≤ G.size ∧ ∀ i, i < q → G.get! (p + i) = R.get! (s + i) := by
  intro w
  induction w with
  | zero => intro lo; simp only [nearS, Bool.false_eq_true, false_iff]; rintro ⟨p, h1, h2, -⟩; omega
  | succ w ih =>
    intro lo
    simp only [nearS, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, GRead.size_bytes, ih,
      matchQ_iff R G s lo q (Nat.le_refl _), Nat.sub_self, Nat.zero_le, true_implies]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨p, h1, h2, h3, h4⟩)
      · exact ⟨lo, Nat.le_refl _, by omega, h1, h2⟩
      · exact ⟨p, by omega, by omega, h3, h4⟩
    · rintro ⟨p, h1, h2, h3, h4⟩
      by_cases e : p = lo
      · subst e; exact Or.inl ⟨h3, h4⟩
      · exact Or.inr ⟨p, by omega, by omega, h3, h4⟩

/-- `seedNear` inside the chromosome: some read start `s0 + e` (`e ≤ 2r`) spells the seed. -/
theorem seedNear_iff (R G : ByteArray) (Ls r D j : Nat) (hD : R.size + r ≤ D) (hA : j * Ls + q ≤ R.size)
    (hG : D + r ≤ G.size) :
    seedNear R G Ls r D j = true ↔ ∃ e, e ≤ 2 * r ∧
      ∀ i, i < q → G.get! (D - R.size - r + e + j * Ls + i) = R.get! (j * Ls + i) := by
  unfold seedNear
  simp only []
  rw [if_neg (by omega), Bool.or_eq_true, nearS_iff, show min (2 * r) (D + j * Ls + r - R.size) = 2 * r by omega]
  simp only [Bool.and_eq_true, decide_eq_true_eq, GRead.size_bytes, matchQ_iff R G _ _ q (Nat.le_refl _),
    Nat.sub_self, Nat.zero_le, true_implies]
  constructor
  · rintro (⟨-, h⟩ | ⟨p, h1, h2, -, h4⟩)
    · refine ⟨r, by omega, fun i hi => ?_⟩
      rw [show D - R.size - r + r + j * Ls + i = D + j * Ls + r - R.size - r + i by omega]; exact h i hi
    · refine ⟨p - (D + j * Ls + r - R.size - 2 * r), by omega, fun i hi => ?_⟩
      rw [show D - R.size - r + (p - (D + j * Ls + r - R.size - 2 * r)) + j * Ls + i = p + i by omega]
      exact h4 i hi
  · rintro ⟨e, he, h⟩
    refine Or.inr ⟨D - R.size - r + e + j * Ls, by omega, by omega, by omega, fun i hi => ?_⟩
    exact h i hi

theorem svAny_iff (gs : Array UInt64) (sv : UInt64) : ∀ k t,
    svAny gs sv t k = true ↔ ∃ e, e < k ∧ eq25 (gAt gs (t + e)) sv = true := by
  intro k
  induction k with
  | zero => intro t; simp [svAny]
  | succ k ih =>
    intro t
    simp only [svAny, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨e, h1, h2⟩)
      · exact ⟨0, by omega, h⟩
      · exact ⟨e + 1, by omega, by rw [show t + (e + 1) = t + 1 + e by omega]; exact h2⟩
    · rintro ⟨e, h1, h2⟩
      cases e with
      | zero => exact Or.inl h2
      | succ e => exact Or.inr ⟨e, by omega, by rw [show t + 1 + e = t + (e + 1) by omega]; exact h2⟩

/-- 25 fields by one compare. -/
theorem eq25_iff (x y : UInt64) : eq25 x y = true ↔ ∀ t, t < 25 → dig x.toNat t = dig y.toNat t := by
  unfold eq25
  rw [beq0_iff]
  constructor
  · intro h t ht
    have := h t (by omega)
    rw [lowF_dig _ _ _ (by omega), if_pos ht, xor_dig] at this
    exact this
  · intro h t ht
    rw [lowF_dig _ _ _ ht]
    split
    · rw [xor_dig]; exact h t (by omega)
    · rfl

/-- The seed test by words is the seed test by letters. -/
theorem seedW_iff {R : ByteArray} {P : PGen} {Gb : ByteArray} {r D : Nat}
    (h : WS R P Gb (D - R.size - r) (R.size + 2 * r)) (A e : Nat) (hA : A + q ≤ R.size)
    (he : e ≤ 2 * r) :
    eq25 (gAt (loadW P.w ((P.o + (D - R.size - r)) / 32) (((P.o + (D - R.size - r)) % 32 + 2 * r + R.size) / 32 + 2)
      (Array.emptyWithCapacity 12)) ((P.o + (D - R.size - r)) % 32 + A + e)) (gAt (packRP R).w A) = true ↔
      ∀ i, i < q → Gb.get! (D - R.size - r + e + A + i) = R.get! (A + i) := by
  have hq : q = 25 := rfl
  rw [eq25_iff]
  apply forall_congr'; intro i
  constructor
  · intro hh hi
    have := hh (by omega)
    rw [rAt_dig R h.ok A i (by omega) (by omega)] at this
    rw [fieldW h (((P.o + (D - R.size - r)) % 32 + 2 * r + R.size) / 32 + 2) ((P.o + (D - R.size - r)) % 32 + A + e) (A + i) (by omega) (by omega) i (by omega) (by omega) (by omega)] at this
    rw [← this]; congr 1; omega
  · intro hh hi
    rw [rAt_dig R h.ok A i (by omega) (by omega)]
    rw [fieldW h (((P.o + (D - R.size - r)) % 32 + 2 * r + R.size) / 32 + 2) ((P.o + (D - R.size - r)) % 32 + A + e) (A + i) (by omega) (by omega) i (by omega) (by omega) (by omega)]
    rw [← hh (by omega)]; congr 1; omega

theorem unlookV_eq (K : RP) (gs : Array UInt64) (R : ByteArray) {Gt : Type} [GRead Gt] (G : Gt)
    (o Ls r D sb : Nat)
    (h : ∀ j, j * Ls + q ≤ R.size → (eq25 (gAt gs (o + j * Ls + r)) (gAt K.w (j * Ls)) ||
      svAny gs (gAt K.w (j * Ls)) (o + j * Ls) (2 * r + 1)) = seedNear R G Ls r D j) :
    ∀ us f, unlookV K gs R G o Ls r D sb us f = unlook R G Ls r D sb us f := by
  intro us
  induction us with
  | nil => intro f; rfl
  | cons j us ih =>
    intro f
    simp only [unlookV, unlook]
    have e : (if j * Ls + q ≤ R.size then
        (eq25 (gAt gs (o + j * Ls + r)) (gAt K.w (j * Ls)) || svAny gs (gAt K.w (j * Ls)) (o + j * Ls) (2 * r + 1))
        else seedNear R G Ls r D j) = seedNear R G Ls r D j := by
      split
      · exact h j ‹_›
      · rfl
    rw [e, ih, ih]

/-- Per seed, inside the window: words = letters. -/
theorem seedV_eq {R : ByteArray} {P : PGen} {Gb : ByteArray} {r D : Nat}
    (h : WS R P Gb (D - R.size - r) (R.size + 2 * r)) (hD : R.size + r ≤ D) (Ls j : Nat) (hA : j * Ls + q ≤ R.size) :
    (eq25 (gAt (loadW P.w ((P.o + (D - R.size - r)) / 32) (((P.o + (D - R.size - r)) % 32 + 2 * r + R.size) / 32 + 2)
      (Array.emptyWithCapacity 12)) ((P.o + (D - R.size - r)) % 32 + j * Ls + r)) (gAt (packRP R).w (j * Ls)) ||
      svAny (loadW P.w ((P.o + (D - R.size - r)) / 32) (((P.o + (D - R.size - r)) % 32 + 2 * r + R.size) / 32 + 2)
        (Array.emptyWithCapacity 12)) (gAt (packRP R).w (j * Ls)) ((P.o + (D - R.size - r)) % 32 + j * Ls) (2 * r + 1))
      = seedNear R Gb Ls r D j := by
  have hG : D + r ≤ Gb.size := by
    have hq : q = 25 := rfl
    rw [← h.rep.1]; have := (h.win (D + r - 1) (by omega) (by omega)).1; omega
  apply Bool.eq_iff_iff.mpr
  rw [seedNear_iff R Gb Ls r D j hD hA hG, Bool.or_eq_true, svAny_iff]
  constructor
  · rintro (h1 | ⟨e, he, h2⟩)
    · exact ⟨r, by omega, (seedW_iff h _ r hA (by omega)).mp h1⟩
    · exact ⟨e, by omega, (seedW_iff h _ e hA (by omega)).mp h2⟩
  · rintro ⟨e, he, h2⟩
    refine Or.inr ⟨e, by omega, ?_⟩
    exact (seedW_iff h _ e hA he).mpr h2

/-! ### Pieces -/

theorem fineOk_cnt {Gt : Type} [GRead Gt] (R : ByteArray) (G : Gt) (l Ls r D sb : Nat) : ∀ k j f, f ≤ sb →
    fineOk R G l Ls r D sb j f k = decide (f + cntP (fun j => !pieceNear R G l Ls r D j) j k ≤ sb) := by
  intro k
  induction k with
  | zero => intro j f hf; simp [fineOk, cntP, hf]
  | succ k ih =>
    intro j f hf
    unfold fineOk
    cases hp : pieceNear R G l Ls r D j
    · have e : cntP (fun j => !pieceNear R G l Ls r D j) j (k + 1)
          = 1 + cntP (fun j => !pieceNear R G l Ls r D j) (j + 1) k := by simp [cntP, hp]
      rw [e]
      by_cases hs : sb < f + 1
      · simp only [Bool.false_eq_true, if_false, hs, if_true]
        exact (decide_eq_false (by omega)).symm
      · simp only [Bool.false_eq_true, if_false, hs, if_false, ih (j + 1) (f + 1) (by omega)]
        exact decide_eq_decide.mpr (by omega)
    · have e : cntP (fun j => !pieceNear R G l Ls r D j) j (k + 1)
          = cntP (fun j => !pieceNear R G l Ls r D j) (j + 1) k := by simp [cntP, hp]
      rw [e]; simp only [if_true, ih (j + 1) f hf]

theorem cntP_compl (p : Nat → Bool) : ∀ k i, cntP p i k + cntP (fun x => !p x) i k = k := by
  intro k
  induction k with
  | zero => intro i; rfl
  | succ k ih =>
    intro i
    have := ih (i + 1)
    simp only [cntP]
    by_cases hp : p i = true
    · simp [hp]; omega
    · simp [hp]; omega

theorem matchLn_iff (R G : ByteArray) (s p l : Nat) : ∀ k, k ≤ l →
    (matchLn R G s p l k = true ↔ ∀ i, l - k ≤ i → i < l → G.get! (p + i) = R.get! (s + i)) := by
  intro k
  induction k with
  | zero => intro _; simp only [matchLn, true_iff]; intro i h1 h2; omega
  | succ k ih =>
    intro hk
    simp only [matchLn, Bool.and_eq_true, beq_iff_eq, GRead.get_bytes, ih (by omega)]
    constructor
    · rintro ⟨h1, h2⟩ i hi1 hi2
      by_cases e : i = l - (k + 1)
      · subst e; exact h1
      · exact h2 i (by omega) hi2
    · intro h
      exact ⟨h _ (Nat.le_refl _) (by omega), fun i h1 h2 => h i (by omega) h2⟩

theorem nearL_iff (R G : ByteArray) (s l : Nat) : ∀ w lo, nearL R G s l lo w = true ↔
    ∃ p, lo ≤ p ∧ p < lo + w ∧ p + l ≤ G.size ∧ ∀ i, i < l → G.get! (p + i) = R.get! (s + i) := by
  intro w
  induction w with
  | zero => intro lo; simp only [nearL, Bool.false_eq_true, false_iff]; rintro ⟨p, h1, h2, -⟩; omega
  | succ w ih =>
    intro lo
    simp only [nearL, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, GRead.size_bytes, ih,
      matchLn_iff R G s lo l l (Nat.le_refl _), Nat.sub_self, Nat.zero_le, true_implies]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨p, h1, h2, h3, h4⟩)
      · exact ⟨lo, Nat.le_refl _, by omega, h1, h2⟩
      · exact ⟨p, by omega, by omega, h3, h4⟩
    · rintro ⟨p, h1, h2, h3, h4⟩
      by_cases e : p = lo
      · subst e; exact Or.inl ⟨h3, h4⟩
      · exact Or.inr ⟨p, by omega, by omega, h3, h4⟩

theorem pieceNear_iff (R G : ByteArray) (l Ls r D j : Nat) (hD : R.size + r ≤ D) (hA : j * Ls + l ≤ R.size)
    (hG : D + r ≤ G.size) :
    pieceNear R G l Ls r D j = true ↔ ∃ e, e ≤ 2 * r ∧
      ∀ i, i < l → G.get! (D - R.size - r + e + j * Ls + i) = R.get! (j * Ls + i) := by
  unfold pieceNear
  simp only []
  rw [if_neg (by omega), Bool.or_eq_true, nearL_iff, show min (2 * r) (D + j * Ls + r - R.size) = 2 * r by omega]
  simp only [Bool.and_eq_true, decide_eq_true_eq, GRead.size_bytes, matchLn_iff R G _ _ l l (Nat.le_refl _),
    Nat.sub_self, Nat.zero_le, true_implies]
  constructor
  · rintro (⟨-, h⟩ | ⟨p, h1, h2, -, h4⟩)
    · refine ⟨r, by omega, fun i hi => ?_⟩
      rw [show D - R.size - r + r + j * Ls + i = D + j * Ls + r - R.size - r + i by omega]; exact h i hi
    · refine ⟨p - (D + j * Ls + r - R.size - 2 * r), by omega, fun i hi => ?_⟩
      rw [show D - R.size - r + (p - (D + j * Ls + r - R.size - 2 * r)) + j * Ls + i = p + i by omega]
      exact h4 i hi
  · rintro ⟨e, he, h⟩
    exact Or.inr ⟨D - R.size - r + e + j * Ls, by omega, by omega, by omega, fun i hi => h i hi⟩

/-! ### Pieces by lanes -/

/-- A folded, cut mismatch field is clear iff the two fields agree. -/
theorem mdig0 (a g : UInt64) (c t : Nat) (ht : t < 32) (htc : t < c) :
    (lowF (fold (a ^^^ g)) c).toNat.testBit (2 * t) = false ↔ dig a.toNat t = dig g.toNat t := by
  have h := lowF_dig (fold (a ^^^ g)) c t ht
  rw [if_pos htc, fold_dig _ _ ht] at h
  have hle : dig (lowF (fold (a ^^^ g)) c).toNat t ≤ 1 := by rw [h]; split <;> omega
  have h2 := dig_le1 _ t hle
  rw [← xor_dig]
  constructor
  · intro hb
    rw [hb] at h2
    rw [h2] at h
    by_cases hne : dig (a ^^^ g).toNat t = 0
    · exact hne
    · rw [if_neg hne] at h
      simp at h
  · intro h0
    rw [if_pos h0] at h
    rw [h] at h2
    cases hb : (lowF (fold (a ^^^ g)) c).toNat.testBit (2 * t)
    · rfl
    · rw [hb] at h2; simp at h2

/-- Lane `i` of read word `w` at field offset `o + e`: the piece `4w + i` at read start `s0 + e`. -/
theorem laneW {R : ByteArray} {P : PGen} {Gb : ByteArray} {s0 r k o u0 : Nat}
    (h : WS R P Gb s0 (R.size + 2 * r)) (ho : o = (P.o + s0) % 32) (hu : u0 = (P.o + s0) / 32)
    (hk : (o + 2 * r + R.size) / 32 + 2 ≤ k)
    (e w i : Nat) (he : e ≤ 2 * r) (hi : i < 4) (hn : 32 * w + 8 * i + 8 ≤ R.size) :
    (laneZ (lowF (mAt (packRP R) (loadW P.w u0 k (Array.emptyWithCapacity 12)) (o + e) w)
      (R.size - 32 * w))).toNat.testBit (16 * i) = true ↔
      ∀ b, b < 8 → Gb.get! (s0 + e + (32 * w + 8 * i) + b) = R.get! (32 * w + 8 * i + b) := by
  subst ho hu
  rw [laneZ_bit _ i hi]
  apply forall_congr'; intro b
  apply imp_congr_right; intro hb
  unfold mAt
  rw [show 16 * i + 2 * b = 2 * (8 * i + b) by omega, mdig0 _ _ _ _ (by omega) (by omega),
    kw_dig R h.ok w (8 * i + b) (by omega) (by omega), show 32 * w + 8 * i + b = 32 * w + (8 * i + b) by omega]
  have hf := fieldW h k ((P.o + s0) % 32 + e + 32 * w) (32 * w + (8 * i + b)) (by omega) (by omega) (8 * i + b)
    (by omega) (by omega) (by omega)
  rw [show s0 + ((P.o + s0) % 32 + e + 32 * w + (8 * i + b) - (P.o + s0) % 32) = s0 + e + (32 * w + 8 * i) + b
    by omega] at hf
  constructor
  · intro hh; exact hf.mp hh.symm
  · intro hh; exact (hf.mpr hh).symm

theorem lanesAny_bit (K : RP) (gs : Array UInt64) (n w : Nat) (full : UInt64) (i : Nat) :
    ∀ k t F, (lanesAny K gs n w full F t k &&& full).toNat.testBit (16 * i) = true ↔
      full.toNat.testBit (16 * i) = true ∧ (F.toNat.testBit (16 * i) = true ∨
        ∃ e, e < k ∧ (laneZ (lowF (mAt K gs (t + e) w) (n - 32 * w))).toNat.testBit (16 * i) = true) := by
  intro k
  induction k with
  | zero =>
    intro t F
    simp only [lanesAny, UInt64.toNat_and, Nat.testBit_and, Bool.and_eq_true]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, Or.inl h1⟩
    · rintro ⟨h2, h1 | ⟨e, he, -⟩⟩
      · exact ⟨h1, h2⟩
      · omega
  | succ k ih =>
    intro t F
    simp only [lanesAny]
    split
    · rename_i hfull
      rw [beq_iff_eq] at hfull
      have hb := congrArg (fun x => x.toNat.testBit (16 * i)) hfull
      simp only [UInt64.toNat_and, Nat.testBit_and, UInt64.toNat_or, Nat.testBit_or] at hb
      rw [hfull]
      constructor
      · intro h1
        refine ⟨h1, ?_⟩
        simp only [h1, Bool.and_true, Bool.or_eq_true] at hb
        rcases hb with h2 | h2
        · exact Or.inl h2
        · exact Or.inr ⟨0, by omega, by simpa using h2⟩
      · exact fun h => h.1
    · rw [ih]
      simp only [UInt64.toNat_or, Nat.testBit_or, Bool.or_eq_true]
      constructor
      · rintro ⟨h1, (h2 | h2) | ⟨e, he, h3⟩⟩
        · exact ⟨h1, Or.inl h2⟩
        · exact ⟨h1, Or.inr ⟨0, by omega, by simpa using h2⟩⟩
        · exact ⟨h1, Or.inr ⟨e + 1, by omega, by rw [show t + (e + 1) = t + 1 + e by omega]; exact h3⟩⟩
      · rintro ⟨h1, h2 | ⟨e, he, h3⟩⟩
        · exact ⟨h1, Or.inl (Or.inl h2)⟩
        · cases e with
          | zero => exact ⟨h1, Or.inl (Or.inr (by simpa using h3))⟩
          | succ e =>
            exact ⟨h1, Or.inr ⟨e, by omega, by rw [show t + 1 + e = t + (e + 1) by omega]; exact h3⟩⟩

/-- The lanes word of `fineV`: lane `i` set iff `i < np` and the lane is clear at some offset. -/
theorem wordF_bit (K : RP) (gs : Array UInt64) (n w o r np : Nat) (hnp : np ≤ 4) (i : Nat) (hi : i < 4) :
    (let full := fullL np
     let F := laneZ (lowF (mAt K gs (o + r) w) (n - 32 * w)) &&& full
     if F == full then F else lanesAny K gs n w full F o (2 * r + 1) &&& full).toNat.testBit (16 * i) = true ↔
      i < np ∧ ∃ e, e < 2 * r + 1 ∧ (laneZ (lowF (mAt K gs (o + e) w) (n - 32 * w))).toNat.testBit (16 * i) = true := by
  have hf := fullL_bit np i hnp hi
  simp only []
  split
  · rename_i heq
    rw [beq_iff_eq] at heq
    have hb := congrArg (fun x => x.toNat.testBit (16 * i)) heq
    simp only [UInt64.toNat_and, Nat.testBit_and] at hb
    rw [heq, hf, decide_eq_true_iff]
    constructor
    · intro h1
      rw [hf, decide_eq_true h1, Bool.and_true] at hb
      exact ⟨h1, r, by omega, hb⟩
    · exact fun h => h.1
  · rw [lanesAny_bit]
    simp only [UInt64.toNat_and, Nat.testBit_and, hf, Bool.and_eq_true, decide_eq_true_iff]
    constructor
    · rintro ⟨h1, ⟨h2, -⟩ | h2⟩
      · exact ⟨h1, r, by omega, h2⟩
      · exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inr h2⟩

theorem cnt4 (p : Nat → Bool) (a np : Nat) (hnp : np ≤ 4) :
    cntP p a np = (if 0 < np then (if p (a + 0) then 1 else 0) else 0) +
      (if 1 < np then (if p (a + 1) then 1 else 0) else 0) +
      (if 2 < np then (if p (a + 2) then 1 else 0) else 0) +
      (if 3 < np then (if p (a + 3) then 1 else 0) else 0) := by
  obtain _ | _ | _ | _ | _ | np := np
  · simp [cntP]
  · simp [cntP]
  · simp [cntP]
  · simp [cntP, Nat.add_assoc]
  · simp [cntP, Nat.add_assoc]
  · omega

theorem lcCount (F : UInt64) (p : Nat → Bool) (a np : Nat) (hnp : np ≤ 4)
    (hF : ∀ i, i < 4 → (F.toNat.testBit (16 * i) = true ↔ i < np ∧ p (a + i) = true)) :
    lc F = cntP p a np := by
  have e : ∀ i, i < 4 → (if F.toNat.testBit (16 * i) then 1 else 0) =
      if i < np then (if p (a + i) then 1 else 0) else 0 := by
    intro i hi
    by_cases h1 : F.toNat.testBit (16 * i) = true
    · obtain ⟨h2, h3⟩ := (hF i hi).mp h1
      simp [h1, h2, h3]
    · have hn : ¬ (i < np ∧ p (a + i) = true) := fun hh => h1 ((hF i hi).mpr hh)
      by_cases h2 : i < np
      · have h3 : p (a + i) = false := by simpa [h2] using hn
        simp [h1, h2, h3]
      · simp [h1, h2]
  have e0 : (if F.toNat.testBit 0 then 1 else 0) = _ := e 0 (by omega)
  have e1 : (if F.toNat.testBit 16 then 1 else 0) = _ := e 1 (by omega)
  have e2 : (if F.toNat.testBit 32 then 1 else 0) = _ := e 2 (by omega)
  have e3 : (if F.toNat.testBit 48 then 1 else 0) = _ := e 3 (by omega)
  rw [lc_eq, e0, e1, e2, e3, cnt4 p a np hnp]

/-- Piece `4w + i` near `D` iff its lane is clear at some offset. -/
theorem pieceW {R : ByteArray} {P : PGen} {Gb : ByteArray} {r k o u0 D : Nat}
    (h : WS R P Gb (D - R.size - r) (R.size + 2 * r)) (ho : o = (P.o + (D - R.size - r)) % 32)
    (hu : u0 = (P.o + (D - R.size - r)) / 32) (hk : (o + 2 * r + R.size) / 32 + 2 ≤ k)
    (hD : R.size + r ≤ D) (hG : D + r ≤ Gb.size) (w i : Nat) (hi : i < 4) (hn : 32 * w + 8 * i + 8 ≤ R.size) :
    pieceNear R Gb 8 8 r D (4 * w + i) = true ↔ ∃ e, e < 2 * r + 1 ∧
      (laneZ (lowF (mAt (packRP R) (loadW P.w u0 k (Array.emptyWithCapacity 12)) (o + e) w)
        (R.size - 32 * w))).toNat.testBit (16 * i) = true := by
  rw [pieceNear_iff R Gb 8 8 r D (4 * w + i) hD (by omega) hG,
    show (4 * w + i) * 8 = 32 * w + 8 * i by omega]
  constructor
  · rintro ⟨e, he, hh⟩
    exact ⟨e, by omega, (laneW h ho hu hk e w i he hi hn).mpr hh⟩
  · rintro ⟨e, he, hh⟩
    exact ⟨e, by omega, (laneW h ho hu hk e w i (by omega) hi hn).mp hh⟩

theorem fineV_cnt {R : ByteArray} {P : PGen} {Gb : ByteArray} {r k o u0 D : Nat}
    (h : WS R P Gb (D - R.size - r) (R.size + 2 * r)) (ho : o = (P.o + (D - R.size - r)) % 32)
    (hu : u0 = (P.o + (D - R.size - r)) / 32) (hk : (o + 2 * r + R.size) / 32 + 2 ≤ k)
    (hD : R.size + r ≤ D) (hG : D + r ≤ Gb.size) (m : Nat) (hm : 8 * m ≤ R.size) :
    ∀ c j acc, fineV (packRP R) (loadW P.w u0 k (Array.emptyWithCapacity 12)) o R.size r m j c acc =
      acc + cntP (fun j => pieceNear R Gb 8 8 r D j) (4 * j) (min (4 * c) (m - 4 * j)) := by
  intro c
  induction c with
  | zero => intro j acc; simp [fineV, cntP]
  | succ c ih =>
    intro j acc
    rw [fineV, ih]
    rw [lcCount _ (fun j => pieceNear R Gb 8 8 r D j) (4 * j) (min 4 (m - 4 * j)) (by omega) (fun i hi => ?hF)]
    case hF =>
      rw [wordF_bit (packRP R) _ R.size j o r (min 4 (m - 4 * j)) (by omega) i hi]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, (pieceW h ho hu hk hD hG j i hi (by omega)).mpr h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, (pieceW h ho hu hk hD hG j i hi (by omega)).mp h2⟩
    rw [show min (4 * (c + 1)) (m - 4 * j) = min 4 (m - 4 * j) + min (4 * c) (m - 4 * (j + 1)) by omega,
      cntP_add]
    by_cases hc : 4 ≤ m - 4 * j
    · rw [show 4 * j + min 4 (m - 4 * j) = 4 * (j + 1) by omega]; omega
    · rw [show min (4 * c) (m - 4 * (j + 1)) = 0 by omega]; simp only [cntP]; omega

/-- The piece count by words is `fineOk`. -/
theorem fineW_eq {R : ByteArray} {P : PGen} {Gb : ByteArray} {r k o u0 D : Nat}
    (h : WS R P Gb (D - R.size - r) (R.size + 2 * r)) (ho : o = (P.o + (D - R.size - r)) % 32)
    (hu : u0 = (P.o + (D - R.size - r)) / 32) (hk : (o + 2 * r + R.size) / 32 + 2 ≤ k)
    (hD : R.size + r ≤ D) (hG : D + r ≤ Gb.size) (h8 : R.size / (R.size / pl) = 8) (sb : Nat) :
    decide (R.size / pl ≤ sb + fineV (packRP R) (loadW P.w u0 k (Array.emptyWithCapacity 12)) o R.size r
      (R.size / pl) 0 ((R.size + 31) / 32) 0) = fineOk R Gb pl (R.size / (R.size / pl)) r D sb 0 0 (R.size / pl) := by
  have hpl : pl = 8 := rfl
  rw [h8, fineOk_cnt _ _ _ _ _ _ _ _ _ _ (Nat.zero_le _), hpl,
    fineV_cnt h ho hu hk hD hG (R.size / 8) (by omega)]
  rw [show min (4 * ((R.size + 31) / 32)) (R.size / 8 - 4 * 0) = R.size / 8 by omega, Nat.mul_zero]
  have hc := cntP_compl (fun j => pieceNear R Gb 8 8 r D j) (R.size / 8) 0
  exact decide_eq_decide.mpr (by omega)

theorem kfiltV_eq {Gt : Type} [GRead Gt] [GPk Gt] (R : ByteArray) (G : Gt) (acc : List (Array Nat))
    (us : List Nat) (Ls lim : Nat) (b : Best) (D : Nat) :
    kfiltV (packRP R) R G acc us Ls lim b D = kfilt R G acc us Ls lim b D := by
  unfold kfiltV
  simp only []
  split
  · rename_i hf
    split
    · rename_i P hP
      split
      · rename_i hw
        simp only [wordWin, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hw
        obtain ⟨⟨⟨hok, hD⟩, h8⟩, hwin⟩ := hw
        have hS := GPk.pk_same G P hP
        have hR := Mz.rep_unpack P
        have hGb : SameG G (Mz.unpack P) :=
          ⟨hS.1.trans hR.1, fun i => (hS.2 i).trans (hR.2 i)⟩
        have hfl := winOk_flags P _ _ hwin
        have hW : WS R P (Mz.unpack P) (D - R.size - 2 * gapBound sc0 (-(min lim b.pen : Nat) : Int))
            (R.size + 2 * (2 * gapBound sc0 (-(min lim b.pen : Nat) : Int))) :=
          ⟨hR, hok, fun y h1 h2 => ⟨by omega, hfl.2 y h1 h2⟩⟩
        have hG : D + 2 * gapBound sc0 (-(min lim b.pen : Nat) : Int) ≤ (Mz.unpack P).size := by
          rw [← hW.rep.1]; omega
        unfold kfilt
        simp only []
        rw [decide_eq_true hf, Bool.true_and, fineOk_same hGb, ← fineW_eq hW rfl rfl (Nat.le_refl _) hD hG h8]
        congr 1
        apply unlookV_eq
        intro j hA
        rw [seedNear_same hGb]
        exact seedV_eq hW hD Ls j hA
      · rfl
    · rfl
  · rename_i hf
    unfold kfilt
    simp only []
    rw [decide_eq_false hf, Bool.false_and, Bool.false_and]

theorem stageKSV_eq {Gt : Type} [GRead Gt] [GPk Gt] (body : Nat → Best → Best) (R : ByteArray) (G : Gt)
    (acc : List (Array Nat)) (us : List Nat) (Ls lim : Nat) (ds : List Nat) (b : Best) :
    stageKSV body (packRP R) R G acc us Ls lim ds b = stageKS body R G acc us Ls lim ds b := by
  simp only [stageKSV, stageKS, kfiltV_eq]

end MapSpec.Fast
