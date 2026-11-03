import FastGenPairPacked
import FastGenK250

/-!
# The diagonal filter by words (`wordFilter = kfilt`)

`kfilt` (codecs/FastGenAlgo.lean) checks, for a diagonal `D`, the 25-letter seeds not
looked up (`unlook`) and the 8-letter pieces (`fineOk`) at each of the `2r + 1` read
starts `s ∈ [D − n − r, D − n + r]`, letter by letter.  When the genome is a packed
`PGen` (`PackedOf`), the read is ACGT and packed (`packRP`), and the whole window lies in
all-ACGT blocks away from the chromosome start, `wordFilter` does the same tests on
2-bit words: the genome words of the window are loaded once into one unboxed object
that keeps no reference to the genome (`loadWords`); a seed is 25 fields compared at once
(`seedEqual`); the pieces of a read word are four 16-bit lanes of its folded mismatch word,
all tested at once (`laneClear`), and the piece count stops once its outcome is known
(`piecesEnough_eq`).  Elsewhere it is `kfilt`.  A stage looks up the packed genome once
(`packedFor`, `wordFilterPacked`), and the word path does not pass the genome on, so the genome shared by
the mapping tasks has its reference count touched per stage, not per diagonal.

    wordFilter (packRP R) R G acc us Ls lim b D = kfilt R G acc us Ls lim b D      (wordFilter_eq)
-/

namespace MapSpec.Fast

open MapSpec MapSpec.Packed

/-- A genome representation that may carry its packed form (same letters). -/
class PackedOf (Gt : Type) [GRead Gt] where
  pk : Gt → Option PGen
  pk_same : ∀ (G : Gt) (P : PGen), pk G = some P → SameG G P

instance : PackedOf ByteArray := ⟨fun _ => none, fun _ _ h => by cases h⟩

instance : PackedOf PGen := ⟨some, fun G P h => by cases h; exact ⟨rfl, fun _ => rfl⟩⟩

/-- Words `u0, u0 + 1, …` (`k` more) of the blocks pushed onto `a`. -/
def loadWordsList (w : ByteArray) (u0 : Nat) : Nat → Array UInt64 → Array UInt64
  | 0, a => a
  | k + 1, a => loadWordsList w (u0 + 1) k (a.push (gword w u0))

/-- The genome words of a window, unboxed: words `i < 16` in fields (0 past the `k`
loaded), later ones in `rest` (empty unless `k > 16`).  No reference to the genome is
kept, so the shared genome's count is not touched per window. -/
structure GenomeWords where
  rest : Array UInt64
  (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : UInt64)

/-- Word `u0 + i` if `i < k`. -/
@[inline] def loadWordAt (w : ByteArray) (u0 k i : Nat) : UInt64 := if i < k then gword w (u0 + i) else 0

/-- Words `u0, u0 + 1, …` (`k` of them) of the blocks. -/
@[inline] def loadWords (w : ByteArray) (u0 k : Nat) : GenomeWords :=
  ⟨loadWordsList w (u0 + 16) (k - 16) #[], loadWordAt w u0 k 0, loadWordAt w u0 k 1, loadWordAt w u0 k 2, loadWordAt w u0 k 3, loadWordAt w u0 k 4, loadWordAt w u0 k 5, loadWordAt w u0 k 6, loadWordAt w u0 k 7, loadWordAt w u0 k 8, loadWordAt w u0 k 9, loadWordAt w u0 k 10, loadWordAt w u0 k 11, loadWordAt w u0 k 12, loadWordAt w u0 k 13, loadWordAt w u0 k 14, loadWordAt w u0 k 15⟩

/-- `loadWordAt` on machine words (`loadWordAtWord_eq`). -/
@[inline] def loadWordAtWord (w : ByteArray) (u0 k i : USize) : UInt64 := if i < k then gwordU w (u0 + i) else 0

theorem loadWordAtWord_eq (w : ByteArray) (u0 k i : USize) (hu : u0.toNat + 16 < 2 ^ 28) (hi : i.toNat < 16) :
    loadWordAtWord w u0 k i = loadWordAt w u0.toNat k.toNat i.toNat := by
  unfold loadWordAtWord loadWordAt
  have e : (u0 + i).toNat = u0.toNat + i.toNat := usz_add' _ _ (by omega)
  by_cases c : i < k
  · rw [if_pos c, if_pos (show i.toNat < k.toNat from c), gwordU_eq w _ (by omega), e]
  · rw [if_neg c, if_neg (show ¬ i.toNat < k.toNat from c)]

/-- `loadWords` with the 16 field words read on machine words when the window fits (`loadWords_eqU`). -/
@[inline] def loadWordsWord (w : ByteArray) (u0 k : Nat) : GenomeWords :=
  if u0 + 16 < 2 ^ 28 ∧ k < 2 ^ 28 then
    let uU := u0.toUSize
    let kU := k.toUSize
    ⟨loadWordsList w (u0 + 16) (k - 16) #[], loadWordAtWord w uU kU 0, loadWordAtWord w uU kU 1, loadWordAtWord w uU kU 2, loadWordAtWord w uU kU 3,
      loadWordAtWord w uU kU 4, loadWordAtWord w uU kU 5, loadWordAtWord w uU kU 6, loadWordAtWord w uU kU 7, loadWordAtWord w uU kU 8, loadWordAtWord w uU kU 9,
      loadWordAtWord w uU kU 10, loadWordAtWord w uU kU 11, loadWordAtWord w uU kU 12, loadWordAtWord w uU kU 13, loadWordAtWord w uU kU 14, loadWordAtWord w uU kU 15⟩
  else loadWords w u0 k

@[csimp] theorem loadWords_eqU : @loadWords = @loadWordsWord := by
  funext w u0 k
  unfold loadWordsWord
  split
  · next h =>
    have hu : u0.toUSize.toNat = u0 := usz_n _ (by omega)
    have hk : k.toUSize.toNat = k := usz_n _ (by omega)
    have l : ∀ i : Nat, i < 16 → loadWordAtWord w u0.toUSize k.toUSize (OfNat.ofNat i) = loadWordAt w u0 k i := by
      intro i hi
      rw [loadWordAtWord_eq w _ _ _ (by rw [hu]; omega) (by rw [usz_lit i (by omega)]; exact hi), hu, hk, usz_lit i (by omega)]
    simp only [loadWords, l 0 (by decide), l 1 (by decide), l 2 (by decide), l 3 (by decide), l 4 (by decide),
      l 5 (by decide), l 6 (by decide), l 7 (by decide), l 8 (by decide), l 9 (by decide), l 10 (by decide),
      l 11 (by decide), l 12 (by decide), l 13 (by decide), l 14 (by decide), l 15 (by decide)]
  · rfl

/-- Word `i` of the window. -/
@[inline] def GenomeWords.get (g : GenomeWords) (i : Nat) : UInt64 :=
  if i < 8 then
    if i < 4 then (if i < 2 then (if i = 0 then g.w0 else g.w1) else (if i = 2 then g.w2 else g.w3))
    else (if i < 6 then (if i = 4 then g.w4 else g.w5) else (if i = 6 then g.w6 else g.w7))
  else if i < 16 then
    if i < 12 then (if i < 10 then (if i = 8 then g.w8 else g.w9) else (if i = 10 then g.w10 else g.w11))
    else (if i < 14 then (if i = 12 then g.w12 else g.w13) else (if i = 14 then g.w14 else g.w15))
  else g.rest.getD (i - 16) 0

/-- The 32 fields starting at field `t` of the words `gs`. -/
@[inline] def fieldsAt (gs : Array UInt64) (t : Nat) : UInt64 :=
  let s := t % 32
  comb (gs.getD (t / 32) 0) (gs.getD (t / 32 + 1) 0) s (2 * s).toUInt64 (64 - 2 * s).toUInt64

/-- `fieldsAt` on window words. -/
@[inline] def windowAt (gs : GenomeWords) (t : Nat) : UInt64 :=
  let s := t % 32
  comb (gs.get (t / 32)) (gs.get (t / 32 + 1)) s (2 * s).toUInt64 (64 - 2 * s).toUInt64

/-- The low 25 fields agree. -/
@[inline] def seedEqual (x y : UInt64) : Bool := lowF (x ^^^ y) 25 == 0

/-- The seed `sv` is at some field offset `t, t + 1, …` (`k` of them) of `gs`. -/
def seedAny (gs : GenomeWords) (sv : UInt64) (t : Nat) : Nat → Bool
  | 0 => false
  | k + 1 => seedEqual (windowAt gs t) sv || seedAny gs sv (t + 1) k

/-! `seedAny` and `laneScan` on machine words (compiled code only): `seedAny_eq_svAnyF` (a rolling window,
`seedAnyRoll`, below), `laneScan_eq_lanesAnyF` (`@[csimp]`). The `laneScan` loops keep the field offset `t` in `USize` (word
`t >>> 5 + j`, shift `t &&& 31`: `windowAtWord`) and read the window words through `GenomeWords.getU` (`USize`
compares); `laneScanWord` also hoists the read word `K.w.getD j 0` and the field count `n - 32 j`. -/

/-- `GenomeWords.get` at a machine-word index (`GenomeWords.getU_eq`). -/
@[inline] def GenomeWords.getU (g : GenomeWords) (i : USize) : UInt64 :=
  if i < 8 then
    if i < 4 then (if i < 2 then (if i = 0 then g.w0 else g.w1) else (if i = 2 then g.w2 else g.w3))
    else (if i < 6 then (if i = 4 then g.w4 else g.w5) else (if i = 6 then g.w6 else g.w7))
  else if i < 16 then
    if i < 12 then (if i < 10 then (if i = 8 then g.w8 else g.w9) else (if i = 10 then g.w10 else g.w11))
    else (if i < 14 then (if i = 12 then g.w12 else g.w13) else (if i = 14 then g.w14 else g.w15))
  else g.rest.getD (i - 16).toNat 0

theorem usz_lt_iff (i : USize) (c : Nat) (hc : c < 2 ^ 32) : (i < (OfNat.ofNat c : USize)) ↔ i.toNat < c := by
  show i.toNat < (OfNat.ofNat c : USize).toNat ↔ _
  rw [usz_lit c hc]

theorem usz_eq_iff (i : USize) (c : Nat) (hc : c < 2 ^ 32) : (i = (OfNat.ofNat c : USize)) ↔ i.toNat = c := by
  constructor
  · intro h; rw [h, usz_lit c hc]
  · intro h; apply USize.toNat_inj.mp; rw [h, usz_lit c hc]

theorem GenomeWords.getU_eq (g : GenomeWords) (i : USize) : g.getU i = g.get i.toNat := by
  unfold GenomeWords.getU GenomeWords.get
  simp only [usz_lt_iff i 8 (by decide), usz_lt_iff i 4 (by decide), usz_lt_iff i 2 (by decide),
    usz_lt_iff i 6 (by decide), usz_lt_iff i 16 (by decide), usz_lt_iff i 12 (by decide),
    usz_lt_iff i 10 (by decide), usz_lt_iff i 14 (by decide), usz_eq_iff i 0 (by decide),
    usz_eq_iff i 2 (by decide), usz_eq_iff i 4 (by decide), usz_eq_iff i 6 (by decide),
    usz_eq_iff i 8 (by decide), usz_eq_iff i 10 (by decide), usz_eq_iff i 12 (by decide),
    usz_eq_iff i 14 (by decide)]
  split
  · rfl
  · split
    · rfl
    · rename_i h1 h2
      rw [USize.toNat_sub_of_le _ _ (by show (16 : USize).toNat ≤ i.toNat; rw [usz_lit 16 (by decide)]; omega),
        usz_lit 16 (by decide)]

/-- `windowAt gs (t + 32 j)` with `t`, `j` in `USize` (`windowAtWord_eq`). -/
@[inline] def windowAtWord (gs : GenomeWords) (t jU : USize) : UInt64 :=
  let u := (t >>> 5) + jU
  let s := t &&& 31
  comb (gs.getU u) (gs.getU (u + 1)) s.toNat (2 * s).toUInt64 (64 - 2 * s).toUInt64

theorem windowAtWord_eq (gs : GenomeWords) (tU jU : USize) (t j : Nat) (ht : tU.toNat = t) (hj : jU.toNat = j)
    (hb : t + 32 * j < 2 ^ 31) : windowAtWord gs tU jU = windowAt gs (t + 32 * j) := by
  have hs : (tU &&& 31).toNat = (t + 32 * j) % 32 := by
    rw [USize.toNat_and, usz_lit 31 (by decide), ht, show (31 : Nat) = 2 ^ 5 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]; omega
  have hu : ((tU >>> 5) + jU).toNat = (t + 32 * j) / 32 := by
    rw [usz_add' _ _ (by rw [usz_shr5]; omega), usz_shr5, ht, hj]; omega
  have hu1 : ((tU >>> 5) + jU + 1).toNat = (t + 32 * j) / 32 + 1 := by
    rw [usz_add' _ _ (by rw [hu, usz_lit 1 (by decide)]; omega), hu, usz_lit 1 (by decide)]
  have hlt : (tU &&& 31).toNat < 32 := by rw [hs]; omega
  have h2 : (2 * (tU &&& 31)).toNat = 2 * ((t + 32 * j) % 32) := by
    rw [usz_mul' _ _ (by rw [usz_lit 2 (by decide)]; omega), usz_lit 2 (by decide), hs]
  have h64le : (2 * (tU &&& 31)).toNat ≤ (64 : USize).toNat := by rw [h2, usz_lit 64 (by decide)]; omega
  have h64 : (64 - 2 * (tU &&& 31)).toNat = 64 - 2 * ((t + 32 * j) % 32) := by
    rw [USize.toNat_sub_of_le _ _ h64le, h2, usz_lit 64 (by decide)]
  have c1 : (2 * (tU &&& 31)).toUInt64 = (2 * ((t + 32 * j) % 32)).toUInt64 := by
    apply UInt64.toNat_inj.mp
    rw [USize.toNat_toUInt64, h2, Nat.toUInt64_eq, UInt64.toNat_ofNat']
    exact (Nat.mod_eq_of_lt (by omega)).symm
  have c2 : (64 - 2 * (tU &&& 31)).toUInt64 = (64 - 2 * ((t + 32 * j) % 32)).toUInt64 := by
    apply UInt64.toNat_inj.mp
    rw [USize.toNat_toUInt64, h64, Nat.toUInt64_eq, UInt64.toNat_ofNat']
    exact (Nat.mod_eq_of_lt (by omega)).symm
  unfold windowAtWord windowAt
  simp only []
  rw [GenomeWords.getU_eq, GenomeWords.getU_eq, hu, hu1, hs, c1, c2]

/-- `windowAt` (its slow path; not rewritten by `csimp`). -/
@[inline] def windowAtSlow (gs : GenomeWords) (t : Nat) : UInt64 :=
  let s := t % 32
  comb (gs.get (t / 32)) (gs.get (t / 32 + 1)) s (2 * s).toUInt64 (64 - 2 * s).toUInt64

/-- `windowAt` for the compiled code (`windowAt_eqF`): `USize` offsets and `GenomeWords.getU`. -/
@[inline] def windowAtFast (gs : GenomeWords) (t : Nat) : UInt64 :=
  if t < 2147483648 then windowAtWord gs t.toUSize 0 else windowAtSlow gs t

@[csimp] theorem windowAt_eqF : @windowAt = @windowAtFast := by
  funext gs t
  unfold windowAtFast; split
  · rename_i h
    have := windowAtWord_eq gs t.toUSize 0 t 0 (usz_n _ (by omega)) (usz_lit 0 (by decide)) (by omega)
    rw [Nat.mul_zero, Nat.add_zero] at this
    exact this.symm
  · rfl
/-- `seedAny` (its slow path; not rewritten by `csimp`). -/
def seedAnySlow (gs : GenomeWords) (sv : UInt64) (t : Nat) : Nat → Bool
  | 0 => false
  | k + 1 => seedEqual (windowAt gs t) sv || seedAnySlow gs sv (t + 1) k

theorem seedAnySlow_eq (gs : GenomeWords) (sv : UInt64) : ∀ k t, seedAnySlow gs sv t k = seedAny gs sv t k := by
  intro k
  induction k with
  | zero => intro t; rfl
  | succ k ih => intro t; simp only [seedAnySlow, seedAny, ih]

/-! `seedAny` on a rolling window (`seedAny_eq_svAnyF`): the 32 window fields at the current offset in one register `a`,
one field shifted in per step from a pending word `b` (refilled every 32 steps), as `laneScanRoll` below. -/

/-- Field `p` of the window words. -/
def windowField (gs : GenomeWords) (p : Nat) : Nat := dig (gs.get (p / 32)).toNat (p % 32)

theorem windowAt_dig (gs : GenomeWords) (T f : Nat) (hf : f < 32) : dig (windowAt gs T).toNat f = windowField gs (T + f) := by
  unfold windowAt windowField
  rw [comb_dig _ _ _ _ (Nat.mod_lt _ (by omega)) hf]
  split
  · rw [show (T + f) / 32 = T / 32 by omega, show (T + f) % 32 = T % 32 + f by omega]
  · rw [show (T + f) / 32 = T / 32 + 1 by omega, show (T + f) % 32 = T % 32 + f - 32 by omega]

theorem roll_eq (gs : GenomeWords) (T : Nat) (a b : UInt64) (ha : a = windowAt gs T)
    (hb : dig b.toNat 0 = windowField gs (T + 32)) : (a >>> 2) ||| (b <<< 62) = windowAt gs (T + 1) := by
  apply UInt64.toNat_inj.mp
  apply eq_of_dig 32 _ _ (by have := UInt64.toNat_lt ((a >>> 2) ||| (b <<< 62)); simpa using this)
    (by have := UInt64.toNat_lt (windowAt gs (T + 1)); simpa using this)
  intro f hf
  rw [windowAt_dig _ _ _ hf]
  have h2 : (2 : UInt64).toNat = 2 * 1 := rfl
  have h62 : (62 : UInt64).toNat = 2 * 31 := rfl
  by_cases h31 : f < 31
  · rw [or_dig_l _ _ _ (by rw [shl_dig _ _ 31 f h62 (by omega) hf, if_neg (by omega)]),
      shr_dig _ _ 1 f h2 (by omega), ha, windowAt_dig _ _ _ (by omega)]
    congr 1; omega
  · rw [or_dig_r _ _ _ (by rw [shr_dig _ _ 1 f h2 (by omega)]; exact dig_hi _ _ (by omega)),
      shl_dig _ _ 31 f h62 (by omega) hf, if_pos (by omega), show f - 31 = 0 by omega, hb]
    congr 1; omega

/-- The rolling state: `b` holds the `c` fields after the window at `T` (from word `u`). -/
def RInv (gs : GenomeWords) (T : Nat) (b : UInt64) (c u : USize) : Prop :=
  1 ≤ c.toNat ∧ c.toNat ≤ 32 ∧ T + 32 + c.toNat = 32 * (u.toNat + 1) ∧
    ∀ f, f < c.toNat → dig b.toNat f = windowField gs (T + 32 + f)

theorem rinv_step (gs : GenomeWords) (T : Nat) (b : UInt64) (c u : USize) (h : RInv gs T b c u) (hu : u.toNat + 2 < 2 ^ 32) :
    (if c == 1 then RInv gs (T + 1) (gs.getU (u + 1)) 32 (u + 1) else RInv gs (T + 1) (b >>> 2) (c - 1) u) := by
  obtain ⟨h1, h32, he, hf⟩ := h
  have hu1 : (u + 1).toNat = u.toNat + 1 := by rw [usz_add' _ _ (by rw [usz_lit 1 (by decide)]; omega), usz_lit 1 (by decide)]
  split
  · rename_i hc
    have hc1 : c.toNat = 1 := by rw [beq_iff_eq] at hc; rw [hc]; exact usz_lit 1 (by decide)
    refine ⟨by rw [usz_lit 32 (by decide)]; omega, by rw [usz_lit 32 (by decide)]; omega,
      by rw [usz_lit 32 (by decide), hu1]; omega, ?_⟩
    intro f hf'
    rw [usz_lit 32 (by decide)] at hf'
    rw [GenomeWords.getU_eq, hu1]
    unfold windowField
    rw [show (T + 1 + 32 + f) / 32 = u.toNat + 1 by omega, show (T + 1 + 32 + f) % 32 = f by omega]
  · rename_i hc
    have hc1 : c.toNat ≠ 1 := fun e => hc (by rw [beq_iff_eq]; exact USize.toNat_inj.mp (by rw [e, usz_lit 1 (by decide)]))
    have hcs : (c - 1).toNat = c.toNat - 1 := by
      rw [USize.toNat_sub_of_le _ _ (by show (1 : USize).toNat ≤ c.toNat; rw [usz_lit 1 (by decide)]; omega),
        usz_lit 1 (by decide)]
    refine ⟨by omega, by omega, by omega, ?_⟩
    intro f hf'
    rw [shr_dig _ _ 1 f rfl (by omega), hf _ (by omega)]
    congr 1; omega

/-- `seedAny gs sv T k` on the rolling window `a = windowAt gs T`, `b` (`RInv`): `seedAnyRoll_eq`. -/
def seedAnyRoll (gs : GenomeWords) (sv : UInt64) (k : USize) (a b : UInt64) (c u : USize) : Bool :=
  if h : k = 0 then false else
    if seedEqual a sv then true else
      let a' := (a >>> 2) ||| (b <<< 62)
      if c == 1 then seedAnyRoll gs sv (k - 1) a' (gs.getU (u + 1)) 32 (u + 1)
      else seedAnyRoll gs sv (k - 1) a' (b >>> 2) (c - 1) u
termination_by k.toNat
decreasing_by
  all_goals
    have h0 : k.toNat ≠ 0 := fun e => h (USize.toNat_inj.mp (by rw [e]; rfl))
    rw [USize.toNat_sub_of_le _ _ (by show (1 : USize).toNat ≤ k.toNat; rw [usz_lit 1 (by decide)]; omega),
      usz_lit 1 (by decide)]
    omega

theorem seedAnyRoll_eq (gs : GenomeWords) (sv : UInt64) :
    ∀ n (k : USize), k.toNat = n → ∀ T a b c u, a = windowAt gs T → RInv gs T b c u → T + n + 64 < 2 ^ 31 →
      seedAnyRoll gs sv k a b c u = seedAny gs sv T n := by
  intro n
  induction n with
  | zero =>
    intro k hk T a b c u _ _ _
    have : k = 0 := USize.toNat_inj.mp (by rw [hk]; rfl)
    rw [seedAnyRoll, dif_pos this]; rfl
  | succ n ih =>
    intro k hk T a b c u ha hI hB
    have h0 : k ≠ 0 := fun e => by rw [e] at hk; simp at hk
    have hk1 : (k - 1).toNat = n := by
      rw [USize.toNat_sub_of_le _ _ (by show (1 : USize).toNat ≤ k.toNat; rw [usz_lit 1 (by decide)]; omega),
        usz_lit 1 (by decide)]; omega
    have hu : u.toNat + 2 < 2 ^ 32 := by obtain ⟨_, _, he, _⟩ := hI; omega
    have ha' : (a >>> 2) ||| (b <<< 62) = windowAt gs (T + 1) :=
      roll_eq gs T a b ha (by obtain ⟨h1, _, _, hf⟩ := hI; simpa using hf 0 (by omega))
    have hstep := rinv_step gs T b c u hI hu
    rw [seedAnyRoll, dif_neg h0, seedAny, ← ha]
    simp only []
    split
    · rename_i he; rw [he, Bool.true_or]
    · rename_i he
      rw [Bool.eq_false_iff.mpr he, Bool.false_or]
      split
      · rename_i hc; rw [if_pos hc] at hstep; exact ih _ hk1 _ _ _ _ _ ha' hstep (by omega)
      · rename_i hc; rw [if_neg hc] at hstep; exact ih _ hk1 _ _ _ _ _ ha' hstep (by omega)

/-- The rolling state at field offset `t` (`seedAnyFast`, `wordPieces`): word `t / 32 + 1` shifted to start at field `t + 32`. -/
theorem rinv_start (gs : GenomeWords) (t : Nat) (ht : t + 64 < 2 ^ 31) :
    RInv gs t (gs.getU (t.toUSize >>> 5 + 1) >>> (2 * (t.toUSize &&& 31)).toUInt64) (32 - (t.toUSize &&& 31))
      (t.toUSize >>> 5 + 1) := by
  have ho : t.toUSize.toNat = t := usz_n _ (by omega)
  have hs : (t.toUSize &&& 31).toNat = t % 32 := by
    rw [USize.toNat_and, usz_lit 31 (by decide), ho, show (31 : Nat) = 2 ^ 5 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  have hu : (t.toUSize >>> 5 + 1).toNat = t / 32 + 1 := by
    rw [usz_add' _ _ (by rw [usz_shr5, ho, usz_lit 1 (by decide)]; omega), usz_shr5, ho, usz_lit 1 (by decide)]
  have hc : (32 - (t.toUSize &&& 31)).toNat = 32 - t % 32 := by
    rw [USize.toNat_sub_of_le _ _ (by show (t.toUSize &&& 31).toNat ≤ (32 : USize).toNat; rw [hs, usz_lit 32 (by decide)]; omega),
      hs, usz_lit 32 (by decide)]
  have h2s : ((2 * (t.toUSize &&& 31)).toUInt64).toNat = 2 * (t % 32) := by
    rw [USize.toNat_toUInt64, usz_mul' _ _ (by rw [hs, usz_lit 2 (by decide)]; omega), usz_lit 2 (by decide), hs]
  refine ⟨by rw [hc]; omega, by rw [hc]; omega, by rw [hc, hu]; omega, ?_⟩
  intro f hf'
  rw [hc] at hf'
  rw [shr_dig _ _ (t % 32) f h2s (by omega), GenomeWords.getU_eq, hu]
  unfold windowField
  rw [show (t + 32 + f) / 32 = t / 32 + 1 by omega, show (t + 32 + f) % 32 = f + t % 32 by omega]

/-- `seedAny` for the compiled code (`seedAny_eq_svAnyF`): the rolling scan within its bounds. -/
@[inline] def seedAnyFast (gs : GenomeWords) (sv : UInt64) (t k : Nat) : Bool :=
  if t + k + 64 < 2147483648 then
    let tU := t.toUSize
    seedAnyRoll gs sv k.toUSize (windowAtWord gs tU 0) (gs.getU (tU >>> 5 + 1) >>> (2 * (tU &&& 31)).toUInt64) (32 - (tU &&& 31))
      (tU >>> 5 + 1)
  else seedAnySlow gs sv t k

@[csimp] theorem seedAny_eq_svAnyF : @seedAny = @seedAnyFast := by
  funext gs sv t k
  unfold seedAnyFast; split
  · rename_i h
    have ha : windowAtWord gs t.toUSize 0 = windowAt gs t := by
      have := windowAtWord_eq gs t.toUSize 0 t 0 (usz_n _ (by omega)) (usz_lit 0 (by decide)) (by omega)
      rwa [Nat.mul_zero, Nat.add_zero] at this
    exact (seedAnyRoll_eq gs sv k _ (usz_n _ (by omega)) t _ _ _ _ ha (rinv_start gs t (by omega)) (by omega)).symm
  · exact (seedAnySlow_eq gs sv k t).symm

/-- `unlook` by words, for seeds inside the read: read start `s` ↦ field `o + (s − s0)`
of `gs` (`s0 = D − n − r`).  The genome is not passed (its count is not touched). -/
def unseenSeedsOk (K : RP) (gs : GenomeWords) (o Ls r sb : Nat) : List Nat → Nat → Bool
  | [], _ => true
  | j :: us, f =>
    let A := j * Ls
    let sv := fieldsAt K.w A
    let ok := seedEqual (windowAt gs (o + A + r)) sv || seedAny gs sv (o + A) (2 * r + 1)
    if ok then unseenSeedsOk K gs o Ls r sb us f
    else if sb < f + 1 then false else unseenSeedsOk K gs o Ls r sb us (f + 1)

/-- The seeds `us` as (read start, seed word), computed once per read (`unseenSeedsOkWords_eq`). -/
def seedWords (K : RP) (Ls : Nat) (us : List Nat) : List (Nat × UInt64) := us.map fun j => (j * Ls, fieldsAt K.w (j * Ls))

/-- `unseenSeedsOk` on the seeds' precomputed starts and words (`unseenSeedsOkWords_eq`). -/
def unseenSeedsOkWords (gs : GenomeWords) (o r sb : Nat) : List (Nat × UInt64) → Nat → Bool
  | [], _ => true
  | (A, sv) :: svs, f =>
    let ok := seedEqual (windowAt gs (o + A + r)) sv || seedAny gs sv (o + A) (2 * r + 1)
    if ok then unseenSeedsOkWords gs o r sb svs f
    else if sb < f + 1 then false else unseenSeedsOkWords gs o r sb svs (f + 1)

theorem unseenSeedsOkWords_eq (K : RP) (gs : GenomeWords) (o Ls r sb : Nat) :
    ∀ us f, unseenSeedsOkWords gs o r sb (seedWords K Ls us) f = unseenSeedsOk K gs o Ls r sb us f := by
  intro us
  induction us with
  | nil => intro f; rfl
  | cons j us ih => intro f; simp only [seedWords, List.map_cons, unseenSeedsOkWords, unseenSeedsOk] at ih ⊢; simp only [ih]

/-- The seeds `us` lie inside the read (`j·Ls + q ≤ n`). -/
def seedsInside (Ls n : Nat) : List Nat → Bool
  | [] => true
  | j :: us => decide (j * Ls + q ≤ n) && seedsInside Ls n us

theorem seedsInside_mem (Ls n : Nat) : ∀ us, seedsInside Ls n us = true → ∀ j, j ∈ us → j * Ls + q ≤ n
  | [], _, j, hj => by cases hj
  | i :: us, h, j, hj => by
    simp only [seedsInside, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hj with e | e
    · subst e; exact h.1
    · exact seedsInside_mem Ls n us h.2 j e

/-- Folded mismatches of read word `j` against the genome at field offset `t`. -/
@[inline] def mismatchAt (K : RP) (gs : GenomeWords) (t j : Nat) : UInt64 :=
  fold (K.w.getD j 0 ^^^ windowAt gs (t + 32 * j))

/-- Bit `16i` set iff the 16-bit lane `i` of `m` is zero (nothing else set). -/
@[inline] def laneClear (m : UInt64) : UInt64 :=
  let x := m ||| m >>> 2
  let x := x ||| x >>> 4
  let x := x ||| x >>> 8
  ~~~x &&& 0x0001000100010001

/-- The low `np` lanes (`np ≤ 4`). -/
@[inline] def laneMask (np : Nat) : UInt64 :=
  if np = 0 then 0 else if np = 1 then 1 else if np = 2 then 0x10001 else if np = 3 then 0x100010001
  else 0x1000100010001

/-- Lanes of read word `j` found zero at field offsets `t, t + 1, …` (`k`), or-ed into `F`;
stops once all of `full` are found. -/
def laneScan (K : RP) (gs : GenomeWords) (n j : Nat) (full F : UInt64) (t : Nat) : Nat → UInt64
  | 0 => F
  | k + 1 =>
    let F := F ||| laneClear (lowF (mismatchAt K gs t j) (n - 32 * j))
    if F &&& full == full then F else laneScan K gs n j full F (t + 1) k

/-! `laneScan` on machine words: see `seedAny_eq_svAnyF` above. -/

/-- `laneScan K gs n j full F t k` with `wj = K.w.getD j 0`, `c = n - 32 j`, `jU = j` and `t` in
`USize` (`laneScanWord_eq`). -/
def laneScanWord (gs : GenomeWords) (wj : UInt64) (c : Nat) (jU : USize) (full F : UInt64) (t : USize) : Nat → UInt64
  | 0 => F
  | k + 1 =>
    let F := F ||| laneClear (lowF (fold (wj ^^^ windowAtWord gs t jU)) c)
    if F &&& full == full then F else laneScanWord gs wj c jU full F (t + 1) k

theorem laneScanWord_eq (K : RP) (gs : GenomeWords) (n j : Nat) (jU : USize) (hj : jU.toNat = j) (full : UInt64) :
    ∀ k (tU : USize) t F, tU.toNat = t → t + k + 32 * j < 2 ^ 31 →
      laneScanWord gs (K.w.getD j 0) (n - 32 * j) jU full F tU k = laneScan K gs n j full F t k := by
  intro k
  induction k with
  | zero => intro tU t F _ _; rfl
  | succ k ih =>
    intro tU t F ht hb
    simp only [laneScanWord, laneScan, mismatchAt]
    rw [windowAtWord_eq gs tU jU t j ht hj (by omega)]
    split
    · rename_i hc; simp only [hc, ↓reduceIte]
    · rename_i hc; simp only [hc, ↓reduceIte, Bool.false_eq_true]
      exact ih _ _ _ (by rw [usz_add' _ _ (by rw [usz_lit 1 (by decide)]; omega), usz_lit 1 (by decide), ht])
          (by omega)

/-- The mask of `lowF · c`, computed once (`lowF_eqM`). -/
@[inline] def lowMask (c : Nat) : UInt64 := if c < 32 then (1 <<< (2 * c).toUInt64) - 1 else -1

theorem lowF_eqM (x : UInt64) (c : Nat) : lowF x c = x &&& lowMask c := by
  unfold lowF lowMask; split <;> simp

/-- `laneScanWord` with the field mask `m = lowMask c` passed in and the count `k` in `USize`
(`laneScanMask_eq`): no `Nat` per step. -/
def laneScanMask (gs : GenomeWords) (wj m : UInt64) (jU : USize) (full F : UInt64) (t k : USize) : UInt64 :=
  if h : k = 0 then F else
    let F := F ||| laneClear (fold (wj ^^^ windowAtWord gs t jU) &&& m)
    if F &&& full == full then F else laneScanMask gs wj m jU full F (t + 1) (k - 1)
termination_by k.toNat
decreasing_by
  have h0 : k.toNat ≠ 0 := fun e => h (USize.toNat_inj.mp (by rw [e]; rfl))
  rw [USize.toNat_sub_of_le _ _ (by show (1 : USize).toNat ≤ k.toNat; rw [usz_lit 1 (by decide)]; omega),
    usz_lit 1 (by decide)]
  omega

theorem laneScanMask_eq (gs : GenomeWords) (wj : UInt64) (c : Nat) (jU : USize) (full : UInt64) :
    ∀ k (kU : USize), kU.toNat = k → ∀ t F,
      laneScanMask gs wj (lowMask c) jU full F t kU = laneScanWord gs wj c jU full F t k := by
  intro k
  induction k with
  | zero =>
    intro kU hk t F
    have : kU = 0 := USize.toNat_inj.mp (by rw [hk]; rfl)
    rw [laneScanMask, dif_pos this]; rfl
  | succ k ih =>
    intro kU hk t F
    have h0 : kU ≠ 0 := fun e => by rw [e] at hk; simp at hk
    rw [laneScanMask, dif_neg h0, laneScanWord, lowF_eqM]
    simp only []
    split
    · rfl
    · exact ih _ (by rw [USize.toNat_sub_of_le _ _ (by show (1 : USize).toNat ≤ kU.toNat; rw [usz_lit 1 (by decide)]; omega),
        usz_lit 1 (by decide)]; omega) _ _

/-- `laneScanMask` with the two field words of `windowAtWord` kept while the word index `(t >>> 5) + jU` stays the same
(`laneScanCached_eq`): no `GenomeWords.getU` per step. -/
def laneScanCached (gs : GenomeWords) (wj m : UInt64) (jU : USize) (full F : UInt64) (t k u : USize) (a b : UInt64) : UInt64 :=
  if h : k = 0 then F else
    let s := t &&& 31
    let F := F ||| laneClear (fold (wj ^^^ comb a b s.toNat (2 * s).toUInt64 (64 - 2 * s).toUInt64) &&& m)
    if F &&& full == full then F else
      let u' := ((t + 1) >>> 5) + jU
      if u' == u then laneScanCached gs wj m jU full F (t + 1) (k - 1) u a b
      else laneScanCached gs wj m jU full F (t + 1) (k - 1) u' (gs.getU u') (gs.getU (u' + 1))
termination_by k.toNat
decreasing_by
  all_goals
    have h0 : k.toNat ≠ 0 := fun e => h (USize.toNat_inj.mp (by rw [e]; rfl))
    rw [USize.toNat_sub_of_le _ _ (by show (1 : USize).toNat ≤ k.toNat; rw [usz_lit 1 (by decide)]; omega),
      usz_lit 1 (by decide)]
    omega

theorem laneScanCached_eq (gs : GenomeWords) (wj m : UInt64) (jU : USize) (full : UInt64) :
    ∀ n (k : USize), k.toNat = n → ∀ (t : USize) (F : UInt64),
      laneScanCached gs wj m jU full F t k ((t >>> 5) + jU) (gs.getU ((t >>> 5) + jU)) (gs.getU ((t >>> 5) + jU + 1)) =
        laneScanMask gs wj m jU full F t k := by
  intro n
  induction n with
  | zero =>
    intro k hk t F
    have : k = 0 := USize.toNat_inj.mp (by rw [hk]; rfl)
    rw [laneScanCached, laneScanMask, dif_pos this, dif_pos this]
  | succ n ih =>
    intro k hk t F
    have h0 : k ≠ 0 := fun e => by rw [e] at hk; simp at hk
    have hk1 : (k - 1).toNat = n := by
      rw [USize.toNat_sub_of_le _ _ (by show (1 : USize).toNat ≤ k.toNat; rw [usz_lit 1 (by decide)]; omega),
        usz_lit 1 (by decide)]; omega
    rw [laneScanCached, laneScanMask, dif_neg h0, dif_neg h0]
    simp only [windowAtWord]
    have key : ∀ F' : UInt64,
        (if (F' &&& full == full) = true then F' else
          if ((t + 1) >>> 5 + jU == t >>> 5 + jU) = true then
            laneScanCached gs wj m jU full F' (t + 1) (k - 1) (t >>> 5 + jU) (gs.getU (t >>> 5 + jU)) (gs.getU (t >>> 5 + jU + 1))
          else laneScanCached gs wj m jU full F' (t + 1) (k - 1) ((t + 1) >>> 5 + jU) (gs.getU ((t + 1) >>> 5 + jU))
            (gs.getU ((t + 1) >>> 5 + jU + 1))) =
        (if (F' &&& full == full) = true then F' else laneScanMask gs wj m jU full F' (t + 1) (k - 1)) := by
      intro F'
      by_cases hc : (F' &&& full == full) = true
      · simp only [hc, if_true]
      · simp only [hc, Bool.false_eq_true, if_false]
        by_cases heq : ((t + 1) >>> 5 + jU == t >>> 5 + jU) = true
        · rw [if_pos heq]
          have e : (t + 1) >>> 5 + jU = t >>> 5 + jU := by simpa using heq
          rw [← e]
          exact ih _ hk1 _ _
        · rw [if_neg heq]
          exact ih _ hk1 _ _
    exact key _

/-- Compiled `laneScanMask`. -/
@[inline] def laneScanCachedStart (gs : GenomeWords) (wj m : UInt64) (jU : USize) (full F : UInt64) (t k : USize) : UInt64 :=
  let u := (t >>> 5) + jU
  laneScanCached gs wj m jU full F t k u (gs.getU u) (gs.getU (u + 1))

@[csimp] theorem laneScanMask_eqW : @laneScanMask = @laneScanCachedStart := by
  funext gs wj m jU full F t k
  exact (laneScanCached_eq gs wj m jU full k.toNat k rfl t F).symm

/-- `laneScan` (its slow path; not rewritten by `csimp`). -/
def laneScanSlow (K : RP) (gs : GenomeWords) (n j : Nat) (full F : UInt64) (t : Nat) : Nat → UInt64
  | 0 => F
  | k + 1 =>
    let F := F ||| laneClear (lowF (mismatchAt K gs t j) (n - 32 * j))
    if F &&& full == full then F else laneScanSlow K gs n j full F (t + 1) k

theorem laneScanSlow_eq (K : RP) (gs : GenomeWords) (n j : Nat) (full : UInt64) :
    ∀ k t F, laneScanSlow K gs n j full F t k = laneScan K gs n j full F t k := by
  intro k
  induction k with
  | zero => intro t F; rfl
  | succ k ih => intro t F; simp only [laneScanSlow, laneScan, ih]

/-- `laneScan` for the compiled code (`laneScan_eq_lanesAnyF`). -/
@[inline] def laneScanFast (K : RP) (gs : GenomeWords) (n j : Nat) (full F : UInt64) (t k : Nat) : UInt64 :=
  if t + k + 32 * j < 2147483648 then
    laneScanMask gs (K.w.getD j 0) (lowMask (n - 32 * j)) j.toUSize full F t.toUSize k.toUSize
  else laneScanSlow K gs n j full F t k

@[csimp] theorem laneScan_eq_lanesAnyF : @laneScan = @laneScanFast := by
  funext K gs n j full F t k
  unfold laneScanFast; split
  · rename_i h
    rw [laneScanMask_eq gs _ _ _ full k _ (usz_n _ (by omega))]
    exact (laneScanWord_eq K gs n j _ (usz_n _ (by omega)) full k _ t F (usz_n _ (by omega)) (by omega)).symm
  · exact (laneScanSlow_eq K gs n j full k t F).symm

/-- Number of lanes `0 … 3` flagged (bit `16i`). -/
@[inline] def laneCount (F : UInt64) : Nat :=
  (F &&& 1).toNat + (F >>> 16 &&& 1).toNat + (F >>> 32 &&& 1).toNat + (F >>> 48 &&& 1).toNat

/-- Pieces found (of `m`), read words `j, j + 1, …` (`k` of them), added to `acc`. -/
def piecesFound (K : RP) (gs : GenomeWords) (o n r m : Nat) : Nat → Nat → Nat → Nat
  | _, 0, acc => acc
  | j, k + 1, acc =>
    let full := laneMask (min 4 (m - 4 * j))
    let F := laneClear (lowF (mismatchAt K gs (o + r) j) (n - 32 * j)) &&& full
    let F := if F == full then F else laneScan K gs n j full F o (2 * r + 1) &&& full
    piecesFound K gs o n r m (j + 1) k (acc + laneCount F)

/-- `need ≤ piecesFound … j k acc`, stopping as soon as it is reached or out of reach
(word `j` and later hold at most `m − 4j` pieces): `piecesEnough_eq`. -/
def piecesEnough (K : RP) (gs : GenomeWords) (o n r m need : Nat) : Nat → Nat → Nat → Bool
  | _, 0, acc => decide (need ≤ acc)
  | j, k + 1, acc =>
    if need ≤ acc then true
    else if acc + (m - 4 * j) < need then false
    else
      let full := laneMask (min 4 (m - 4 * j))
      let F := laneClear (lowF (mismatchAt K gs (o + r) j) (n - 32 * j)) &&& full
      let F := if F == full then F else laneScan K gs n j full F o (2 * r + 1) &&& full
      piecesEnough K gs o n r m need (j + 1) k (acc + laneCount F)

/-- `piecesEnough` (its slow path; not rewritten by `csimp`). -/
def piecesEnoughSlow (K : RP) (gs : GenomeWords) (o n r m need : Nat) : Nat → Nat → Nat → Bool
  | _, 0, acc => decide (need ≤ acc)
  | j, k + 1, acc =>
    if need ≤ acc then true
    else if acc + (m - 4 * j) < need then false
    else
      let full := laneMask (min 4 (m - 4 * j))
      let F := laneClear (lowF (mismatchAt K gs (o + r) j) (n - 32 * j)) &&& full
      let F := if F == full then F else laneScan K gs n j full F o (2 * r + 1) &&& full
      piecesEnoughSlow K gs o n r m need (j + 1) k (acc + laneCount F)

theorem piecesEnoughSlow_eq (K : RP) (gs : GenomeWords) (o n r m need : Nat) :
    ∀ k j acc, piecesEnoughSlow K gs o n r m need j k acc = piecesEnough K gs o n r m need j k acc := by
  intro k
  induction k with
  | zero => intro j acc; rfl
  | succ k ih => intro j acc; simp only [piecesEnoughSlow, piecesEnough, ih]

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

theorem laneCount_eq (F : UInt64) : laneCount F = (if F.toNat.testBit 0 then 1 else 0) + (if F.toNat.testBit 16 then 1 else 0) +
    (if F.toNat.testBit 32 then 1 else 0) + (if F.toNat.testBit 48 then 1 else 0) := by
  unfold laneCount
  rw [show F &&& 1 = F >>> (0 : Nat).toUInt64 &&& 1 by simp, bit1 F 0 (by omega),
    show (16 : UInt64) = (16 : Nat).toUInt64 from rfl, bit1 F 16 (by omega),
    show (32 : UInt64) = (32 : Nat).toUInt64 from rfl, bit1 F 32 (by omega),
    show (48 : UInt64) = (48 : Nat).toUInt64 from rfl, bit1 F 48 (by omega)]

theorem tb_shr (x : UInt64) (k b : Nat) (hk : k < 64) :
    (x >>> k.toUInt64).toNat.testBit b = x.toNat.testBit (b + k) := by
  rw [UInt64.toNat_shiftRight]
  have e : k.toUInt64.toNat % 64 = k := by simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
  rw [e, Nat.testBit_shiftRight, Nat.add_comm]

theorem laneClear_bit (m : UInt64) (i : Nat) (hi : i < 4) :
    (laneClear m).toNat.testBit (16 * i) = true ↔ ∀ b, b < 8 → m.toNat.testBit (16 * i + 2 * b) = false := by
  unfold laneClear
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

theorem laneMask_bit (np i : Nat) (hnp : np ≤ 4) (hi : i < 4) :
    (laneMask np).toNat.testBit (16 * i) = decide (i < np) := by
  unfold laneMask
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

theorem loadWordsList_getD (w : ByteArray) : ∀ (k u0 : Nat) (a : Array UInt64) (i : Nat),
    (loadWordsList w u0 k a).getD i 0 =
      if i < a.size then a.getD i 0 else if i < a.size + k then gword w (u0 + (i - a.size)) else 0 := by
  intro k
  induction k with
  | zero =>
    intro u0 a i
    simp only [loadWordsList, Nat.add_zero]
    by_cases h : i < a.size
    · simp [h]
    · simp [h, Array.getD_eq_getD_getElem?]
  | succ k ih =>
    intro u0 a i
    rw [loadWordsList, ih, Array.size_push, getD_push]
    by_cases h1 : i < a.size
    · simp [h1, show i < a.size + 1 by omega]
    by_cases h2 : i = a.size
    · subst h2; simp
    · simp only [show ¬ i < a.size + 1 by omega, h1, h2, if_false]
      by_cases h3 : i < a.size + (k + 1)
      · rw [if_pos (by omega), if_pos h3, show u0 + 1 + (i - (a.size + 1)) = u0 + (i - a.size) by omega]
      · rw [if_neg (by omega), if_neg h3]

theorem loadWords_get (w : ByteArray) (u0 k i : Nat) (hi : i < k) :
    (loadWords w u0 k).get i = gword w (u0 + i) := by
  unfold GenomeWords.get
  by_cases h16 : i < 16
  · unfold loadWords loadWordAt
    obtain _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i := i <;> first | omega | simp [hi]
  · rw [if_neg (show ¬ i < 8 by omega), if_neg h16]
    unfold loadWords
    rw [loadWordsList_getD]
    simp only [List.size_toArray, List.length_nil, Nat.not_lt_zero, if_false, Nat.zero_add, Nat.sub_zero]
    rw [if_pos (by omega)]
    congr 1; omega

/-- Genome fields of the loaded words. -/
theorem fieldsAt_dig (P : PGen) (u0 k t i : Nat) (hk : t / 32 + 1 < k) (hi : i < 32) :
    dig (windowAt (loadWords P.w u0 k) t).toNat i = (P.code (32 * u0 + t + i)).toNat := by
  unfold windowAt
  simp only []
  rw [comb_dig _ _ _ _ (Nat.mod_lt _ (by omega)) hi, loadWords_get _ _ _ _ (by omega), loadWords_get _ _ _ _ hk]
  split
  · rw [code_dig _ _ _ (by omega)]; congr 2; omega
  · rw [code_dig _ _ _ (by omega)]; congr 2; omega

/-- Read fields of the packed read. -/
theorem rAt_dig (R : ByteArray) (hok : (packRP R).ok = true) (A i : Nat) (hi : i < 32) (hA : A + i < R.size) :
    dig (fieldsAt (packRP R).w A).toNat i = c2N (R.get! (A + i)) := by
  have hR := (packRP_ok R hok).2 (A + i) hA
  unfold fieldsAt
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
structure WindowSame (R : ByteArray) (P : PGen) (Gb : ByteArray) (s0 L : Nat) : Prop where
  rep : Rep P Gb
  ok : (packRP R).ok = true
  win : ∀ y, s0 ≤ y → y < s0 + L → y < P.n ∧ P.w.get! (17 * ((P.o + y) / 64)) = 1

/-- Field `t` of the words loaded from `P.o + s0` is genome place `s0 + (t − o)`. -/
theorem fieldW {R : ByteArray} {P : PGen} {Gb : ByteArray} {s0 L : Nat} (h : WindowSame R P Gb s0 L) (k t x : Nat)
    (hk : t / 32 + 1 < k) (ht : (P.o + s0) % 32 ≤ t) (i : Nat) (hi : i < 32) (hx : x < R.size)
    (hy : t + i - (P.o + s0) % 32 < L) :
    dig (windowAt (loadWords P.w ((P.o + s0) / 32) k) t).toNat i = c2N (R.get! x) ↔
      Gb.get! (s0 + (t + i - (P.o + s0) % 32)) = R.get! x := by
  rw [fieldsAt_dig P _ k t i hk hi]
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

theorem seedAny_iff (gs : GenomeWords) (sv : UInt64) : ∀ k t,
    seedAny gs sv t k = true ↔ ∃ e, e < k ∧ seedEqual (windowAt gs (t + e)) sv = true := by
  intro k
  induction k with
  | zero => intro t; simp [seedAny]
  | succ k ih =>
    intro t
    simp only [seedAny, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨e, h1, h2⟩)
      · exact ⟨0, by omega, h⟩
      · exact ⟨e + 1, by omega, by rw [show t + (e + 1) = t + 1 + e by omega]; exact h2⟩
    · rintro ⟨e, h1, h2⟩
      cases e with
      | zero => exact Or.inl h2
      | succ e => exact Or.inr ⟨e, by omega, by rw [show t + 1 + e = t + (e + 1) by omega]; exact h2⟩

/-- 25 fields by one compare. -/
theorem seedEqual_iff (x y : UInt64) : seedEqual x y = true ↔ ∀ t, t < 25 → dig x.toNat t = dig y.toNat t := by
  unfold seedEqual
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
    (h : WindowSame R P Gb (D - R.size - r) (R.size + 2 * r)) (A e : Nat) (hA : A + q ≤ R.size)
    (he : e ≤ 2 * r) :
    seedEqual (windowAt (loadWords P.w ((P.o + (D - R.size - r)) / 32) (((P.o + (D - R.size - r)) % 32 + 2 * r + R.size) / 32 + 2)) ((P.o + (D - R.size - r)) % 32 + A + e)) (fieldsAt (packRP R).w A) = true ↔
      ∀ i, i < q → Gb.get! (D - R.size - r + e + A + i) = R.get! (A + i) := by
  have hq : q = 25 := rfl
  rw [seedEqual_iff]
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

theorem unseenSeedsOk_eq (K : RP) (gs : GenomeWords) (R : ByteArray) {Gt : Type} [GRead Gt] (G : Gt)
    (o Ls r D sb : Nat)
    (h : ∀ j, j * Ls + q ≤ R.size → (seedEqual (windowAt gs (o + j * Ls + r)) (fieldsAt K.w (j * Ls)) ||
      seedAny gs (fieldsAt K.w (j * Ls)) (o + j * Ls) (2 * r + 1)) = seedNear R G Ls r D j) :
    ∀ us f, (∀ j, j ∈ us → j * Ls + q ≤ R.size) →
      unseenSeedsOk K gs o Ls r sb us f = unlook R G Ls r D sb us f := by
  intro us
  induction us with
  | nil => intro f _; rfl
  | cons j us ih =>
    intro f hus
    simp only [unseenSeedsOk, unlook]
    have hj := hus j (List.mem_cons_self ..)
    have hus' : ∀ i, i ∈ us → i * Ls + q ≤ R.size := fun i hi => hus i (List.mem_cons_of_mem _ hi)
    rw [h j hj, ih _ hus', ih _ hus']

/-- Per seed, inside the window: words = letters. -/
theorem seedV_eq {R : ByteArray} {P : PGen} {Gb : ByteArray} {r D : Nat}
    (h : WindowSame R P Gb (D - R.size - r) (R.size + 2 * r)) (hD : R.size + r ≤ D) (Ls j : Nat) (hA : j * Ls + q ≤ R.size) :
    (seedEqual (windowAt (loadWords P.w ((P.o + (D - R.size - r)) / 32) (((P.o + (D - R.size - r)) % 32 + 2 * r + R.size) / 32 + 2)) ((P.o + (D - R.size - r)) % 32 + j * Ls + r)) (fieldsAt (packRP R).w (j * Ls)) ||
      seedAny (loadWords P.w ((P.o + (D - R.size - r)) / 32) (((P.o + (D - R.size - r)) % 32 + 2 * r + R.size) / 32 + 2)) (fieldsAt (packRP R).w (j * Ls)) ((P.o + (D - R.size - r)) % 32 + j * Ls) (2 * r + 1))
      = seedNear R Gb Ls r D j := by
  have hG : D + r ≤ Gb.size := by
    have hq : q = 25 := rfl
    rw [← h.rep.1]; have := (h.win (D + r - 1) (by omega) (by omega)).1; omega
  apply Bool.eq_iff_iff.mpr
  rw [seedNear_iff R Gb Ls r D j hD hA hG, Bool.or_eq_true, seedAny_iff]
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
    (h : WindowSame R P Gb s0 (R.size + 2 * r)) (ho : o = (P.o + s0) % 32) (hu : u0 = (P.o + s0) / 32)
    (hk : (o + 2 * r + R.size) / 32 + 2 ≤ k)
    (e w i : Nat) (he : e ≤ 2 * r) (hi : i < 4) (hn : 32 * w + 8 * i + 8 ≤ R.size) :
    (laneClear (lowF (mismatchAt (packRP R) (loadWords P.w u0 k) (o + e) w)
      (R.size - 32 * w))).toNat.testBit (16 * i) = true ↔
      ∀ b, b < 8 → Gb.get! (s0 + e + (32 * w + 8 * i) + b) = R.get! (32 * w + 8 * i + b) := by
  subst ho hu
  rw [laneClear_bit _ i hi]
  apply forall_congr'; intro b
  apply imp_congr_right; intro hb
  unfold mismatchAt
  rw [show 16 * i + 2 * b = 2 * (8 * i + b) by omega, mdig0 _ _ _ _ (by omega) (by omega),
    kw_dig R h.ok w (8 * i + b) (by omega) (by omega), show 32 * w + 8 * i + b = 32 * w + (8 * i + b) by omega]
  have hf := fieldW h k ((P.o + s0) % 32 + e + 32 * w) (32 * w + (8 * i + b)) (by omega) (by omega) (8 * i + b)
    (by omega) (by omega) (by omega)
  rw [show s0 + ((P.o + s0) % 32 + e + 32 * w + (8 * i + b) - (P.o + s0) % 32) = s0 + e + (32 * w + 8 * i) + b
    by omega] at hf
  constructor
  · intro hh; exact hf.mp hh.symm
  · intro hh; exact (hf.mpr hh).symm

theorem laneScan_bit (K : RP) (gs : GenomeWords) (n w : Nat) (full : UInt64) (i : Nat) :
    ∀ k t F, (laneScan K gs n w full F t k &&& full).toNat.testBit (16 * i) = true ↔
      full.toNat.testBit (16 * i) = true ∧ (F.toNat.testBit (16 * i) = true ∨
        ∃ e, e < k ∧ (laneClear (lowF (mismatchAt K gs (t + e) w) (n - 32 * w))).toNat.testBit (16 * i) = true) := by
  intro k
  induction k with
  | zero =>
    intro t F
    simp only [laneScan, UInt64.toNat_and, Nat.testBit_and, Bool.and_eq_true]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, Or.inl h1⟩
    · rintro ⟨h2, h1 | ⟨e, he, -⟩⟩
      · exact ⟨h1, h2⟩
      · omega
  | succ k ih =>
    intro t F
    simp only [laneScan]
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

/-- The lanes word of `piecesFound`: lane `i` set iff `i < np` and the lane is clear at some offset. -/
theorem wordF_bit (K : RP) (gs : GenomeWords) (n w o r np : Nat) (hnp : np ≤ 4) (i : Nat) (hi : i < 4) :
    (let full := laneMask np
     let F := laneClear (lowF (mismatchAt K gs (o + r) w) (n - 32 * w)) &&& full
     if F == full then F else laneScan K gs n w full F o (2 * r + 1) &&& full).toNat.testBit (16 * i) = true ↔
      i < np ∧ ∃ e, e < 2 * r + 1 ∧ (laneClear (lowF (mismatchAt K gs (o + e) w) (n - 32 * w))).toNat.testBit (16 * i) = true := by
  have hf := laneMask_bit np i hnp hi
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
  · rw [laneScan_bit]
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
    laneCount F = cntP p a np := by
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
  rw [laneCount_eq, e0, e1, e2, e3, cnt4 p a np hnp]

/-- Piece `4w + i` near `D` iff its lane is clear at some offset. -/
theorem pieceW {R : ByteArray} {P : PGen} {Gb : ByteArray} {r k o u0 D : Nat}
    (h : WindowSame R P Gb (D - R.size - r) (R.size + 2 * r)) (ho : o = (P.o + (D - R.size - r)) % 32)
    (hu : u0 = (P.o + (D - R.size - r)) / 32) (hk : (o + 2 * r + R.size) / 32 + 2 ≤ k)
    (hD : R.size + r ≤ D) (hG : D + r ≤ Gb.size) (w i : Nat) (hi : i < 4) (hn : 32 * w + 8 * i + 8 ≤ R.size) :
    pieceNear R Gb 8 8 r D (4 * w + i) = true ↔ ∃ e, e < 2 * r + 1 ∧
      (laneClear (lowF (mismatchAt (packRP R) (loadWords P.w u0 k) (o + e) w)
        (R.size - 32 * w))).toNat.testBit (16 * i) = true := by
  rw [pieceNear_iff R Gb 8 8 r D (4 * w + i) hD (by omega) hG,
    show (4 * w + i) * 8 = 32 * w + 8 * i by omega]
  constructor
  · rintro ⟨e, he, hh⟩
    exact ⟨e, by omega, (laneW h ho hu hk e w i he hi hn).mpr hh⟩
  · rintro ⟨e, he, hh⟩
    exact ⟨e, by omega, (laneW h ho hu hk e w i (by omega) hi hn).mp hh⟩

theorem piecesFound_cnt {R : ByteArray} {P : PGen} {Gb : ByteArray} {r k o u0 D : Nat}
    (h : WindowSame R P Gb (D - R.size - r) (R.size + 2 * r)) (ho : o = (P.o + (D - R.size - r)) % 32)
    (hu : u0 = (P.o + (D - R.size - r)) / 32) (hk : (o + 2 * r + R.size) / 32 + 2 ≤ k)
    (hD : R.size + r ≤ D) (hG : D + r ≤ Gb.size) (m : Nat) (hm : 8 * m ≤ R.size) :
    ∀ c j acc, piecesFound (packRP R) (loadWords P.w u0 k) o R.size r m j c acc =
      acc + cntP (fun j => pieceNear R Gb 8 8 r D j) (4 * j) (min (4 * c) (m - 4 * j)) := by
  intro c
  induction c with
  | zero => intro j acc; simp [piecesFound, cntP]
  | succ c ih =>
    intro j acc
    rw [piecesFound, ih]
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
    (h : WindowSame R P Gb (D - R.size - r) (R.size + 2 * r)) (ho : o = (P.o + (D - R.size - r)) % 32)
    (hu : u0 = (P.o + (D - R.size - r)) / 32) (hk : (o + 2 * r + R.size) / 32 + 2 ≤ k)
    (hD : R.size + r ≤ D) (hG : D + r ≤ Gb.size) (h8 : R.size / (R.size / pl) = 8) (sb : Nat) :
    decide (R.size / pl ≤ sb + piecesFound (packRP R) (loadWords P.w u0 k) o R.size r
      (R.size / pl) 0 ((R.size + 31) / 32) 0) = fineOk R Gb pl (R.size / (R.size / pl)) r D sb 0 0 (R.size / pl) := by
  have hpl : pl = 8 := rfl
  rw [h8, fineOk_cnt _ _ _ _ _ _ _ _ _ _ (Nat.zero_le _), hpl,
    piecesFound_cnt h ho hu hk hD hG (R.size / 8) (by omega)]
  rw [show min (4 * ((R.size + 31) / 32)) (R.size / 8 - 4 * 0) = R.size / 8 by omega, Nat.mul_zero]
  have hc := cntP_compl (fun j => pieceNear R Gb 8 8 r D j) (R.size / 8) 0
  exact decide_eq_decide.mpr (by omega)

/-! ### The early-stopping piece count -/

theorem laneCount_full (X : UInt64) (np : Nat) (hnp : np ≤ 4) : laneCount (X &&& laneMask np) ≤ np := by
  have h0 := laneMask_bit np 0 hnp (by omega)
  have h1 := laneMask_bit np 1 hnp (by omega)
  have h2 := laneMask_bit np 2 hnp (by omega)
  have h3 := laneMask_bit np 3 hnp (by omega)
  simp only [Nat.mul_zero, Nat.mul_one, show 16 * 2 = 32 from rfl, show 16 * 3 = 48 from rfl] at h0 h1 h2 h3
  rw [laneCount_eq]
  simp only [UInt64.toNat_and, Nat.testBit_and, h0, h1, h2, h3]
  cases X.toNat.testBit 0 <;> cases X.toNat.testBit 16 <;> cases X.toNat.testBit 32 <;>
    cases X.toNat.testBit 48 <;> simp <;> repeat' (first | omega | split)

theorem piecesFound_add (K : RP) (gs : GenomeWords) (o n r m : Nat) :
    ∀ k j a acc, piecesFound K gs o n r m j k (a + acc) = a + piecesFound K gs o n r m j k acc := by
  intro k
  induction k with
  | zero => intro j a acc; rfl
  | succ k ih => intro j a acc; simp only [piecesFound]; rw [Nat.add_assoc, ih]

theorem piecesFound_ge (K : RP) (gs : GenomeWords) (o n r m : Nat) :
    ∀ k j acc, acc ≤ piecesFound K gs o n r m j k acc := by
  intro k
  induction k with
  | zero => intro j acc; exact Nat.le_refl _
  | succ k ih => intro j acc; simp only [piecesFound]; exact Nat.le_trans (Nat.le_add_right _ _) (ih _ _)

theorem piecesFound_le (K : RP) (gs : GenomeWords) (o n r m : Nat) :
    ∀ k j acc, piecesFound K gs o n r m j k acc ≤ acc + (m - 4 * j) := by
  intro k
  induction k with
  | zero => intro j acc; simp [piecesFound]
  | succ k ih =>
    intro j acc
    simp only [piecesFound]
    refine Nat.le_trans (ih _ _) ?_
    have hl : ∀ F : UInt64, laneCount ((if F == laneMask (min 4 (m - 4 * j)) then F
        else laneScan K gs n j (laneMask (min 4 (m - 4 * j))) F o (2 * r + 1) &&& laneMask (min 4 (m - 4 * j))))
        ≤ min 4 (m - 4 * j) := by
      intro F
      split
      · rename_i he
        rw [beq_iff_eq.mp he]
        have := laneCount_full (laneMask (min 4 (m - 4 * j))) (min 4 (m - 4 * j)) (by omega)
        rwa [UInt64.and_self] at this
      · exact laneCount_full _ _ (by omega)
    have := hl (laneClear (lowF (mismatchAt K gs (o + r) j) (n - 32 * j)) &&& laneMask (min 4 (m - 4 * j)))
    omega

theorem piecesEnough_eq (K : RP) (gs : GenomeWords) (o n r m need : Nat) :
    ∀ k j acc, piecesEnough K gs o n r m need j k acc = decide (need ≤ piecesFound K gs o n r m j k acc) := by
  intro k
  induction k with
  | zero => intro j acc; rfl
  | succ k ih =>
    intro j acc
    have hge := piecesFound_ge K gs o n r m (k + 1) j acc
    have hle := piecesFound_le K gs o n r m (k + 1) j acc
    simp only [piecesEnough]
    split
    · exact (decide_eq_true (by omega)).symm
    split
    · exact (decide_eq_false (by omega)).symm
    rw [ih]; rfl

theorem piecesEnough_sb (K : RP) (gs : GenomeWords) (o n r m need k sb : Nat) :
    piecesEnough K gs o n r m need 0 k sb = decide (need ≤ sb + piecesFound K gs o n r m 0 k 0) := by
  rw [piecesEnough_eq, ← piecesFound_add, Nat.add_zero]

/-! ### The piece scan on a rolling window (`piecesEnough_eqC`) -/

/-- Bit `16i + 15` set iff the 16-bit lane `i` of `x` is zero (nothing else set). -/
@[inline] def laneZeros (x : UInt64) : UInt64 :=
  ~~~(((x &&& 0x7FFF7FFF7FFF7FFF) + 0x7FFF7FFF7FFF7FFF) ||| x) &&& 0x8000800080008000

theorem lane_key (X M k : Nat) (hM1 : M / 2 ^ k % 2 ^ 16 = 0x7FFF) (hM2 : 2 * (M % 2 ^ k) < 2 ^ k) :
    ((X &&& M) + M).testBit (k + 15) = decide (X / 2 ^ k % 2 ^ 15 ≠ 0) := by
  have hp : 0 < 2 ^ k := Nat.two_pow_pos k
  have hc : (X &&& M) % 2 ^ k + M % 2 ^ k < 2 ^ k := by
    rw [Nat.and_mod_two_pow]
    have := Nat.and_le_right (n := X % 2 ^ k) (m := M % 2 ^ k)
    omega
  have hd : ((X &&& M) + M) / 2 ^ k = (X &&& M) / 2 ^ k + M / 2 ^ k := by
    rw [Nat.add_div hp]; simp only [show ¬ (2 ^ k ≤ (X &&& M) % 2 ^ k + M % 2 ^ k) by omega, ↓reduceIte, Nat.add_zero]
  have hl : (X &&& M) / 2 ^ k % 2 ^ 16 = X / 2 ^ k % 2 ^ 15 := by
    rw [← Nat.shiftRight_eq_div_pow, Nat.shiftRight_and_distrib, Nat.and_mod_two_pow,
      Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, hM1]
    rw [show (0x7FFF : Nat) = 2 ^ 15 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_mod_of_dvd _ (by decide)
  have hs : ((X &&& M) + M) / 2 ^ k % 2 ^ 16 = X / 2 ^ k % 2 ^ 15 + 0x7FFF := by
    rw [hd, Nat.add_mod, hl, hM1]
    have : X / 2 ^ k % 2 ^ 15 < 2 ^ 15 := Nat.mod_lt _ (by decide)
    rw [Nat.mod_eq_of_lt (by omega)]
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  have e : ((X &&& M) + M) / 2 ^ k / 2 ^ 15 % 2 = (((X &&& M) + M) / 2 ^ k % 2 ^ 16) / 2 ^ 15 := by
    omega
  rw [e, hs]
  have : X / 2 ^ k % 2 ^ 15 < 2 ^ 15 := Nat.mod_lt _ (by decide)
  by_cases h0 : X / 2 ^ k % 2 ^ 15 = 0
  · simp only [h0]; decide
  · have : (X / 2 ^ k % 2 ^ 15 + 0x7FFF) / 2 ^ 15 = 1 := by omega
    simp [this, h0]

theorem mod_two_pow_zero (n k : Nat) : n % 2 ^ k = 0 ↔ ∀ b, b < k → n.testBit b = false := by
  constructor
  · intro h b hb
    have := congrArg (fun x => x.testBit b) h
    simp only [Nat.testBit_mod_two_pow, Nat.zero_testBit] at this
    simpa [hb] using this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro b
    rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
    by_cases hb : b < k
    · simp [hb, h b hb]
    · simp [hb]

theorem laneZeros_bit (x : UInt64) (i : Nat) (hi : i < 4) :
    (laneZeros x).toNat.testBit (16 * i + 15) = true ↔ ∀ b, b < 16 → x.toNat.testBit (16 * i + b) = false := by
  have hM : (0x7FFF7FFF7FFF7FFF : UInt64).toNat = 0x7FFF7FFF7FFF7FFF := rfl
  have hadd : ((x &&& 0x7FFF7FFF7FFF7FFF) + 0x7FFF7FFF7FFF7FFF : UInt64).toNat =
      (x.toNat &&& 0x7FFF7FFF7FFF7FFF) + 0x7FFF7FFF7FFF7FFF := by
    rw [UInt64.toNat_add, UInt64.toNat_and, hM]
    have := Nat.and_le_right (n := x.toNat) (m := 0x7FFF7FFF7FFF7FFF)
    rw [Nat.mod_eq_of_lt (by omega)]
  unfold laneZeros
  rw [UInt64.toNat_and, Nat.testBit_and, tb_not, UInt64.toNat_or, Nat.testBit_or, hadd]
  have hH : (0x8000800080008000 : UInt64).toNat.testBit (16 * i + 15) = true := by
    obtain _ | _ | _ | _ | i := i <;> first | omega | decide
  have hk := lane_key x.toNat 0x7FFF7FFF7FFF7FFF (16 * i)
    (by obtain _ | _ | _ | _ | i := i <;> first | omega | decide)
    (by obtain _ | _ | _ | _ | i := i <;> first | omega | decide)
  rw [hH, hk, decide_eq_true (show 16 * i + 15 < 64 by omega)]
  have h15 := mod_two_pow_zero (x.toNat / 2 ^ (16 * i)) 15
  simp only [Nat.testBit_div_two_pow] at h15
  simp only [Bool.true_and, Bool.and_true, Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not,
    Decidable.not_not]
  rw [h15]
  constructor
  · rintro ⟨h1, h2⟩ b hb
    by_cases hb' : b < 15
    · have := h1 b hb'; rwa [Nat.add_comm] at this
    · rwa [show b = 15 by omega]
  · intro h
    exact ⟨fun b hb => by rw [Nat.add_comm]; exact h b (by omega), h 15 (by omega)⟩

/-- Lane `i` of `x` is zero iff its 8 fields are. -/
theorem lane0_dig (X i : Nat) :
    (∀ b, b < 16 → X.testBit (16 * i + b) = false) ↔ ∀ f, f < 8 → dig X (8 * i + f) = 0 := by
  constructor
  · intro h f hf
    rw [dig_eq, show 2 * (8 * i + f) + 1 = 16 * i + (2 * f + 1) by omega, show 2 * (8 * i + f) = 16 * i + 2 * f by omega,
      h _ (by omega), h _ (by omega)]; rfl
  · intro h b hb
    have := dig_zero_bits _ _ (h (b / 2) (by omega))
    rcases Nat.mod_two_eq_zero_or_one b with e | e
    · rw [show 16 * i + b = 2 * (8 * i + b / 2) by omega]; exact this.2
    · rw [show 16 * i + b = 2 * (8 * i + b / 2) + 1 by omega]; exact this.1

theorem laneZeros_lane (a g : UInt64) (i : Nat) (hi : i < 4) :
    (laneZeros (a ^^^ g)).toNat.testBit (16 * i + 15) = true ↔ ∀ f, f < 8 → dig a.toNat (8 * i + f) = dig g.toNat (8 * i + f) := by
  rw [laneZeros_bit _ _ hi, lane0_dig]
  exact forall_congr' fun f => imp_congr_right fun _ => xor_dig a g _

/-- The shift scan on a rolling window: `a` = the 32 fields at the current offset, `b` = the next `c`
fields (low first), `u` = the word `b` came from. Flags in bit `16i + 15`. -/
def laneScanRoll (gs : GenomeWords) (wj full F : UInt64) (k : USize) (a b : UInt64) (c u : USize) : UInt64 :=
  if h : k = 0 then F else
    let F := F ||| laneZeros (wj ^^^ a)
    if F &&& full == full then F else
      let a' := (a >>> 2) ||| (b <<< 62)
      if c == 1 then laneScanRoll gs wj full F (k - 1) a' (gs.getU (u + 1)) 32 (u + 1)
      else laneScanRoll gs wj full F (k - 1) a' (b >>> 2) (c - 1) u
termination_by k.toNat
decreasing_by
  all_goals
    have h0 : k.toNat ≠ 0 := fun e => h (USize.toNat_inj.mp (by rw [e]; rfl))
    rw [USize.toNat_sub_of_le _ _ (by show (1 : USize).toNat ≤ k.toNat; rw [usz_lit 1 (by decide)]; omega),
      usz_lit 1 (by decide)]
    omega

theorem laneScanRoll_bit (gs : GenomeWords) (wj full : UInt64) (i : Nat) :
    ∀ n (k : USize), k.toNat = n → ∀ T a b c u F, a = windowAt gs T → RInv gs T b c u → T + n + 64 < 2 ^ 31 →
      (((laneScanRoll gs wj full F k a b c u) &&& full).toNat.testBit i = true ↔
        full.toNat.testBit i = true ∧ (F.toNat.testBit i = true ∨
          ∃ e, e < n ∧ (laneZeros (wj ^^^ windowAt gs (T + e))).toNat.testBit i = true)) := by
  intro n
  induction n with
  | zero =>
    intro k hk T a b c u F _ _ _
    have : k = 0 := USize.toNat_inj.mp (by rw [hk]; rfl)
    rw [laneScanRoll, dif_pos this]
    simp only [UInt64.toNat_and, Nat.testBit_and, Bool.and_eq_true]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, Or.inl h1⟩
    · rintro ⟨h2, h1 | ⟨e, he, -⟩⟩
      · exact ⟨h1, h2⟩
      · omega
  | succ n ih =>
    intro k hk T a b c u F ha hI hB
    have h0 : k ≠ 0 := fun e => by rw [e] at hk; simp at hk
    have hk1 : (k - 1).toNat = n := by
      rw [USize.toNat_sub_of_le _ _ (by show (1 : USize).toNat ≤ k.toNat; rw [usz_lit 1 (by decide)]; omega),
        usz_lit 1 (by decide)]; omega
    have hu : u.toNat + 2 < 2 ^ 32 := by obtain ⟨_, _, he, _⟩ := hI; omega
    have ha' : (a >>> 2) ||| (b <<< 62) = windowAt gs (T + 1) :=
      roll_eq gs T a b ha (by obtain ⟨h1, _, _, hf⟩ := hI; simpa using hf 0 (by omega))
    have hstep := rinv_step gs T b c u hI hu
    rw [laneScanRoll, dif_neg h0]
    simp only []
    have key : ∀ F', ((if (c == 1) = true then laneScanRoll gs wj full F' (k - 1) ((a >>> 2) ||| (b <<< 62)) (gs.getU (u + 1)) 32 (u + 1)
        else laneScanRoll gs wj full F' (k - 1) ((a >>> 2) ||| (b <<< 62)) (b >>> 2) (c - 1) u) &&& full).toNat.testBit i = true ↔
        full.toNat.testBit i = true ∧ (F'.toNat.testBit i = true ∨
          ∃ e, e < n ∧ (laneZeros (wj ^^^ windowAt gs (T + 1 + e))).toNat.testBit i = true) := by
      intro F'
      split
      · rename_i hc; rw [if_pos hc] at hstep; exact ih _ hk1 _ _ _ _ _ F' ha' hstep (by omega)
      · rename_i hc; rw [if_neg hc] at hstep; exact ih _ hk1 _ _ _ _ _ F' ha' hstep (by omega)
    split
    · rename_i hfull
      rw [beq_iff_eq] at hfull
      have hb := congrArg (fun x => x.toNat.testBit i) hfull
      simp only [UInt64.toNat_and, Nat.testBit_and, UInt64.toNat_or, Nat.testBit_or] at hb
      rw [hfull]
      constructor
      · intro h1
        refine ⟨h1, ?_⟩
        simp only [h1, Bool.and_true, Bool.or_eq_true] at hb
        rcases hb with h2 | h2
        · exact Or.inl h2
        · exact Or.inr ⟨0, by omega, by rw [Nat.add_zero, ← ha]; exact h2⟩
      · exact fun h => h.1
    · rw [key]
      simp only [UInt64.toNat_or, Nat.testBit_or, Bool.or_eq_true]
      constructor
      · rintro ⟨h1, (h2 | h2) | ⟨e, he, h3⟩⟩
        · exact ⟨h1, Or.inl h2⟩
        · exact ⟨h1, Or.inr ⟨0, by omega, by rw [Nat.add_zero, ← ha]; exact h2⟩⟩
        · exact ⟨h1, Or.inr ⟨e + 1, by omega, by rw [show T + (e + 1) = T + 1 + e by omega]; exact h3⟩⟩
      · rintro ⟨h1, h2 | ⟨e, he, h3⟩⟩
        · exact ⟨h1, Or.inl (Or.inl h2)⟩
        · cases e with
          | zero => exact ⟨h1, Or.inl (Or.inr (by rw [ha]; simpa using h3))⟩
          | succ e =>
            exact ⟨h1, Or.inr ⟨e, by omega, by rw [show T + 1 + e = T + (e + 1) by omega]; exact h3⟩⟩

/-- `laneMask` on a machine word (`laneMaskWord_eq`). -/
@[inline] def laneMaskWord (np : USize) : UInt64 :=
  if np = 0 then 0 else if np = 1 then 1 else if np = 2 then 0x10001 else if np = 3 then 0x100010001
  else 0x1000100010001

theorem laneMaskWord_eq (np : USize) : laneMaskWord np = laneMask np.toNat := by
  unfold laneMaskWord laneMask
  simp only [usz_eq_iff np 0 (by decide), usz_eq_iff np 1 (by decide), usz_eq_iff np 2 (by decide),
    usz_eq_iff np 3 (by decide)]

/-- `laneCount` on machine words (`laneCountWord_eq`). -/
@[inline] def laneCountWord (F : UInt64) : UInt64 :=
  (F &&& (1 : UInt64)) + ((F >>> (16 : UInt64)) &&& (1 : UInt64)) + ((F >>> (32 : UInt64)) &&& (1 : UInt64)) +
    ((F >>> (48 : UInt64)) &&& (1 : UInt64))

theorem laneCountWord_eq (F : UInt64) : (laneCountWord F).toNat = laneCount F := by
  unfold laneCountWord laneCount
  have b : ∀ x : UInt64, (x &&& 1).toNat ≤ 1 := fun x => by
    rw [UInt64.toNat_and]; exact Nat.and_le_right
  have h1 := b F; have h2 := b (F >>> 16); have h3 := b (F >>> 32); have h4 := b (F >>> 48)
  rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add]
  omega

/-- Read word `j`'s pieces found (bit `16i`) at the field offsets `o, …, o + 2r` (`wordPieces_bit`): the
diagonal (`tU = o + r`) first, then the rolling scan. -/
@[inline] def wordPieces (K : RP) (gs : GenomeWords) (oU tU rU j np : USize) : UInt64 :=
  let wj := K.w.getD j.toNat 0
  let full := laneMaskWord np <<< 15
  let F := laneZeros (wj ^^^ windowAtWord gs tU j) &&& full
  let F := if F == full then F else
    let s := oU &&& 31
    laneScanRoll gs wj full F rU (windowAtWord gs oU j) (gs.getU ((oU >>> 5) + j + 1) >>> (2 * s).toUInt64) (32 - s)
      ((oU >>> 5) + j + 1) &&& full
  F >>> 15

theorem shr15_bit (x : UInt64) (i : Nat) : (x >>> 15).toNat.testBit (16 * i) = x.toNat.testBit (16 * i + 15) := by
  rw [UInt64.toNat_shiftRight, show (15 : UInt64).toNat % 64 = 15 from rfl, Nat.testBit_shiftRight, Nat.add_comm]

theorem full15_bit (np : Nat) (hnp : np ≤ 4) (i : Nat) (hi : i < 4) :
    (laneMask np <<< 15).toNat.testBit (16 * i + 15) = decide (i < np) := by
  rw [UInt64.toNat_shiftLeft, show (15 : UInt64).toNat % 64 = 15 from rfl, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftLeft, show 16 * i + 15 - 15 = 16 * i by omega, laneMask_bit np i hnp hi]
  simp [show 16 * i + 15 < 64 by omega]

theorem wordPieces_bit (K : RP) (gs : GenomeWords) (o r j np : Nat) (hnp : np ≤ 4) (hb : o + 32 * j + 2 * r + 1 + 64 < 2 ^ 31)
    (i : Nat) (hi : i < 4) :
    (wordPieces K gs o.toUSize (o + r).toUSize (2 * r + 1).toUSize j.toUSize np.toUSize).toNat.testBit (16 * i) = true ↔
      i < np ∧ ∃ e, e < 2 * r + 1 ∧ (laneZeros (K.w.getD j 0 ^^^ windowAt gs (o + e + 32 * j))).toNat.testBit (16 * i + 15) = true := by
  have hj : j.toUSize.toNat = j := usz_n _ (by omega)
  have ho : o.toUSize.toNat = o := usz_n _ (by omega)
  have hnpU : np.toUSize.toNat = np := usz_n _ (by omega)
  have hrU : (2 * r + 1).toUSize.toNat = 2 * r + 1 := usz_n _ (by omega)
  have hf := full15_bit np hnp i hi
  have hdiag : windowAtWord gs (o + r).toUSize j.toUSize = windowAt gs (o + r + 32 * j) :=
    windowAtWord_eq gs _ _ (o + r) j (usz_n _ (by omega)) hj (by omega)
  have ha : windowAtWord gs o.toUSize j.toUSize = windowAt gs (o + 32 * j) := windowAtWord_eq gs _ _ o j ho hj (by omega)
  unfold wordPieces
  simp only [hj, laneMaskWord_eq _, hnpU]
  rw [shr15_bit]
  split
  · rename_i heq
    rw [beq_iff_eq] at heq
    have hb := congrArg (fun x => x.toNat.testBit (16 * i + 15)) heq
    simp only [UInt64.toNat_and, Nat.testBit_and] at hb
    rw [heq, hf, decide_eq_true_iff]
    constructor
    · intro h1
      rw [hf, decide_eq_true h1, Bool.and_true, hdiag] at hb
      exact ⟨h1, r, by omega, by rw [show o + r + 32 * j = o + r + 32 * j from rfl]; exact hb⟩
    · exact fun h => h.1
  · have hs : (o.toUSize &&& 31).toNat = o % 32 := by
      rw [USize.toNat_and, usz_lit 31 (by decide), ho, show (31 : Nat) = 2 ^ 5 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod]
    have hu : (o.toUSize >>> 5 + j.toUSize + 1).toNat = o / 32 + j + 1 := by
      rw [usz_add' _ _ (by rw [usz_add' _ _ (by rw [usz_shr5, ho, hj]; omega), usz_shr5, ho, hj, usz_lit 1 (by decide)]; omega),
        usz_add' _ _ (by rw [usz_shr5, ho, hj]; omega), usz_shr5, ho, hj, usz_lit 1 (by decide)]
    have hc : (32 - (o.toUSize &&& 31)).toNat = 32 - o % 32 := by
      rw [USize.toNat_sub_of_le _ _ (by show (o.toUSize &&& 31).toNat ≤ (32 : USize).toNat; rw [hs, usz_lit 32 (by decide)]; omega),
        hs, usz_lit 32 (by decide)]
    have h2s : ((2 * (o.toUSize &&& 31)).toUInt64).toNat = 2 * (o % 32) := by
      rw [USize.toNat_toUInt64, usz_mul' _ _ (by rw [hs, usz_lit 2 (by decide)]; omega), usz_lit 2 (by decide), hs]
    have hI : RInv gs (o + 32 * j) (gs.getU (o.toUSize >>> 5 + j.toUSize + 1) >>> (2 * (o.toUSize &&& 31)).toUInt64)
        (32 - (o.toUSize &&& 31)) (o.toUSize >>> 5 + j.toUSize + 1) := by
      refine ⟨by rw [hc]; omega, by rw [hc]; omega, by rw [hc, hu]; omega, ?_⟩
      intro f hf'
      rw [hc] at hf'
      rw [shr_dig _ _ (o % 32) f h2s (by omega), GenomeWords.getU_eq, hu]
      unfold windowField
      rw [show (o + 32 * j + 32 + f) / 32 = o / 32 + j + 1 by omega,
        show (o + 32 * j + 32 + f) % 32 = f + o % 32 by omega]
    rw [laneScanRoll_bit gs _ _ _ (2 * r + 1) _ hrU (o + 32 * j) _ _ _ _ _ ha hI (by omega)]
    simp only [UInt64.toNat_and, Nat.testBit_and, hf, Bool.and_eq_true, decide_eq_true_iff]
    constructor
    · rintro ⟨h1, ⟨h2, -⟩ | ⟨e, he, h3⟩⟩
      · exact ⟨h1, r, by omega, by rw [← hdiag]; exact h2⟩
      · exact ⟨h1, e, he, by rw [show o + e + 32 * j = o + 32 * j + e by omega]; exact h3⟩
    · rintro ⟨h1, e, he, h3⟩
      exact ⟨h1, Or.inr ⟨e, he, by rw [show o + 32 * j + e = o + e + 32 * j by omega]; exact h3⟩⟩

theorem lane_equiv (K : RP) (gs : GenomeWords) (n j t i : Nat) (hi : i < 4) (hin : 8 * i + 8 ≤ n - 32 * j) :
    (laneClear (lowF (mismatchAt K gs t j) (n - 32 * j))).toNat.testBit (16 * i) = true ↔
      (laneZeros (K.w.getD j 0 ^^^ windowAt gs (t + 32 * j))).toNat.testBit (16 * i + 15) = true := by
  rw [laneClear_bit _ _ hi, laneZeros_lane _ _ _ hi]
  unfold mismatchAt
  apply forall_congr'; intro b; apply imp_congr_right; intro hb
  rw [show 16 * i + 2 * b = 2 * (8 * i + b) by omega]
  exact mdig0 _ _ _ _ (by omega) (by omega)

/-- `piecesEnough` on machine words, the pieces by `wordPieces` (`piecesEnoughWord_eq`). -/
def piecesEnoughWord (K : RP) (gs : GenomeWords) (oU tU rU m need : USize) (j k acc : USize) : Bool :=
  if h : k = 0 then decide (need ≤ acc)
  else if need ≤ acc then true
  else
    let rest := if 4 * j ≤ m then m - 4 * j else 0
    if acc + rest < need then false
    else piecesEnoughWord K gs oU tU rU m need (j + 1) (k - 1)
      (acc + (laneCountWord (wordPieces K gs oU tU rU j (if rest < 4 then rest else 4))).toUSize)
termination_by k.toNat
decreasing_by
  have h0 : k.toNat ≠ 0 := fun e => h (USize.toNat_inj.mp (by rw [e]; rfl))
  rw [USize.toNat_sub_of_le _ _ (by show (1 : USize).toNat ≤ k.toNat; rw [usz_lit 1 (by decide)]; omega),
    usz_lit 1 (by decide)]
  omega

theorem usz_le_iff (a b : USize) : a ≤ b ↔ a.toNat ≤ b.toNat := Iff.rfl
theorem usz_lt_iff' (a b : USize) : a < b ↔ a.toNat < b.toNat := Iff.rfl

/-- The pieces of word `j` counted the same way. -/
theorem laneCount_word (K : RP) (gs : GenomeWords) (o n r m j : Nat) (hm : 8 * m ≤ n) (hj4 : 4 * j < m)
    (hb : o + 32 * j + 2 * r + 1 + 64 < 2 ^ 31) :
    (laneCountWord (wordPieces K gs o.toUSize (o + r).toUSize (2 * r + 1).toUSize j.toUSize (min 4 (m - 4 * j)).toUSize)).toNat =
      laneCount (let full := laneMask (min 4 (m - 4 * j))
          let F := laneClear (lowF (mismatchAt K gs (o + r) j) (n - 32 * j)) &&& full
          if F == full then F else laneScan K gs n j full F o (2 * r + 1) &&& full) := by
  rw [laneCountWord_eq]
  have hbit : ∀ i, i < 4 →
      (wordPieces K gs o.toUSize (o + r).toUSize (2 * r + 1).toUSize j.toUSize (min 4 (m - 4 * j)).toUSize).toNat.testBit (16 * i) =
      (let full := laneMask (min 4 (m - 4 * j))
       let F := laneClear (lowF (mismatchAt K gs (o + r) j) (n - 32 * j)) &&& full
       if F == full then F else laneScan K gs n j full F o (2 * r + 1) &&& full).toNat.testBit (16 * i) := by
    intro i hi
    apply Bool.eq_iff_iff.mpr
    rw [wordPieces_bit K gs o r j _ (by omega) hb i hi, wordF_bit K gs n j o r _ (by omega) i hi]
    constructor
    · rintro ⟨h1, e, he, h2⟩
      exact ⟨h1, e, he, (lane_equiv K gs n j (o + e) i hi (by omega)).mpr h2⟩
    · rintro ⟨h1, e, he, h2⟩
      exact ⟨h1, e, he, (lane_equiv K gs n j (o + e) i hi (by omega)).mp h2⟩
  rw [laneCount_eq, laneCount_eq]
  have b0 := hbit 0 (by omega); have b1 := hbit 1 (by omega); have b2 := hbit 2 (by omega); have b3 := hbit 3 (by omega)
  simp only [Nat.mul_zero, Nat.mul_one] at b0 b1 b2 b3
  rw [show (32 : Nat) = 16 * 2 from rfl, show (48 : Nat) = 16 * 3 from rfl, b0, b1, hbit 2 (by omega), hbit 3 (by omega)]

theorem piecesEnoughWord_eq (K : RP) (gs : GenomeWords) (o n r m need : Nat) (hm : 8 * m ≤ n) (hM : m < 2 ^ 30) (hN : need < 2 ^ 30) :
    ∀ k j acc, o + 32 * (j + k) + 2 * r + 1 + 64 < 2 ^ 31 → acc + 4 * k < 2 ^ 30 →
      piecesEnoughWord K gs o.toUSize (o + r).toUSize (2 * r + 1).toUSize m.toUSize need.toUSize j.toUSize k.toUSize acc.toUSize =
        piecesEnough K gs o n r m need j k acc := by
  intro k
  induction k with
  | zero =>
    intro j acc _ ha
    rw [piecesEnoughWord, dif_pos (by rfl), piecesEnough]
    simp only [usz_le_iff, usz_n _ (show need < 2 ^ 32 by omega), usz_n _ (show acc < 2 ^ 32 by omega)]
  | succ k ih =>
    intro j acc hb ha
    have hk0 : (k + 1).toUSize ≠ 0 := fun e => by
      have := congrArg USize.toNat e; rw [usz_n _ (by omega)] at this; simp at this
    have hjU : j.toUSize.toNat = j := usz_n _ (by omega)
    have hmU : m.toUSize.toNat = m := usz_n _ (by omega)
    have hnU : need.toUSize.toNat = need := usz_n _ (by omega)
    have haU : acc.toUSize.toNat = acc := usz_n _ (by omega)
    have h4j : (4 * j.toUSize).toNat = 4 * j := by rw [usz_mul' _ _ (by rw [usz_lit 4 (by decide), hjU]; omega), usz_lit 4 (by decide), hjU]
    have hrest : (if 4 * j.toUSize ≤ m.toUSize then m.toUSize - 4 * j.toUSize else 0) = (m - 4 * j).toUSize := by
      apply USize.toNat_inj.mp
      rw [usz_n _ (by omega)]
      split
      · rename_i h; rw [usz_le_iff, h4j, hmU] at h
        rw [USize.toNat_sub_of_le _ _ (by rw [usz_le_iff, h4j, hmU]; exact h), h4j, hmU]
      · rename_i h; rw [usz_le_iff, h4j, hmU] at h; rw [show (0 : USize).toNat = 0 from rfl]; omega
    have hnp : (if (m - 4 * j).toUSize < 4 then (m - 4 * j).toUSize else 4) = (min 4 (m - 4 * j)).toUSize := by
      apply USize.toNat_inj.mp
      rw [usz_n _ (by omega)]
      split
      · rename_i h; rw [usz_lt_iff', usz_n _ (by omega), usz_lit 4 (by decide)] at h; rw [usz_n _ (by omega)]; omega
      · rename_i h; rw [usz_lt_iff', usz_n _ (by omega), usz_lit 4 (by decide)] at h; rw [usz_lit 4 (by decide)]; omega
    rw [piecesEnoughWord, dif_neg hk0, piecesEnough]
    simp only [hrest, hnp]
    have hle : (need.toUSize ≤ acc.toUSize) ↔ need ≤ acc := by rw [usz_le_iff, hnU, haU]
    have hlt : (acc.toUSize + (m - 4 * j).toUSize < need.toUSize) ↔ acc + (m - 4 * j) < need := by
      rw [usz_lt_iff', usz_add' _ _ (by rw [haU, usz_n _ (by omega)]; omega), haU, usz_n _ (by omega), hnU]
    by_cases c1 : need ≤ acc
    · rw [if_pos (hle.mpr c1), if_pos c1]
    · rw [if_neg (fun h => c1 (hle.mp h)), if_neg c1]
      by_cases c2 : acc + (m - 4 * j) < need
      · rw [if_pos (hlt.mpr c2), if_pos c2]
      · rw [if_neg (fun h => c2 (hlt.mp h)), if_neg c2]
        have hj4 : 4 * j < m := by omega
        have hL := laneCount_word K gs o n r m j hm hj4 (by omega)
        have hlc4 : laneCount (let full := laneMask (min 4 (m - 4 * j))
            let F := laneClear (lowF (mismatchAt K gs (o + r) j) (n - 32 * j)) &&& full
            if F == full then F else laneScan K gs n j full F o (2 * r + 1) &&& full) ≤ 4 := by
          rw [laneCount_eq]; split <;> split <;> split <;> split <;> omega
        have e1 : j.toUSize + 1 = (j + 1).toUSize := by
          apply USize.toNat_inj.mp; rw [usz_add' _ _ (by rw [hjU, usz_lit 1 (by decide)]; omega), hjU, usz_lit 1 (by decide), usz_n _ (by omega)]
        have e2 : (k + 1).toUSize - 1 = k.toUSize := by
          apply USize.toNat_inj.mp
          rw [USize.toNat_sub_of_le _ _ (by show (1 : USize).toNat ≤ ((k + 1).toUSize).toNat; rw [usz_lit 1 (by decide), usz_n _ (by omega)]; omega),
            usz_lit 1 (by decide), usz_n _ (by omega), usz_n _ (by omega)]; omega
        have e3 : acc.toUSize + (laneCountWord (wordPieces K gs o.toUSize (o + r).toUSize (2 * r + 1).toUSize j.toUSize (min 4 (m - 4 * j)).toUSize)).toUSize =
            (acc + laneCount (let full := laneMask (min 4 (m - 4 * j))
              let F := laneClear (lowF (mismatchAt K gs (o + r) j) (n - 32 * j)) &&& full
              if F == full then F else laneScan K gs n j full F o (2 * r + 1) &&& full)).toUSize := by
          apply USize.toNat_inj.mp
          have e : ∀ x a : Nat, x ≤ 4 → a < 2 ^ 30 → (a + x % 2 ^ System.Platform.numBits) % 2 ^ System.Platform.numBits = a + x := by
            intro x a hx ha'
            have := usz_pow
            rw [Nat.mod_eq_of_lt (show x < 2 ^ System.Platform.numBits by omega), Nat.mod_eq_of_lt (by omega)]
          rw [USize.toNat_add, UInt64.toNat_toUSize, haU, hL, e _ _ hlc4 (by omega), usz_n _ (by omega)]
        rw [e1, e2, e3]
        exact ih _ _ (by omega) (by omega)

/-- `piecesEnough` for the compiled code (`piecesEnough_eqC`): the machine-word loop `piecesEnoughWord` within its bounds. -/
@[inline] def piecesEnoughFast (K : RP) (gs : GenomeWords) (o n r m need j k acc : Nat) : Bool :=
  if o + 32 * (j + k) + 2 * r + 1 + 64 < 2147483648 ∧ 8 * m ≤ n ∧ m < 1073741824 ∧ need < 1073741824 ∧
      acc + 4 * k < 1073741824 then
    piecesEnoughWord K gs o.toUSize (o + r).toUSize (2 * r + 1).toUSize m.toUSize need.toUSize j.toUSize k.toUSize acc.toUSize
  else piecesEnoughSlow K gs o n r m need j k acc

@[csimp] theorem piecesEnough_eqC : @piecesEnough = @piecesEnoughFast := by
  funext K gs o n r m need j k acc
  unfold piecesEnoughFast
  split
  · rename_i h
    exact (piecesEnoughWord_eq K gs o n r m need h.2.1 h.2.2.1 h.2.2.2.1 k j acc h.1 h.2.2.2.2).symm
  · exact (piecesEnoughSlow_eq K gs o n r m need k j acc).symm

/-! ### The word path -/

/-- The word path applies: packed read, the window `[D − n − r, D + r)` inside the
chromosome and in all-ACGT blocks, pieces of 8 letters 8 apart. -/
@[inline] def wordPathOk (K : RP) (n r D : Nat) (P : PGen) : Bool :=
  K.ok && decide (n + r ≤ D) && n / (n / pl) == 8 && winOk P (D - n - r) (n + 2 * r)

/-- The packed genome for the word path: `PackedOf.pk G` when the seeds `us` lie inside the
read (`seedsInside`), else `none`.  A stage computes it once (`wordFilterPacked`), so neither the
seed check nor the instance call (which touches the shared genome's count) is per
diagonal. -/
@[inline] def packedFor {Gt : Type} [GRead Gt] [PackedOf Gt] (G : Gt) (Ls n : Nat) (us : List Nat) : Option PGen :=
  if seedsInside Ls n us then PackedOf.pk G else none

/-- `wordFilter` with the packed genome `pk` given (`packedFor`). -/
@[inline] def wordFilterPacked {Gt : Type} [GRead Gt] (pk : Option PGen) (K : RP) (R : ByteArray) (G : Gt)
    (acc : List (Array Nat)) (us : List Nat) (Ls lim : Nat) (b : Best) (D : Nat) : Bool :=
  let Q := min lim b.pen
  let r := 2 * gapBound sc0 (-(Q : Int))
  let n := R.size
  let fJ := acc.length - suppA acc D r
  let sb := sbound Q
  if fJ ≤ sb then
    match pk with
    | some P =>
      if wordPathOk K n r D P then
        let a := P.o + (D - n - r)
        let o := a % 32
        let gs := loadWords P.w (a / 32) ((o + 2 * r + n) / 32 + 2)
        unseenSeedsOk K gs o Ls r sb us fJ &&
          piecesEnough K gs o n r (n / pl) (n / pl) 0 ((n + 31) / 32) sb
      else kfilt R G acc us Ls lim b D
    | none => kfilt R G acc us Ls lim b D
  else false

/-- `kfilt` with the word path where it applies. -/
@[inline] def wordFilter {Gt : Type} [GRead Gt] [PackedOf Gt] (K : RP) (R : ByteArray) (G : Gt) (acc : List (Array Nat))
    (us : List Nat) (Ls lim : Nat) (b : Best) (D : Nat) : Bool :=
  wordFilterPacked (packedFor G Ls R.size us) K R G acc us Ls lim b D

/-- `stageKS` with `wordFilter`. -/
@[specialize] def stageWordFilter {Gt : Type} [GRead Gt] [PackedOf Gt] (body : Nat → Best → Best) (K : RP) (R : ByteArray)
    (G : Gt) (acc : List (Array Nat)) (us : List Nat) (Ls lim : Nat) (ds : List Nat) (b : Best) : Best :=
  let pk := packedFor G Ls R.size us
  ds.foldl (fun b D => if wordFilterPacked pk K R G acc us Ls lim b D then body D b else b) b

theorem wordFilterPacked_eq {Gt : Type} [GRead Gt] (pk : Option PGen) (R : ByteArray) (G : Gt)
    (acc : List (Array Nat)) (us : List Nat) (Ls lim : Nat) (b : Best) (D : Nat)
    (hpk : ∀ P, pk = some P → SameG G P ∧ seedsInside Ls R.size us = true) :
    wordFilterPacked pk (packRP R) R G acc us Ls lim b D = kfilt R G acc us Ls lim b D := by
  unfold wordFilterPacked
  simp only []
  split
  · rename_i hf
    rcases pk with _ | P
    · rfl
    · have hP : (some P : Option PGen) = some P := rfl
      dsimp only
      split
      · rename_i hw
        simp only [wordPathOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hw
        obtain ⟨⟨⟨hok, hD⟩, h8⟩, hwin⟩ := hw
        have hS := (hpk P hP).1
        have hall := seedsInside_mem _ _ _ (hpk P hP).2
        have hR := Mz.rep_unpack P
        have hGb : SameG G (Mz.unpack P) :=
          ⟨hS.1.trans hR.1, fun i => (hS.2 i).trans (hR.2 i)⟩
        have hfl := winOk_flags P _ _ hwin
        have hW : WindowSame R P (Mz.unpack P) (D - R.size - 2 * gapBound sc0 (-(min lim b.pen : Nat) : Int))
            (R.size + 2 * (2 * gapBound sc0 (-(min lim b.pen : Nat) : Int))) :=
          ⟨hR, hok, fun y h1 h2 => ⟨by omega, hfl.2 y h1 h2⟩⟩
        have hG : D + 2 * gapBound sc0 (-(min lim b.pen : Nat) : Int) ≤ (Mz.unpack P).size := by
          rw [← hW.rep.1]; omega
        unfold kfilt
        simp only []
        rw [piecesEnough_sb, decide_eq_true hf, Bool.true_and, fineOk_same hGb, ← fineW_eq hW rfl rfl (Nat.le_refl _) hD hG h8]
        congr 1
        refine unseenSeedsOk_eq _ _ R G _ Ls _ D _ ?_ us _ hall
        intro j hA
        rw [seedNear_same hGb]
        exact seedV_eq hW hD Ls j hA
      · rfl
  · rename_i hf
    unfold kfilt
    simp only []
    rw [decide_eq_false hf, Bool.false_and, Bool.false_and]

theorem packedFor_ok {Gt : Type} [GRead Gt] [PackedOf Gt] (G : Gt) (Ls n : Nat) (us : List Nat) :
    ∀ P, packedFor G Ls n us = some P → SameG G P ∧ seedsInside Ls n us = true := by
  intro P h
  unfold packedFor at h
  split at h
  · exact ⟨PackedOf.pk_same G P h, ‹_›⟩
  · cases h

theorem wordFilter_eq {Gt : Type} [GRead Gt] [PackedOf Gt] (R : ByteArray) (G : Gt) (acc : List (Array Nat))
    (us : List Nat) (Ls lim : Nat) (b : Best) (D : Nat) :
    wordFilter (packRP R) R G acc us Ls lim b D = kfilt R G acc us Ls lim b D :=
  wordFilterPacked_eq _ R G acc us Ls lim b D (packedFor_ok G Ls R.size us)

theorem stageWordFilter_eq {Gt : Type} [GRead Gt] [PackedOf Gt] (body : Nat → Best → Best) (R : ByteArray) (G : Gt)
    (acc : List (Array Nat)) (us : List Nat) (Ls lim : Nat) (ds : List Nat) (b : Best) :
    stageWordFilter body (packRP R) R G acc us Ls lim ds b = stageKS body R G acc us Ls lim ds b := by
  have e : ∀ b D, wordFilterPacked (packedFor G Ls R.size us) (packRP R) R G acc us Ls lim b D = kfilt R G acc us Ls lim b D :=
    fun b D => wordFilter_eq R G acc us Ls lim b D
  simp only [stageWordFilter, stageKS, e]

end MapSpec.Fast
