import MapperFastAlgo

/-!
The hashed 25-mer index: what `checkIdx` certifies, and what `lookupSeed`
returns through a certified index.

* `hash_inj`: on ACGT words, (bucket, key) of the hash determines the word
  (`mix` is multiplication by an odd constant mod `2^50`, inverted by `MIXINV`).
* `lookupSeed_spec`: through an index with `checkIdx ix G = true`, the anchors
  of seed `j` are increasing and are exactly `(p + BIAS − j·q)·16 + 2^j` for the
  places `p` where the seed occurs in `G` (hashed path for ACGT seeds, the
  `odd` lists for the others).
-/

namespace MapSpec.Fast

/-! ## Codes -/

def c2N (b : UInt8) : Nat := if b = 67 then 1 else if b = 71 then 2 else if b = 84 then 3 else 0

set_option maxRecDepth 100000 in
theorem c2_tab : ∀ n, n < 256 → ((codeTab.get! n).toUInt64 &&& 3).toNat = c2N n.toUInt8 := by decide +kernel

set_option maxRecDepth 100000 in
theorem acgt_tab : ∀ n, n < 256 → codeTab.get! n < 4 → n = 65 ∨ n = 67 ∨ n = 71 ∨ n = 84 := by decide +kernel

theorem c2_toNat (b : UInt8) : (c2 b).toNat = c2N b := by
  have := c2_tab b.toNat (UInt8.toNat_lt b)
  rwa [show b.toNat.toUInt8 = b by simp] at this

theorem c2N_lt (b : UInt8) : c2N b < 4 := by
  unfold c2N
  by_cases h1 : b = 67
  · simp [h1]
  · by_cases h2 : b = 71
    · simp [h2]
    · by_cases h3 : b = 84 <;> simp [h1, h2, h3]

theorem acgt_cases (b : UInt8) (h : acgt b = true) : b = 65 ∨ b = 67 ∨ b = 71 ∨ b = 84 := by
  unfold acgt at h
  have := acgt_tab b.toNat (UInt8.toNat_lt b) (by simpa using h)
  rcases this with e | e | e | e
  · left; exact UInt8.toNat_inj.mp e
  · right; left; exact UInt8.toNat_inj.mp e
  · right; right; left; exact UInt8.toNat_inj.mp e
  · right; right; right; exact UInt8.toNat_inj.mp e

theorem c2N_inj (b b' : UInt8) (h : acgt b = true) (h' : acgt b' = true) (e : c2N b = c2N b') : b = b' := by
  rcases acgt_cases b h with r | r | r | r <;> rcases acgt_cases b' h' with r' | r' | r' | r' <;>
    subst r r' <;> simp_all [c2N]

/-- Base-4 value of `B[i, i+m)`, first letter most significant. -/
def wN (B : ByteArray) (i : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => c2N (B.get! i) * 4 ^ m + wN B (i + 1) m

theorem wN_lt (B : ByteArray) (i m : Nat) : wN B i m < 4 ^ m := by
  induction m generalizing i with
  | zero => simp [wN]
  | succ m ih =>
    simp only [wN, Nat.pow_succ]
    have := ih (i + 1)
    have := c2N_lt (B.get! i)
    have : c2N (B.get! i) * 4 ^ m ≤ 3 * 4 ^ m := Nat.mul_le_mul_right _ (by omega)
    omega

theorem wcode_toNat (B : ByteArray) (stop : Nat) :
    ∀ d i x, stop - i = d → (wcode B i stop x).toNat = (x.toNat * 4 ^ (stop - i) + wN B i (stop - i)) % 2 ^ 64 := by
  intro d
  induction d with
  | zero =>
    intro i x hd
    unfold wcode; rw [if_neg (by omega), hd]; simp [wN]
  | succ d ih =>
    intro i x hd
    unfold wcode
    rw [if_pos (by omega), ih (i + 1) _ (by omega)]
    rw [show stop - i = (stop - (i + 1)) + 1 by omega, wN, UInt64.toNat_add, UInt64.toNat_mul, c2_toNat]
    simp only [show (4 : UInt64).toNat = 4 from rfl]
    rw [Nat.mod_add_mod, Nat.add_mod, Nat.mod_mul_mod, ← Nat.add_mod]
    congr 1
    rw [Nat.pow_succ]
    generalize 4 ^ (stop - (i + 1)) = P
    rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 4 P, Nat.add_assoc]

theorem hashWord_toNat (B : ByteArray) (p : Nat) : (wcode B p (p + q) 0).toNat = wN B p q := by
  rw [wcode_toNat B (p + q) _ p 0 rfl, show p + q - p = q by omega]
  simp only [UInt64.toNat_zero, Nat.zero_mul, Nat.zero_add]
  apply Nat.mod_eq_of_lt
  have := wN_lt B p q
  simp only [q] at this ⊢
  omega

theorem wN_congr (B B' : ByteArray) (i i' m : Nat) (h : ∀ k, k < m → B.get! (i + k) = B'.get! (i' + k)) :
    wN B i m = wN B' i' m := by
  induction m generalizing i i' with
  | zero => rfl
  | succ m ih =>
    simp only [wN]
    rw [show B.get! i = B'.get! i' by simpa using h 0 (by omega),
      ih (i + 1) (i' + 1) (fun k hk => by
        rw [show i + 1 + k = i + (k + 1) by omega, show i' + 1 + k = i' + (k + 1) by omega]
        exact h (k + 1) (by omega))]

theorem wN_inj (B B' : ByteArray) (i i' m : Nat)
    (ha : ∀ k, k < m → acgt (B.get! (i + k)) = true) (ha' : ∀ k, k < m → acgt (B'.get! (i' + k)) = true)
    (e : wN B i m = wN B' i' m) : ∀ k, k < m → B.get! (i + k) = B'.get! (i' + k) := by
  induction m generalizing i i' with
  | zero => intro k hk; omega
  | succ m ih =>
    simp only [wN] at e
    have l1 := wN_lt B (i + 1) m
    have l2 := wN_lt B' (i' + 1) m
    have hc : c2N (B.get! i) = c2N (B'.get! i') := by
      have d1 := Nat.add_mul_div_right (wN B (i + 1) m) (c2N (B.get! i)) (show 0 < 4 ^ m from Nat.pow_pos (by omega))
      have d2 := Nat.add_mul_div_right (wN B' (i' + 1) m) (c2N (B'.get! i')) (show 0 < 4 ^ m from Nat.pow_pos (by omega))
      rw [Nat.div_eq_of_lt l1] at d1
      rw [Nat.div_eq_of_lt l2] at d2
      have e' : wN B (i + 1) m + c2N (B.get! i) * 4 ^ m = wN B' (i' + 1) m + c2N (B'.get! i') * 4 ^ m := by
        omega
      rw [e'] at d1
      omega
    have hr : wN B (i + 1) m = wN B' (i' + 1) m := by rw [hc] at e; omega
    intro k hk
    by_cases k0 : k = 0
    · subst k0
      exact c2N_inj _ _ (by simpa using ha 0 (by omega)) (by simpa using ha' 0 (by omega)) hc
    · have := ih (i + 1) (i' + 1)
        (fun k hk => by rw [show i + 1 + k = i + (k + 1) by omega]; exact ha (k + 1) (by omega))
        (fun k hk => by rw [show i' + 1 + k = i' + (k + 1) by omega]; exact ha' (k + 1) (by omega))
        hr (k - 1) (by omega)
      rwa [show i + 1 + (k - 1) = i + k by omega, show i' + 1 + (k - 1) = i' + k by omega] at this

/-! ## The hash -/

def MIXINV : Nat := 707954914849597

theorem mix_toNat (y : UInt64) : (mix y).toNat = y.toNat * MIXC.toNat % 2 ^ 50 := by
  unfold mix
  rw [UInt64.toNat_and, UInt64.toNat_mul, show (0x3FFFFFFFFFFFF : UInt64).toNat = 2 ^ 50 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd _ (by decide)]

theorem mix_lt (y : UInt64) : (mix y).toNat < 2 ^ 50 := by rw [mix_toNat]; exact Nat.mod_lt _ (by decide)

theorem mix_inj (a b : Nat) (ha : a < 2 ^ 50) (hb : b < 2 ^ 50)
    (h : a * MIXC.toNat % 2 ^ 50 = b * MIXC.toNat % 2 ^ 50) : a = b := by
  have key : ∀ x, x < 2 ^ 50 → x * MIXC.toNat % 2 ^ 50 * MIXINV % 2 ^ 50 = x := by
    intro x hx
    rw [Nat.mod_mul_mod, Nat.mul_assoc, Nat.mul_mod, show MIXC.toNat * MIXINV % 2 ^ 50 = 1 by decide,
      Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt hx]
  rw [← key a ha, ← key b hb, h]

theorem bucket_key_inj (y y' : UInt64) (hb : bucketOf y = bucketOf y') (hk : keyOf y = keyOf y') :
    y.toNat = y'.toNat := by
  unfold bucketOf at hb
  unfold keyOf at hk
  rw [UInt64.toNat_shiftRight, UInt64.toNat_shiftRight, show (26 : UInt64).toNat % 64 = 26 from rfl,
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow] at hb
  have hk' := hk
  rw [UInt64.toNat_and, UInt64.toNat_and,
    show (0x3FFFFFF : UInt64).toNat = 2 ^ 26 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.and_two_pow_sub_one_eq_mod] at hk'
  omega

theorem allACGT_spec (B : ByteArray) (stop : Nat) :
    ∀ d i, stop - i = d → (allACGT B i stop = true ↔ ∀ k, i ≤ k → k < stop → acgt (B.get! k) = true) := by
  intro d
  induction d with
  | zero => intro i hd; unfold allACGT; rw [if_neg (by omega)]; simp; intro k h1 h2; omega
  | succ d ih =>
    intro i hd
    unfold allACGT
    rw [if_pos (by omega), Bool.and_eq_true, ih (i + 1) (by omega)]
    constructor
    · rintro ⟨h1, h2⟩ k hk1 hk2
      by_cases hk : k = i
      · subst hk; exact h1
      · exact h2 k (by omega) hk2
    · intro h; exact ⟨h i (Nat.le_refl _) (by omega), fun k h1 h2 => h k (by omega) h2⟩

theorem allACGT_word (B : ByteArray) (p : Nat) :
    allACGT B p (p + q) = true ↔ ∀ k, k < q → acgt (B.get! (p + k)) = true := by
  rw [allACGT_spec B (p + q) _ p rfl]
  constructor
  · intro h k hk; exact h (p + k) (by omega) (by omega)
  · intro h k h1 h2; have := h (k - p) (by omega); rwa [Nat.add_sub_cancel' h1] at this

/-- **Hash injectivity.**  Two ACGT 25-letter words with the same bucket and key are equal. -/
theorem hash_inj (B B' : ByteArray) (p p' : Nat) (ha : allACGT B p (p + q) = true)
    (ha' : allACGT B' p' (p' + q) = true) (hb : bucketOf (hashAt B p) = bucketOf (hashAt B' p'))
    (hk : keyOf (hashAt B p) = keyOf (hashAt B' p')) : ∀ k, k < q → B.get! (p + k) = B'.get! (p' + k) := by
  have e := bucket_key_inj _ _ hb hk
  unfold hashAt at e
  rw [mix_toNat, mix_toNat, hashWord_toNat, hashWord_toNat] at e
  have l1 := wN_lt B p q
  have l2 := wN_lt B' p' q
  simp only [q] at l1 l2
  have := mix_inj _ _ (by simpa [q] using l1) (by simpa [q] using l2) e
  exact wN_inj B B' p p' q ((allACGT_word B p).1 ha) ((allACGT_word B' p').1 ha') this

theorem hash_congr (B B' : ByteArray) (p p' : Nat) (h : ∀ k, k < q → B.get! (p + k) = B'.get! (p' + k)) :
    hashAt B p = hashAt B' p' := by
  unfold hashAt
  congr 1
  apply UInt64.toNat_inj.mp
  rw [hashWord_toNat, hashWord_toNat, wN_congr B B' p p' q h]

theorem bucketOf_lt (y : UInt64) (h : y.toNat < 2 ^ 50) : bucketOf y < NB := by
  unfold bucketOf NB
  rw [UInt64.toNat_shiftRight, show (26 : UInt64).toNat % 64 = 26 from rfl, Nat.shiftRight_eq_div_pow]
  show _ < 2 ^ 24
  omega

/-! ## What the checker certifies -/

/-- The seed `R[s, s+q)` occurs in `G` at `p`. -/
def MatchAt (G : ByteArray) (p : Nat) (R : ByteArray) (s : Nat) : Prop :=
  p + q ≤ G.size ∧ ∀ k, k < q → G.get! (p + k) = R.get! (s + k)

theorem checkOdd_spec (ix : HIdx) (G : ByteArray) :
    ∀ k p cur, checkOdd ix G cur k p = true → ∀ p', p ≤ p' → p' < p + k → acgt (G.get! p') = false →
      ∃ t, t < ix.odd[(G.get! p').toNat]!.size ∧ ix.odd[(G.get! p').toNat]![t]! = p' := by
  intro k
  induction k with
  | zero => intro p cur _ p' h1 h2; omega
  | succ k ih =>
    intro p cur h p' h1 h2 hodd
    unfold checkOdd at h
    by_cases hp : p' = p
    · subst hp
      rw [if_neg (by simp [hodd])] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
      exact ⟨_, h.1.1, h.1.2⟩
    · split at h
      · exact ih _ _ h p' (by omega) (by omega) hodd
      · simp only [Bool.and_eq_true] at h
        exact ih _ _ h.2 p' (by omega) (by omega) hodd

theorem increasing_spec (a : Array Nat) :
    ∀ k i, increasing a k i = true → ∀ i', i ≤ i' → i' < i + k → a[i']! < a[i' + 1]! := by
  intro k
  induction k with
  | zero => intro i _ i' h1 h2; omega
  | succ k ih =>
    intro i h i' h1 h2
    simp only [increasing, Bool.and_eq_true, decide_eq_true_eq] at h
    by_cases hi : i' = i
    · subst hi; exact h.1
    · exact ih (i + 1) h.2 i' (by omega) (by omega)

theorem chain_lt (f : Nat → Nat) (lo hi : Nat) (h : ∀ t, lo ≤ t → t + 1 < hi → f t < f (t + 1)) :
    ∀ d t t', t' = t + d + 1 → lo ≤ t → t' < hi → f t < f t' := by
  intro d
  induction d with
  | zero => intro t t' e h1 h2; subst e; exact h t h1 h2
  | succ d ih =>
    intro t t' e h1 h2
    have := ih t (t + d + 1) rfl h1 (by omega)
    have := h (t + d + 1) (by omega) (by omega)
    subst e; rw [show t + (d + 1) + 1 = t + d + 1 + 1 by omega]; omega

/-! ### The rolling scan -/

theorem wN_snoc (B : ByteArray) (i m : Nat) : wN B i (m + 1) = wN B i m * 4 + c2N (B.get! (i + m)) := by
  induction m generalizing i with
  | zero => simp [wN]
  | succ m ih =>
    rw [wN, ih (i + 1), wN, Nat.pow_succ, show i + 1 + m = i + (m + 1) by omega]
    simp only [Nat.add_mul, Nat.mul_assoc]; omega

theorem getElem!_set! (a : Array Nat) (i j : Nat) (v : Nat) :
    (a.set! i v)[j]! = if i = j ∧ i < a.size then v else a[j]! := by
  rw [Array.set!_eq_setIfInBounds]
  simp only [getElem!_def, Array.getElem?_setIfInBounds]
  by_cases h1 : i = j
  · subst h1; by_cases h2 : i < a.size <;> simp [h2]
  · simp [h1]

/-- Entry `t` of bucket `b` was checked against a word before `e`. -/
def Good (ix : HIdx) (G : ByteArray) (b t e : Nat) : Prop :=
  (u32 ix.ent (2 * t)) + q ≤ e ∧ allACGT G (u32 ix.ent (2 * t)) ((u32 ix.ent (2 * t)) + q) = true ∧
    bucketOf (hashAt G (u32 ix.ent (2 * t))) = b ∧ keyOf (hashAt G (u32 ix.ent (2 * t))) = (u32 ix.ent (2 * t + 1)) ∧
    ((u32 ix.offs (b)) < t → (u32 ix.ent (2 * (t - 1))) < (u32 ix.ent (2 * t)))

/-- Every ACGT word ending before `e` is in its bucket. -/
def Found (ix : HIdx) (G : ByteArray) (e : Nat) : Prop :=
  ∀ p, p + q ≤ e → allACGT G p (p + q) = true →
    ∃ t, (u32 ix.offs (bucketOf (hashAt G p))) ≤ t ∧ t < (u32 ix.offs (bucketOf (hashAt G p) + 1)) ∧
      (u32 ix.ent (2 * t)) = p ∧ (u32 ix.ent (2 * t + 1)) = keyOf (hashAt G p)

def Filled (ix : HIdx) (G : ByteArray) (e : Nat) (fill : Array Nat) : Prop :=
  ∀ b, b < NB → (u32 ix.offs (b)) ≤ fill[b]! ∧ ∀ t, (u32 ix.offs (b)) ≤ t → t < fill[b]! → Good ix G b t e

def Run (G : ByteArray) (e : Nat) (x : UInt64) (r : Nat) : Prop :=
  r ≤ q ∧ r ≤ e ∧ (∀ k, e - r ≤ k → k < e → acgt (G.get! k) = true) ∧
    (r < q → r = e ∨ acgt (G.get! (e - r - 1)) = false) ∧ x.toNat = wN G (e - r) r

theorem good_mono (ix : HIdx) (G : ByteArray) (b t e e' : Nat) (h : Good ix G b t e) (he : e ≤ e') :
    Good ix G b t e' := ⟨by have := h.1; omega, h.2⟩

theorem roll_toNat (x : UInt64) (v : UInt8) (hx : x.toNat < 2 ^ 50) :
    ((x * 4 + c2 v) &&& 0x3FFFFFFFFFFFF).toNat = (x.toNat * 4 + c2N v) % 2 ^ 50 := by
  rw [UInt64.toNat_and, show (0x3FFFFFFFFFFFF : UInt64).toNat = 2 ^ 50 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, UInt64.toNat_add, UInt64.toNat_mul, c2_toNat,
    show (4 : UInt64).toNat = 4 from rfl]
  have := c2N_lt v
  rw [Nat.mod_eq_of_lt (show x.toNat * 4 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show x.toNat * 4 + c2N v < 2 ^ 64 by omega)]

theorem scanIdx_spec (ix : HIdx) (G : ByteArray) :
    ∀ k e x r fill fill', e + k ≤ G.size → Run G e x r → Filled ix G e fill → Found ix G e →
      scanIdx ix G k e x r fill = some fill' → Filled ix G (e + k) fill' ∧ Found ix G (e + k) := by
  have hq25 : q = 25 := rfl
  intro k
  induction k with
  | zero =>
    intro e x r fill fill' _ _ hf hfo h
    simp only [scanIdx, Option.some.injEq] at h
    subst h; exact ⟨hf, hfo⟩
  | succ k ih =>
    intro e x r fill fill' hk hrun hf hfo h
    obtain ⟨hr1, hr2, hr3, hr4, hr5⟩ := hrun
    unfold scanIdx at h
    simp only [] at h
    rw [show e + (k + 1) = (e + 1) + k by omega]
    by_cases hv : acgt (G.get! e) = true
    · rw [if_pos hv] at h
      have hx50 : x.toNat < 2 ^ 50 := by
        rw [hr5]; have := wN_lt G (e - r) r
        have : 4 ^ r ≤ 4 ^ 25 := Nat.pow_le_pow_right (by omega) (by simp [q] at hr1; omega)
        simp at *; omega
      have hroll := roll_toNat x (G.get! e) hx50
      -- the new run
      have hrun' : Run G (e + 1) ((x * 4 + c2 (G.get! e)) &&& 0x3FFFFFFFFFFFF) (min (r + 1) q) := by
        refine ⟨by omega, by omega, fun k h1 h2 => ?_, fun h1 => ?_, ?_⟩
        · by_cases hke : k = e
          · subst hke; exact hv
          · exact hr3 k (by omega) (by omega)
        · rcases hr4 (by omega) with h2 | h2
          · left; omega
          · right; rw [show e + 1 - min (r + 1) q - 1 = e - r - 1 by omega]; exact h2
        · rw [hroll]
          by_cases hr25 : r < q
          · rw [show min (r + 1) q = r + 1 by omega, show e + 1 - (r + 1) = e - r by omega, wN_snoc,
              show e - r + r = e by omega, ← hr5]
            apply Nat.mod_eq_of_lt
            have := wN_snoc G (e - r) r
            have := wN_lt G (e - r) (r + 1)
            rw [show e - r + r = e by omega, ← hr5] at *
            have : 4 ^ (r + 1) ≤ 4 ^ 25 := Nat.pow_le_pow_right (by omega) (by simp [q] at hr25; omega)
            simp at *; omega
          · have hr' : r = q := by omega
            subst hr'
            rw [show min (q + 1) q = q by simp [q], hr5]
            have e1 := wN_snoc G (e - q) q
            have e2 : wN G (e - q) (q + 1) = c2N (G.get! (e - q)) * 4 ^ q + wN G (e - q + 1) q := rfl
            have l := wN_lt G (e - q + 1) q
            rw [show e - q + q = e by omega] at e1
            rw [show e + 1 - q = e - q + 1 by omega]
            simp only [q] at *
            omega
      by_cases hq : min (r + 1) q = q
      · rw [if_pos hq] at h
        -- the word ending at `e`
        have hp : e + 1 - q + q = e + 1 := by simp [q] at hq ⊢; omega
        have hall : allACGT G (e + 1 - q) (e + 1 - q + q) = true := by
          rw [allACGT_word]; intro k hk
          exact hrun'.2.2.1 _ (by rw [hq]; omega) (by omega)
        have hy : mix ((x * 4 + c2 (G.get! e)) &&& 0x3FFFFFFFFFFFF) = hashAt G (e + 1 - q) := by
          unfold hashAt; congr 1
          apply UInt64.toNat_inj.mp
          rw [hashWord_toNat, hrun'.2.2.2.2, hq, show e + 1 - q = e + 1 - q from rfl]
        rw [hy] at h
        generalize hb : bucketOf (hashAt G (e + 1 - q)) = b at h
        split at h
        · next hc =>
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
          obtain ⟨⟨⟨hc1, hc2⟩, hc3⟩, hc4⟩ := hc
          have hbN : b < NB := by rw [← hb]; exact bucketOf_lt _ (mix_lt _)
          refine ih (e + 1) _ _ _ fill' (by omega) hrun' ?_ ?_ h
          · intro b' hb'
            rw [getElem!_set!]
            by_cases hbb : b = b' ∧ b < fill.size
            · obtain ⟨rfl, hbs⟩ := hbb
              rw [if_pos ⟨rfl, hbs⟩]
              refine ⟨by omega, fun t h1 h2 => ?_⟩
              by_cases ht : t = fill[b]!
              · subst ht
                refine ⟨by rw [hc3]; omega, by rw [hc3]; exact hall, by rw [hc3]; exact hb,
                  by rw [hc3, hc4], fun hlt => ?_⟩
                have := ((hf b hbN).2 (fill[b]! - 1) (by omega) (by omega)).1
                rw [hc3]; omega
              · exact good_mono ix G b t e (e + 1) ((hf b hbN).2 t h1 (by omega)) (by omega)
            · rw [if_neg hbb]
              exact ⟨(hf b' hb').1, fun t h1 h2 => good_mono ix G b' t e (e + 1) ((hf b' hb').2 t h1 h2) (by omega)⟩
          · intro p hp' hpa
            by_cases hpe : p + q = e + 1
            · rw [show p = e + 1 - q by omega, hb]
              exact ⟨_, hc1, hc2, by rw [hc3], by rw [hc4]⟩
            · exact hfo p (by omega) hpa
        · cases h
      · rw [if_neg hq] at h
        refine ih (e + 1) _ _ _ fill' (by omega) hrun' ?_ ?_ h
        · intro b hb; exact ⟨(hf b hb).1, fun t h1 h2 => good_mono ix G b t e (e + 1) ((hf b hb).2 t h1 h2) (by omega)⟩
        · intro p hp' hpa
          by_cases hpe : p + q = e + 1
          · exfalso; apply hq
            have : ∀ k, p ≤ k → k ≤ e → acgt (G.get! k) = true := by
              intro k h1 h2
              have := (allACGT_word G p).1 hpa (k - p) (by omega)
              rwa [Nat.add_sub_cancel' h1] at this
            by_cases hr' : r + 1 < q
            · rcases hr4 (by omega) with h2 | h2
              · omega
              · have := this (e - r - 1) (by omega) (by omega); rw [this] at h2; cases h2
            · omega
          · exact hfo p (by omega) hpa
    · rw [if_neg hv] at h
      refine ih (e + 1) _ _ _ fill' (by omega) ⟨by simp [q], by omega, fun k h1 h2 => by omega,
        fun _ => Or.inr (by simpa using hv), by simp [wN]⟩ ?_ ?_ h
      · intro b hb; exact ⟨(hf b hb).1, fun t h1 h2 => good_mono ix G b t e (e + 1) ((hf b hb).2 t h1 h2) (by omega)⟩
      · intro p hp' hpa
        by_cases hpe : p + q = e + 1
        · exfalso; apply hv
          have := (allACGT_word G p).1 hpa (e - p) (by omega)
          rwa [show p + (e - p) = e by omega] at this
        · exact hfo p (by omega) hpa

theorem fillOk_spec (ix : HIdx) (fill : Array Nat) :
    ∀ k b, fillOk ix fill k b = true → ∀ b', b ≤ b' → b' < b + k → fill[b']! = (u32 ix.offs (b' + 1)) := by
  intro k
  induction k with
  | zero => intro b _ b' h1 h2; omega
  | succ k ih =>
    intro b h b' h1 h2
    simp only [fillOk, Bool.and_eq_true, beq_iff_eq] at h
    by_cases hb : b' = b
    · subst hb; exact h.1
    · exact ih (b + 1) h.2 b' (by omega) (by omega)

/-- What `checkIdx` certifies about entry `t` of bucket `b`. -/
def EntryGood (ix : HIdx) (G : ByteArray) (b t : Nat) : Prop :=
  (u32 ix.ent (2 * t)) + q ≤ G.size ∧ allACGT G (u32 ix.ent (2 * t)) ((u32 ix.ent (2 * t)) + q) = true ∧
    bucketOf (hashAt G (u32 ix.ent (2 * t))) = b ∧ keyOf (hashAt G (u32 ix.ent (2 * t))) = (u32 ix.ent (2 * t + 1)) ∧
    (t + 1 < (u32 ix.offs (b + 1)) → (u32 ix.ent (2 * t)) < (u32 ix.ent (2 * t + 2)))

/-- The four facts `checkIdx` certifies. -/
theorem checkIdx_spec (ix : HIdx) (G : ByteArray) (h : checkIdx ix G = true) :
    (∀ p, p + q ≤ G.size → allACGT G p (p + q) = true →
      ∃ t, (u32 ix.offs (bucketOf (hashAt G p))) ≤ t ∧ t < (u32 ix.offs (bucketOf (hashAt G p) + 1)) ∧
        (u32 ix.ent (2 * t)) = p ∧ (u32 ix.ent (2 * t + 1)) = keyOf (hashAt G p)) ∧
    (∀ b, b < NB → ∀ t, (u32 ix.offs (b)) ≤ t → t < (u32 ix.offs (b + 1)) → EntryGood ix G b t) ∧
    (∀ p, p < G.size → acgt (G.get! p) = false →
      ∃ t, t < ix.odd[(G.get! p).toNat]!.size ∧ ix.odd[(G.get! p).toNat]![t]! = p) ∧
    (∀ v, v < 256 → ∀ i, i + 1 < ix.odd[v]!.size → ix.odd[v]![i]! < ix.odd[v]![i + 1]!) := by
  unfold checkIdx at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hs, ho⟩, hi⟩ := h
  split at hs
  · next fill hfill =>
    obtain ⟨hF, hFo⟩ := scanIdx_spec ix G _ 0 0 0 _ fill (by omega)
      ⟨by simp [q], Nat.le_refl _, fun k _ h2 => by omega, fun _ => Or.inl rfl, by simp [wN]⟩
      (fun b hb => by
        have e : ((Array.range NB).map (u32 ix.offs))[b]! = u32 ix.offs b := by
          rw [getElem!_pos _ b (by simpa using hb)]; simp
        rw [e]; exact ⟨Nat.le_refl _, fun t h1 h2 => by omega⟩) (fun p hp _ => by simp [q] at hp)
      hfill
    rw [Nat.zero_add] at hF hFo
    have hfo := fillOk_spec ix fill _ 0 hs
    refine ⟨hFo, fun b hb t h1 h2 => ?_,
      fun p hp ha => checkOdd_spec ix G _ 0 _ ho p (by omega) (by omega) ha,
      fun v hv i hi' => increasing_spec _ _ 0 (hi v hv) i (by omega) (by omega)⟩
    have hfb := hfo b (by omega) (by simp [NB] at hb ⊢; omega)
    have hg := (hF b hb).2 t h1 (by rw [hfb]; exact h2)
    refine ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1, fun ht => ?_⟩
    have hg' := (hF b hb).2 (t + 1) (by omega) (by rw [hfb]; exact ht)
    have := hg'.2.2.2.2 (by omega)
    rw [show 2 * (t + 1 - 1) = 2 * t by omega, show 2 * (t + 1) = 2 * t + 2 by omega] at this
    exact this
  · cases hs

/-! ## Lookups -/

theorem eqRun_spec (a b : ByteArray) : ∀ k i j, eqRun a b i j k = true ↔ ∀ m, m < k → a.get! (i + m) = b.get! (j + m) := by
  intro k
  induction k with
  | zero => intro i j; simp [eqRun]
  | succ k ih =>
    intro i j
    simp only [eqRun, Bool.and_eq_true, beq_iff_eq, ih]
    constructor
    · rintro ⟨h0, h⟩ m hm
      by_cases m0 : m = 0
      · subst m0; simpa using h0
      · have := h (m - 1) (by omega); rwa [show i + 1 + (m - 1) = i + m by omega,
          show j + 1 + (m - 1) = j + m by omega] at this
    · intro h
      refine ⟨by simpa using h 0 (by omega), fun m hm => ?_⟩
      rw [show i + 1 + m = i + (m + 1) by omega, show j + 1 + m = j + (m + 1) by omega]
      exact h (m + 1) (by omega)

theorem firstOdd_spec (B : ByteArray) (stop : Nat) :
    ∀ d i, stop - i = d → i ≤ stop →
      i ≤ firstOdd B i stop ∧ firstOdd B i stop ≤ stop ∧
      (∀ k, i ≤ k → k < firstOdd B i stop → acgt (B.get! k) = true) ∧
      (firstOdd B i stop < stop → acgt (B.get! (firstOdd B i stop)) = false) := by
  intro d
  induction d with
  | zero =>
    intro i hd hi
    unfold firstOdd; rw [if_neg (by omega)]
    exact ⟨hi, Nat.le_refl _, fun k h1 h2 => by omega, fun h => by omega⟩
  | succ d ih =>
    intro i hd hi
    unfold firstOdd; rw [if_pos (by omega)]
    split
    · next ha =>
      obtain ⟨h1, h2, h3, h4⟩ := ih (i + 1) (by omega) (by omega)
      refine ⟨by omega, h2, fun k hk1 hk2 => ?_, h4⟩
      by_cases hk : k = i
      · subst hk; exact ha
      · exact h3 k (by omega) hk2
    · next ha =>
      exact ⟨Nat.le_refl _, hi, fun k h1 h2 => by omega, fun _ => by simpa using ha⟩


theorem scanBucket_toList (ent : ByteArray) (key : Nat) (base bit hi : Nat) :
    ∀ d t acc, hi - t = d → (scanBucket ent key base bit hi t acc).toList = acc.toList ++
      (List.range' t (hi - t)).filterMap (fun t => if u32 ent (2 * t + 1) == key then
        some ((u32 ent (2 * t) + base) * 16 + bit) else none) := by
  intro d
  induction d with
  | zero => intro t acc hd; unfold scanBucket; rw [if_neg (by omega), hd]; simp
  | succ d ih =>
    intro t acc hd
    unfold scanBucket
    rw [if_pos (by omega), ih (t + 1) _ (by omega), show hi - t = (hi - (t + 1)) + 1 by omega,
      List.range'_succ, List.filterMap_cons]
    by_cases hk : (u32 ent (2 * t + 1) == key) = true
    · rw [if_pos hk, if_pos hk, Array.toList_push, List.append_assoc]; rfl
    · rw [if_neg hk, if_neg hk]

theorem scanOdd_toList (G R : ByteArray) (ps : Array Nat) (o s base bit : Nat) :
    ∀ d t acc, ps.size - t = d → (scanOdd G R ps o s base bit t acc).toList = acc.toList ++
      (List.range' t (ps.size - t)).filterMap (fun t =>
        if (o ≤ ps[t]! && ps[t]! - o + q ≤ G.size && eqRun G R (ps[t]! - o) s q) = true then
          some ((ps[t]! - o + base) * 16 + bit) else none) := by
  intro d
  induction d with
  | zero => intro t acc hd; unfold scanOdd; rw [if_neg (by omega), hd]; simp
  | succ d ih =>
    intro t acc hd
    unfold scanOdd
    rw [if_pos (by omega)]
    simp only []
    rw [ih (t + 1) _ (by omega), show ps.size - t = (ps.size - (t + 1)) + 1 by omega,
      List.range'_succ, List.filterMap_cons]
    by_cases hk : (o ≤ ps[t]! && ps[t]! - o + q ≤ G.size && eqRun G R (ps[t]! - o) s q) = true
    · rw [if_pos hk, if_pos hk, Array.toList_push, List.append_assoc]; rfl
    · rw [if_neg hk, if_neg hk]


/-- Packed anchor of seed `j` at genome place `p`. -/
def anchorOf (j p : Nat) : Nat := (p + (BIAS - j * q)) * 16 + 2 ^ j

theorem range'_pairwise_in (lo n : Nat) :
    (List.range' lo n).Pairwise (fun a a' => lo ≤ a ∧ a < a' ∧ a' < lo + n) := by
  apply List.Pairwise.imp_of_mem _ List.pairwise_lt_range'
  intro a b ha hb hab
  rw [List.mem_range'_1] at ha hb
  omega

/-- **Lookup.**  Through a certified index, seed `j`'s anchors are increasing and
are exactly the anchors of the places where the seed occurs. -/
theorem lookupSeed_spec (ix : HIdx) (G R : ByteArray) (j : Nat) (hchk : checkIdx ix G = true) :
    (lookupSeed ix G R j).toList.Pairwise (· < ·) ∧
    ∀ e, e ∈ (lookupSeed ix G R j).toList ↔ ∃ p, MatchAt G p R (j * q) ∧ e = anchorOf j p := by
  obtain ⟨hC, hS, hO, hI⟩ := checkIdx_spec ix G hchk
  unfold lookupSeed
  simp only []
  have hfo := firstOdd_spec R (j * q + q) _ (j * q) rfl (by omega)
  generalize ho : firstOdd R (j * q) (j * q + q) = o at hfo
  split
  · -- every letter of the seed is ACGT: the hashed buckets
    next hall =>
    have hoe : o = j * q + q := by simpa using hall
    have hacgt : allACGT R (j * q) (j * q + q) = true := by
      rw [allACGT_spec R _ _ _ rfl]
      intro k h1 h2; exact hfo.2.2.1 k h1 (by omega)
    generalize hy : hashAt R (j * q) = y
    have hb : bucketOf y < NB := by rw [← hy]; exact bucketOf_lt _ (mix_lt _)
    rw [scanBucket_toList _ _ _ _ _ _ _ _ rfl, show (#[] : Array Nat).toList = [] from rfl, List.nil_append]
    have hent := hS _ hb
    unfold EntryGood at hent
    generalize hlo : (u32 ix.offs (bucketOf y)) = lo at hent
    generalize hhi : (u32 ix.offs (bucketOf y + 1)) = hi at hent
    have hpos : ∀ t t', lo ≤ t → t < t' → t' < hi → (u32 ix.ent (2 * t)) < (u32 ix.ent (2 * t')) := by
      intro t t' h1 h2 h3
      apply chain_lt (fun t => (u32 ix.ent (2 * t))) lo hi _ (t' - t - 1) t t' (by omega) h1 h3
      intro u hu1 hu2
      have := (hent u hu1 (by omega)).2.2.2.2 hu2
      rwa [show 2 * u + 2 = 2 * (u + 1) by omega] at this
    constructor
    · apply List.Pairwise.filterMap _ _ (range'_pairwise_in lo (hi - lo))
      intro t t' htt' b1 hb1 b2 hb2
      simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hb1 hb2
      obtain ⟨-, rfl⟩ := hb1
      obtain ⟨-, rfl⟩ := hb2
      have := hpos t t' htt'.1 htt'.2.1 (by omega)
      omega
    · intro e
      rw [List.mem_filterMap]
      constructor
      · rintro ⟨t, ht, he⟩
        rw [List.mem_range'_1] at ht
        simp only [Option.ite_none_right_eq_some, Option.some.injEq, beq_iff_eq] at he
        obtain ⟨hk, rfl⟩ := he
        obtain ⟨h1, h2, h3, h4, -⟩ := hent t ht.1 (by omega)
        refine ⟨_, ⟨h1, ?_⟩, rfl⟩
        have := hash_inj G R _ (j * q) h2 hacgt (by rw [h3, hy]) (by rw [h4, hk, hy])
        exact this
      · rintro ⟨p, ⟨hp1, hp2⟩, rfl⟩
        have hga : allACGT G p (p + q) = true := by
          rw [allACGT_word]; intro k hk; rw [hp2 k hk]
          exact (allACGT_word R (j * q)).1 hacgt k hk
        have hh : hashAt G p = y := by rw [← hy]; exact hash_congr G R p (j * q) hp2
        obtain ⟨t, ht1, ht2, ht3, ht4⟩ := hC p hp1 hga
        rw [hh, hlo, hhi] at *
        refine ⟨t, List.mem_range'_1.2 ⟨ht1, by omega⟩, ?_⟩
        simp only [ht4, beq_self_eq_true, if_true, ht3]
        rfl
  · -- a letter other than ACGT at `o`: the places of that letter
    next hall =>
    have hoe : o < j * q + q := by have := hfo.2.1; simp at hall; omega
    have hodd := hfo.2.2.2 hoe
    rw [scanOdd_toList _ _ _ _ _ _ _ _ _ _ rfl, show (#[] : Array Nat).toList = [] from rfl, List.nil_append,
      Nat.sub_zero]
    generalize hv : (R.get! o).toNat = v
    have hv256 : v < 256 := by rw [← hv]; exact UInt8.toNat_lt _
    generalize hps : ix.odd[v]! = ps
    have hinc : ∀ t t', t < t' → t' < ps.size → ps[t]! < ps[t']! := by
      intro t t' h1 h2
      apply chain_lt (fun t => ps[t]!) 0 ps.size _ (t' - t - 1) t t' (by omega) (by omega) h2
      intro u _ hu; have := hI v hv256 u; rw [hps] at this; exact this hu
    constructor
    · apply List.Pairwise.filterMap _ _ (range'_pairwise_in 0 ps.size)
      intro t t' htt' b1 hb1 b2 hb2
      simp only [Option.ite_none_right_eq_some, Option.some.injEq, Bool.and_eq_true,
        decide_eq_true_eq] at hb1 hb2
      obtain ⟨⟨⟨h1, -⟩, -⟩, rfl⟩ := hb1
      obtain ⟨⟨⟨h1', -⟩, -⟩, rfl⟩ := hb2
      have := hinc t t' htt'.2.1 (by omega)
      omega
    · intro e
      rw [List.mem_filterMap]
      constructor
      · rintro ⟨t, -, he⟩
        simp only [Option.ite_none_right_eq_some, Option.some.injEq, Bool.and_eq_true,
          decide_eq_true_eq] at he
        obtain ⟨⟨⟨h1, h2⟩, h3⟩, rfl⟩ := he
        exact ⟨_, ⟨h2, (eqRun_spec G R q _ _).1 h3⟩, rfl⟩
      · rintro ⟨p, ⟨hp1, hp2⟩, rfl⟩
        have hgo : G.get! (p + (o - j * q)) = R.get! o := by
          rw [hp2 _ (by omega)]; congr 1; omega
        obtain ⟨t, ht1, ht2⟩ := hO (p + (o - j * q)) (by omega) (by rw [hgo]; exact hodd)
        rw [hgo, hv, hps] at ht1 ht2
        refine ⟨t, List.mem_range'_1.2 ⟨by omega, by omega⟩, ?_⟩
        have hp' : ps[t]! - (o - j * q) = p := by omega
        rw [if_pos (by
          simp only [Bool.and_eq_true, decide_eq_true_eq, hp']
          exact ⟨⟨by omega, hp1⟩, (eqRun_spec G R q _ _).2 hp2⟩), hp']
        rfl

end MapSpec.Fast

#print axioms MapSpec.Fast.lookupSeed_spec
