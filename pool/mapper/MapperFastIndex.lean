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

theorem c2_toNat (b : UInt8) : (c2 b).toNat = c2N b := by
  unfold c2 c2N
  by_cases h1 : b = 67
  · simp [h1]
  · by_cases h2 : b = 71
    · simp [h2]
    · by_cases h3 : b = 84
      · simp [h3]
      · simp [h1, h2, h3]

theorem c2N_lt (b : UInt8) : c2N b < 4 := by
  unfold c2N
  by_cases h1 : b = 67
  · simp [h1]
  · by_cases h2 : b = 71
    · simp [h2]
    · by_cases h3 : b = 84 <;> simp [h1, h2, h3]

theorem acgt_cases (b : UInt8) (h : acgt b = true) : b = 65 ∨ b = 67 ∨ b = 71 ∨ b = 84 := by
  unfold acgt at h; simp at h; rcases h with ((h | h) | h) | h <;> simp [h]

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
  have hk' := congrArg UInt32.toNat hk
  rw [UInt64.toNat_toUInt32, UInt64.toNat_toUInt32, UInt64.toNat_and, UInt64.toNat_and,
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

theorem checkComplete_spec (ix : HIdx) (G : ByteArray) :
    ∀ k p fill, checkComplete ix G fill k p = true → ∀ p', p ≤ p' → p' < p + k →
      allACGT G p' (p' + q) = true →
      ∃ t, ix.offs[bucketOf (hashAt G p')]!.toNat ≤ t ∧ t < ix.offs[bucketOf (hashAt G p') + 1]!.toNat ∧
        ix.ent[2 * t]!.toNat = p' ∧ ix.ent[2 * t + 1]! = keyOf (hashAt G p') := by
  intro k
  induction k with
  | zero => intro p fill _ p' h1 h2; omega
  | succ k ih =>
    intro p fill h p' h1 h2 ha
    unfold checkComplete at h
    by_cases hp : p' = p
    · subst hp
      rw [if_pos ha] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
      exact ⟨_, h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2⟩
    · split at h
      · simp only [Bool.and_eq_true] at h
        exact ih _ _ h.2 p' (by omega) (by omega) ha
      · exact ih _ _ h p' (by omega) (by omega) ha

theorem checkBucket_spec (ix : HIdx) (G : ByteArray) (b hi : Nat) :
    ∀ k t, checkBucket ix G b hi k t = true → ∀ t', t ≤ t' → t' < t + k → entryOk ix G b hi t' = true := by
  intro k
  induction k with
  | zero => intro t _ t' h1 h2; omega
  | succ k ih =>
    intro t h t' h1 h2
    simp only [checkBucket, Bool.and_eq_true] at h
    by_cases ht : t' = t
    · subst ht; exact h.1
    · exact ih (t + 1) h.2 t' (by omega) (by omega)

theorem checkSound_spec (ix : HIdx) (G : ByteArray) :
    ∀ k b, checkSound ix G k b = true → ∀ b', b ≤ b' → b' < b + k → ∀ t,
      ix.offs[b']!.toNat ≤ t → t < ix.offs[b' + 1]!.toNat → entryOk ix G b' ix.offs[b' + 1]!.toNat t = true := by
  intro k
  induction k with
  | zero => intro b _ b' h1 h2; omega
  | succ k ih =>
    intro b h b' h1 h2 t ht1 ht2
    simp only [checkSound, Bool.and_eq_true] at h
    by_cases hb : b' = b
    · subst hb; exact checkBucket_spec ix G _ _ _ _ h.1 t ht1 (by omega)
    · exact ih (b + 1) h.2 b' (by omega) (by omega) t ht1 ht2

theorem entryOk_spec (ix : HIdx) (G : ByteArray) (b hi t : Nat) (h : entryOk ix G b hi t = true) :
    ix.ent[2 * t]!.toNat + q ≤ G.size ∧ allACGT G ix.ent[2 * t]!.toNat (ix.ent[2 * t]!.toNat + q) = true ∧
      bucketOf (hashAt G ix.ent[2 * t]!.toNat) = b ∧ keyOf (hashAt G ix.ent[2 * t]!.toNat) = ix.ent[2 * t + 1]! ∧
      (t + 1 < hi → ix.ent[2 * t]!.toNat < ix.ent[2 * t + 2]!.toNat) := by
  unfold entryOk at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, fun ht => by rcases h.2 with h2 | h2 <;> omega⟩

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

/-- The four facts `checkIdx` certifies. -/
theorem checkIdx_spec (ix : HIdx) (G : ByteArray) (h : checkIdx ix G = true) :
    (∀ p, p + q ≤ G.size → allACGT G p (p + q) = true →
      ∃ t, ix.offs[bucketOf (hashAt G p)]!.toNat ≤ t ∧ t < ix.offs[bucketOf (hashAt G p) + 1]!.toNat ∧
        ix.ent[2 * t]!.toNat = p ∧ ix.ent[2 * t + 1]! = keyOf (hashAt G p)) ∧
    (∀ b, b < NB → ∀ t, ix.offs[b]!.toNat ≤ t → t < ix.offs[b + 1]!.toNat →
      entryOk ix G b ix.offs[b + 1]!.toNat t = true) ∧
    (∀ p, p < G.size → acgt (G.get! p) = false →
      ∃ t, t < ix.odd[(G.get! p).toNat]!.size ∧ ix.odd[(G.get! p).toNat]![t]! = p) ∧
    (∀ v, v < 256 → ∀ i, i + 1 < ix.odd[v]!.size → ix.odd[v]![i]! < ix.odd[v]![i + 1]!) := by
  unfold checkIdx at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨hc, hs⟩, ho⟩, hi⟩ := h
  refine ⟨fun p hp ha => checkComplete_spec ix G _ 0 _ hc p (by omega) (by simp [q] at hp ⊢; omega) ha,
    fun b hb t h1 h2 => checkSound_spec ix G _ 0 hs b (by omega) (by omega) t h1 h2,
    fun p hp ha => checkOdd_spec ix G _ 0 _ ho p (by omega) (by omega) ha,
    fun v hv i hi' => increasing_spec _ _ 0 (hi v hv) i (by omega) (by omega)⟩

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


theorem scanBucket_toList (ent : Array UInt32) (key : UInt32) (base bit hi : Nat) :
    ∀ d t acc, hi - t = d → (scanBucket ent key base bit hi t acc).toList = acc.toList ++
      (List.range' t (hi - t)).filterMap (fun t => if ent[2 * t + 1]! == key then
        some ((ent[2 * t]!.toNat + base) * 16 + bit) else none) := by
  intro d
  induction d with
  | zero => intro t acc hd; unfold scanBucket; rw [if_neg (by omega), hd]; simp
  | succ d ih =>
    intro t acc hd
    unfold scanBucket
    rw [if_pos (by omega), ih (t + 1) _ (by omega), show hi - t = (hi - (t + 1)) + 1 by omega,
      List.range'_succ, List.filterMap_cons]
    by_cases hk : (ent[2 * t + 1]! == key) = true
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
    generalize hlo : ix.offs[bucketOf y]!.toNat = lo at hent
    generalize hhi : ix.offs[bucketOf y + 1]!.toNat = hi at hent
    have hpos : ∀ t t', lo ≤ t → t < t' → t' < hi → ix.ent[2 * t]!.toNat < ix.ent[2 * t']!.toNat := by
      intro t t' h1 h2 h3
      apply chain_lt (fun t => ix.ent[2 * t]!.toNat) lo hi _ (t' - t - 1) t t' (by omega) h1 h3
      intro u hu1 hu2
      have := (entryOk_spec ix G _ _ u (hent u hu1 (by omega))).2.2.2.2 hu2
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
        obtain ⟨h1, h2, h3, h4, -⟩ := entryOk_spec ix G _ _ t (hent t ht.1 (by omega))
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
