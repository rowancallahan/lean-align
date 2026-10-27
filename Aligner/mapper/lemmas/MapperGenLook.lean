import MapperFastIndex

/-!
Seed lookups at any read offset `s`, writing `(p + base)·16 + bit` for each
genome place `p` where the 25 letters `R[s, s+25)` occur (`LookOkS`).
`lookupHG_spec`: through a hashed index passing `checkIdx`, `lookupHG` with the
word's hash `seedHashAt R s` gives exactly those, increasing.  `LookG` is the
interface the general mapper uses (any index with such a lookup).
-/

namespace MapSpec.Fast

open MapSpec

/-- Hash of the word `R[s, s+25)` when all its letters are ACGT. -/
def seedHashAt (R : ByteArray) (s : Nat) : Option UInt64 :=
  let v := seedCode R s (s + q) 0 0
  if v >>> 56 == 0 then some (mix v) else none

/-- Places of the word at `R[s ..]` through a hashed index, as `(p + base)·16 + bit`. -/
def lookupHG (ix : HIdx) (G R : ByteArray) (s base bit : Nat) (h : Option UInt64) : Array Nat :=
  match h with
  | some y =>
    let b := bucketOf y
    scanBucket ix.ent (keyOf y) base bit (u32 ix.offs (b + 1)) (u32 ix.offs b) #[]
  | none =>
    let o := firstOdd R s (s + q)
    scanOdd G R ix.odd[(R.get! o).toNat]! (o - s) s base bit 0 #[]

theorem lookupHG_some (ix : HIdx) (G R : ByteArray) (s base bit : Nat) (y : UInt64) :
    lookupHG ix G R s base bit (some y) = scanBucket ix.ent (keyOf y) base bit
      (u32 ix.offs (bucketOf y + 1)) (u32 ix.offs (bucketOf y)) #[] := rfl

theorem lookupHG_none (ix : HIdx) (G R : ByteArray) (s base bit : Nat) :
    lookupHG ix G R s base bit none = scanOdd G R ix.odd[(R.get! (firstOdd R s (s + q))).toNat]!
      (firstOdd R s (s + q) - s) s base bit 0 #[] := rfl

/-- What a lookup of the word at `R[s ..]` must give. -/
def LookOkS (G R : ByteArray) (s base bit : Nat) (a : Array Nat) : Prop :=
  a.toList.Pairwise (· < ·) ∧ ∀ e, e ∈ a.toList ↔ ∃ p, MatchAt G p R s ∧ e = (p + base) * 16 + bit

/-- A seed lookup at any offset.  `prep ix h` is computed once per seed
(`h = seedHashAt R s`); `look ix G R s base (prep ix (seedHashAt R s))` must be
`LookOkS G R s base 0`; `size` only orders the seeds. -/
class LookG (L : Type) (P : outParam Type) where
  prep : L → Option UInt64 → P
  size : L → P → Nat
  look : L → ByteArray → ByteArray → Nat → Nat → P → Array Nat

/-- The hashed index. -/
instance : LookG HIdx (Option UInt64) := ⟨fun _ h => h, sizeH, fun ix G R s base h => lookupHG ix G R s base 0 h⟩

theorem seedHashAt_spec (R : ByteArray) (s : Nat) :
    seedHashAt R s = if allACGT R (s) (s + q) then some (hashAt R (s)) else none := by
  unfold seedHashAt
  simp only []
  rw [seedCode_eq R _ _ (s) 0 0 rfl]
  have hc := cntU_toNat R (s + q) _ (s) 0 rfl (by simp [q])
  have hw := wcode_lt R (s)
  have hle := cntP_le (fun k => !acgt (R.get! k)) (s) (s + q - s)
  simp only [UInt64.toNat_zero, Nat.zero_add, show s + q - s = q by omega] at hc hle
  generalize hW : wcode R (s) (s + q) 0 = W at *
  generalize hC : cntU R (s) (s + q) 0 = C at *
  generalize hn : cntP (fun k => !acgt (R.get! k)) (s) q = n at *
  have hq : q = 25 := rfl
  have hv : (W + C <<< 56).toNat = W.toNat + n * 2 ^ 56 := by
    rw [UInt64.toNat_add, UInt64.toNat_shiftLeft, show (56 : UInt64).toNat % 64 = 56 from rfl,
      Nat.shiftLeft_eq, hc]
    rw [hq] at hle
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hsh : ((W + C <<< 56) >>> 56).toNat = n := by
    rw [UInt64.toNat_shiftRight, show (56 : UInt64).toNat % 64 = 56 from rfl, Nat.shiftRight_eq_div_pow, hv]
    omega
  have hiff := allACGT_cnt R (s) q
  rw [hn] at hiff
  by_cases h0 : n = 0
  · have hv0 : W + C <<< 56 = W := UInt64.toNat_inj.mp (by rw [hv, h0]; simp)
    have hz : ((W + C <<< 56) >>> 56 == 0) = true := by
      rw [beq_iff_eq, ← UInt64.toNat_inj, hsh, h0]; rfl
    rw [if_pos hz, if_pos (hiff.2 h0), hv0]
    unfold hashAt; rw [hW]
  · have hz : ¬ ((W + C <<< 56) >>> 56 == 0) = true := by
      rw [beq_iff_eq, ← UInt64.toNat_inj, hsh]; simpa using h0
    rw [if_neg hz, if_neg (fun h => h0 (hiff.1 h))]


theorem lookupHG_spec (ix : HIdx) (G R : ByteArray) (s base bit : Nat) (hchk : checkIdx ix G = true) :
    LookOkS G R s base bit (lookupHG ix G R s base bit (seedHashAt R s)) := by
  obtain ⟨hC, hS, hO, hI⟩ := checkIdx_spec ix G hchk
  unfold LookOkS
  rw [seedHashAt_spec]
  have hfo := firstOdd_spec R (s + q) _ (s) rfl (by omega)
  generalize ho : firstOdd R (s) (s + q) = o at hfo
  by_cases hacgt : allACGT R (s) (s + q) = true
  · -- every letter of the seed is ACGT: the hashed buckets
    rw [if_pos hacgt, lookupHG_some]
    generalize hy : hashAt R (s) = y
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
        have := hash_inj G R _ (s) h2 hacgt (by rw [h3, hy]) (by rw [h4, hk, hy])
        exact this
      · rintro ⟨p, ⟨hp1, hp2⟩, rfl⟩
        have hga : allACGT G p (p + q) = true := by
          rw [allACGT_word]; intro k hk; rw [hp2 k hk]
          exact (allACGT_word R (s)).1 hacgt k hk
        have hh : hashAt G p = y := by rw [← hy]; exact hash_congr G R p (s) hp2
        obtain ⟨t, ht1, ht2, ht3, ht4⟩ := hC p hp1 hga
        rw [hh, hlo, hhi] at *
        refine ⟨t, List.mem_range'_1.2 ⟨ht1, by omega⟩, ?_⟩
        simp only [ht4, beq_self_eq_true, if_true, ht3]
  · -- a letter other than ACGT at `o`: the places of that letter
    rw [if_neg hacgt, lookupHG_none, ho]
    have hoe : o < s + q := by
      apply Classical.byContradiction; intro hlt
      apply hacgt; rw [allACGT_spec R _ _ _ rfl]
      intro k h1 h2; exact hfo.2.2.1 k h1 (by omega)
    have hodd := hfo.2.2.2 hoe
    rw [scanOdd_toList _ _ _ _ _ _ _ _ _ _ rfl, show (#[] : Array Nat).toList = [] from rfl, List.nil_append,
      Nat.sub_zero]
    generalize hv : (R.get! o).toNat = v
    have hv256 : v < 256 := by rw [← hv]; exact UInt8.toNat_lt _
    generalize hps : ix.odd[v]! = ps
    have hinc : ∀ t t', t < t' → t' < len32 ps → u32 ps t < u32 ps t' := by
      intro t t' h1 h2
      apply chain_lt (fun t => u32 ps t) 0 (len32 ps) _ (t' - t - 1) t t' (by omega) (by omega) h2
      intro u _ hu; have := hI v hv256 u; rw [hps] at this; exact this hu
    constructor
    · apply List.Pairwise.filterMap _ _ (range'_pairwise_in 0 (len32 ps))
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
        have hgo : G.get! (p + (o - s)) = R.get! o := by
          rw [hp2 _ (by omega)]; congr 1; omega
        obtain ⟨t, ht1, ht2⟩ := hO (p + (o - s)) (by omega) (by rw [hgo]; exact hodd)
        rw [hgo, hv, hps] at ht1 ht2
        refine ⟨t, List.mem_range'_1.2 ⟨by omega, by omega⟩, ?_⟩
        have hp' : u32 ps t - (o - s) = p := by omega
        rw [if_pos (by
          simp only [Bool.and_eq_true, decide_eq_true_eq, hp']
          exact ⟨⟨by omega, hp1⟩, (eqRun_spec G R q _ _).2 hp2⟩), hp']


end MapSpec.Fast

#print axioms MapSpec.Fast.lookupHG_spec
