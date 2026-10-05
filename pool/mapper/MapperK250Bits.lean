import MapperK250

/-!
# Bit lemmas for the word kernels

Base-4 digits (`Packed.dig`) of the `UInt64` operations used by the word kernels:
the fold of each 2-bit field to one bit, the field masks, XOR, the shifted pair of
aligned words (`comb`), the 8-byte gather (`gword`), and the selection of the
`k+1`-th lowest / highest set field (`selLow`, `selHigh`).
-/

namespace MapSpec.Fast

open MapSpec MapSpec.Packed

theorem dig_hi (x : UInt64) (t : Nat) (ht : 32 ≤ t) : dig x.toNat t = 0 := by
  sorry

theorem cntNZ_congr (n x y : Nat) (h : ∀ t, t < n → dig x t = dig y t) : cntNZ n x = cntNZ n y := by
  sorry

theorem xor_dig (x y : UInt64) (t : Nat) : dig (x ^^^ y).toNat t = 0 ↔ dig x.toNat t = dig y.toNat t := by
  sorry

theorem fold_dig (x : UInt64) (t : Nat) (ht : t < 32) :
    dig (fold x).toNat t = if dig x.toNat t = 0 then 0 else 1 := by
  sorry

theorem lowF_dig (x : UInt64) (c t : Nat) (ht : t < 32) :
    dig (lowF x c).toNat t = if t < c then dig x.toNat t else 0 := by
  sorry

theorem highF_dig (x : UInt64) (c t : Nat) (ht : t < 32) :
    dig (highF x c).toNat t = if t < c then 0 else dig x.toNat t := by
  sorry

theorem comb_dig (cur nxt : UInt64) (s t : Nat) (hs : s < 32) (ht : t < 32) :
    dig (comb cur nxt s (2 * s).toUInt64 (64 - 2 * s).toUInt64).toNat t =
      if s + t < 32 then dig cur.toNat (s + t) else dig nxt.toNat (s + t - 32) := by
  sorry

theorem gword_dig (w : ByteArray) (u t : Nat) (ht : t < 32) :
    dig (gword w u).toNat t = (w.get! (17 * (u / 2) + 1 + 8 * (u % 2) + t / 4)).toNat / 4 ^ (t % 4) % 4 := by
  sorry

end MapSpec.Fast
