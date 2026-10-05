import MapperK250

/-!
# Selecting set fields

For `m : UInt64` whose 32 fields are `0` or `1` (`Bin`): `selLow m k` is the field
of the `k+1`-th lowest set field (`lowIdx`: `cnt64 (m ^^^ (m - 1)) − 1`, then clear the
lowest with `m &&& (m - 1)`), `selHigh m k` the `k+1`-th highest (`highIdx`: smear right
and count, then clear the highest).
-/

namespace MapSpec.Fast

open MapSpec MapSpec.Packed

/-- All 32 fields are `0` or `1`. -/
def Bin (m : UInt64) : Prop := ∀ t, t < 32 → dig m.toNat t ≤ 1

/-- The `k+1`-th lowest set field. -/
theorem selLow_spec (m : UInt64) (hb : Bin m) (k : Nat) (hk : k < cntNZ 32 m.toNat) :
    selLow m k < 32 ∧ cntNZ (selLow m k) m.toNat = k ∧ dig m.toNat (selLow m k) = 1 := by
  sorry

/-- The `k+1`-th highest set field: `k` set fields above it. -/
theorem selHigh_spec (m : UInt64) (hb : Bin m) (k : Nat) (hk : k < cntNZ 32 m.toNat) :
    selHigh m k < 32 ∧ cntNZ (selHigh m k + 1) m.toNat + k = cntNZ 32 m.toNat ∧
      dig m.toNat (selHigh m k) = 1 := by
  sorry

end MapSpec.Fast
