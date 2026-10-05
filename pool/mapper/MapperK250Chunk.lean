import MapperK250Bits
import MapperFastIndex

/-!
# Chunks: packed read against the packed genome

`packRP_ok`: a read that passed the pack check is ACGT with its codes in the words.
`chunk_dig`: digit `t` of read word `j` XOR the genome letters of that chunk (the two
aligned words shifted, `comb`) is `0` iff the bytes match, when the genome letter lies
in a flagged block of a `PGen` that spells `G`.
-/

namespace MapSpec.Fast

open MapSpec MapSpec.Packed

/-- The packed read: every letter ACGT, its code in field `i % 32` of word `i / 32`. -/
theorem packRP_ok (R : ByteArray) (h : (packRP R).ok = true) :
    R.size ≤ 256 ∧ ∀ i, i < R.size → acgt (R.get! i) = true ∧
      dig ((packRP R).w[i / 32]!).toNat (i % 32) = c2N (R.get! i) := by
  sorry

/-- Read chunk `j` against the genome at window start `st`: digit `t` of the XOR is `0`
iff read letter `32j + t` matches. -/
theorem chunk_dig (R G : ByteArray) (P : PGen) (hP : Rep P G) (hok : (packRP R).ok = true)
    (st j t : Nat) (ht : t < 32) (hx : 32 * j + t < R.size) (hin : st + 32 * j + t < P.n)
    (hfl : P.w.get! (17 * ((P.o + st + 32 * j + t) / 64)) = 1) :
    dig ((packRP R).w[j]! ^^^ comb (gword P.w ((P.o + st) / 32 + j)) (gword P.w ((P.o + st) / 32 + j + 1))
        ((P.o + st) % 32) (2 * ((P.o + st) % 32)).toUInt64 (64 - 2 * ((P.o + st) % 32)).toUInt64).toNat t = 0 ↔
      R.get! (32 * j + t) = G.get! (st + 32 * j + t) := by
  sorry

end MapSpec.Fast
