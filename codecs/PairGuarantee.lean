import PairLadder

/-!
# Codec `pairGK`: the pair-level guarantee at total penalty `G`

Every hit of each mate within penalty `G` (`hitsAtKP G`, exact over the packed whole genome),
then the best proper pair of the two lists (`bestPairD`) and the flag "a proper pair was seen":

    pairGK … = some (pairSpecUT sc0 dc sl lo hi (−G) (−G) g m1 m2, flag)        (pairGK_eq)

**Guarantee** (`pairGK_guarantee`).  If some proper pair (`properPairU sl`: 1 kb cap, no
dovetail beyond `sl`) at any caps `P1, P2 ≥ G` has pair score `≥ −G` (with `dcost0`: total penalty
`≤ G`), the kernel returns `some (r, true)` with `r = pairSpecUT … (−P1) (−P2)`: the unique best
pair, or `none` with `PairTieOk` (`pairTie`: proper pairs exist, no unique best).

**Read-length condition** (hypotheses, `fastT G` for both mates): `0 < n / 25` and
`sbound G < n / 25`.  `G = 4`: both mates `≥ 50` bp (`pairGK_guarantee4`); `G = 0`: `≥ 25` bp
(`pairGK_guarantee0`).  Outside it the kernel returns `none` (outside the guarantee).
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-- The pair-level guarantee kernel at `Gc`: `none` when a mate is outside the length condition. -/
def pairGK {L Pp : Type} [LookG L Pp] [Inhabited Pp] (dc : Nat → Nat) (sl lo hi Gc : Nat) (ix : L)
    (G : ByteArray) (offs : Array Nat) (pgs : Array PGen) (R1 R2 : ByteArray) :
    Option (Option PairHit × Bool) :=
  match hitsAtKP Gc ix G offs pgs R1, hitsAtKP Gc ix G offs pgs R2 with
  | some l1, some l2 => some (bestPairD dc sl lo hi l1 l2, !(properPairs sl lo hi l1 l2).isEmpty)
  | _, _ => none

theorem hitsAtKP_some {L Pp : Type} [LookG L Pp] [Inhabited Pp] (lim : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (pgs : Array PGen) (R : ByteArray) (h : fastT lim R = true) :
    ∃ l, hitsAtKP lim ix G offs pgs R = some l := by
  unfold hitsAtKP
  rw [if_pos h]
  exact ⟨_, rfl⟩

theorem sbound_four : sbound 4 = 1 := by decide

theorem sbound_zero : sbound 0 = 0 := by decide

theorem fastT_four (R : ByteArray) (h : 50 ≤ R.size) : fastT 4 R = true := by
  unfold fastT
  rw [sbound_four]
  have : 2 ≤ R.size / 25 := (Nat.le_div_iff_mul_le (by decide)).mpr (by omega)
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem fastT_zero (R : ByteArray) (h : 25 ≤ R.size) : fastT 0 R = true := by
  unfold fastT
  rw [sbound_zero]
  have : 1 ≤ R.size / 25 := (Nat.le_div_iff_mul_le (by decide)).mpr (by omega)
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- A hit within the caps of a pair of score `≥ −c` is a hit within `c`. -/
theorem hitsBoth_lower {T : Int} {c : Nat} {g : Genome} {m : List Char} {x : Placement × Int}
    (hx : x ∈ hitsBoth sc0 T g m) (hT : T ≤ -(c : Int)) (hs : -(c : Int) ≤ x.2) :
    x ∈ hitsBoth sc0 (-(c : Int)) g m := by
  have e := hitsBoth_filter sc0 T (-(c : Int)) g m
  rw [Int.max_eq_right hT] at e
  rw [← e]
  exact List.mem_filter.mpr ⟨hx, by simpa using hs⟩

section top
variable (dc : Nat → Nat) (sl lo hi Gc : Nat) (g : Genome) (m1 m2 : List Char) (ix : Mz.MzIdx) (G : PGen)
  (offs ns : Array Nat) (R1 R2 : ByteArray)
  (hcut : cutOk G offs ns = true) (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) g)
  (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hchk : Mz.check2P ix G = true)

include hcut hg h1 h2 hchk in
/-- **The kernel is the specification at caps `G`**, and its flag says whether a proper pair with
both mates within `G` exists. -/
theorem pairGK_eq (hG : Gc ≤ 16) (f1 : fastT Gc R1 = true) (f2 : fastT Gc R2 = true) :
    ∃ b, pairGK dc sl lo hi Gc ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) R1 R2 =
      some (pairSpecUT sc0 dc sl lo hi (-(Gc : Int)) (-(Gc : Int)) g m1 m2, b) ∧
      (b = true ↔ ∃ w, w ∈ properPairs sl lo hi (hitsBoth sc0 (-(Gc : Int)) g m1)
        (hitsBoth sc0 (-(Gc : Int)) g m2)) := by
  obtain ⟨l1, e1⟩ := hitsAtKP_some Gc ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) R1 f1
  obtain ⟨l2, e2⟩ := hitsAtKP_some Gc ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) R2 f2
  have i1 := mem_hitsAtKP_mz Gc hG g m1 ix G offs ns R1 hcut hg h1 hchk l1 e1
  have i2 := mem_hitsAtKP_mz Gc hG g m2 ix G offs ns R2 hcut hg h2 hchk l2 e2
  have ep : ∀ p, p ∈ properPairs sl lo hi l1 l2 ↔
      p ∈ properPairs sl lo hi (hitsBoth sc0 (-(Gc : Int)) g m1) (hitsBoth sc0 (-(Gc : Int)) g m2) := by
    intro p; rw [mem_properPairs, mem_properPairs, i1, i2]
  refine ⟨!(properPairs sl lo hi l1 l2).isEmpty, ?_, ?_⟩
  · unfold pairGK
    rw [e1, e2]
    simp only [Option.some.injEq, Prod.mk.injEq, and_true]
    exact bestPairD_congr dc sl lo hi i1 i2 (hitsBoth_scoreFun _ _ _ _) (hitsBoth_scoreFun _ _ _ _)
  · simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff]
    constructor
    · intro h
      obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ h
      exact ⟨w, (ep w).1 hw⟩
    · rintro ⟨w, hw⟩ he
      rw [he] at ep
      exact List.not_mem_nil ((ep w).2 hw)

include hcut hg h1 h2 hchk in
/-- **The pair-level guarantee.**  Mates within the length condition (`fastT G`); a proper pair
`w` at caps `P1, P2 ≥ G` with pair score `≥ −G`: the kernel returns `(r, true)`, `r` the
specification's answer at `P1, P2`, and `r = none` only for `pairTie`. -/
theorem pairGK_guarantee (hG : Gc ≤ 16) (f1 : fastT Gc R1 = true) (f2 : fastT Gc R2 = true)
    (P1 P2 : Nat) (hP1 : Gc ≤ P1) (hP2 : Gc ≤ P2) (w : PairHit)
    (hw : w ∈ properPairs sl lo hi (hitsBoth sc0 (-(P1 : Int)) g m1) (hitsBoth sc0 (-(P2 : Int)) g m2))
    (hW : -(Gc : Int) ≤ pairScoreD dc w) :
    ∃ r, pairGK dc sl lo hi Gc ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) R1 R2 = some (r, true) ∧
      r = pairSpecUT sc0 dc sl lo hi (-(P1 : Int)) (-(P2 : Int)) g m1 m2 ∧
      (r = none → PairTieOk dc sl lo hi (-(P1 : Int)) (-(P2 : Int)) g m1 m2) := by
  obtain ⟨b, he, hb⟩ := pairGK_eq dc sl lo hi Gc g m1 m2 ix G offs ns R1 R2 hcut hg h1 h2 hchk hG f1 f2
  have hc := pairSpecUT_caps dc sl lo hi P1 P2 Gc Gc g m1 m2 w hw hP1 hP2 (Or.inr hW) (Or.inr hW)
  obtain ⟨a1, a2, ap⟩ := mem_properPairs.mp hw
  have n1 := hitsBoth_nonpos _ _ _ _ a1
  have n2 := hitsBoth_nonpos _ _ _ _ a2
  have hd : (0 : Int) ≤ (dc (fragLen w.1.1 w.2.1) : Int) := Int.natCast_nonneg _
  have s1 : pairScoreD dc w ≤ w.1.2 := by unfold pairScoreD; omega
  have s2 : pairScoreD dc w ≤ w.2.2 := by unfold pairScoreD; omega
  have hwG : w ∈ properPairs sl lo hi (hitsBoth sc0 (-(Gc : Int)) g m1) (hitsBoth sc0 (-(Gc : Int)) g m2) :=
    mem_properPairs.mpr ⟨hitsBoth_lower a1 (by omega) (by omega), hitsBoth_lower a2 (by omega) (by omega), ap⟩
  have hbt : b = true := hb.2 ⟨w, hwG⟩
  subst hbt
  refine ⟨_, he, hc, fun hn => ⟨by rw [← hc]; exact hn, w, hw⟩⟩

include hcut hg h1 h2 hchk in
/-- **`G = 4`, mates of at least 50 bp**, `dcost0`: a proper pair with total penalty `≤ 4` (at any
caps `P1, P2 ≥ 4`) → the specification's answer or `pairTie`. -/
theorem pairGK_guarantee4 (n1 : 50 ≤ m1.length) (n2 : 50 ≤ m2.length)
    (P1 P2 : Nat) (hP1 : 4 ≤ P1) (hP2 : 4 ≤ P2) (w : PairHit)
    (hw : w ∈ properPairs sl lo hi (hitsBoth sc0 (-(P1 : Int)) g m1) (hitsBoth sc0 (-(P2 : Int)) g m2))
    (hW : -4 ≤ w.1.2 + w.2.2) :
    ∃ r, pairGK dcost0 sl lo hi 4 ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) R1 R2 = some (r, true) ∧
      r = pairSpecUT sc0 dcost0 sl lo hi (-(P1 : Int)) (-(P2 : Int)) g m1 m2 ∧
      (r = none → PairTieOk dcost0 sl lo hi (-(P1 : Int)) (-(P2 : Int)) g m1 m2) :=
  pairGK_guarantee dcost0 sl lo hi 4 g m1 m2 ix G offs ns R1 R2 hcut hg h1 h2 hchk (by decide)
    (fastT_four R1 (by rw [h1.1]; exact n1)) (fastT_four R2 (by rw [h2.1]; exact n2)) P1 P2 hP1 hP2 w hw
    (by unfold pairScoreD dcost0; simpa using hW)

include hcut hg h1 h2 hchk in
/-- **`G = 0`, mates of at least 25 bp**, `dcost0`: a proper pair of two perfect hits → the
specification's answer or `pairTie`. -/
theorem pairGK_guarantee0 (n1 : 25 ≤ m1.length) (n2 : 25 ≤ m2.length)
    (P1 P2 : Nat) (w : PairHit)
    (hw : w ∈ properPairs sl lo hi (hitsBoth sc0 (-(P1 : Int)) g m1) (hitsBoth sc0 (-(P2 : Int)) g m2))
    (hW : 0 ≤ w.1.2 + w.2.2) :
    ∃ r, pairGK dcost0 sl lo hi 0 ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) R1 R2 = some (r, true) ∧
      r = pairSpecUT sc0 dcost0 sl lo hi (-(P1 : Int)) (-(P2 : Int)) g m1 m2 ∧
      (r = none → PairTieOk dcost0 sl lo hi (-(P1 : Int)) (-(P2 : Int)) g m1 m2) :=
  pairGK_guarantee dcost0 sl lo hi 0 g m1 m2 ix G offs ns R1 R2 hcut hg h1 h2 hchk (by decide)
    (fastT_zero R1 (by rw [h1.1]; exact n1)) (fastT_zero R2 (by rw [h2.1]; exact n2)) P1 P2
    (Nat.zero_le _) (Nat.zero_le _) w hw
    (by unfold pairScoreD dcost0; simpa using hW)

end top

end MapSpec.Fast

#print axioms MapSpec.Fast.pairGK_eq
#print axioms MapSpec.Fast.pairGK_guarantee
#print axioms MapSpec.Fast.pairGK_guarantee4
#print axioms MapSpec.Fast.pairGK_guarantee0
