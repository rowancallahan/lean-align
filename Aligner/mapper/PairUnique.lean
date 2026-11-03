import PairConcat

/-!
# Codec `pairFastU`: pair-level uniqueness (DRAFT spec `pairSpecU`)

Against `pairSpecU` (spec/PairSpec.lean): among all proper pairs of hits, the
unique best by summed score.  One index over the concatenated genome, as
`pairFastC` (codecs/PairConcat.lean).

1. Both mates through the proved per-mate search (`mapChromsCS` = `mapChromsC`
   plus the strands' final states).  A mate with no hit at all (`pen > 12`): no
   pair (`none`, `no_hit`).
2. Both mates unique and the two form a proper pair: that pair is the unique
   best pair (any other pair moves a mate to a strictly worse hit,
   `pairSpecU_of_unique`), so the answer is `pairFastC`'s.
3. Otherwise (a per-mate tie, or unique bests that are not a proper pair): the
   exact fallback `pairLevels`.  Every proper pair sums to at least `l1 + l2`
   (the mates' best penalties, `le_best`).  Level `X` (from `l1 + l2`, step 4):
   every pair summing to `≤ X` has mate 1 at `≤ X − l2` and mate 2 at `≤ X − l1`.
   The strands' final search states hold the anchors of `J` seeds; `deepen`
   looks up more seeds (anchors merged, nothing scored) until `lim < 4·|J|`, so by
   the pigeonhole lemmas (`same_lower_J`, `gap_lower`) every placement within
   `lim` has an anchor within 3 diagonals (`anchor_near`).  Placements are listed
   from those anchors, scoring only anchors with an anchor of the other mate
   within `hi + 128` diagonals (`nearA`; a proper pair is that close,
   `proper_close`).  If some pairs sum to `≤ X`, the best pair is the best of
   those (`bestPair_restrict`; one pass, `selPairs`); otherwise the next level.

    … → pairFastU lk lo hi ix G offs gbs R1 R2 = pairSpecU sc0 (-12) lo hi g m1 m2   (pairFastU_eq_pairSpecU)
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-! ## Algorithm -/

/-! ## Selection -/

section sel

variable {β κ : Type} [DecidableEq κ] (key : β → κ) (sc : β → Int)

/-- The `find?` form (as in `bestPair`) has the same characterization. -/
theorem findU_iff (same : β → β → Bool) (l : List β) (hfun : ∀ x ∈ l, ∀ y ∈ l, same x y = true → x = y)
    (y : β) :
    l.find? (fun p => l.all fun p' => decide (sc p' < sc p) || same p' p) = some y ↔
      y ∈ l ∧ ∀ x ∈ l, sc x < sc y ∨ same x y = true := by
  have hq : ∀ a : β, (l.all fun b => decide (sc b < sc a) || same b a) = true ↔
      ∀ b ∈ l, sc b < sc a ∨ same b a = true := by
    intro a; simp [List.all_eq_true]
  constructor
  · intro h
    have h' := List.find?_some h
    exact ⟨List.mem_of_find?_eq_some h, (hq y).1 h'⟩
  · rintro ⟨hm, hp⟩
    cases h : l.find? (fun a => l.all fun b => decide (sc b < sc a) || same b a) with
    | none => exact absurd ((hq y).2 hp) (by simpa using List.find?_eq_none.1 h y hm)
    | some c =>
      have h' := List.find?_some h
      have hc := (hq c).1 h'
      have hcm := List.mem_of_find?_eq_some h
      rcases hp c hcm with h1 | h1
      · rcases hc y hm with h2 | h2
        · omega
        · rw [hfun y hm c hcm h2]
      · rw [hfun c hcm y hm h1]

end sel

/-! ## Exact penalties -/

section enum

variable {L P : Type} (lk : Look L P) (ix : L) (G : ByteArray) (offs : Array Nat) (gbs : Array ByteArray)

end enum

/-! ## Against the spec -/

/-! ## The searches' final states -/

section twoS

variable (cw : Window → Nat) (hc13 : ∀ w, cw w ≤ 13) {L P : Type} [Inhabited P] (lk : Look L P) (ix : L)
  (G : ByteArray) (gbs : Array ByteArray) (offs : Array Nat) (R1 R2 : ByteArray) (c1 c2 : Nat)
  (hcw1 : ∀ c, c < gbs.size → ∀ st len, cw ⟨c1 + c, st, len⟩ = penB R1 gbs[c]! st len) (hn1 : 100 ≤ R1.size)
  (hsl1 : ∀ j, j < 4 → ∀ c, c < gbs.size →
    LookOk gbs[c]! R1 j (sliceA (lk.look ix G R1 j (lk.prep ix (seedHash R1 j))) j offs[c]! gbs[c]!.size))
  (hcw2 : ∀ c, c < gbs.size → ∀ st len, cw ⟨c2 + c, st, len⟩ = penB R2 gbs[c]! st len) (hn2 : 100 ≤ R2.size)
  (hsl2 : ∀ j, j < 4 → ∀ c, c < gbs.size →
    LookOk gbs[c]! R2 j (sliceA (lk.look ix G R2 j (lk.prep ix (seedHash R2 j))) j offs[c]! gbs[c]!.size))

include hc13 hcw1 hn1 hsl1 hcw2 hn2 hsl2

end twoS

/-! ## Every hit of one read -/

/-! ## Top theorems -/

end MapSpec.Fast

