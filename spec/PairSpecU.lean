import PairSpecTier

/-!
# Pair-level uniqueness with per-mate caps (`pairSpecUT`; DRAFT for Rowan, not frozen)

Built on `MapSpec` / `PairSpec` / `PairSpecTier` without changing them.  This is the
proper-pair mode (Rowan, 2026-10-05); `pairSpecT` (each mate unique on its own, then
the proper-pair test) stays as the "all mappings" mode.

* **Hits.**  Mate 1's hits are its windows on both strands with score `≥ T1`, mate 2's
  with score `≥ T2` (`hitsBoth`).  The per-mate caps bound the mate penalties only.
* **Proper pair `properPairU sl lo hi`.**  `properPair lo hi` (same chromosome,
  opposite strands, fragment from forward-mate start to reverse-mate end in
  `[lo, hi]`) and, in addition, no dovetailing beyond `sl` letters: the forward mate
  starts at most `sl` letters after the reverse mate starts, and ends at most `sl`
  letters after the reverse mate ends.  Default `sl = 0`, `lo = 100`, `hi = 1000`.
* **Ranking.**  A pair's score is the sum of its mates' scores minus `dc (fragment)`;
  `dc` is a parameter (any `Nat`-valued function, so `≥ 0`).  Default `dcost0 = 0`:
  rank by `pen1 + pen2` only, closest is not best (Rowan, 2026-10-05).  Option
  `dcost1k`: `0` up to 1000 letters, then `+1` per full extra 1000 letters (no effect
  at `hi = 1000`).
* **Uniqueness.**  The pair reported is the proper pair whose score beats every other
  proper pair at different placements.  A tie between different pairs (even two pairs
  sharing one mate) is not reported (unmapped reason `pairTie` in the codecs).
-/

namespace MapSpec

open AlignmentSpec

/-- A pair of hits: (placement, score) of mate 1 and of mate 2. -/
abbrev PairHit := (Placement × Int) × (Placement × Int)

/-- The two placements ordered (forward-strand one, other one). -/
def fwdRev (a b : Placement) : Placement × Placement :=
  if a.2 = Strand.fwd then (a, b) else (b, a)

/-- Fragment length: forward mate start to reverse mate end. -/
def fragLen (a b : Placement) : Nat :=
  (fwdRev a b).2.1.start + (fwdRev a b).2.1.len - (fwdRev a b).1.1.start

/-- Proper pair with no dovetailing beyond `sl` letters. -/
def properPairU (sl lo hi : Nat) (a b : Placement) : Bool :=
  properPair lo hi a b &&
    decide ((fwdRev a b).1.1.start ≤ (fwdRev a b).2.1.start + sl) &&
    decide ((fwdRev a b).1.1.start + (fwdRev a b).1.1.len ≤
      (fwdRev a b).2.1.start + (fwdRev a b).2.1.len + sl)

/-- Pair score: summed mate scores minus the distance cost of the fragment. -/
def pairScoreD (dc : Nat → Nat) (p : PairHit) : Int :=
  p.1.2 + p.2.2 - (dc (fragLen p.1.1 p.2.1) : Int)

/-- All proper pairs `(a, b)`, `a` from `h1`, `b` from `h2`. -/
def properPairs (sl lo hi : Nat) (h1 h2 : List (Placement × Int)) : List PairHit :=
  h1.flatMap fun a => (h2.filter fun b => properPairU sl lo hi a.1 b.1).map fun b => (a, b)

/-- The proper pair whose score beats every other proper pair at different
placements, if there is one. -/
def bestPairD (dc : Nat → Nat) (sl lo hi : Nat) (h1 h2 : List (Placement × Int)) :
    Option PairHit :=
  (properPairs sl lo hi h1 h2).find? fun p => (properPairs sl lo hi h1 h2).all fun p' =>
    decide (pairScoreD dc p' < pairScoreD dc p) || decide (p'.1.1 = p.1.1 ∧ p'.2.1 = p.2.1)

/-- Default distance cost: none; pairs are ranked by `pen1 + pen2` only. -/
def dcost0 : Nat → Nat := fun _ => 0

/-- Optional distance cost: 0 up to 1000 letters, +1 per full extra 1000 letters. -/
def dcost1k (f : Nat) : Nat := (f - 1000) / 1000

/-- Where a pair maps under pair-level uniqueness, mate 1 at cap `T1`, mate 2 at `T2`;
`none` = not reported. -/
def pairSpecUT (sc : Scoring) (dc : Nat → Nat) (sl lo hi : Nat) (T1 T2 : Int) (g : Genome)
    (mate1 mate2 : List Char) : Option PairHit :=
  bestPairD dc sl lo hi (hitsBoth sc T1 g mate1) (hitsBoth sc T2 g mate2)

/-- Tier 1: each mate at the cap from its length (`capOf`); a too-short mate is not
reported. -/
def pairSpecUTier1 (sc : Scoring) (dc : Nat → Nat) (sl lo hi : Nat) (g : Genome)
    (mate1 mate2 : List Char) : Option PairHit :=
  match capOf mate1.length, capOf mate2.length with
  | some P1, some P2 => pairSpecUT sc dc sl lo hi (-(P1 : Int)) (-(P2 : Int)) g mate1 mate2
  | _, _ => none

end MapSpec
