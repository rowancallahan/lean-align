import MapSpec

/-!
# Both strands and proper pairs (DRAFT, for Rowan to review/rewrite; not frozen)

Built on `MapSpec` without changing it.

* **Both strands.**  A read is placed against every window twice: as given
  (forward strand) and as its reverse complement (reverse strand).  A window on
  the reverse strand is a different placement from the same window on the
  forward strand.  The read maps when exactly one placement has the highest
  hit score; a tie between different placements (including the same window on
  the two strands) is unmapped.
* **Proper pairs.**  A pair is reported only when both mates map (both
  strands), on the same chromosome, on opposite strands, facing each other,
  with fragment length (forward mate start to reverse mate end) in `[lo, hi]`.
  Otherwise the pair is unmapped.  Users who keep only uniquely mapped reads in
  proper pairs get exactly this.
-/

namespace MapSpec

open AlignmentSpec

inductive Strand where
  | fwd
  | rev
deriving DecidableEq, Repr

/-- Complement of one letter; letters other than A, C, G, T are kept. -/
def complement : Char → Char
  | 'A' => 'T' | 'C' => 'G' | 'G' => 'C' | 'T' => 'A'
  | c => c

def revComp (read : List Char) : List Char := (read.map complement).reverse

/-- A placement: a window and the strand the read is aligned on. -/
abbrev Placement := Window × Strand

/-- The hit that beats every hit at a different key, if there is one
(`selectUnique` for any key type). -/
def selectUniqueBy {α : Type} [DecidableEq α] (hits : List (α × Int)) : Option (α × Int) :=
  hits.find? fun a => hits.all fun b => decide (b.2 < a.2) || decide (b.1 = a.1)

/-- Hits on both strands, each tagged with its strand. -/
def hitsBoth (sc : Scoring) (T : Int) (g : Genome) (read : List Char) : List (Placement × Int) :=
  (hitsOf (windowScore sc read g) T (allWindows g)).map (fun h => ((h.1, Strand.fwd), h.2)) ++
  (hitsOf (windowScore sc (revComp read) g) T (allWindows g)).map (fun h => ((h.1, Strand.rev), h.2))

/-- Where the read maps over both strands, with its score; `none` = unmapped. -/
def mapSpecBoth (sc : Scoring) (T : Int) (g : Genome) (read : List Char) : Option (Placement × Int) :=
  selectUniqueBy (hitsBoth sc T g read)

/-- Proper pair: same chromosome, opposite strands, facing, fragment length
(forward mate start to reverse mate end) in `[lo, hi]`. -/
def properPair (lo hi : Nat) (a b : Placement) : Bool :=
  let (f, r) := if a.2 = Strand.fwd then (a, b) else (b, a)
  decide (f.1.chr = r.1.chr) && decide (f.2 = Strand.fwd) && decide (r.2 = Strand.rev) &&
    decide (f.1.start ≤ r.1.start + r.1.len) &&
    decide (lo ≤ r.1.start + r.1.len - f.1.start) && decide (r.1.start + r.1.len - f.1.start ≤ hi)

/-- Where a pair maps when only proper pairs are kept; `none` = not reported. -/
def pairSpec (sc : Scoring) (T : Int) (lo hi : Nat) (g : Genome) (mate1 mate2 : List Char) :
    Option ((Placement × Int) × (Placement × Int)) :=
  match mapSpecBoth sc T g mate1, mapSpecBoth sc T g mate2 with
  | some a, some b => if properPair lo hi a.1 b.1 then some (a, b) else none
  | _, _ => none

/-! ## Pair-level uniqueness (second DRAFT, for Rowan to review; `pairSpec` above is kept)

`pairSpec` asks each mate to map uniquely on its own.  `pairSpecU` instead looks at
every proper pair `(a, b)` with `a` a hit of mate 1 and `b` a hit of mate 2 (each
over both strands, score `≥ T`) and keeps the pair whose summed score beats every
other proper pair; a tie between different pairs (even pairs sharing one mate) is
unmapped.  A per-mate tie that only one proper pair can resolve is then mapped. -/

/-- The proper pair of hits (`a` from `h1`, `b` from `h2`) whose summed score beats
every other proper pair at different placements, if there is one. -/
def bestPair (lo hi : Nat) (h1 h2 : List (Placement × Int)) :
    Option ((Placement × Int) × (Placement × Int)) :=
  let ps := h1.flatMap fun a => (h2.filter fun b => properPair lo hi a.1 b.1).map fun b => (a, b)
  ps.find? fun p => ps.all fun p' =>
    decide (p'.1.2 + p'.2.2 < p.1.2 + p.2.2) || decide (p'.1.1 = p.1.1 ∧ p'.2.1 = p.2.1)

/-- DRAFT: where a pair maps under pair-level uniqueness; `none` = not reported. -/
def pairSpecU (sc : Scoring) (T : Int) (lo hi : Nat) (g : Genome) (mate1 mate2 : List Char) :
    Option ((Placement × Int) × (Placement × Int)) :=
  bestPair lo hi (hitsBoth sc T g mate1) (hitsBoth sc T g mate2)

/-- `selectUnique` is the `Window` instance of `selectUniqueBy`. -/
theorem selectUnique_eq_by (hits : List (Window × Int)) : selectUnique hits = selectUniqueBy hits := rfl

end MapSpec
