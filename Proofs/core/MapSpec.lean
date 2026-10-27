import AlignmentSpec

/-!
# Read-mapping specification (DRAFT, for Rowan to rewrite; not frozen)

No index, no seeds.  A read is placed against every window of every
chromosome; a window's score is the optimal global alignment score of the read
against that window (`getBestAlignment`, the frozen pairwise spec).  Windows
scoring at least the threshold `T` are hits.  The read maps when exactly one
window has the highest hit score; otherwise it is unmapped (`none`).
Forward strand only.
-/

namespace MapSpec

open AlignmentSpec

structure Chromosome where
  name : String
  seq : List Char

abbrev Genome := List Chromosome

/-- Chromosome index, 0-based start, length. -/
structure Window where
  chr : Nat
  start : Nat
  len : Nat
deriving DecidableEq, Repr

/-- The letters of a window; `none` when it does not fit in its chromosome. -/
def windowSeq (g : Genome) (w : Window) : Option (List Char) :=
  match g[w.chr]? with
  | some c => if w.start + w.len ≤ c.seq.length then some ((c.seq.drop w.start).take w.len) else none
  | none => none

/-- Optimal global alignment score of the read against the window. -/
def windowScore (sc : Scoring) (read : List Char) (g : Genome) (w : Window) : Option Int :=
  match windowSeq g w with
  | some ys =>
    match getBestAlignment sc read ys with
    | some best => some best.2
    | none => none
  | none => none

/-- Every window of every chromosome. -/
def allWindows (g : Genome) : List Window :=
  (List.range g.length).flatMap fun c =>
    let n := match g[c]? with
      | some chromosome => chromosome.seq.length
      | none => 0
    (List.range (n + 1)).flatMap fun start =>
      (List.range (n - start + 1)).map fun len => { chr := c, start := start, len := len }

/-- The windows among `ws` whose score is at least `T`, with their scores. -/
def hitsOf (score : Window → Option Int) (T : Int) (ws : List Window) : List (Window × Int) :=
  ws.filterMap fun w =>
    match score w with
    | some s => if T ≤ s then some (w, s) else none
    | none => none

/-- The hit that beats every hit at a different window, if there is one. -/
def selectUnique (hits : List (Window × Int)) : Option (Window × Int) :=
  hits.find? fun a => hits.all fun b => decide (b.2 < a.2) || decide (b.1 = a.1)

/-- Where the read maps, with its score; `none` = unmapped. -/
def mapSpec (sc : Scoring) (T : Int) (g : Genome) (read : List Char) : Option (Window × Int) :=
  selectUnique (hitsOf (windowScore sc read g) T (allWindows g))

end MapSpec
