# Alignment spec — theorem statements for review

Everything here is copied verbatim from `AlignmentSpec.lean` (which compiles
clean; axiom audit shows only propext / Classical.choice / Quot.sound).
Only the *statements* are reproduced — proofs are irrelevant to this review.
The question you are answering for each: **is this the sentence I want to be
true?**

---

## The definitions the theorems talk about

You cannot check a theorem statement without checking the definitions it
mentions, so these four come first. These ARE the spec.

```lean
inductive Step where
  | diag  -- consume a letter from both strings (match or mismatch)
  | gapX  -- gap in x: consume a letter from y only (insertion)
  | gapY  -- gap in y: consume a letter from x only (deletion)

def xConsumed : Step → Nat
  | .diag => 1
  | .gapY => 1
  | .gapX => 0

def yConsumed : Step → Nat
  | .diag => 1
  | .gapX => 1
  | .gapY => 0

-- The validity predicate: a step list is a monotone lattice path over
-- xs and ys exactly when its steps consume all of xs and all of ys.
def IsMonotoneWalk (path : List Step) (xs ys : List Char) : Prop :=
  (path.map xConsumed).sum = xs.length ∧
  (path.map yConsumed).sum = ys.length
```

```lean
structure Scoring where
  matchScore    : Int
  mismatchScore : Int
  gapOpen       : Int   -- a gap run of length k costs gapOpen + k * gapExtend
  gapExtend     : Int

-- Walk one alignment along both strings and add up its score.
-- Carried state: the previous step (that one bit is "affine").
def scoreWalk (sc : Scoring) :
    List Step → List Char → List Char → Option Step → Int
  | [], _, _, _ => 0
  | .diag :: rest, x :: xs, y :: ys, _ =>
      (if x = y then sc.matchScore else sc.mismatchScore)
        + scoreWalk sc rest xs ys (some .diag)
  | .gapX :: rest, xs, _ :: ys, prev =>
      (if prev = some .gapX then sc.gapExtend
       else sc.gapOpen + sc.gapExtend)
        + scoreWalk sc rest xs ys (some .gapX)
  | .gapY :: rest, _ :: xs, ys, prev =>
      (if prev = some .gapY then sc.gapExtend
       else sc.gapOpen + sc.gapExtend)
        + scoreWalk sc rest xs ys (some .gapY)
  | _, _, _, _ => 0   -- unreachable for paths satisfying IsMonotoneWalk

def walkScore (sc : Scoring) (xs ys : List Char) (path : List Step) : Int :=
  scoreWalk sc path xs ys none
```

```lean
-- The frozen reference algorithm: enumerate, score, keep the best.
-- Ties: maxOn? keeps the EARLIEST maximum, so tie policy = enumeration
-- order of allPaths (diag before gapX before gapY, at the earliest
-- position where two alignments differ).
def getBestAlignment (sc : Scoring) (xs ys : List Char) :
    Option (List Step × Int) :=
  ((allPaths xs ys).map fun path => (path, walkScore sc xs ys path)).maxOn?
    fun item => item.2
```

(`allPaths` is the three-way branching enumerator; its definition matters
less to this review because Theorem 1 below characterizes it exactly.)

---

## Theorem 1 — the enumeration is exactly your predicate

```lean
theorem mem_allPaths_iff_isMonotoneWalk
    (path : List Step) (xs ys : List Char) :
    path ∈ allPaths xs ys ↔ IsMonotoneWalk path xs ys
```

**Reading:** a step list appears in the enumeration *if and only if* it
satisfies `IsMonotoneWalk`. The `→` direction: the generator produces no
junk. The `←` direction (completeness): the generator misses nothing —
if `allPaths` silently dropped an alignment, this direction would be
unprovable.

**What to confirm:** that `IsMonotoneWalk` is your definition of "valid
alignment." It only requires the consumption totals to match. There is no
separate monotonicity clause — every step strictly advances, so no step
list can "go backwards"; the only possible defect is consuming too much or
too little of either string.

---

## Theorem 2 — never returns none

```lean
theorem getBestAlignment_returns_some
    (sc : Scoring) (xs ys : List Char) :
    ∃ best : List Step × Int,
      getBestAlignment sc xs ys = some best
```

**Reading:** for every scoring and every pair of strings — including one or
both empty — the algorithm returns something. Rules out the vacuous
always-`none` implementation. (Contrast with the window project, where
empty input returns `none`; here even two empty strings have the empty
alignment, score 0.)

---

## Theorem 3 — the returned pair is a real, honestly scored alignment

```lean
theorem getBestAlignment_returns_a_valid_walk
    (sc : Scoring) (xs ys : List Char)
    (bestPath : List Step) (bestScore : Int)
    (hreturned : getBestAlignment sc xs ys = some (bestPath, bestScore)) :
    IsMonotoneWalk bestPath xs ys ∧
    walkScore sc xs ys bestPath = bestScore
```

**Reading:** whatever the algorithm returns, (a) the path is a valid
alignment of these two strings, and (b) the score in the pair really is
that path's score under `walkScore` — not an unattached number.

---

## Theorem 4 — nothing valid scores higher

```lean
theorem getBestAlignment_returns_a_maximum_score
    (sc : Scoring) (xs ys : List Char)
    (bestPath : List Step) (bestScore : Int)
    (candidate : List Step)
    (hreturned : getBestAlignment sc xs ys = some (bestPath, bestScore))
    (hcandidate : IsMonotoneWalk candidate xs ys) :
    walkScore sc xs ys candidate ≤ bestScore
```

**Reading:** every step list satisfying your predicate scores at most
`bestScore`. Note the statement quantifies over `IsMonotoneWalk`
candidates, not over `allPaths` — the enumeration does not appear.

**Why 3 and 4 are both needed:** 4 alone permits returning score = 10⁹ out
of thin air (nothing beats it, vacuously fine); 3 alone permits returning
any valid-but-terrible alignment. Together: achieved and unbeaten =
optimal.

---

## What the theorems do NOT check (your eyes only)

1. **That `scoreWalk` is the affine cost you intend.** All four theorems
   hold for *any* `Scoring` and would hold equally well if `scoreWalk`
   implemented some other cost. The intended meaning is guarded only by
   your reading of `scoreWalk` plus the witnesses below.
2. **The tie policy.** No theorem pins which optimal alignment is returned
   when several tie; that is fixed by the frozen definition (enumeration
   order: diag, then gapX, then gapY). Future submitters must reproduce it
   exactly under a full-equality contract.
3. **The `o + k·e` convention.** Every gap column pays `gapExtend`; the
   first column of a run additionally pays `gapOpen`. If you wanted
   `o + (k−1)·e`, the spec must change.
4. **End gaps are penalized like any other gaps** (this is global
   alignment; semiglobal/local variants would change this).

## The witnesses (all machine-checked at compile time via #guard)

With `matchScore=2, mismatchScore=-1, gapOpen=-3, gapExtend=-1`:

| Input | Expected | Why |
|---|---|---|
| paths of ABC vs ABBC | 129 paths | Delannoy D(3,4) |
| ABC vs ABBC | `([diag,diag,gapX,diag], 2)` | 3 matches +6, one length-1 gap −4 |
| ACB vs ACB | `([diag,diag,diag], 6)` | matches only |
| ε vs AB | `([gapX,gapX], -5)` | one run: −3 − 2·1 |
| ε vs ε | `([], 0)` | the empty alignment |
| ABBA vs AA | `([diag,gapY,gapY,diag], -1)` | +4 − (3+2·1); adjacent gaps open once — the affine-specific check |

---

**If any statement above is not the sentence you want:** the fix goes in
`AlignmentSpec.lean` Part 1 (spec) — and the proofs get redone against
your corrected statement, not the other way around.
