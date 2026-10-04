import AlignmentWfaOff

/-!
# Banded, array-backed offsets-only wavefront level (layer R)

`nextLevelO` (AlignmentWfaOff.lean) is the full-width offsets-only
level step.  This file gives the executed version on banded arrays of
`Nat` codes (`0` = no cell, `k + 1` = offset `k`) and proves it equal
to `nextLevelO` through a denotation.

Two hops, mirroring the cell-level construction in AlignmentWfa.lean:

* layer B — banded lists of `Option Nat` (`BFront`, `bden`), where the
  banding argument lives (`nextLevelB_den`);
* layer R — banded `Array Nat` (`RFront`, `rtob`), where the encoding
  argument lives (`rtobL_nextLevelR`).

The one new ingredient over the cell-level construction is that the
per-cell map is index-aware (`mapFrom`): entry `i` of a band starting
at `lo` sits on absolute diagonal `lo + i`.
-/

namespace AlignmentSpec

-- ══════════════════════════════════════════════════════════════════
-- Layer B: banded lists of Option Nat
-- ══════════════════════════════════════════════════════════════════

/-- Pad (or truncate) to exactly `len` optional offsets. -/
def padToO (len : Nat) (l : List (Option Nat)) : OFrontW :=
  l.take len ++ List.replicate (len - l.length) none

/-- A banded offsets front: `lo` empty diagonals, then the stored band. -/
structure BFront where
  lo   : Nat
  body : List (Option Nat)

def bden (len : Nat) (f : BFront) : OFrontW :=
  padToO len (List.replicate f.lo none ++ f.body)

/-- `zipWith betterO` extended with implicit trailing `none`s. -/
def zipExtO : List (Option Nat) → List (Option Nat) → List (Option Nat)
  | [], b => b
  | a, [] => a
  | x :: a, y :: b => betterO x y :: zipExtO a b

def zipB : BFront → BFront → BFront
  | ⟨_, []⟩, g => g
  | f, ⟨_, []⟩ => f
  | ⟨p, a⟩, ⟨q, b⟩ =>
      let lo := min p q
      ⟨lo, zipExtO (List.replicate (p - lo) none ++ a)
        (List.replicate (q - lo) none ++ b)⟩

def shiftUpB (f : BFront) : BFront := ⟨f.lo + 1, f.body⟩

def shiftDownB (len : Nat) (f : BFront) : BFront :=
  match f.lo with
  | p + 1 => ⟨p, f.body.take (len - (p + 1))⟩
  | 0 => ⟨0, (f.body.drop 1).take (len - 1)⟩

/-- Index-aware map over the band: entry `i` is on diagonal `lo + i`. -/
def mapB (g : Nat → Nat → Option Nat) (f : BFront) : BFront :=
  ⟨f.lo, mapFrom g f.lo f.body⟩

structure BLevel where
  mf : BFront
  xf : BFront
  yf : BFront

def bdenL (len : Nat) (lv : BLevel) : OLevelW :=
  ⟨bden len lv.mf, bden len lv.xf, bden len lv.yf⟩

def frontAtB (hist : List BLevel) (delta : Nat) (sel : BLevel → BFront) : BFront :=
  match hist[delta - 1]? with
  | some lv => sel lv
  | none => ⟨0, []⟩

def nextLevelB (m n : Nat) (xs ys : List Char) (len : Nat)
    (pe po px : Nat) (hist : List BLevel) : BLevel :=
  let xf := zipB
    (shiftUpB (mapB (pushXO m n) (frontAtB hist pe (·.xf))))
    (shiftUpB (mapB (pushXO m n) (frontAtB hist po (·.mf))))
  let yf := zipB
    (shiftDownB len (mapB (pushYO m n) (frontAtB hist pe (·.yf))))
    (shiftDownB len (mapB (pushYO m n) (frontAtB hist po (·.mf))))
  let base := zipB (zipB (mapB (pushDO m n) (frontAtB hist px (·.mf))) xf) yf
  ⟨mapB (fun t off => some (extO m xs ys t off)) base, xf, yf⟩

def seedB (m : Nat) (xs ys : List Char) : BLevel :=
  ⟨⟨m, [some (lcp xs ys)]⟩, ⟨0, []⟩, ⟨0, []⟩⟩

def bget (f : BFront) (n : Nat) : Option Nat :=
  if n < f.lo then none else (f.body[n - f.lo]?).getD none

def cornerB (m n : Nat) (lv : BLevel) : Bool := bget lv.mf n == some m

-- ── padToO lemmas ──

theorem padToO_zero (l : List (Option Nat)) : padToO 0 l = [] := by
  simp [padToO]

theorem padToO_nil (len : Nat) : padToO len [] = List.replicate len none := by
  simp [padToO]

theorem padToO_succ_cons (len : Nat) (x : Option Nat) (l : List (Option Nat)) :
    padToO (len + 1) (x :: l) = x :: padToO len l := by
  simp [padToO, List.take_succ_cons, Nat.succ_sub_succ]

theorem padToO_succ_nil (len : Nat) :
    padToO (len + 1) [] = none :: padToO len [] := by
  simp [padToO_nil, List.replicate_succ]

theorem padToO_length (len : Nat) (l : List (Option Nat)) :
    (padToO len l).length = len := by
  induction len generalizing l with
  | zero => simp [padToO_zero]
  | succ len ih =>
      cases l with
      | nil => rw [padToO_succ_nil]; simp [ih]
      | cons x l => rw [padToO_succ_cons]; simp [ih]

theorem dropLast_cons_cons' (x y : Option Nat) (l : List (Option Nat)) :
    (x :: y :: l).dropLast = x :: (y :: l).dropLast := by
  simp [List.dropLast]

theorem padToO_dropLast (len : Nat) :
    ∀ l : List (Option Nat), (padToO (len + 1) l).dropLast = padToO len l := by
  induction len with
  | zero =>
      intro l
      cases l with
      | nil => rw [padToO_succ_nil, padToO_zero]; simp
      | cons x l => rw [padToO_succ_cons, padToO_zero]; simp [padToO_zero]
  | succ len ih =>
      intro l
      cases l with
      | nil =>
          rw [padToO_succ_nil, padToO_succ_nil, dropLast_cons_cons',
            ← padToO_succ_nil, ih [], padToO_succ_nil]
      | cons x l =>
          rw [padToO_succ_cons, padToO_succ_cons]
          cases hl : padToO (len + 1) l with
          | nil =>
              have hlen := padToO_length (len + 1) l
              rw [hl] at hlen
              simp at hlen
          | cons y t =>
              rw [dropLast_cons_cons', ← hl, ih l]

theorem padToO_drop_one (len : Nat) (l : List (Option Nat)) :
    (padToO (len + 1) l).drop 1 = padToO len (l.drop 1) := by
  cases l with
  | nil => rw [padToO_succ_nil]; rfl
  | cons x l => rw [padToO_succ_cons]; rfl

theorem padToO_snoc_none (len : Nat) :
    ∀ l : List (Option Nat), padToO len l ++ [none] = padToO (len + 1) (l.take len) := by
  induction len with
  | zero => intro l; simp [padToO_zero, padToO_succ_nil]
  | succ len ih =>
      intro l
      cases l with
      | nil =>
          rw [padToO_succ_nil, List.cons_append, ih []]
          simp [padToO_succ_nil]
      | cons x l =>
          rw [padToO_succ_cons, List.cons_append, ih l,
            List.take_succ_cons, padToO_succ_cons]

theorem padToO_rep (len p : Nat) :
    padToO len (List.replicate p (none : Option Nat)) = List.replicate len none := by
  simp only [padToO, List.take_replicate, List.length_replicate,
    List.replicate_append_replicate]
  rw [show min len p + (len - p) = len from by omega]

theorem padToO_rep_take :
    ∀ (p len : Nat) (body : List (Option Nat)),
      padToO (len + 1) (List.replicate p none ++ body.take (len - p)) =
        padToO (len + 1) ((List.replicate p none ++ body).take len) := by
  intro p
  induction p with
  | zero => intro len body; simp
  | succ p ih =>
      intro len body
      cases len with
      | zero =>
          rw [Nat.zero_sub, List.take_zero, List.take_zero,
            List.append_nil, padToO_rep, padToO_nil]
      | succ len =>
          simp only [List.replicate_succ, List.cons_append,
            Nat.succ_sub_succ, padToO_succ_cons, List.take_succ_cons]
          rw [ih len body]

theorem padToO_rep_singleton :
    ∀ (m len : Nat) (c : Option Nat), m < len →
      padToO len (List.replicate m none ++ [c]) =
        (List.replicate len (none : Option Nat)).set m c := by
  intro m
  induction m with
  | zero =>
      intro len c hlen
      cases len with
      | zero => exact absurd hlen (Nat.lt_irrefl 0)
      | succ len =>
          rw [List.replicate_zero, List.nil_append, padToO_succ_cons,
            padToO_nil, List.replicate_succ]
          rfl
  | succ m ih =>
      intro len c hlen
      cases len with
      | zero => exact absurd hlen (Nat.not_lt_zero _)
      | succ len =>
          rw [List.replicate_succ, List.cons_append, padToO_succ_cons,
            ih len c (Nat.lt_of_succ_lt_succ hlen),
            List.replicate_succ (n := len)]
          rfl

theorem padToO_getElem? :
    ∀ (len n : Nat) (l : List (Option Nat)), n < len →
      (padToO len l)[n]? = some (l[n]?.getD none) := by
  intro len
  induction len with
  | zero => intro n l h; exact absurd h (Nat.not_lt_zero n)
  | succ len ih =>
      intro n l h
      cases l with
      | nil =>
          rw [padToO_succ_nil]
          cases n with
          | zero => rfl
          | succ n =>
              rw [List.getElem?_cons_succ, ih n [] (Nat.lt_of_succ_lt_succ h)]
              simp
      | cons x l =>
          rw [padToO_succ_cons]
          cases n with
          | zero => rfl
          | succ n =>
              rw [List.getElem?_cons_succ, List.getElem?_cons_succ,
                ih n l (Nat.lt_of_succ_lt_succ h)]

-- ── zip lemmas ──

theorem betterO_none_left (b : Option Nat) : betterO none b = b := by
  cases b <;> rfl

theorem betterO_none_right (a : Option Nat) : betterO a none = a := by
  cases a <;> rfl

theorem zipExtO_nil_right (a : List (Option Nat)) : zipExtO a [] = a := by
  cases a <;> rfl

theorem zip_padToO (len : Nat) :
    ∀ a b : List (Option Nat),
      List.zipWith betterO (padToO len a) (padToO len b) = padToO len (zipExtO a b) := by
  induction len with
  | zero => intro a b; simp [padToO_zero]
  | succ len ih =>
      intro a b
      cases a with
      | nil =>
          cases b with
          | nil =>
              rw [padToO_succ_nil, List.zipWith_cons_cons, ih [] []]
              simp [zipExtO, betterO, padToO_succ_nil]
          | cons y b =>
              rw [padToO_succ_nil, padToO_succ_cons, List.zipWith_cons_cons, ih [] b]
              simp [zipExtO, betterO_none_left, padToO_succ_cons]
      | cons x a =>
          cases b with
          | nil =>
              rw [padToO_succ_cons, padToO_succ_nil, List.zipWith_cons_cons, ih a [],
                betterO_none_right, zipExtO_nil_right, zipExtO_nil_right, padToO_succ_cons]
          | cons y b =>
              rw [padToO_succ_cons, padToO_succ_cons, List.zipWith_cons_cons, ih a b]
              simp [zipExtO, padToO_succ_cons]

theorem zipExtO_rep :
    ∀ (k : Nat) (a b : List (Option Nat)),
      zipExtO (List.replicate k none ++ a) (List.replicate k none ++ b) =
        List.replicate k none ++ zipExtO a b := by
  intro k
  induction k with
  | zero => intro a b; rfl
  | succ k ih =>
      intro a b
      simp only [List.replicate_succ, List.cons_append]
      show betterO none none :: _ = _
      rw [show betterO none none = none from rfl, ih]

theorem zipExtO_shift (p q : Nat) (a b : List (Option Nat)) :
    zipExtO (List.replicate p none ++ a) (List.replicate q none ++ b) =
      List.replicate (min p q) none ++
        zipExtO (List.replicate (p - min p q) none ++ a)
          (List.replicate (q - min p q) none ++ b) := by
  rcases Nat.le_total p q with h | h
  · rw [Nat.min_eq_left h]
    obtain ⟨d, rfl⟩ : ∃ d, q = p + d := ⟨q - p, (Nat.add_sub_cancel' h).symm⟩
    rw [Nat.sub_self, Nat.add_sub_cancel_left, ← List.replicate_append_replicate,
      List.append_assoc, zipExtO_rep, List.replicate_zero, List.nil_append]
  · rw [Nat.min_eq_right h]
    obtain ⟨d, rfl⟩ : ∃ d, p = q + d := ⟨p - q, (Nat.add_sub_cancel' h).symm⟩
    rw [Nat.sub_self, Nat.add_sub_cancel_left, ← List.replicate_append_replicate,
      List.append_assoc, zipExtO_rep, List.replicate_zero, List.nil_append]

theorem zipWithO_rep_left (L : OFrontW) :
    List.zipWith betterO (List.replicate L.length none) L = L := by
  induction L with
  | nil => rfl
  | cons x L ih =>
      simp only [List.length_cons, List.replicate_succ, List.zipWith_cons_cons, ih,
        betterO_none_left]

theorem zipWithO_rep_right (L : OFrontW) :
    List.zipWith betterO L (List.replicate L.length none) = L := by
  induction L with
  | nil => rfl
  | cons x L ih =>
      simp only [List.length_cons, List.replicate_succ, List.zipWith_cons_cons, ih,
        betterO_none_right]

theorem bden_rep_nil (len p : Nat) : bden len ⟨p, []⟩ = List.replicate len none := by
  simp [bden, padToO_rep]

theorem bden_length (len : Nat) (f : BFront) : (bden len f).length = len := by
  simp [bden, padToO_length]

theorem bden_zipB (len : Nat) (f g : BFront) :
    bden len (zipB f g) = List.zipWith betterO (bden len f) (bden len g) := by
  obtain ⟨p, a⟩ := f
  obtain ⟨q, b⟩ := g
  cases a with
  | nil =>
      show bden len ⟨q, b⟩ = _
      rw [bden_rep_nil]
      have := zipWithO_rep_left (bden len ⟨q, b⟩)
      rw [bden_length] at this
      exact this.symm
  | cons x a =>
      cases b with
      | nil =>
          show bden len ⟨p, x :: a⟩ = _
          rw [bden_rep_nil]
          have := zipWithO_rep_right (bden len ⟨p, x :: a⟩)
          rw [bden_length] at this
          exact this.symm
      | cons y b =>
          show bden len ⟨min p q, zipExtO _ _⟩ = _
          simp only [bden]
          rw [← zipExtO_shift, zip_padToO]

theorem bden_shiftUpB (len : Nat) (f : BFront) :
    bden (len + 1) (shiftUpB f) = shiftUpO (bden (len + 1) f) := by
  simp only [bden, shiftUpB, shiftUpO, List.replicate_succ, List.cons_append,
    padToO_succ_cons, padToO_dropLast]

theorem bden_shiftDownB (len : Nat) (f : BFront) :
    bden (len + 1) (shiftDownB (len + 1) f) = shiftDownO (bden (len + 1) f) := by
  obtain ⟨lo, body⟩ := f
  cases lo with
  | zero =>
      simp only [bden, shiftDownB, shiftDownO, List.replicate_zero, List.nil_append,
        padToO_drop_one, padToO_snoc_none, Nat.add_sub_cancel]
  | succ p =>
      simp only [bden, shiftDownB, shiftDownO, List.replicate_succ, List.cons_append,
        padToO_drop_one, padToO_snoc_none, List.drop_succ_cons, List.drop_zero,
        Nat.succ_sub_succ, padToO_rep_take]

-- ── index-aware map lemmas ──

theorem mapFrom_padToO (g : Nat → Nat → Option Nat) :
    ∀ (len t : Nat) (l : List (Option Nat)),
      mapFrom g t (padToO len l) = padToO len (mapFrom g t l) := by
  intro len
  induction len with
  | zero => intro t l; simp [padToO_zero, mapFrom]
  | succ len ih =>
      intro t l
      cases l with
      | nil =>
          rw [padToO_succ_nil]
          simp only [mapFrom, Option.bind_none, ih, padToO_succ_nil]
      | cons x l =>
          rw [padToO_succ_cons]
          simp only [mapFrom, ih, padToO_succ_cons]

theorem mapFrom_rep_append (g : Nat → Nat → Option Nat) :
    ∀ (p t : Nat) (l : List (Option Nat)),
      mapFrom g t (List.replicate p none ++ l) =
        List.replicate p none ++ mapFrom g (t + p) l := by
  intro p
  induction p with
  | zero => intro t l; simp
  | succ p ih =>
      intro t l
      simp only [List.replicate_succ, List.cons_append, mapFrom, Option.bind_none, ih]
      rw [show t + 1 + p = t + (p + 1) from by omega]

theorem bden_mapB (len : Nat) (g : Nat → Nat → Option Nat) (f : BFront) :
    bden len (mapB g f) = mapFrom g 0 (bden len f) := by
  simp only [bden, mapB, mapFrom_padToO, mapFrom_rep_append, Nat.zero_add]

theorem frontAtB_den (len : Nat) (hist : List BLevel) (delta : Nat)
    (selB : BLevel → BFront) (selO : OLevelW → OFrontW)
    (hsel : ∀ lv, selO (bdenL len lv) = bden len (selB lv)) :
    bden len (frontAtB hist delta selB) =
      frontAtO len (hist.map (bdenL len)) delta selO := by
  simp only [frontAtB, frontAtO, List.getElem?_map]
  cases hist[delta - 1]? with
  | some lv => simp [hsel]
  | none => simp [bden_rep_nil]

theorem nextLevelB_den (m n : Nat) (xs ys : List Char) (len : Nat)
    (pe po px : Nat) (hist : List BLevel) :
    bdenL (len + 1) (nextLevelB m n xs ys (len + 1) pe po px hist) =
      nextLevelO m n xs ys (len + 1) pe po px (hist.map (bdenL (len + 1))) := by
  simp only [nextLevelB, nextLevelO, bdenL, OLevelW.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [bden_zipB, bden_shiftUpB, bden_shiftDownB, bden_mapB,
      frontAtB_den (len + 1) hist pe (·.xf) (·.xf) (fun _ => rfl),
      frontAtB_den (len + 1) hist po (·.mf) (·.mf) (fun _ => rfl),
      frontAtB_den (len + 1) hist pe (·.yf) (·.yf) (fun _ => rfl),
      frontAtB_den (len + 1) hist px (·.mf) (·.mf) (fun _ => rfl)]

theorem seedB_den (m len : Nat) (xs ys : List Char) (h : m < len) :
    bdenL len (seedB m xs ys) = seedO m len xs ys := by
  simp only [bdenL, seedB, seedO, bden, OLevelW.mk.injEq]
  refine ⟨padToO_rep_singleton m len _ h, ?_, ?_⟩ <;> simp [padToO_nil]

theorem bget_den (len n : Nat) (f : BFront) (h : n < len) :
    (bden len f)[n]? = some (bget f n) := by
  rw [bden, padToO_getElem? len n _ h, bget]
  rcases Nat.lt_or_ge n f.lo with hn | hn
  · rw [if_pos hn, List.getElem?_append_left (by simpa using hn), List.getElem?_replicate]
    simp [hn]
  · rw [if_neg (Nat.not_lt.mpr hn), List.getElem?_append_right (by simpa using hn)]
    simp

theorem cornerB_den (m n len : Nat) (h : n < len) (lv : BLevel) :
    cornerB m n lv = cornerO m n (bdenL len lv) := by
  simp only [cornerB, cornerO, bdenL, bget_den len n lv.mf h]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Option.some.injEq]

-- ══════════════════════════════════════════════════════════════════
-- Layer R: banded arrays of Nat codes (0 = none, k + 1 = offset k)
-- ══════════════════════════════════════════════════════════════════

/-- banded front: entry i is diagonal lo + i; stored value 0 = none, k+1 = offset k -/
structure RFront where
  lo   : Nat
  body : Array Nat
deriving Inhabited, Repr

structure RLevel where
  mf : RFront
  xf : RFront
  yf : RFront
deriving Inhabited, Repr

def decodeR (k : Nat) : Option Nat := if k = 0 then none else some (k - 1)

/-- full-width denotation, truncated/padded to exactly len entries -/
def rdenF (len : Nat) (f : RFront) : OFrontW :=
  padToO len (List.replicate f.lo none ++ f.body.toList.map decodeR)

def rdenL (len : Nat) (lv : RLevel) : OLevelW :=
  ⟨rdenF len lv.mf, rdenF len lv.xf, rdenF len lv.yf⟩

/-- The banded list front an array front denotes. -/
def rtob (f : RFront) : BFront := ⟨f.lo, f.body.toList.map decodeR⟩

def rtobL (lv : RLevel) : BLevel := ⟨rtob lv.mf, rtob lv.xf, rtob lv.yf⟩

theorem rdenL_eq (len : Nat) (lv : RLevel) : rdenL len lv = bdenL len (rtobL lv) := rfl

-- ── executed pieces ──

/-- `betterO` on codes: left-biased max. -/
@[inline] def betterR (a b : Nat) : Nat := if b ≤ a then a else b

def zipExtN : List Nat → List Nat → List Nat
  | [], b => b
  | a, [] => a
  | x :: a, y :: b => betterR x y :: zipExtN a b

def azipExtR (a b : Array Nat) : Array Nat :=
  if a.size ≤ b.size then
    Array.zipWith betterR a b ++ b.extract a.size b.size
  else
    Array.zipWith betterR a b ++ a.extract b.size a.size

def zipR (f g : RFront) : RFront :=
  if f.body.isEmpty then g
  else if g.body.isEmpty then f
  else
    let lo := min f.lo g.lo
    ⟨lo, azipExtR (Array.replicate (f.lo - lo) 0 ++ f.body)
      (Array.replicate (g.lo - lo) 0 ++ g.body)⟩

def shiftUpR (f : RFront) : RFront := ⟨f.lo + 1, f.body⟩

/-- Banded `shiftDownO`; a band that already fits the window is reused
without copying. -/
def shiftDownR (len : Nat) (f : RFront) : RFront :=
  match f.lo with
  | p + 1 =>
      if f.body.size ≤ len - (p + 1) then ⟨p, f.body⟩
      else ⟨p, f.body.extract 0 (len - (p + 1))⟩
  | 0 => ⟨0, f.body.extract 1 (1 + (len - 1))⟩

/-- Index-aware map on codes. -/
def mapR (gR : Nat → Nat → Nat) (f : RFront) : RFront :=
  ⟨f.lo, f.body.mapIdx (fun i a => gR (f.lo + i) a)⟩

@[inline] def pushXR (m n t a : Nat) : Nat :=
  if a = 0 then 0 else
    let off := a - 1
    if joffOf m t off < n then a
    else if 1 ≤ off ∧ 1 ≤ joffOf m t off then off else 0

@[inline] def pushYR (m _n t a : Nat) : Nat :=
  if a = 0 then 0 else
    let off := a - 1
    if off < m then a + 1
    else if 1 ≤ off ∧ 1 ≤ joffOf m t off then a else 0

@[inline] def pushDR (m n t a : Nat) : Nat :=
  if a = 0 then 0 else
    let off := a - 1
    if off < m ∧ joffOf m t off < n then a + 1
    else if 1 ≤ off ∧ 1 ≤ joffOf m t off then a else 0

/-- Longest common prefix of `xa[i..]` and `ya[j..]`, accumulator loop. -/
def lcpArrGo (xa ya : Array Char) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | fuel + 1, i, j, acc =>
      if h : i < xa.size ∧ j < ya.size then
        if xa[i] = ya[j] then lcpArrGo xa ya fuel (i + 1) (j + 1) (acc + 1) else acc
      else acc

@[inline] def lcpArr (xa ya : Array Char) (i j : Nat) : Nat :=
  lcpArrGo xa ya (xa.size - i) i j 0

@[inline] def extR (m : Nat) (xa ya : Array Char) (t a : Nat) : Nat :=
  if a = 0 then 0 else
    let off := a - 1
    off + lcpArr xa ya off (joffOf m t off) + 1

@[inline] def frontAtR (hist : List RLevel) (delta : Nat) (sel : RLevel → RFront) : RFront :=
  match hist[delta - 1]? with
  | some lv => sel lv
  | none => ⟨0, #[]⟩

def nextLevelR (m n : Nat) (xa ya : Array Char) (len pe po px : Nat)
    (hist : List RLevel) : RLevel :=
  let xf := zipR
    (shiftUpR (mapR (pushXR m n) (frontAtR hist pe (·.xf))))
    (shiftUpR (mapR (pushXR m n) (frontAtR hist po (·.mf))))
  let yf := zipR
    (shiftDownR len (mapR (pushYR m n) (frontAtR hist pe (·.yf))))
    (shiftDownR len (mapR (pushYR m n) (frontAtR hist po (·.mf))))
  let base := zipR (zipR (mapR (pushDR m n) (frontAtR hist px (·.mf))) xf) yf
  ⟨mapR (extR m xa ya) base, xf, yf⟩

/-- `len` is unused (the seed band is a singleton); kept for signature
symmetry with `seedO`. -/
def seedR (m _len : Nat) (xa ya : Array Char) : RLevel :=
  ⟨⟨m, #[lcpArr xa ya 0 0 + 1]⟩, ⟨0, #[]⟩, ⟨0, #[]⟩⟩

/-- The code the band holds at absolute diagonal `n` — constant time. -/
@[inline] def rget (f : RFront) (n : Nat) : Nat :=
  if n < f.lo then 0 else (f.body[n - f.lo]?).getD 0

def cornerR (m n : Nat) (lv : RLevel) : Bool := rget lv.mf n == m + 1

-- ── encoding lemmas ──

@[simp] theorem decodeR_zero : decodeR 0 = none := rfl

@[simp] theorem decodeR_succ (a : Nat) : decodeR (a + 1) = some a := by
  simp [decodeR]

theorem decodeR_betterR (a b : Nat) :
    decodeR (betterR a b) = betterO (decodeR a) (decodeR b) := by
  cases a with
  | zero =>
      cases b with
      | zero => rfl
      | succ b => simp [betterR, betterO]
  | succ a =>
      cases b with
      | zero => simp [betterR, betterO]
      | succ b =>
          by_cases h : b ≤ a
          · simp [betterR, betterO, h]
          · simp [betterR, betterO, h]

theorem zipExtN_decode :
    ∀ (a b : List Nat), (zipExtN a b).map decodeR = zipExtO (a.map decodeR) (b.map decodeR) := by
  intro a
  induction a with
  | nil => intro b; cases b <;> simp [zipExtN, zipExtO]
  | cons x a ih =>
      intro b
      cases b with
      | nil => simp [zipExtN, zipExtO]
      | cons y b => simp [zipExtN, zipExtO, ih, decodeR_betterR]

theorem zipExtN_eq_append (la : List Nat) :
    ∀ lb : List Nat,
      zipExtN la lb = List.zipWith betterR la lb ++
        (if la.length ≤ lb.length then lb.drop la.length else la.drop lb.length) := by
  induction la with
  | nil => intro lb; simp [zipExtN]
  | cons x a ih =>
      intro lb
      cases lb with
      | nil => simp [zipExtN]
      | cons y b =>
          simp only [zipExtN, List.zipWith_cons_cons, List.length_cons,
            Nat.add_le_add_iff_right, List.drop_succ_cons, List.cons_append, ih b]

theorem azipExtR_toList (a b : Array Nat) :
    (azipExtR a b).toList = zipExtN a.toList b.toList := by
  unfold azipExtR
  by_cases h : a.size ≤ b.size
  · rw [if_pos h, Array.toList_append, Array.toList_zipWith, Array.toList_extract,
      zipExtN_eq_append, if_pos (by simp only [Array.length_toList]; exact h),
      List.extract_eq_take_drop, Array.length_toList]
    congr 1
    exact List.take_of_length_le (by simp [Array.length_toList])
  · rw [if_neg h, Array.toList_append, Array.toList_zipWith, Array.toList_extract,
      zipExtN_eq_append, if_neg (by simp only [Array.length_toList]; exact h),
      List.extract_eq_take_drop, Array.length_toList]
    congr 1
    exact List.take_of_length_le (by simp [Array.length_toList])

theorem toListN_eq_nil_of_isEmpty (a : Array Nat) (h : a.isEmpty = true) : a.toList = [] := by
  have hs : a.size = 0 := by simpa [Array.isEmpty] using h
  have hl := Array.length_toList (xs := a)
  exact List.eq_nil_of_length_eq_zero (by omega)

theorem toListN_cons_of_not_isEmpty (a : Array Nat) (h : a.isEmpty = false) :
    ∃ x t, a.toList = x :: t := by
  have hs : a.size ≠ 0 := by simpa [Array.isEmpty] using h
  cases ht : a.toList with
  | nil =>
      exfalso
      have hl := Array.length_toList (xs := a)
      rw [ht] at hl
      simp at hl
      exact hs hl.symm
  | cons x t => exact ⟨x, t, rfl⟩

theorem rtob_zipR (f g : RFront) : rtob (zipR f g) = zipB (rtob f) (rtob g) := by
  obtain ⟨fp, fb⟩ := f
  obtain ⟨gp, gb⟩ := g
  unfold zipR
  cases hf : fb.isEmpty with
  | true =>
      simp only [if_true]
      have h0 := toListN_eq_nil_of_isEmpty fb hf
      show rtob ⟨gp, gb⟩ = zipB ⟨fp, fb.toList.map decodeR⟩ (rtob ⟨gp, gb⟩)
      rw [h0]
      rfl
  | false =>
      obtain ⟨x, ft, hft⟩ := toListN_cons_of_not_isEmpty fb hf
      cases hg : gb.isEmpty with
      | true =>
          simp only [if_false, if_true, Bool.false_eq_true]
          have h0 := toListN_eq_nil_of_isEmpty gb hg
          show (⟨fp, fb.toList.map decodeR⟩ : BFront) =
            zipB ⟨fp, fb.toList.map decodeR⟩ ⟨gp, gb.toList.map decodeR⟩
          rw [h0, hft]
          rfl
      | false =>
          obtain ⟨y, gt, hgt⟩ := toListN_cons_of_not_isEmpty gb hg
          simp only [if_false, Bool.false_eq_true]
          show (⟨min fp gp,
            (azipExtR (Array.replicate (fp - min fp gp) 0 ++ fb)
              (Array.replicate (gp - min fp gp) 0 ++ gb)).toList.map decodeR⟩ : BFront) =
            zipB ⟨fp, fb.toList.map decodeR⟩ ⟨gp, gb.toList.map decodeR⟩
          rw [azipExtR_toList, Array.toList_append, Array.toList_append,
            Array.toList_replicate, Array.toList_replicate, zipExtN_decode,
            List.map_append, List.map_append, List.map_replicate, List.map_replicate,
            decodeR_zero, hft, hgt, List.map_cons, List.map_cons]
          rfl

theorem rtob_shiftUpR (f : RFront) : rtob (shiftUpR f) = shiftUpB (rtob f) := rfl

theorem rtob_shiftDownR (len : Nat) (f : RFront) :
    rtob (shiftDownR len f) = shiftDownB len (rtob f) := by
  obtain ⟨lo, body⟩ := f
  cases lo with
  | zero =>
      simp only [shiftDownR, shiftDownB, rtob, Array.toList_extract,
        List.extract_eq_take_drop, List.map_take, List.map_drop]
      rw [show 1 + (len - 1) - 1 = len - 1 from by omega]
  | succ p =>
      simp only [shiftDownR, shiftDownB, rtob]
      split
      · rename_i h
        rw [List.take_of_length_le (by rw [List.length_map, Array.length_toList]; exact h)]
      · simp only [Array.toList_extract, List.extract_eq_take_drop, List.drop_zero, Nat.sub_zero,
          List.map_take]

theorem mapIdx_decode (g : Nat → Nat → Option Nat) (gR : Nat → Nat → Nat)
    (hg : ∀ t a, decodeR (gR t a) = (decodeR a).bind (g t)) :
    ∀ (l : List Nat) (t : Nat),
      (List.mapIdx (fun i a => gR (t + i) a) l).map decodeR = mapFrom g t (l.map decodeR) := by
  intro l
  induction l with
  | nil => intro t; simp [mapFrom]
  | cons x l ih =>
      intro t
      simp only [List.mapIdx_cons, List.map_cons, mapFrom, Nat.add_zero, hg]
      congr 1
      have hfun : (fun i a => gR (t + (i + 1)) a) = (fun i a => gR (t + 1 + i) a) := by
        funext i a
        rw [show t + (i + 1) = t + 1 + i from by omega]
      rw [hfun, ih]

theorem rtob_mapR (g : Nat → Nat → Option Nat) (gR : Nat → Nat → Nat)
    (hg : ∀ t a, decodeR (gR t a) = (decodeR a).bind (g t)) (f : RFront) :
    rtob (mapR gR f) = mapB g (rtob f) := by
  simp only [rtob, mapR, mapB, Array.toList_mapIdx, mapIdx_decode g gR hg]

theorem frontAtR_den (hist : List RLevel) (delta : Nat)
    (selR : RLevel → RFront) (selB : BLevel → BFront)
    (hsel : ∀ lv, selB (rtobL lv) = rtob (selR lv)) :
    rtob (frontAtR hist delta selR) = frontAtB (hist.map rtobL) delta selB := by
  simp only [frontAtR, frontAtB, List.getElem?_map]
  cases hist[delta - 1]? with
  | some lv => simp [hsel]
  | none => rfl

-- ── push / extension on codes ──

theorem decodeR_pushXR (m n t a : Nat) :
    decodeR (pushXR m n t a) = (decodeR a).bind (pushXO m n t) := by
  cases a with
  | zero => rfl
  | succ a =>
      simp only [pushXR, pushXO, decodeR_succ, Option.bind_some, Nat.succ_ne_zero, if_false,
        Nat.add_sub_cancel]
      by_cases h1 : joffOf m t a < n
      · simp [h1]
      · by_cases h2 : 1 ≤ a ∧ 1 ≤ joffOf m t a
        · have ha : a ≠ 0 := by omega
          simp [h1, h2, decodeR, ha]
        · simp [h1, h2]

theorem decodeR_pushYR (m n t a : Nat) :
    decodeR (pushYR m n t a) = (decodeR a).bind (pushYO m n t) := by
  cases a with
  | zero => rfl
  | succ a =>
      simp only [pushYR, pushYO, decodeR_succ, Option.bind_some, Nat.succ_ne_zero, if_false,
        Nat.add_sub_cancel]
      by_cases h1 : a < m
      · simp [h1]
      · by_cases h2 : 1 ≤ a ∧ 1 ≤ joffOf m t a
        · simp [h1, h2]
        · simp [h1, h2]

theorem decodeR_pushDR (m n t a : Nat) :
    decodeR (pushDR m n t a) = (decodeR a).bind (pushDO m n t) := by
  cases a with
  | zero => rfl
  | succ a =>
      simp only [pushDR, pushDO, decodeR_succ, Option.bind_some, Nat.succ_ne_zero, if_false,
        Nat.add_sub_cancel]
      by_cases h1 : a < m ∧ joffOf m t a < n
      · simp [h1]
      · by_cases h2 : 1 ≤ a ∧ 1 ≤ joffOf m t a
        · simp [h1, h2]
        · simp [h1, h2]

theorem lcp_nil_right (xs : List Char) : lcp xs [] = 0 := by
  cases xs <;> rfl

theorem lcpArrGo_eq (xa ya : Array Char) :
    ∀ (fuel i j acc : Nat), xa.size ≤ i + fuel →
      lcpArrGo xa ya fuel i j acc = acc + lcp (xa.toList.drop i) (ya.toList.drop j) := by
  intro fuel
  induction fuel with
  | zero =>
      intro i j acc h
      rw [List.drop_of_length_le (l := xa.toList) (by rw [Array.length_toList]; omega)]
      rfl
  | succ fuel ih =>
      intro i j acc h
      simp only [lcpArrGo]
      split
      · rename_i hij
        rw [List.drop_eq_getElem_cons (l := xa.toList) (i := i)
            (by rw [Array.length_toList]; exact hij.1),
          List.drop_eq_getElem_cons (l := ya.toList) (i := j)
            (by rw [Array.length_toList]; exact hij.2)]
        simp only [lcp, Array.getElem_toList]
        split
        · rw [ih (i + 1) (j + 1) (acc + 1) (by omega)]
          omega
        · rfl
      · rename_i hij
        rcases Nat.lt_or_ge i xa.size with hi | hi
        · have hj : ya.size ≤ j := Nat.le_of_not_lt (fun hc => hij ⟨hi, hc⟩)
          rw [List.drop_of_length_le (l := ya.toList) (by rw [Array.length_toList]; exact hj),
            lcp_nil_right]
          rfl
        · rw [List.drop_of_length_le (l := xa.toList) (by rw [Array.length_toList]; exact hi)]
          rfl

theorem lcpArr_eq (xa ya : Array Char) (i j : Nat) :
    lcpArr xa ya i j = lcp (xa.toList.drop i) (ya.toList.drop j) := by
  unfold lcpArr
  rw [lcpArrGo_eq xa ya _ i j 0 (by omega), Nat.zero_add]

theorem decodeR_extR (m : Nat) (xs ys : List Char) (xa ya : Array Char)
    (hx : xa.toList = xs) (hy : ya.toList = ys) (t a : Nat) :
    decodeR (extR m xa ya t a) = (decodeR a).bind (fun off => some (extO m xs ys t off)) := by
  cases a with
  | zero => rfl
  | succ a =>
      simp only [extR, extO, decodeR_succ, Option.bind_some, Nat.succ_ne_zero, if_false,
        Nat.add_sub_cancel, lcpArr_eq, hx, hy]

-- ── level step ──

theorem rtobL_nextLevelR (m n : Nat) (xs ys : List Char) (xa ya : Array Char)
    (hx : xa.toList = xs) (hy : ya.toList = ys) (len pe po px : Nat) (hist : List RLevel) :
    rtobL (nextLevelR m n xa ya len pe po px hist) =
      nextLevelB m n xs ys len pe po px (hist.map rtobL) := by
  simp only [nextLevelR, nextLevelB, rtobL, BLevel.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [rtob_zipR, rtob_shiftUpR, rtob_shiftDownR,
      rtob_mapR (pushXO m n) (pushXR m n) (decodeR_pushXR m n),
      rtob_mapR (pushYO m n) (pushYR m n) (decodeR_pushYR m n),
      rtob_mapR (pushDO m n) (pushDR m n) (decodeR_pushDR m n),
      rtob_mapR (fun t off => some (extO m xs ys t off)) (extR m xa ya)
        (decodeR_extR m xs ys xa ya hx hy),
      frontAtR_den hist pe (·.xf) (·.xf) (fun _ => rfl),
      frontAtR_den hist po (·.mf) (·.mf) (fun _ => rfl),
      frontAtR_den hist pe (·.yf) (·.yf) (fun _ => rfl),
      frontAtR_den hist px (·.mf) (·.mf) (fun _ => rfl)]

theorem rdenL_nextLevelR (m n : Nat) (xs ys : List Char) (xa ya : Array Char)
    (hx : xa.toList = xs) (hy : ya.toList = ys) (len pe po px : Nat) (hist : List RLevel)
    (hlen : len = m + n + 1) :
    rdenL len (nextLevelR m n xa ya len pe po px hist) =
      nextLevelO m n xs ys len pe po px (hist.map (rdenL len)) := by
  subst hlen
  rw [rdenL_eq, rtobL_nextLevelR m n xs ys xa ya hx hy, nextLevelB_den, List.map_map]
  rfl

theorem rtobL_seedR (m len : Nat) (xs ys : List Char) (xa ya : Array Char)
    (hx : xa.toList = xs) (hy : ya.toList = ys) :
    rtobL (seedR m len xa ya) = seedB m xs ys := by
  simp [rtobL, rtob, seedR, seedB, lcpArr_eq, hx, hy]

theorem rdenL_seedR (m len : Nat) (xs ys : List Char) (xa ya : Array Char)
    (hx : xa.toList = xs) (hy : ya.toList = ys) (hm : m < len) :
    rdenL len (seedR m len xa ya) = seedO m len xs ys := by
  rw [rdenL_eq, rtobL_seedR m len xs ys xa ya hx hy, seedB_den m len xs ys hm]

theorem decodeR_rget (f : RFront) (n : Nat) : decodeR (rget f n) = bget (rtob f) n := by
  simp only [rget, bget, rtob, List.getElem?_map, ← Array.getElem?_toList]
  split
  · rfl
  · cases f.body.toList[n - f.lo]? with
    | none => rfl
    | some k => rfl

theorem cornerR_eqB (m n : Nat) (lv : RLevel) : cornerR m n lv = cornerB m n (rtobL lv) := by
  simp only [cornerR, cornerB, rtobL, ← decodeR_rget]
  generalize rget lv.mf n = k
  apply Bool.eq_iff_iff.mpr
  cases k with
  | zero => simp
  | succ k => simp

theorem cornerR_eq (m n len : Nat) (hn : n < len) (lv : RLevel) :
    cornerR m n lv = cornerO m n (rdenL len lv) := by
  rw [cornerR_eqB, rdenL_eq, cornerB_den m n len hn]

end AlignmentSpec

#print axioms AlignmentSpec.rdenL_nextLevelR
#print axioms AlignmentSpec.rdenL_seedR
#print axioms AlignmentSpec.cornerR_eq
