import PairGuarQE
import PairRouter
import MateFloor
import AlignmentCigarCheck

/-!
# The tier router (`tierPair`): mode RTX's decisions, proved

Every pair gets a tag with what is proved about it (`tierPair_sound`):

* `T0`: a mate was trimmed away (`ReadTrim`; reason `trimmedAway`).
* `T1`: the router RT (`routeG` with `kpKerB`) mapped the pair: `pairSpecT` at RT's caps.
* `T1g` / `T1gm`: the fast pair guarantee `pairGQC` at `G0 ≤ 7` (`G0 = G`, or `0` with suffix `z`
  when the enumerated mate is too short for `G`): the unique proper pair `pairSpecUT` at every caps
  `≥ G0`, or a proved tie (`PairTieOk`).  The enumerated mate is on the fast path (`fastT G0`).
* `T2`: both mates have a ceiling (a placement within it exists; a CIGAR re-checked by `checkRuns`
  when one is reported) and proved floors.
* `T3`: proved floors only.

Floors come from: empty seed lookups (`floor_look`), RT's `noHit` at cap `c` (`c + 1`, from
`routeKPB_ok`), RT's known best (`noPartner`), the guarantee's completed enumeration of one mate
(its hits within `G0` are exactly `hitsBoth (−G0)`; none: 4 or 8, by the gapless score arithmetic
above −8), and pair > `G0` when the guarantee found no proper pair.  Untrusted inputs (any function
gives a sound answer): the budget gate, the mate-order preference of the guarantee, the rarest-seed
ceiling diagonal, and the tier 2 heuristic, whose alignments are re-checked here with `checkRuns`.
Suffix `x`: the guarantee applies to neither mate (both too short).
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec MapSpec.Packed

/-- One mate of the tier router, as the bench prints it: `st` (U unique best, B bounds, S no seed,
P pair guarantee), display cap, floor `cd` (and its parts `pU` empty lookups, `pC` enumeration, `pD`
RT no hit), `pen`, the placement `pl`, ceiling `pH` (1000000 = none) and its source `pR`, `rs` (the
ceiling's alignment re-checked), `cg` (`pl` is an alignment with CIGAR `runs`). -/
structure MateX where
  st : String := "S"
  cap : Nat := 0
  cd : Nat := 0
  pen : Nat := 0
  pl : Option (Placement × Int) := none
  pU : Nat := 1000000
  pC : Nat := 1000000
  pH : Nat := 1000000
  pD : Nat := 1000000
  pR : Nat := 1000000
  rs : Bool := true
  cg : Bool := false
  runs : List (Step × Nat) := []
deriving Inhabited

/-- A ceiling is claimed. -/
def MateX.ok (m : MateX) : Bool := decide (m.pH < 1000000) && m.rs

/-- The proved checker on the runs: the read against letters `[st, st + len)` of `G`. -/
def rescoreRuns (R : ByteArray) (G : PGen) (st len : Nat) (runs : List (Step × Nat)) : Option Int :=
  let xa : Array Char := (List.range R.size).toArray.map fun i => Char.ofNat (R.get! i).toNat
  let ya : Array Char := (List.range len).toArray.map fun i => Char.ofNat (G.get (st + i)).toNat
  AlignmentSpec.checkRuns sc0 xa ya runs ⟨0, 0, none, 0⟩

/-- An alignment `h` with CIGAR `runs` re-checked: inside its chromosome, score ≤ 0, and `checkRuns`
gives its score (`R` forward read, `Rr` its reverse complement). -/
def chkCand (pgs : Array PGen) (R Rr : ByteArray) (h : Placement × Int) (runs : List (Step × Nat)) : Bool :=
  decide (h.1.1.chr < pgs.size) && decide (h.1.1.start + h.1.1.len ≤ pgs[h.1.1.chr]!.n) && decide (h.2 ≤ 0) &&
    rescoreRuns (if h.1.2 = Strand.fwd then R else Rr) pgs[h.1.1.chr]! h.1.1.start h.1.1.len runs == some h.2

/-- A mate's ceiling replaced by a re-checked alignment (source `src`). -/
def MateX.withC (m : MateX) (h : Placement × Int) (src : Nat) (runs : List (Step × Nat)) : MateX :=
  { m with st := if m.st == "U" then "B" else m.st, pl := some h, pH := (-h.2).toNat, pR := src, rs := true,
           cg := true, runs := runs }

/-- An alignment proposed by the (untrusted) tier 2 heuristic. -/
structure Cand where
  pl : Placement × Int
  runs : List (Step × Nat)
  src : Nat

/-- A proposal is taken only when it passes `chkCand`. -/
def applyC (pgs : Array PGen) (R Rr : ByteArray) (m : MateX) : Option Cand → MateX
  | some c => if chkCand pgs R Rr c.pl c.runs then m.withC c.pl c.src c.runs else m
  | none => m

/-- Blocks of one strand `Rx` (read length `n`, `n / 25` blocks) whose seed lookup is empty. -/
def emptyCnt (pk : PkMz) (n : Nat) (Rx : ByteArray) (pp : Array MzP) : Nat :=
  ((List.range (n / 25)).filter fun j => (pp[j]!).ok && LookG.size pk pp[j]! == 0 &&
    (LookG.look pk ByteArray.empty Rx (j * (n / (n / 25))) (n - j * (n / (n / 25))) pp[j]!).isEmpty).length

/-- A gapless alignment at virtual chromosome `v` (`< nc`: forward), start `st`, `mm` mismatches, and
whether it passes `chkCand`. -/
def alnC (pgs : Array PGen) (R Rr : ByteArray) (v st mm : Nat) : (Placement × Int) × Bool :=
  let h := (decB pgs.size ⟨v, st, R.size⟩, -((4 * mm : Nat) : Int))
  (h, chkCand pgs R Rr h [(Step.diag, R.size)])

/-- The best-scoring entry of a list. -/
def bestOf (l : List (Placement × Int)) : Option (Placement × Int) :=
  l.foldl (fun acc x => match acc with | some y => if y.2 < x.2 then some x else acc | none => some x) none

/-- The enumerated mate's floor and best hit (virtual chromosome, start, mismatches) from its exact hits
within `G0` (none: 4 when `G0 < 4`, else 8). -/
def gxOf (nc G0 : Nat) (lX : List (Placement × Int)) : Nat × Option (Nat × Nat × Nat) :=
  match bestOf lX with
  | none => (if G0 / 4 == 0 then 4 else 8, none)
  | some (p, sc) =>
    let pen := (-sc).toNat
    (pen, some ((if decide (p.2 = Strand.fwd) then 0 else nc) + p.1.chr, p.1.start, pen / 4))

/-- A gapless candidate `(v, st, mm)` (source `src`) replaces the ceiling when smaller; its alignment is
re-checked (`rs`). -/
def upA (pgs : Array PGen) (R Rr : ByteArray) (x : MateX) (v st mm src : Nat) : MateX :=
  if 4 * mm < x.pH then
    let a := alnC pgs R Rr v st mm
    { x with pH := 4 * mm, pR := src, pl := some a.1, rs := a.2, cg := true, runs := [(Step.diag, R.size)] }
  else x

/-- A mate's floors with no unique best: empty seed lookups (on the fast path), RT's `noHit` at its
cap `c` (`nh`), and the guarantee's enumeration (`gx`). -/
def mateB0 (pk : PkMz) (R : ByteArray) (s : PrepM MzP) (cap c : Nat) (nh : Bool)
    (gx : Option (Nat × Option (Nat × Nat × Nat))) : MateX :=
  let fC := if nh then c + 1 else 0
  let fX := (gx.map (·.1)).getD 0
  let ft := fastT 0 R
  let fE := if ft then 4 * min (emptyCnt pk R.size R s.ps) (emptyCnt pk R.size s.Rr s.pr) else 0
  { st := if ft then "B" else "S", cap := cap, cd := max (max fE fC) fX, pU := fE, pC := fX, pD := fC, pR := 0 }

/-- Ceiling `c` when RT found a hit within its cap `c`. -/
def capStep (x : MateX) (c : Nat) (capC : Bool) : MateX := if capC then { x with pH := c, pR := 2 } else x

/-- The guarantee's best hit as a ceiling candidate. -/
def gxStep (pgs : Array PGen) (R Rr : ByteArray) (x : MateX) : Option (Nat × Option (Nat × Nat × Nat)) → MateX
  | some (_, some (v, st, mm)) => upA pgs R Rr x v st mm 3
  | _ => x

/-- The rarest-seed diagonal `(v, D, mm)` as a ceiling candidate. -/
def ceilStep (pgs : Array PGen) (R Rr : ByteArray) (x : MateX) : Option (Nat × Nat × Nat) → MateX
  | some (v, D, mm) => upA pgs R Rr x v (D - R.size) mm 4
  | none => x

/-- One mate's floor and ceilings.  `cap`: display cap; `c`: RT's cap for this mate; `nh`: RT found
no hit within `c`; `capC`: RT found a hit within `c` (tie / not proper); `kn`: RT's unique best;
`gx`: the guarantee's floor and best hit; `ceil`: a candidate gapless diagonal (untrusted). -/
def mateT (pk : PkMz) (pgs : Array PGen) (R : ByteArray) (s : PrepM MzP) (cap c : Nat) (nh capC : Bool)
    (kn : Option (Placement × Int)) (gx : Option (Nat × Option (Nat × Nat × Nat)))
    (ceil : Unit → Option (Nat × Nat × Nat)) : MateX :=
  match kn with
  | some a =>
    { st := "U", cap := cap, cd := (-a.2).toNat, pen := (-a.2).toNat, pl := some a, pH := (-a.2).toNat, pR := 1 }
  | none =>
    ceilStep pgs R s.Rr (gxStep pgs R s.Rr (capStep (mateB0 pk R s cap c nh gx) c capC) gx)
      (if fastT 0 R then ceil () else none)

/-- RT's reason says mate `mt` has no hit within its cap. -/
def nhOf (mt : Mate) : Option (Reason × Option (Placement × Int)) → Bool
  | some (.noHit m, _) => m == mt
  | _ => false

/-- RT's reason says mate `mt` has a hit within its cap (a tie, or not proper). -/
def ccOf (mt : Mate) : Option (Reason × Option (Placement × Int)) → Bool
  | some (.tie m, _) => m == mt
  | some (.notProper, _) => true
  | _ => false

/-- RT's unique best of mate `mt` (its partner had no proper hit). -/
def knOf (mt : Mate) : Option (Reason × Option (Placement × Int)) → Option (Placement × Int)
  | some (.noPartner m, k) => if m.other == mt then k else none
  | _ => none

/-- Tags. -/
inductive Tag where
  | t0 | t1 | t1g | t1gm | t2 | t3
deriving DecidableEq, Repr, Inhabited

def Tag.str : Tag → String
  | .t0 => "T0" | .t1 => "T1" | .t1g => "T1g" | .t1gm => "T1gm" | .t2 => "T2" | .t3 => "T3"

/-- A routed pair: tag, suffix (`""`, `z` guarantee at 0, `x` no guarantee), mates, RT's or the
trimmer's reason, RT's caps, the guarantee's `G0` and enumerated mate (`sw`: mate 2), and `pf = some G0`
when the guarantee found no proper pair within `G0`. -/
structure TierOut where
  tag : Tag
  sfx : String := ""
  m1 : MateX := {}
  m2 : MateX := {}
  why : Option Reason := none
  c1 : Nat := 0
  c2 : Nat := 0
  g0 : Nat := 0
  sw : Bool := false
  pf : Option Nat := none
deriving Inhabited

def TierOut.tagStr (t : TierOut) : String := t.tag.str ++ t.sfx

/-- Settings and untrusted helpers of the tier router.  `pg`: the guarantee's `G` (none: off; used
when `≤ 7`); `xZ`: fall back to the guarantee at 0; `gate`: pairs that skip RT (any gate is sound);
`pref`: when both mates are on the fast path at `G0`, enumerate mate 2 (`true`); `ceil`: a gapless
diagonal `(v, D, mm)` as a ceiling candidate (re-checked); `heur`: the tier 2 heuristic's alignments
(re-checked). -/
structure TierCfg where
  rcfg : RouteCfg
  j1 : Bool := false
  j2 : Bool := false
  hint : Bool := true
  lo : Nat
  hi : Nat
  usl : Nat := 0
  pg : Option Nat := some 4
  xZ : Bool := true
  gate : ByteArray → ByteArray → Bool := fun _ _ => false
  pref : Nat → ByteArray → ByteArray → PrepM MzP → PrepM MzP → Bool := fun _ _ _ _ _ => false
  ceil : ByteArray → PrepM MzP → Option (Nat × Nat × Nat) := fun _ _ => none
  heur : ByteArray → ByteArray → PrepM MzP → PrepM MzP → MateX → MateX → Option Cand × Option Cand :=
    fun _ _ _ _ _ _ => (none, none)

section router
variable (cfg : TierCfg) (pk : PkMz) (offs : Array Nat) (pgs : Array PGen)

/-- RT's kernel (pass `j`: the anchor join pre-check). -/
def tierKer (j : Bool) : PassKer :=
  kpKerB cfg.lo cfg.hi pk (fun a b => ((pk, a, b) : RgMz)) ByteArray.empty offs pgs j cfg.hint

/-- RT (mode RT of the bench). -/
def tierRT (a b : ByteArray) : Routed :=
  routeG cfg.rcfg (tierKer cfg pk offs pgs cfg.j1) (tierKer cfg pk offs pgs cfg.j2) cfg.lo cfg.hi (some a) (some b)

/-- The guarantee at `G0` with the enumerated mate (none: neither mate on the fast path at `G0`). -/
def tierG (G0 : Nat) (a b : ByteArray) (s1 s2 : PrepM MzP) :
    Option (Bool × (Option PairHit × Bool × List (Placement × Int))) :=
  let f1 := fastT G0 a
  let f2 := fastT G0 b
  if !(f1 || f2) then none else
  let swap := if f1 && f2 then cfg.pref G0 a b s1 s2 else !f1
  (pairGQC dcost0 cfg.usl cfg.lo cfg.hi G0 swap (pk : PkMzR) offs pgs a b).map fun v => (swap, v)

/-- Floors and ceilings of both mates, then the heuristic: T2 when both claim a ceiling, else T3. -/
def tierB (a b : ByteArray) (s1 s2 : PrepM MzP) (rk : Option (Reason × Option (Placement × Int))) (c1 c2 : Nat)
    (g1 g2 : Option (Nat × Option (Nat × Nat × Nat))) : Tag × MateX × MateX :=
  let m1 := mateT pk pgs a s1 (cfg.rcfg.cap1 a.size) c1 (nhOf .one rk) (ccOf .one rk) (knOf .one rk) g1
    (fun _ => cfg.ceil a s1)
  let m2 := mateT pk pgs b s2 (cfg.rcfg.cap1 b.size) c2 (nhOf .two rk) (ccOf .two rk) (knOf .two rk) g2
    (fun _ => cfg.ceil b s2)
  let h := cfg.heur a b s1 s2 m1 m2
  let m1 := applyC pgs a s1.Rr m1 h.1
  let m2 := applyC pgs b s2.Rr m2 h.2
  (if m1.ok && m2.ok then .t2 else .t3, m1, m2)

/-- The guarantee at `G`, else at 0 (suffix `z`), else none (suffix `x`). -/
def tierPick (G : Nat) (a b : ByteArray) (s1 s2 : PrepM MzP) :
    Nat × String × Option (Bool × (Option PairHit × Bool × List (Placement × Int))) :=
  match tierG cfg pk offs pgs G a b s1 s2 with
  | some v => (G, "", some v)
  | none => if 0 < G && cfg.xZ then (0, "z", tierG cfg pk offs pgs 0 a b s1 s2) else (G, "x", none)

/-- Pairs RT did not map (or skipped): the guarantee, then floors and ceilings. -/
def tierRest (a b : ByteArray) (rk : Option (Reason × Option (Placement × Int))) (c1 c2 : Nat) : TierOut :=
  let s1 : PrepM MzP := prepMate pk a
  let s2 : PrepM MzP := prepMate pk b
  let why := rk.map (·.1)
  let plain := fun (sfx : String) =>
    let t := tierB cfg pk pgs a b s1 s2 rk c1 c2 none none
    ({ tag := t.1, sfx := sfx, m1 := t.2.1, m2 := t.2.2, why := why, c1 := c1, c2 := c2 } : TierOut)
  match cfg.pg with
  | none => plain ""
  | some G =>
    if 7 < G then plain "" else
    match tierPick cfg pk offs pgs G a b s1 s2 with
    | (_, _, none) => plain "x"
    | (G0, sfx, some (swap, (r, seen, lX))) =>
      match r with
      | some (x, y) =>
        { tag := .t1g, sfx := sfx, why := why, c1 := c1, c2 := c2, g0 := G0, sw := swap,
          m1 := { st := "P", cap := cfg.rcfg.cap1 a.size, pen := (-x.2).toNat, pl := some x },
          m2 := { st := "P", cap := cfg.rcfg.cap1 b.size, pen := (-y.2).toNat, pl := some y } }
      | none =>
        if seen then
          { tag := .t1gm, sfx := sfx, why := why, c1 := c1, c2 := c2, g0 := G0, sw := swap,
            m1 := { st := "P", cap := cfg.rcfg.cap1 a.size }, m2 := { st := "P", cap := cfg.rcfg.cap1 b.size } }
        else
          let gx := gxOf pgs.size G0 lX
          let t := if swap then tierB cfg pk pgs a b s1 s2 rk c1 c2 none (some gx)
            else tierB cfg pk pgs a b s1 s2 rk c1 c2 (some gx) none
          { tag := t.1, sfx := sfx, m1 := t.2.1, m2 := t.2.2, why := why, c1 := c1, c2 := c2, g0 := G0,
            sw := swap, pf := some G0 }

/-- **The tier router** (mode RTX): trimmed-away mates (T0); the gate; RT (T1); the guarantee (T1g,
T1gm); floors, ceilings and the heuristic (T2, T3). -/
def tierPair (O1 O2 : Option ByteArray) : TierOut :=
  match O1, O2 with
  | none, _ => { tag := .t0, why := some (.trimmedAway .one) }
  | _, none => { tag := .t0, why := some (.trimmedAway .two) }
  | some a, some b =>
    if cfg.gate a b then tierRest cfg pk offs pgs a b none 0 0 else
    let r := tierRT cfg pk offs pgs a b
    match r.out with
    | .mapped (x, y) =>
      { tag := .t1, why := none, c1 := r.c1, c2 := r.c2,
        m1 := { st := "U", cap := cfg.rcfg.cap1 a.size, cd := cfg.rcfg.cap1 a.size, pen := (-x.2).toNat, pl := some x },
        m2 := { st := "U", cap := cfg.rcfg.cap1 b.size, cd := cfg.rcfg.cap1 b.size, pen := (-y.2).toNat, pl := some y } }
    | .unmapped rs k => tierRest cfg pk offs pgs a b (some (rs, k)) r.c1 r.c2

end router

/-! ## What the tags mean -/

/-- Every placement of the mate (any score) has penalty at least `f`. -/
def MateFloor (g : Genome) (m : List Char) (f : Nat) : Prop :=
  ∀ T, ∀ x ∈ hitsBoth sc0 T g m, (f : Int) ≤ -x.2

/-- The read on a strand. -/
def strandRead (m : List Char) : Strand → List Char
  | .fwd => m
  | .rev => revComp m

/-- A reported CIGAR is a real alignment of the read (on the placement's strand) to the
placement's window, with the reported score (`checkRuns_sound`). -/
def CigarOk (g : Genome) (m : List Char) (x : Placement × Int) (runs : List (Step × Nat)) : Prop :=
  ∃ ys, windowSeq g x.1.1 = some ys ∧ IsMonotoneWalk (expandCigar runs.toArray) (strandRead m x.1.2) ys ∧
    walkScore sc0 (strandRead m x.1.2) ys (expandCigar runs.toArray) = x.2

/-- What a claimed ceiling means: a placement within it exists; a reported alignment is a real one. -/
def CeilEv (g : Genome) (m : List Char) (t : MateX) : Prop :=
  t.ok = true → hitsBoth sc0 (-(t.pH : Int)) g m ≠ [] ∧
    (t.cg = true → ∃ x, t.pl = some x ∧ x.2 = -(t.pH : Int) ∧ CigarOk g m x t.runs)

/-- A ceiling (tier 2). -/
def CeilOk (g : Genome) (m : List Char) (t : MateX) : Prop := t.ok = true ∧ CeilEv g m t

/-- Proved floors: per mate, and pair > `G0` when the guarantee found no proper pair. -/
def FloorOk (usl lo hi : Nat) (g : Genome) (m1 m2 : List Char) (t : TierOut) : Prop :=
  MateFloor g m1 t.m1.cd ∧ MateFloor g m2 t.m2.cd ∧
    ∀ G0, t.pf = some G0 → ∀ P1 P2 : Nat, G0 ≤ P1 → G0 ≤ P2 →
      ∀ w ∈ properPairs usl lo hi (hitsBoth sc0 (-(P1 : Int)) g m1) (hitsBoth sc0 (-(P2 : Int)) g m2),
        pairScoreD dcost0 w < -(G0 : Int)

/-- What each tag proves. -/
def TierOk (usl lo hi : Nat) (g : Genome) (m1 m2 : List Char) (O1 O2 : Option ByteArray) (t : TierOut) : Prop :=
  match t.tag with
  | .t0 => (O1 = none ∧ t.why = some (.trimmedAway .one)) ∨ (O2 = none ∧ t.why = some (.trimmedAway .two))
  | .t1 => ∃ x y, t.m1.pl = some x ∧ t.m2.pl = some y ∧
      pairSpecT (-(t.c1 : Int)) (-(t.c2 : Int)) lo hi g m1 m2 = some (x, y)
  | .t1g => t.g0 ≤ 7 ∧ (∃ R, (if t.sw then O2 else O1) = some R ∧ fastT t.g0 R = true) ∧
      ∀ P1 P2 : Nat, t.g0 ≤ P1 → t.g0 ≤ P2 → ∃ x y, t.m1.pl = some x ∧ t.m2.pl = some y ∧
        pairSpecUT sc0 dcost0 usl lo hi (-(P1 : Int)) (-(P2 : Int)) g m1 m2 = some (x, y)
  | .t1gm => t.g0 ≤ 7 ∧ (∃ R, (if t.sw then O2 else O1) = some R ∧ fastT t.g0 R = true) ∧
      ∀ P1 P2 : Nat, t.g0 ≤ P1 → t.g0 ≤ P2 → PairTieOk dcost0 usl lo hi (-(P1 : Int)) (-(P2 : Int)) g m1 m2
  | .t2 => FloorOk usl lo hi g m1 m2 t ∧ CeilOk g m1 t.m1 ∧ CeilOk g m2 t.m2
  | .t3 => FloorOk usl lo hi g m1 m2 t

/-! ## Floors -/

theorem mateFloor_zero (g : Genome) (m : List Char) : MateFloor g m 0 := fun _ x hx => by
  have := hitsBoth_nonpos _ _ _ x hx; show ((0 : Nat) : Int) ≤ -x.2; omega

theorem mateFloor_max {g : Genome} {m : List Char} {a b : Nat} (ha : MateFloor g m a) (hb : MateFloor g m b) :
    MateFloor g m (max a b) := fun T x hx => by
  have h1 := ha T x hx; have h2 := hb T x hx
  rcases Nat.le_total a b with h | h
  · rw [Nat.max_eq_right h]; exact h2
  · rw [Nat.max_eq_left h]; exact h1

/-- **RT `noHit` at cap `c` ⇒ floor `c + 1`.** -/
theorem mateFloor_noHit {g : Genome} {m : List Char} {c : Nat} (h : hitsBoth sc0 (-(c : Int)) g m = []) :
    MateFloor g m (c + 1) := fun T x hx => by
  obtain ⟨p, s⟩ := x
  rw [mem_hitsBoth_T] at hx
  refine Int.not_lt.mp fun hlt => ?_
  have : (p, s) ∈ hitsBoth sc0 (-(c : Int)) g m :=
    (mem_hitsBoth_T _ _ _ _ _).mpr ⟨hx.1, hx.2.1, by simp only at hlt ⊢; omega⟩
  rw [h] at this; cases this

/-- **RT's unique best ⇒ floor = its penalty.** -/
theorem mateFloor_best {g : Genome} {m : List Char} {T0 : Int} {a : Placement × Int}
    (h : mapSpecBoth sc0 T0 g m = some a) : MateFloor g m (-a.2).toNat := fun T x hx => by
  obtain ⟨p, s⟩ := x
  obtain ⟨pa, sa⟩ := a
  have ha0 := hitsBoth_nonpos _ _ _ _ (mapSpecBoth_mem h)
  rw [mapSpecBoth_iffT] at h
  obtain ⟨⟨ha, hT⟩, hall⟩ := h
  rw [mem_hitsBoth_T] at hx
  simp only at ha0 ⊢
  have hle : s ≤ sa := by
    by_cases hs : T0 ≤ s
    · rcases hall p s hx.2.1 hs with h1 | h1
      · omega
      · subst h1; rw [ha] at hx; have := hx.2.1; simp only [Option.some.injEq] at this; omega
    · omega
  omega

/-- Above −8 a window score is a multiple of 4 (gapless, mismatch 4). -/
theorem score_mul4 (read : List Char) (g : Genome) (w : Window) (s : Int) (hs : windowScore sc0 read g w = some s)
    (h8 : -8 < s) : ∃ k : Nat, s = -4 * (k : Int) := by
  unfold windowScore at hs
  cases hseq : windowSeq g w with
  | none => rw [hseq] at hs; cases hs
  | some ys =>
    rw [hseq] at hs
    simp only at hs
    cases hbest : getBestAlignment sc0 read ys with
    | none => rw [hbest] at hs; cases hs
    | some best =>
      rw [hbest] at hs
      obtain ⟨path, bs⟩ := best
      have hsb : bs = s := by simpa using hs
      subst hsb
      obtain ⟨-, -, hgs⟩ := best_gapless sc0 valid_sc0 read ys path bs hbest
        (by unfold gapCost1 sc0; simp only; omega)
      rw [gaplessScore_match_zero sc0 rfl] at hgs
      exact ⟨MapSpec.hamming read ys, by rw [hgs]; rfl⟩

theorem strandScore_mul4 (g : Genome) (m : List Char) (st : Strand) (w : Window) (s : Int)
    (hs : strandScore g m st w = some s) (h8 : -8 < s) : ∃ k : Nat, s = -4 * (k : Int) := by
  cases st
  · exact score_mul4 _ _ _ _ hs h8
  · exact score_mul4 _ _ _ _ hs h8

theorem bestOf_spec : ∀ (l : List (Placement × Int)) (acc : Option (Placement × Int)),
    let r := l.foldl (fun acc x => match acc with | some y => if y.2 < x.2 then some x else acc | none => some x) acc
    (r = none → acc = none ∧ l = []) ∧
      ∀ b, r = some b → (acc = some b ∨ b ∈ l) ∧ (∀ y, acc = some y → y.2 ≤ b.2) ∧ ∀ x ∈ l, x.2 ≤ b.2
  | [], acc => by
    refine ⟨fun h => ⟨h, rfl⟩, fun b h => ⟨Or.inl h, fun y hy => ?_, fun x hx => (by cases hx)⟩⟩
    simp only [List.foldl_nil] at h
    rw [h] at hy; cases hy; exact Int.le_refl _
  | x :: l, acc => by
    have ih := bestOf_spec l (match acc with | some y => if y.2 < x.2 then some x else acc | none => some x)
    simp only [List.foldl_cons] at ih ⊢
    refine ⟨fun h => ?_, fun b h => ?_⟩
    · have := (ih.1 h).1
      cases acc with
      | none => cases this
      | some y => simp only at this; split at this <;> cases this
    · obtain ⟨h1, h2, h3⟩ := ih.2 b h
      cases acc with
      | none =>
        simp only at h1 h2
        refine ⟨?_, fun y hy => (by cases hy), ?_⟩
        · rcases h1 with h1 | h1
          · cases h1; exact Or.inr (List.mem_cons_self ..)
          · exact Or.inr (List.mem_cons_of_mem _ h1)
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact h2 z rfl
          · exact h3 z hz
      | some y =>
        simp only at h1 h2
        by_cases hyx : y.2 < x.2
        · simp only [hyx, if_true] at h1 h2
          have hx := h2 x rfl
          refine ⟨?_, fun y' hy' => (by cases hy'; omega), ?_⟩
          · rcases h1 with h1 | h1
            · cases h1; exact Or.inr (List.mem_cons_self ..)
            · exact Or.inr (List.mem_cons_of_mem _ h1)
          · intro z hz
            rcases List.mem_cons.mp hz with rfl | hz
            · exact hx
            · exact h3 z hz
        · simp only [hyx, if_false] at h1 h2
          have hy := h2 y rfl
          refine ⟨?_, fun y' hy' => (by cases hy'; exact hy), ?_⟩
          · rcases h1 with h1 | h1
            · exact Or.inl h1
            · exact Or.inr (List.mem_cons_of_mem _ h1)
          · intro z hz
            rcases List.mem_cons.mp hz with rfl | hz
            · omega
            · exact h3 z hz

theorem bestOf_none {l : List (Placement × Int)} (h : bestOf l = none) : l = [] := ((bestOf_spec l none).1 h).2

theorem bestOf_some {l : List (Placement × Int)} {b : Placement × Int} (h : bestOf l = some b) :
    b ∈ l ∧ ∀ x ∈ l, x.2 ≤ b.2 := by
  obtain ⟨h1, -, h3⟩ := (bestOf_spec l none).2 b h
  exact ⟨by rcases h1 with h1 | h1; cases h1; exact h1, h3⟩

/-- **The guarantee's completed enumeration of a mate ⇒ its floor** (`lX` = its hits within `G0`). -/
theorem mateFloor_enum {g : Genome} {m : List Char} {G0 : Nat} (hG : G0 ≤ 7) (nc : Nat) {lX : List (Placement × Int)}
    (hX : ∀ x, x ∈ lX ↔ x ∈ hitsBoth sc0 (-(G0 : Int)) g m) : MateFloor g m (gxOf nc G0 lX).1 := by
  intro T x hx
  obtain ⟨p, s⟩ := x
  have hx' := (mem_hitsBoth_T _ _ _ _ _).mp hx
  have hs0 := hitsBoth_nonpos _ _ _ _ hx
  simp only at hs0 ⊢
  unfold gxOf
  cases hb : bestOf lX with
  | none =>
    have hl := bestOf_none hb
    simp only
    have hlt : s < -(G0 : Int) := by
      refine Int.not_le.mp fun hle => ?_
      have := (hX (p, s)).mpr ((mem_hitsBoth_T _ _ _ _ _).mpr ⟨hx'.1, hx'.2.1, hle⟩)
      rw [hl] at this; cases this
    by_cases h8 : -8 < s
    · obtain ⟨k, hk⟩ := strandScore_mul4 g m p.2 p.1 s hx'.2.1 h8
      split <;> rename_i h4 <;> simp only [beq_iff_eq] at h4 <;> push_cast <;> omega
    · split <;> push_cast <;> omega
  | some b =>
    obtain ⟨hbm, hbmax⟩ := bestOf_some hb
    have hb' := (hX b).mp hbm
    have hb0 := hitsBoth_nonpos _ _ _ _ hb'
    have hbG := ((mem_hitsBoth_T _ _ _ _ _).mp hb').2.2
    obtain ⟨pb, sb⟩ := b
    simp only at hb0 hbG ⊢
    have : s ≤ sb := by
      by_cases hle : -(G0 : Int) ≤ s
      · exact hbmax (p, s) ((hX (p, s)).mpr ((mem_hitsBoth_T _ _ _ _ _).mpr ⟨hx'.1, hx'.2.1, hle⟩))
      · omega
    omega

section look
variable (g : Genome) (ix : Mz.MzIdx) (G : PGen) (offs ns : Array Nat) (hcut : cutOk G offs ns = true)
  (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) g) (hchk : Mz.check2P ix G = true)

include hcut hg hchk in
/-- **Empty seed lookups on one strand ⇒ floor** (`floor_look`). -/
theorem emptyCnt_floor (Rx : ByteArray) (rd : List Char) (hr : Encodes Rx rd) (w : Window) (s : Int)
    (hs : windowScore sc0 rd g w = some s) :
    4 * (emptyCnt ((ix, G) : PkMz) Rx.size Rx
      (prepG ((ix, G) : PkMz) Rx (Rx.size / 25) (Rx.size / (Rx.size / 25))) : Int) ≤ -s := by
  have h0 := windowScore_nonpos rd g w s hs
  have hn : Rx.size = rd.length := hr.1
  unfold emptyCnt
  rw [hn]
  generalize hL : rd.length = L at hn
  by_cases hm : 0 < L / 25
  · have hLs : 25 ≤ L / (L / 25) := by
      rw [Nat.le_div_iff_mul_le hm, Nat.mul_comm]; exact Nat.div_mul_le_self _ _
    have hbound : ∀ j, j < L / 25 → j * (L / (L / 25)) + q ≤ Rx.size := by
      intro j hj
      have hq : q = 25 := rfl
      have h1 : (j + 1) * (L / (L / 25)) ≤ (L / 25) * (L / (L / 25)) := Nat.mul_le_mul_right _ hj
      have h2 : (L / 25) * (L / (L / 25)) ≤ L := Nat.mul_div_le L (L / 25)
      rw [Nat.add_mul, Nat.one_mul] at h1
      omega
    have hpp : ∀ j, j < L / 25 → (prepG ((ix, G) : PkMz) Rx (L / 25) (L / (L / 25)))[j]! =
        LookG.prep ((ix, G) : PkMz) (seedHashAt Rx (j * (L / (L / 25)))) := by
      intro j hj
      unfold prepG
      rw [getElem!_pos _ j (by simp [hj])]
      simp
    have := floor_look ((ix, G) : PkMz) (Mz.unpack G) offs g rd ((cutAll G offs ns).map Mz.unpack) Rx hg hr
      (catOk_cut G offs ns hcut) (by rw [hL]; exact hm)
      ((List.range (L / 25)).filter fun j =>
        ((prepG ((ix, G) : PkMz) Rx (L / 25) (L / (L / 25)))[j]!).ok &&
          LookG.size ((ix, G) : PkMz) (prepG ((ix, G) : PkMz) Rx (L / 25) (L / (L / 25)))[j]! == 0 &&
          (LookG.look ((ix, G) : PkMz) ByteArray.empty Rx (j * (L / (L / 25))) (L - j * (L / (L / 25)))
            (prepG ((ix, G) : PkMz) Rx (L / 25) (L / (L / 25)))[j]!).isEmpty)
      (List.nodup_range.filter _) (fun j hj => by rw [hL]; exact List.mem_range.mp (List.mem_filter.mp hj).1)
      (fun j => L - j * (L / (L / 25)))
      (fun j hj => by
        have hj' := List.mem_range.mp (List.mem_filter.mp hj).1
        rw [hL]
        exact lookOk_pk ix G hchk Rx _ _ (hbound j hj'))
      (fun j hj => by
        have hj' := List.mem_range.mp (List.mem_filter.mp hj).1
        have hc := (List.mem_filter.mp hj).2
        rw [hpp j hj'] at hc
        simp only [Bool.and_eq_true] at hc
        rw [hL]
        exact Array.isEmpty_iff.mp hc.2)
      w s hs
    exact this
  · have : L / 25 = 0 := by omega
    rw [this]
    simp only [List.range_zero, List.filter_nil, List.length_nil]
    show (4 : Int) * ((0 : Nat) : Int) ≤ -s
    omega

include hcut hg hchk in
/-- **Empty seed lookups ⇒ mate floor** (`4·min` over the two strands). -/
theorem mateFloor_look (R : ByteArray) (m : List Char) (hr : Encodes R m) :
    MateFloor g m (4 * min (emptyCnt ((ix, G) : PkMz) R.size R (prepMate ((ix, G) : PkMz) R : PrepM MzP).ps)
      (emptyCnt ((ix, G) : PkMz) R.size (prepMate ((ix, G) : PkMz) R : PrepM MzP).Rr
        (prepMate ((ix, G) : PkMz) R : PrepM MzP).pr)) := by
  intro T x hx
  obtain ⟨⟨w, st⟩, s⟩ := x
  rw [mem_hitsBoth_T] at hx
  have hrr := revCompK_encodes R m hr
  have hsz := revCompK_size R m hr
  have e1 : (prepMate ((ix, G) : PkMz) R : PrepM MzP).ps =
      prepG ((ix, G) : PkMz) R (R.size / 25) (R.size / (R.size / 25)) := by
    show prepGK _ R (packRP R) _ _ = _; exact prepGK_eq _ _ _ _
  have e2 : (prepMate ((ix, G) : PkMz) R : PrepM MzP).pr =
      prepG ((ix, G) : PkMz) (revCompK R) ((revCompK R).size / 25) ((revCompK R).size / ((revCompK R).size / 25)) := by
    show prepGK _ (revCompK R) (packRP (revCompK R)) _ _ = _; rw [prepGK_eq, hsz]
  have e3 : (prepMate ((ix, G) : PkMz) R : PrepM MzP).Rr = revCompK R := rfl
  rw [e1, e2, e3]
  cases st with
  | fwd =>
    have := emptyCnt_floor g ix G offs ns hcut hg hchk R m hr w s hx.2.1
    simp only at this ⊢
    push_cast
    have := Nat.min_le_left (emptyCnt ((ix, G) : PkMz) R.size R (prepG ((ix, G) : PkMz) R (R.size / 25) (R.size / (R.size / 25))))
      (emptyCnt ((ix, G) : PkMz) R.size (revCompK R) (prepG ((ix, G) : PkMz) (revCompK R) ((revCompK R).size / 25)
        ((revCompK R).size / ((revCompK R).size / 25))))
    omega
  | rev =>
    have := emptyCnt_floor g ix G offs ns hcut hg hchk (revCompK R) (revComp m) hrr w s hx.2.1
    rw [hsz] at this ⊢
    simp only at this ⊢
    push_cast
    have := Nat.min_le_right (emptyCnt ((ix, G) : PkMz) R.size R (prepG ((ix, G) : PkMz) R (R.size / 25) (R.size / (R.size / 25))))
      (emptyCnt ((ix, G) : PkMz) R.size (revCompK R) (prepG ((ix, G) : PkMz) (revCompK R) (R.size / 25)
        (R.size / (R.size / 25))))
    omega

end look

/-! ## Re-checked alignments are real -/

theorem chars_of_encodes (Rx : ByteArray) (rd : List Char) (h : Encodes Rx rd) :
    ((List.range Rx.size).toArray.map fun i => Char.ofNat (Rx.get! i).toNat).toList = rd := by
  apply List.ext_getElem
  · simp [h.1]
  · intro i h1 h2
    simp only [Array.toList_map, List.getElem_map, List.getElem_range]
    rw [h.2 i h2, Char.ofNat_toNat]

theorem chars_of_genome (pgs : Array PGen) (g : Genome) (hg : GenomeBytes (pgs.map Mz.unpack) g) (c st len : Nat)
    (hc : c < pgs.size) (hl : st + len ≤ pgs[c]!.n) :
    windowSeq g ⟨c, st, len⟩ =
      some ((List.range len).toArray.map fun i => Char.ofNat (pgs[c]!.get (st + i)).toNat).toList := by
  have hcg : c < g.length := by rw [← hg.1]; simpa using hc
  have hE := hg.2 c (by simpa using hc) hcg
  have hrep := Mz.rep_unpack pgs[c]!
  have hP : (pgs.map Mz.unpack)[c]'(by simpa using hc) = Mz.unpack pgs[c]! := by
    rw [getElem!_pos pgs c hc]; simp
  rw [hP] at hE
  have hlen : g[c].seq.length = pgs[c]!.n := by rw [← hE.1, ← hrep.1]
  unfold windowSeq
  simp only [List.getElem?_eq_getElem hcg]
  rw [if_pos (by omega)]
  congr 1
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.length_take, List.length_drop] at h1
    simp only [Array.toList_map, List.getElem_map, List.getElem_range, List.getElem_take,
      List.getElem_drop]
    rw [hrep.2, hE.2 (st + i) (by omega), Char.ofNat_toNat]

/-- **A candidate that passes `chkCand` is a real alignment with its score** (`checkRuns_sound`). -/
theorem chkCand_sound (pgs : Array PGen) (g : Genome) (hg : GenomeBytes (pgs.map Mz.unpack) g) (R : ByteArray)
    (m : List Char) (hr : Encodes R m) (h : Placement × Int) (runs : List (Step × Nat))
    (hc : chkCand pgs R (revCompK R) h runs = true) : CigarOk g m h runs ∧ h.2 ≤ 0 := by
  obtain ⟨⟨⟨c, st, len⟩, sd⟩, sc⟩ := h
  unfold chkCand rescoreRuns at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  obtain ⟨hw, hs⟩ := checkRuns_sound sc0 _ _ runs sc h4
  refine ⟨⟨_, chars_of_genome pgs g hg c st len h1 h2, ?_⟩, h3⟩
  have hx : ((List.range (if sd = Strand.fwd then R else revCompK R).size).toArray.map
      fun i => Char.ofNat ((if sd = Strand.fwd then R else revCompK R).get! i).toNat).toList = strandRead m sd := by
    cases sd
    · exact chars_of_encodes R m hr
    · exact chars_of_encodes _ _ (revCompK_encodes R m hr)
  rw [hx] at hw hs
  exact ⟨hw, hs⟩

/-- A real alignment with score `s` ⇒ the placement scores at least `s`. -/
theorem cigar_hit {g : Genome} {m : List Char} {x : Placement × Int} {runs : List (Step × Nat)}
    (h : CigarOk g m x runs) : hitsBoth sc0 x.2 g m ≠ [] := by
  obtain ⟨ys, hws, hw, hs⟩ := h
  obtain ⟨⟨path, bs⟩, hb⟩ := getBestAlignment_returns_some sc0 (strandRead m x.1.2) ys
  have hle := getBestAlignment_returns_a_maximum_score sc0 _ ys path bs _ hb hw
  have hsc : strandScore g m x.1.2 x.1.1 = some bs := by
    have : windowScore sc0 (strandRead m x.1.2) g x.1.1 = some bs := by
      unfold windowScore; rw [hws]; simp only; rw [hb]
    cases hst : x.1.2 <;> rw [hst] at this <;> exact this
  have hmem : (x.1, bs) ∈ hitsBoth sc0 x.2 g m := by
    rw [mem_hitsBoth_T]
    refine ⟨?_, hsc, by omega⟩
    cases hst : x.1.2 <;> rw [hst] at hsc <;> exact mem_allWindows_of_score _ _ _ _ _ hsc
  intro hn; rw [hn] at hmem; cases hmem

theorem hits_self {T : Int} {g : Genome} {m : List Char} {x : Placement × Int} (h : x ∈ hitsBoth sc0 T g m) :
    hitsBoth sc0 x.2 g m ≠ [] := by
  have h' := (mem_hitsBoth_T _ _ _ _ _).mp h
  have hm : x ∈ hitsBoth sc0 x.2 g m := (mem_hitsBoth_T _ _ _ _ _).mpr ⟨h'.1, h'.2.1, Int.le_refl _⟩
  intro hn; rw [hn] at hm; cases hm

/-! ## Mates: floors and ceilings are kept by every step -/

/-- A mate's floor is proved and its claimed ceiling is real. -/
def MInv (g : Genome) (m : List Char) (x : MateX) : Prop := MateFloor g m x.cd ∧ CeilEv g m x

section mates
variable {g : Genome} {ix : Mz.MzIdx} {G : PGen} {offs ns : Array Nat}
  (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) g)

include hg in
theorem upA_inv {R : ByteArray} {m : List Char} (hr : Encodes R m) {x : MateX} (hx : MInv g m x) (v st mm src : Nat) :
    MInv g m (upA (cutAll G offs ns) R (revCompK R) x v st mm src) := by
  unfold upA
  split
  · refine ⟨hx.1, fun hok => ?_⟩
    simp only [MateX.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hc, -⟩ := chkCand_sound _ g hg R m hr _ _ hok.2
    exact ⟨cigar_hit hc, fun _ => ⟨_, rfl, rfl, hc⟩⟩
  · exact hx

include hg in
theorem applyC_inv {R : ByteArray} {m : List Char} (hr : Encodes R m) {x : MateX} (hx : MInv g m x)
    (c : Option Cand) : MInv g m (applyC (cutAll G offs ns) R (revCompK R) x c) := by
  cases c with
  | none => exact hx
  | some c =>
    show MInv g m (if chkCand (cutAll G offs ns) R (revCompK R) c.pl c.runs then x.withC c.pl c.src c.runs else x)
    by_cases hc : chkCand (cutAll G offs ns) R (revCompK R) c.pl c.runs = true
    · rw [if_pos hc]
      obtain ⟨hcg, h0⟩ := chkCand_sound _ g hg R m hr _ _ hc
      have e : -(((-c.pl.2).toNat : Nat) : Int) = c.pl.2 := by omega
      refine ⟨hx.1, fun _ => ?_⟩
      show hitsBoth sc0 (-(((-c.pl.2).toNat : Nat) : Int)) g m ≠ [] ∧
        (true = true → ∃ y, some c.pl = some y ∧ y.2 = -(((-c.pl.2).toNat : Nat) : Int) ∧ CigarOk g m y c.runs)
      rw [e]
      exact ⟨cigar_hit hcg, fun _ => ⟨_, rfl, rfl, hcg⟩⟩
    · rw [if_neg hc]; exact hx

include hg in
theorem mateT_inv (hcut : cutOk G offs ns = true) (hchk : Mz.check2P ix G = true) {R : ByteArray} {m : List Char}
    (hr : Encodes R m) (cap c : Nat) (nh capC : Bool) (kn : Option (Placement × Int))
    (gx : Option (Nat × Option (Nat × Nat × Nat))) (ceil : Unit → Option (Nat × Nat × Nat))
    (hnh : nh = true → hitsBoth sc0 (-(c : Int)) g m = [])
    (hcc : capC = true → hitsBoth sc0 (-(c : Int)) g m ≠ [])
    (hkn : ∀ a, kn = some a → ∃ T, mapSpecBoth sc0 T g m = some a)
    (hgx : ∀ f v, gx = some (f, v) → MateFloor g m f) :
    MInv g m (mateT ((ix, G) : PkMz) (cutAll G offs ns) R (prepMate ((ix, G) : PkMz) R) cap c nh capC kn gx ceil) := by
  unfold mateT
  cases kn with
  | some a =>
    obtain ⟨T, hT⟩ := hkn a rfl
    have ha := mapSpecBoth_mem hT
    have h0 := hitsBoth_nonpos _ _ _ _ ha
    refine ⟨mateFloor_best hT, fun _ => ⟨?_, fun h => by simp at h⟩⟩
    have e : -(((-a.2).toNat : Nat) : Int) = a.2 := by omega
    show hitsBoth sc0 (-(((-a.2).toNat : Nat) : Int)) g m ≠ []
    rw [e]; exact hits_self ha
  | none =>
    have hE := mateFloor_look g ix G offs ns hcut hg hchk R m hr
    have I0 : MInv g m (mateB0 ((ix, G) : PkMz) R (prepMate ((ix, G) : PkMz) R) cap c nh gx) := by
      refine ⟨mateFloor_max (mateFloor_max ?_ ?_) ?_, fun h => by simp [mateB0, MateX.ok] at h⟩
      · show MateFloor g m (if fastT 0 R then _ else 0)
        split
        · exact hE
        · exact mateFloor_zero g m
      · show MateFloor g m (if nh then c + 1 else 0)
        cases nh
        · exact mateFloor_zero g m
        · exact mateFloor_noHit (hnh rfl)
      · show MateFloor g m ((gx.map (·.1)).getD 0)
        cases gx with
        | none => exact mateFloor_zero g m
        | some v => obtain ⟨f, w⟩ := v; exact hgx f w rfl
    have I1 : MInv g m (capStep (mateB0 ((ix, G) : PkMz) R (prepMate ((ix, G) : PkMz) R) cap c nh gx) c capC) := by
      unfold capStep
      cases capC
      · exact I0
      · rw [if_pos rfl]
        exact ⟨I0.1, fun _ => ⟨hcc rfl, fun h => by simp [mateB0] at h⟩⟩
    generalize capStep _ c capC = x1 at I1
    have I2 : MInv g m (gxStep (cutAll G offs ns) R (revCompK R) x1 gx) := by
      unfold gxStep
      split
      · exact upA_inv hg hr I1 _ _ _ _
      · exact I1
    show MInv g m (ceilStep (cutAll G offs ns) R (revCompK R) (gxStep (cutAll G offs ns) R (revCompK R) x1 gx) _)
    generalize gxStep _ R _ x1 gx = x2 at I2
    unfold ceilStep
    split
    · exact upA_inv hg hr I2 _ _ _ _
    · exact I2

end mates

/-! ## RT's reasons as flags -/

/-- RT's reason, when it is a search reason, is right at RT's caps. -/
def RkOk (lo hi : Nat) (g : Genome) (m1 m2 : List Char) (c1 c2 : Nat)
    (rk : Option (Reason × Option (Placement × Int))) : Prop :=
  ∀ rs k, rk = some (rs, k) → rs.searched = true →
    ReasonOk (Mate.sel (-(c1 : Int)) (-(c2 : Int))) lo hi g (Mate.sel m1 m2) rs ∧
      KnownOk (Mate.sel (-(c1 : Int)) (-(c2 : Int))) g (Mate.sel m1 m2) rs k

section flags
variable {lo hi : Nat} {g : Genome} {m1 m2 : List Char} {c1 c2 : Nat} {rk : Option (Reason × Option (Placement × Int))}
  (H : RkOk lo hi g m1 m2 c1 c2 rk)

include H in
theorem nhOf_ok (mt : Mate) (h : nhOf mt rk = true) :
    hitsBoth sc0 (Mate.sel (-(c1 : Int)) (-(c2 : Int)) mt) g (Mate.sel m1 m2 mt) = [] := by
  unfold nhOf at h
  split at h
  · rename_i m k
    have e : m = mt := by simpa using h
    subst e
    exact (H _ _ rfl rfl).1
  · cases h

include H in
theorem ccOf_ok (mt : Mate) (h : ccOf mt rk = true) :
    hitsBoth sc0 (Mate.sel (-(c1 : Int)) (-(c2 : Int)) mt) g (Mate.sel m1 m2 mt) ≠ [] := by
  unfold ccOf at h
  split at h
  · rename_i m k
    have e : m = mt := by simpa using h
    subst e
    exact (H _ _ rfl rfl).1.1
  · rename_i k
    obtain ⟨a, b, ha, hb, -⟩ := (H _ _ rfl rfl).1
    cases mt
    · exact List.ne_nil_of_mem (mapSpecBoth_mem ha)
    · exact List.ne_nil_of_mem (mapSpecBoth_mem hb)
  · cases h

include H in
theorem knOf_ok (mt : Mate) {a : Placement × Int} (h : knOf mt rk = some a) :
    mapSpecBoth sc0 (Mate.sel (-(c1 : Int)) (-(c2 : Int)) mt) g (Mate.sel m1 m2 mt) = some a := by
  unfold knOf at h
  split at h
  · rename_i m k
    by_cases e : (m.other == mt) = true
    · rw [if_pos e] at h
      subst h
      have e' : m.other = mt := by simpa using e
      have := (H _ _ rfl rfl).2
      rw [← e']
      exact this
    · rw [if_neg e] at h; cases h
  · cases h

end flags

/-! ## The guarantee -/

theorem pairGQC_seen {dc : Nat → Nat} {sl lo hi Gc : Nat} {swap : Bool} {ix : PkMzR} {offs : Array Nat}
    {pgs : Array PGen} {R1 R2 : ByteArray} {xy : PairHit} {seen : Bool} {lX : List (Placement × Int)}
    (h : pairGQC dc sl lo hi Gc swap ix offs pgs R1 R2 = some (some xy, seen, lX)) : seen = true := by
  unfold pairGQC at h
  split at h
  · cases h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2, -⟩ := h
    rw [← h2]
    generalize goP _ _ _ _ _ = s at h1 ⊢
    obtain ⟨o, t⟩ := s
    cases t <;> simp_all

section route
variable (cfg : TierCfg) (pk : PkMz) (offs : Array Nat) (pgs : Array PGen)

theorem tierG_ok {G0 : Nat} {a b : ByteArray} {s1 s2 : PrepM MzP} {sw : Bool}
    {v : Option PairHit × Bool × List (Placement × Int)} (h : tierG cfg pk offs pgs G0 a b s1 s2 = some (sw, v)) :
    fastT G0 (if sw then b else a) = true ∧
      pairGQC dcost0 cfg.usl cfg.lo cfg.hi G0 sw (pk : PkMzR) offs pgs a b = some v := by
  unfold tierG at h
  simp only at h
  split at h
  · cases h
  · rename_i hf
    rw [Option.map_eq_some_iff] at h
    obtain ⟨v', hv', he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨?_, hv'⟩
    cases h1 : fastT G0 a <;> cases h2 : fastT G0 b <;> simp_all
    cases cfg.pref G0 a b s1 s2 <;> simp_all

theorem tierPick_ok {G G0 : Nat} {sfx : String} {a b : ByteArray} {s1 s2 : PrepM MzP}
    {v : Bool × (Option PairHit × Bool × List (Placement × Int))}
    (h : tierPick cfg pk offs pgs G a b s1 s2 = (G0, sfx, some v)) :
    (G0 = G ∨ G0 = 0) ∧ tierG cfg pk offs pgs G0 a b s1 s2 = some v := by
  unfold tierPick at h
  split at h
  · rename_i w hw
    simp only [Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨rfl, -, rfl⟩ := h
    exact ⟨Or.inl rfl, hw⟩
  · split at h
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, -, h⟩ := h
      exact ⟨Or.inr rfl, h⟩
    · simp at h

end route

/-! ## The theorem -/

theorem tierOk_B {usl lo hi : Nat} {g : Genome} {m1 m2 : List Char} {O1 O2 : Option ByteArray} {t : TierOut}
    (hB : (t.tag = .t2 ∧ t.m1.ok = true ∧ t.m2.ok = true) ∨ t.tag = .t3)
    (h1 : MInv g m1 t.m1) (h2 : MInv g m2 t.m2)
    (hpf : ∀ G0, t.pf = some G0 → ∀ P1 P2 : Nat, G0 ≤ P1 → G0 ≤ P2 →
      ∀ w ∈ properPairs usl lo hi (hitsBoth sc0 (-(P1 : Int)) g m1) (hitsBoth sc0 (-(P2 : Int)) g m2),
        pairScoreD dcost0 w < -(G0 : Int)) :
    TierOk usl lo hi g m1 m2 O1 O2 t := by
  have hF : FloorOk usl lo hi g m1 m2 t := ⟨h1.1, h2.1, hpf⟩
  unfold TierOk
  rcases hB with ⟨h, k1, k2⟩ | h
  · rw [h]; exact ⟨hF, ⟨k1, h1.2⟩, ⟨k2, h2.2⟩⟩
  · rw [h]; exact hF

section main
variable (cfg : TierCfg) (g : Genome) (m1 m2 : List Char) (ix : Mz.MzIdx) (G : PGen) (offs ns : Array Nat)
  (hcut : cutOk G offs ns = true) (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) g)
  (hchk : Mz.check2P ix G = true)

include hcut hg hchk in
theorem tierB_ok {a b : ByteArray} (ha : Encodes a m1) (hb : Encodes b m2)
    {rk : Option (Reason × Option (Placement × Int))} {c1 c2 : Nat} (H : RkOk cfg.lo cfg.hi g m1 m2 c1 c2 rk)
    {g1 g2 : Option (Nat × Option (Nat × Nat × Nat))}
    (hg1 : ∀ f v, g1 = some (f, v) → MateFloor g m1 f) (hg2 : ∀ f v, g2 = some (f, v) → MateFloor g m2 f) :
    MInv g m1 (tierB cfg ((ix, G) : PkMz) (cutAll G offs ns) a b (prepMate ((ix, G) : PkMz) a)
        (prepMate ((ix, G) : PkMz) b) rk c1 c2 g1 g2).2.1 ∧
      MInv g m2 (tierB cfg ((ix, G) : PkMz) (cutAll G offs ns) a b (prepMate ((ix, G) : PkMz) a)
        (prepMate ((ix, G) : PkMz) b) rk c1 c2 g1 g2).2.2 ∧
      (((tierB cfg ((ix, G) : PkMz) (cutAll G offs ns) a b (prepMate ((ix, G) : PkMz) a)
        (prepMate ((ix, G) : PkMz) b) rk c1 c2 g1 g2).1 = .t2 ∧
        (tierB cfg ((ix, G) : PkMz) (cutAll G offs ns) a b (prepMate ((ix, G) : PkMz) a)
          (prepMate ((ix, G) : PkMz) b) rk c1 c2 g1 g2).2.1.ok = true ∧
        (tierB cfg ((ix, G) : PkMz) (cutAll G offs ns) a b (prepMate ((ix, G) : PkMz) a)
          (prepMate ((ix, G) : PkMz) b) rk c1 c2 g1 g2).2.2.ok = true) ∨
       (tierB cfg ((ix, G) : PkMz) (cutAll G offs ns) a b (prepMate ((ix, G) : PkMz) a)
          (prepMate ((ix, G) : PkMz) b) rk c1 c2 g1 g2).1 = .t3) := by
  have A1 := mateT_inv hg hcut hchk ha (cfg.rcfg.cap1 a.size) c1 (nhOf .one rk) (ccOf .one rk) (knOf .one rk) g1
    (fun _ => cfg.ceil a (prepMate ((ix, G) : PkMz) a)) (nhOf_ok H .one) (ccOf_ok H .one)
    (fun _ h => ⟨_, knOf_ok H .one h⟩) hg1
  have A2 := mateT_inv hg hcut hchk hb (cfg.rcfg.cap1 b.size) c2 (nhOf .two rk) (ccOf .two rk) (knOf .two rk) g2
    (fun _ => cfg.ceil b (prepMate ((ix, G) : PkMz) b)) (nhOf_ok H .two) (ccOf_ok H .two)
    (fun _ h => ⟨_, knOf_ok H .two h⟩) hg2
  unfold tierB
  dsimp only
  generalize mateT _ _ a _ _ c1 _ _ _ g1 _ = x1 at A1 ⊢
  generalize mateT _ _ b _ _ c2 _ _ _ g2 _ = x2 at A2 ⊢
  have B1 := applyC_inv hg ha A1 (cfg.heur a b (prepMate ((ix, G) : PkMz) a) (prepMate ((ix, G) : PkMz) b) x1 x2).1
  have B2 := applyC_inv hg hb A2 (cfg.heur a b (prepMate ((ix, G) : PkMz) a) (prepMate ((ix, G) : PkMz) b) x1 x2).2
  refine ⟨B1, B2, ?_⟩
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    exact Or.inl ⟨rfl, h⟩
  · exact Or.inr rfl

include hcut hg hchk in
theorem tierRest_ok {a b : ByteArray} (ha : Encodes a m1) (hb : Encodes b m2)
    {rk : Option (Reason × Option (Placement × Int))} {c1 c2 : Nat} (H : RkOk cfg.lo cfg.hi g m1 m2 c1 c2 rk) :
    TierOk cfg.usl cfg.lo cfg.hi g m1 m2 (some a) (some b)
      (tierRest cfg ((ix, G) : PkMz) offs (cutAll G offs ns) a b rk c1 c2) := by
  have hB := fun g1 g2 hg1 hg2 => tierB_ok cfg g m1 m2 ix G offs ns hcut hg hchk ha hb H (g1 := g1) (g2 := g2) hg1 hg2
  have hP : ∀ sfx, TierOk cfg.usl cfg.lo cfg.hi g m1 m2 (some a) (some b)
      (let t := tierB cfg ((ix, G) : PkMz) (cutAll G offs ns) a b (prepMate ((ix, G) : PkMz) a)
        (prepMate ((ix, G) : PkMz) b) rk c1 c2 none none
       ({ tag := t.1, sfx := sfx, m1 := t.2.1, m2 := t.2.2, why := rk.map (·.1), c1 := c1, c2 := c2 } : TierOut)) := by
    intro sfx
    obtain ⟨B1, B2, B3⟩ := hB none none (fun _ _ h => by cases h) (fun _ _ h => by cases h)
    exact tierOk_B B3 B1 B2 (fun _ h => by cases h)
  unfold tierRest
  dsimp only
  cases hpg : cfg.pg with
  | none => exact hP ""
  | some G' =>
    dsimp only
    by_cases h7 : 7 < G'
    · rw [if_pos h7]; exact hP ""
    rw [if_neg h7]
    rcases hp : tierPick cfg ((ix, G) : PkMz) offs (cutAll G offs ns) G' a b (prepMate ((ix, G) : PkMz) a)
      (prepMate ((ix, G) : PkMz) b) with ⟨G0, sfx, _ | ⟨sw, r, seen, lX⟩⟩
    · exact hP "x"
    obtain ⟨hG0, htg⟩ := tierPick_ok cfg _ offs _ hp
    obtain ⟨hfast, hq⟩ := tierG_ok cfg _ offs _ htg
    have hG7 : G0 ≤ 7 := by omega
    have S := fun P1 P2 (hP1 : G0 ≤ P1) (hP2 : G0 ≤ P2) =>
      pairGQC_sound dcost0 cfg.usl cfg.lo cfg.hi G0 g m1 m2 ix G offs ns a b hcut hg ha hb hchk hG7 sw P1 P2 hP1 hP2
        r seen lX hq
    have hfR : ∃ R, (if sw then some b else some a) = some R ∧ fastT G0 R = true :=
      ⟨_, by cases sw <;> rfl, hfast⟩
    dsimp only
    cases r with
    | some xy =>
      have hs := pairGQC_seen hq
      obtain ⟨x, y⟩ := xy
      exact ⟨hG7, hfR, fun P1 P2 h1 h2 => ⟨x, y, rfl, rfl, ((S P1 P2 h1 h2).2.2.1 hs).symm⟩⟩
    | none =>
      dsimp only
      by_cases hs : seen = true
      · rw [if_pos hs]
        exact ⟨hG7, hfR, fun P1 P2 h1 h2 => (S P1 P2 h1 h2).2.2.2 hs rfl⟩
      rw [if_neg hs]
      have hX := (S G0 G0 (Nat.le_refl _) (Nat.le_refl _)).1
      have hpf : ∀ G1, some G0 = some G1 → ∀ P1 P2 : Nat, G1 ≤ P1 → G1 ≤ P2 →
          ∀ w ∈ properPairs cfg.usl cfg.lo cfg.hi (hitsBoth sc0 (-(P1 : Int)) g m1) (hitsBoth sc0 (-(P2 : Int)) g m2),
            pairScoreD dcost0 w < -(G1 : Int) := by
        intro G1 he P1 P2 h1 h2 w hw
        cases he
        refine Int.not_le.mp fun hle => hs ?_
        exact (S P1 P2 h1 h2).2.1.mpr ⟨w, hw, hle⟩
      cases sw with
      | false =>
        obtain ⟨B1, B2, B3⟩ := hB (some (gxOf (cutAll G offs ns).size G0 lX)) none
          (fun f v h => by have e := congrArg Prod.fst (Option.some.inj h); simp only at e; rw [← e]; exact mateFloor_enum hG7 _ (by simpa using hX)) (fun _ _ h => by cases h)
        exact tierOk_B B3 B1 B2 hpf
      | true =>
        obtain ⟨B1, B2, B3⟩ := hB none (some (gxOf (cutAll G offs ns).size G0 lX))
          (fun _ _ h => by cases h) (fun f v h => by have e := congrArg Prod.fst (Option.some.inj h); simp only at e; rw [← e]; exact mateFloor_enum hG7 _ (by simpa using hX))
        exact tierOk_B B3 B1 B2 hpf

include hcut hg hchk in
/-- **The tier router is sound**: what each tag claims holds (`TierOk`), for any gate, preference,
ceiling diagonal and heuristic. -/
theorem tierPair_sound (O1 O2 : Option ByteArray) (h1 : ∀ R, O1 = some R → Encodes R m1)
    (h2 : ∀ R, O2 = some R → Encodes R m2) :
    TierOk cfg.usl cfg.lo cfg.hi g m1 m2 O1 O2 (tierPair cfg ((ix, G) : PkMz) offs (cutAll G offs ns) O1 O2) := by
  cases O1 with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some a =>
    cases O2 with
    | none => exact Or.inr ⟨rfl, rfl⟩
    | some b =>
      have ha := h1 a rfl
      have hb := h2 b rfl
      unfold tierPair
      dsimp only
      by_cases hgate : cfg.gate a b = true
      · rw [if_pos hgate]
        exact tierRest_ok cfg g m1 m2 ix G offs ns hcut hg hchk ha hb (fun _ _ h => by cases h)
      rw [if_neg hgate]
      have HS : Settled cfg.lo cfg.hi g m1 m2 a b (tierRT cfg ((ix, G) : PkMz) offs (cutAll G offs ns) a b) :=
        routeKPB_ok cfg.lo cfg.hi g m1 m2 ix G offs ns a b hcut hg ha hb hchk cfg.rcfg cfg.j1 cfg.j2 cfg.hint
      generalize tierRT cfg _ offs _ a b = r at HS ⊢
      unfold Settled at HS
      rcases hr : r.out with ⟨x, y⟩ | ⟨rs, k⟩
      · rw [hr] at HS
        exact ⟨x, y, rfl, rfl, HS⟩
      · rw [hr] at HS
        refine tierRest_ok cfg g m1 m2 ix G offs ns hcut hg hchk ha hb (fun rs' k' he hs => ?_)
        cases he
        cases rs with
        | trimmedAway _ => simp [Reason.searched] at hs
        | tooShort _ => simp [Reason.searched] at hs
        | noHit _ => exact HS
        | tie _ => exact HS
        | noPartner _ => exact HS
        | notProper => exact HS
        | noPair => exact HS

end main

end MapSpec.Fast

#print axioms MapSpec.Fast.tierPair_sound
#print axioms MapSpec.Fast.tierRest_ok
#print axioms MapSpec.Fast.mateT_inv
#print axioms MapSpec.Fast.chkCand_sound
#print axioms MapSpec.Fast.mateFloor_noHit
