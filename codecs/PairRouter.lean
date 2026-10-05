import PairReason

/-!
# Codec `routeKP`: pass kernels in sequence, unmapped pairs with a reason

* **Pluggable kernel** `PassKer` (whole-genome mate search + region test) with its
  obligation `KerOk`; the passes and router (`passG`, `pass2G`, `routeG`) are generic,
  `routeG_ok` holds for any pass-1 / pass-2 kernels meeting `KerOk`.  Today's kernel is
  `kpKer` (`kpKer_ok`), `routeKP` = `routeG` with it in both passes.
* **Pass kernel** `passG P1 P2` = the mate-anchored kernel of `pairRegionKP`
  (codecs/PairRegion.lean) at per-mate caps `P1`, `P2`, returning either the pair or a
  `Reason` (codecs/PairReason.lean).  The mate searched over the genome reports
  whether it has any hit (`mateKP`: best penalty `≤ P`, `pen_le_iff`), so "no hit" and
  "tie" are told apart at no cost.  `passG_ok`: mapped = `pairSpecT`, every reason
  holds of the specification (hence `pairSpecT = none`).
* **Known mate** `passKnownG`: the other mate's answer already known (from pass 1 at a
  cap no deeper: `mapSpecBoth_mono`); only the region (and, on a region hit, the
  whole-genome search) of the remaining mate is run.  `passKnownG_ok`.
* **Router** `routeKP`: pass 1 at caps `cap1 len`; pairs whose reason passes `goOn`
  (default: `noHit`, `noPartner`, `tooShort`; hook for ties / non-proper pairs later)
  go to pass 2 at caps `cap2 len` (a mate keeps its pass-1 cap when the pass-2 cap is
  not deeper or not on the fast path).  `routeKP_ok`: the routed output is settled at
  the caps of the pass that settled it (`Settled`): mapped = `pairSpecT` there, a search
  reason holds there, `tooShort` = off the fast path there.
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-! ## Search: any hit within the cap -/

section top
variable (P : Nat) (read : List Char) (g : Genome) (gbs : Array ByteArray) (R : ByteArray)
  (hg : GenomeBytes gbs g) (hr : Encodes R read)
  {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G : ByteArray) (offs : Array Nat)
  (hcat : catOk G offs gbs = true)
  (hlk : ∀ (R' : ByteArray) s base, s + q ≤ R'.size →
    LookOkS G R' s base 0 (LookG.look ix G R' s base (LookG.prep ix (seedHashAt R' s))))

include hg hr hcat hlk

/-- The search's best penalty is within the cap exactly when the read has a hit. -/
theorem pen_le_iff (hf : fastT P R = true) :
    (mapChromsGB P ix G offs gbs R).pen ≤ P ↔ hitsBoth sc0 (-(P : Int)) g read ≠ [] := by
  unfold fastT at hf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
  obtain ⟨S, hi, hall⟩ := mapChromsGB_inv P read g gbs R hg hr ix G offs hcat hlk hf.1 hf.2
  have key : ∀ (st : Strand) w' s', (strandScore g read st w' = some s' ∧ -(P : Int) ≤ s') ↔
      (cwS P read g st w' ≤ P ∧ s' = -(cwS P read g st w' : Int)) := by
    intro st w' s'
    cases st with
    | fwd => exact cwT_iff P read g w' s'
    | rev => exact cwT_iff P (revComp read) g w' s'
  constructor
  · intro hp hn
    have hw := hi.hit hp
    have hb : cwB P read g (mapChromsGB P ix G offs gbs R).win ≤ P := by omega
    have hd := cwS_decB P read g (mapChromsGB P ix G offs gbs R).win
    generalize decB g.length (mapChromsGB P ix G offs gbs R).win = p at hd
    have h2 := (key p.2 p.1 _).mpr ⟨by omega, rfl⟩
    have hm : (p, -(cwS P read g p.2 p.1 : Int)) ∈ hitsBoth sc0 (-(P : Int)) g read :=
      (mem_hitsBoth_T _ _ _ _ _).mpr ⟨strandScore_allWindows g read p.2 p.1 _ h2.1, h2.1, h2.2⟩
    rw [hn] at hm; cases hm
  · intro hn
    obtain ⟨⟨p, s⟩, hm⟩ := List.exists_mem_of_ne_nil _ hn
    rw [mem_hitsBoth_T] at hm
    obtain ⟨h1, -⟩ := (key p.2 p.1 s).mp ⟨hm.2.1, hm.2.2⟩
    have := hi.min _ (hall _ (by rw [cwB_encB P read g p h1]; exact h1))
    rw [cwB_encB P read g p h1] at this
    omega

end top

/-! ## Algorithm -/

/-- One mate's search: its answer, and whether it has any hit within the cap. -/
abbrev MateR := Option (Placement × Int) × Bool

/-- `mapFastGBKPp` (fast path) with the any-hit flag. -/
def mateKP {L Pp : Type} [LookG L Pp] [Inhabited Pp] (P : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (pgs : Array PGen) (R : ByteArray) (s : PrepM Pp) : MateR :=
  let b := mapChromsGBFG (kerHKG R s.K1 (pgs ++ pgs) (pgs ++ pgs))
    (kerHKG s.Rr s.K2 (pgs ++ pgs) (pgs ++ pgs)) P ix G offs pgs R s.Rr s.ps s.pr
  (decodeP pgs.size P b, decide (b.pen ≤ P))

/-- A pass's answer for a pair. -/
inductive Out where
  | mapped (x : (Placement × Int) × (Placement × Int))
  | unmapped (r : Reason) (k : Option (Placement × Int))
deriving Inhabited, BEq

def Out.toOpt : Out → Option ((Placement × Int) × (Placement × Int))
  | .mapped x => some x
  | .unmapped _ _ => none

/-- Mates exchanged (a pass run with mate 2 first). -/
def Out.swap : Out → Out
  | .mapped x => .mapped (x.2, x.1)
  | .unmapped r k => .unmapped r k

/-- Mate `A` (label `ma`) over the genome, mate `B` (label `mb`) near it first. -/
@[inline] def stepR (ma mb : Mate) (lo hi : Nat) (mA : MateR) (nh : Placement → Bool) (mB : Unit → MateR) : Out :=
  match mA with
  | (none, h) => .unmapped (if h then .tie ma else .noHit ma) none
  | (some a, _) =>
    if nh a.1 then .unmapped (.noPartner mb) (some a) else
    match mB () with
    | (none, h) => .unmapped (if h then .tie mb else .noHit mb) none
    | (some b, _) => if properPair lo hi a.1 b.1 then .mapped (a, b) else .unmapped .notProper none

/-! ### Pluggable pass kernel

A pass kernel (`PassKer`): per-mate preparation, the lookup cost used to pick the
mate searched over the genome, the whole-genome search of a mate at cap `P` (answer +
any-hit flag) and the region test near a placement.  The passes and the router are
generic in it; `KerOk` is what a kernel must prove, and `routeG_ok` holds for any two
kernels (pass 1, pass 2) meeting it.  Today's kernel is `kpKer` (`kpKer_ok`); a faster
proved deep-cap search plugs in as pass 2's kernel. -/
structure PassKer where
  Prep : Type
  prep : ByteArray → Prep
  cost : Nat → Prep → Nat
  mate : Nat → ByteArray → Prep → MateR
  region : Nat → ByteArray → Placement → Bool

/-- **Pass kernel**: mates at caps `P1`, `P2` (both on the fast path, `fastT`); `ord`
picks the mate searched over the genome (`some true` = mate 2), `none` = the cheaper
lookups (`K.cost`). -/
def passG (K : PassKer) (P1 P2 : Nat) (ord : Option Bool) (lo hi : Nat) (R1 R2 : ByteArray) : Out :=
  let s1 := K.prep R1
  let s2 := K.prep R2
  let sw := match ord with
    | some o => o
    | none => decide (K.cost P2 s2 < K.cost P1 s1)
  if sw then
    (stepR .two .one lo hi (K.mate P2 R2 s2) (K.region P1 R1) (fun _ => K.mate P1 R1 s1)).swap
  else
    stepR .one .two lo hi (K.mate P1 R1 s1) (K.region P2 R2) (fun _ => K.mate P2 R2 s2)

/-- **Known mate**: mate `ma`'s answer `a` is known; mate `mb` (read `RB`, cap `PB`) is
searched near it first. -/
def passKnownG (K : PassKer) (ma : Mate) (a : Placement × Int) (PB : Nat) (lo hi : Nat) (RB : ByteArray) : Out :=
  let o := stepR ma ma.other lo hi (some a, true) (K.region PB RB) (fun _ => K.mate PB RB (K.prep RB))
  match ma with
  | .one => o
  | .two => o.swap

/-- Today's kernel: `mateKP` over the (packed) genome, `regionNoHitKP` near a placement. -/
def kpKer {L Pp L2 Pp2 : Type} [LookG L Pp] [Inhabited Pp] [LookG L2 Pp2] [Inhabited Pp2]
    (lo hi : Nat) (ix : L) (rl : Nat → Nat → L2) (G : ByteArray)
    (offs : Array Nat) (pgs : Array PGen) : PassKer where
  Prep := PrepM Pp
  prep R := prepMate ix R
  cost P s := costP ix P s
  mate P R s := mateKP P ix G offs pgs R s
  region P R := regionNoHitKP P lo hi rl G offs pgs R

/-! ## Router -/

/-- Router settings.  `cap1` / `cap2`: penalty cap by mate length for pass 1 / pass 2;
`goOn`: unmapped reasons that get pass 2 (default `noHit`, `noPartner`, `tooShort`).
Hook: ties and non-proper pairs keep their reason today; a later option can send them on
(`goOn`) or to another kernel. -/
structure RouteCfg where
  cap1 : Nat → Nat
  pass2 : Bool := false
  cap2 : Nat → Nat := fun _ => 0
  goOn : Reason → Bool := fun r => match r with
    | .noHit _ | .noPartner _ | .tooShort _ => true
    | _ => false

/-- A routed pair: the answer, the pass that settled it (0 = trimmed away, 1, 2), and the
per-mate caps of that pass. -/
structure Routed where
  out : Out
  pass : Nat
  c1 : Nat
  c2 : Nat
deriving Inhabited

/-- Pass-2 cap of a mate: the pass-2 cap when it is deeper and on the fast path, else the
pass-1 cap. -/
def cap2Of (cfg : RouteCfg) (R : ByteArray) : Nat :=
  let c1 := cfg.cap1 R.size
  let c2 := cfg.cap2 R.size
  if c1 ≤ c2 && fastT c2 R then c2 else c1

/-- One pass at caps `P1`, `P2`: length reasons first, then the kernel. -/
def passLenG (K : PassKer) (P1 P2 : Nat) (ord : Option Bool) (lo hi : Nat) (R1 R2 : ByteArray) : Out :=
  if !fastT P1 R1 then .unmapped (.tooShort .one) none
  else if !fastT P2 R2 then .unmapped (.tooShort .two) none
  else passG K P1 P2 ord lo hi R1 R2

/-- Pass 2 for a pair pass 1 left with reason `r` (pass-1 caps `A1 A2`, pass-2 caps `B1 B2`). -/
def pass2G (K : PassKer) (A1 A2 B1 B2 : Nat) (r : Reason) (lo hi : Nat) (R1 R2 : ByteArray)
    (known : Option (Placement × Int)) : Out :=
  match r, known with
  | .noPartner .two, some a =>
    if A1 ≤ B1 && fastT B2 R2 then passKnownG K .one a B2 lo hi R2
    else passLenG K B1 B2 none lo hi R1 R2
  | .noPartner .one, some a =>
    if A2 ≤ B2 && fastT B1 R1 then passKnownG K .two a B1 lo hi R1
    else passLenG K B1 B2 none lo hi R1 R2
  -- the mate without hits goes near the other one
  | .noHit .one, _ => passLenG K B1 B2 (some true) lo hi R1 R2
  | .noHit .two, _ => passLenG K B1 B2 (some false) lo hi R1 R2
  | _, _ => passLenG K B1 B2 none lo hi R1 R2

/-- **Router**: pass 1 (kernel `K1`), then (option) pass 2 (kernel `K2`) on the pairs
whose reason passes `goOn`. -/
def routeG (cfg : RouteCfg) (K1 K2 : PassKer) (lo hi : Nat) (O1 O2 : Option ByteArray) : Routed :=
  match O1, O2 with
  | none, _ => ⟨.unmapped (.trimmedAway .one) none, 0, 0, 0⟩
  | _, none => ⟨.unmapped (.trimmedAway .two) none, 0, 0, 0⟩
  | some R1, some R2 =>
    let A1 := cfg.cap1 R1.size
    let A2 := cfg.cap1 R2.size
    let o := passLenG K1 A1 A2 none lo hi R1 R2
    match o with
    | .mapped _ => ⟨o, 1, A1, A2⟩
    | .unmapped r k =>
      let B1 := cap2Of cfg R1
      let B2 := cap2Of cfg R2
      if cfg.pass2 && cfg.goOn r && !(B1 == A1 && B2 == A2) then
        ⟨pass2G K2 A1 A2 B1 B2 r lo hi R1 R2 k, 2, B1, B2⟩
      else ⟨o, 1, A1, A2⟩

/-- The router with today's kernel in both passes. -/
def routeKP {L Pp L2 Pp2 : Type} [LookG L Pp] [Inhabited Pp] [LookG L2 Pp2] [Inhabited Pp2] (cfg : RouteCfg)
    (lo hi : Nat) (ix : L) (rl : Nat → Nat → L2) (G : ByteArray)
    (offs : Array Nat) (pgs : Array PGen) (O1 O2 : Option ByteArray) : Routed :=
  let K := kpKer lo hi ix rl G offs pgs
  routeG cfg K K lo hi O1 O2

/-! ## What a routed answer means -/

/-- The other mate's answer carried with `noPartner` (reused by pass 2). -/
def KnownOk (T : Mate → Int) (g : Genome) (rd : Mate → List Char) : Reason → Option (Placement × Int) → Prop
  | .noPartner m, some a => mapSpecBoth sc0 (T m.other) g (rd m.other) = some a
  | _, _ => True

/-- A routed answer, against the specification at the caps `c1`, `c2` it reports. -/
def Settled (lo hi : Nat) (g : Genome) (m1 m2 : List Char) (R1 R2 : ByteArray) (r : Routed) : Prop :=
  match r.out with
  | .mapped x => pairSpecT (-(r.c1 : Int)) (-(r.c2 : Int)) lo hi g m1 m2 = some x
  | .unmapped (.tooShort .one) _ => fastT r.c1 R1 = false
  | .unmapped (.tooShort .two) _ => fastT r.c2 R2 = false
  | .unmapped (.trimmedAway _) _ => False
  | .unmapped rs k => ReasonOk (Mate.sel (-(r.c1 : Int)) (-(r.c2 : Int))) lo hi g (Mate.sel m1 m2) rs ∧
      KnownOk (Mate.sel (-(r.c1 : Int)) (-(r.c2 : Int))) g (Mate.sel m1 m2) rs k

/-- Settled with a search reason: the pair is `none` at the reported caps. -/
theorem settled_none (lo hi : Nat) (g : Genome) (m1 m2 : List Char) (R1 R2 : ByteArray) (r : Routed)
    (rs : Reason) (hrs : rs.searched = true) {k : Option (Placement × Int)} (ho : r.out = .unmapped rs k) (h : Settled lo hi g m1 m2 R1 R2 r) :
    pairSpecT (-(r.c1 : Int)) (-(r.c2 : Int)) lo hi g m1 m2 = none := by
  unfold Settled at h
  rw [ho] at h
  have e := reasonOk_none (Mate.sel (-(r.c1 : Int)) (-(r.c2 : Int))) lo hi g (Mate.sel m1 m2) rs
  cases rs with
  | trimmedAway m => simp [Reason.searched] at hrs
  | tooShort m => simp [Reason.searched] at hrs
  | noHit m => exact e h.1
  | tie m => exact e h.1
  | noPartner m => exact e h.1
  | notProper => exact e h.1

/-! ## Proofs: the step -/

/-- What a mate's search gives (cap `T`): the answer, and the any-hit flag when unmapped. -/
def MateOk (T : Int) (g : Genome) (m : List Char) (x : MateR) : Prop :=
  x.1 = mapSpecBoth sc0 T g m ∧ (x.1 = none → (x.2 = true ↔ hitsBoth sc0 T g m ≠ []))

/-- The step, with mate `A` = `ma` and mate `B` = `ma.other`. -/
theorem stepR_ok (ma : Mate) (T : Mate → Int) (lo hi : Nat) (g : Genome) (rd : Mate → List Char)
    (mA : MateR) (nh : Placement → Bool) (mB : MateR)
    (hA : mA.1 = mapSpecBoth sc0 (T ma) g (rd ma))
    (hAf : mA.1 = none → (mA.2 = true ↔ hitsBoth sc0 (T ma) g (rd ma) ≠ []))
    (hB : MateOk (T ma.other) g (rd ma.other) mB)
    (hnh : ∀ a, nh a = true → ∀ p ∈ hitsBoth sc0 (T ma.other) g (rd ma.other), properPair lo hi a p.1 = false) :
    (∀ x, stepR ma ma.other lo hi mA nh (fun _ => mB) = .mapped x →
      mapSpecBoth sc0 (T ma) g (rd ma) = some x.1 ∧ mapSpecBoth sc0 (T ma.other) g (rd ma.other) = some x.2 ∧
        properPair lo hi x.1.1 x.2.1 = true) ∧
    (∀ rs k, stepR ma ma.other lo hi mA nh (fun _ => mB) = .unmapped rs k →
      (rs = .notProper → ∃ a b, mapSpecBoth sc0 (T ma) g (rd ma) = some a ∧
        mapSpecBoth sc0 (T ma.other) g (rd ma.other) = some b ∧ properPair lo hi a.1 b.1 = false) ∧
      (rs ≠ .notProper → rs.searched = true ∧ ReasonOk T lo hi g rd rs ∧ KnownOk T g rd rs k)) := by
  have oo : ma.other.other = ma := by cases ma <;> rfl
  obtain ⟨xA, fA⟩ := mA
  obtain ⟨xB, fB⟩ := mB
  obtain ⟨hB1, hBf⟩ := hB
  simp only at hA hAf hB1 hBf
  cases xA with
  | none =>
    refine ⟨fun x h => by simp [stepR] at h, fun rs k h => ?_⟩
    simp only [stepR, Out.unmapped.injEq] at h
    obtain ⟨h, hk⟩ := h
    subst hk
    have hf := hAf rfl
    subst h
    by_cases hfa : fA = true
    · simp only [hfa, if_true]
      exact ⟨fun h => Reason.noConfusion h, fun _ => ⟨rfl, ⟨hf.mp hfa, hA.symm⟩, trivial⟩⟩
    · simp only [Bool.not_eq_true] at hfa
      simp only [hfa]
      refine ⟨fun h => Reason.noConfusion h, fun _ => ⟨rfl, ?_, trivial⟩⟩
      show hitsBoth sc0 (T ma) g (rd ma) = []
      apply Classical.byContradiction
      intro hn
      have := hf.mpr hn
      rw [hfa] at this; cases this
  | some a =>
    by_cases hn : nh a.1 = true
    · refine ⟨fun x h => by simp [stepR, hn] at h, fun rs k h => ?_⟩
      simp only [stepR, hn, if_true, Out.unmapped.injEq] at h
      obtain ⟨h, hk⟩ := h
      subst hk
      subst h
      have ha : mapSpecBoth sc0 (T ma.other.other) g (rd ma.other.other) = some a := by rw [oo, ← hA]
      exact ⟨fun h => Reason.noConfusion h, fun _ => ⟨rfl, ⟨a, ha, hnh a.1 hn⟩, ha⟩⟩
    · simp only [Bool.not_eq_true] at hn
      cases xB with
      | none =>
        refine ⟨fun x h => by simp [stepR, hn] at h, fun rs k h => ?_⟩
        simp only [stepR, hn, Bool.false_eq_true, if_false, Out.unmapped.injEq] at h
        obtain ⟨h, hk⟩ := h
        subst hk
        have hf := hBf rfl
        subst h
        by_cases hfb : fB = true
        · simp only [hfb, if_true]
          exact ⟨fun h => Reason.noConfusion h, fun _ => ⟨rfl, ⟨hf.mp hfb, hB1.symm⟩, trivial⟩⟩
        · simp only [Bool.not_eq_true] at hfb
          simp only [hfb]
          refine ⟨fun h => Reason.noConfusion h, fun _ => ⟨rfl, ?_, trivial⟩⟩
          show hitsBoth sc0 (T ma.other) g (rd ma.other) = []
          apply Classical.byContradiction
          intro hn'
          have := hf.mpr hn'
          rw [hfb] at this; cases this
      | some b =>
        by_cases hp : properPair lo hi a.1 b.1 = true
        · refine ⟨fun x h => ?_, fun rs k h => by simp [stepR, hn, hp] at h⟩
          simp only [stepR, hn, hp, Bool.false_eq_true, if_false, if_true, Out.mapped.injEq] at h
          subst h
          exact ⟨hA.symm, hB1.symm, hp⟩
        · simp only [Bool.not_eq_true] at hp
          refine ⟨fun x h => by simp [stepR, hn, hp] at h, fun rs k h => ?_⟩
          simp only [stepR, hn, hp, Bool.false_eq_true, if_false, Out.unmapped.injEq] at h
          obtain ⟨h, hk⟩ := h
          subst hk
          subst h
          exact ⟨fun _ => ⟨a, b, hA.symm, hB1.symm, hp⟩, fun h => absurd rfl h⟩

/-! ## Proofs: the passes, for any kernel meeting `KerOk` -/

section generic
variable (lo hi : Nat) (g : Genome) (m1 m2 : List Char) (R1 R2 : ByteArray)

/-- What a pass kernel guarantees at caps `T1`, `T2`. -/
def PassOk (T1 T2 : Int) (o : Out) : Prop :=
  match o with
  | .mapped x => pairSpecT T1 T2 lo hi g m1 m2 = some x
  | .unmapped rs k => rs.searched = true ∧ ReasonOk (Mate.sel T1 T2) lo hi g (Mate.sel m1 m2) rs ∧
      KnownOk (Mate.sel T1 T2) g (Mate.sel m1 m2) rs k

/-- **What a pass kernel must prove**: for every read on the fast path at cap `P`, the
whole-genome search gives the specification's answer and any-hit flag, and a region
miss rules out every proper partner among the read's hits. -/
def KerOk (K : PassKer) : Prop :=
  ∀ (P : Nat) (R : ByteArray) (m : List Char), Encodes R m → fastT P R = true →
    MateOk (-(P : Int)) g m (K.mate P R (K.prep R)) ∧
    ∀ a, K.region P R a = true → ∀ p ∈ hitsBoth sc0 (-(P : Int)) g m, properPair lo hi a p.1 = false

/-- The step in both orientations gives `PassOk`. -/
theorem stepR_passOk (sw : Bool) (P1 P2 : Nat) (mA mB : MateR) (nh : Placement → Bool)
    (hA : MateOk (-(((if sw then P2 else P1 : Nat)) : Int)) g (if sw then m2 else m1) mA)
    (hB : MateOk (-(((if sw then P1 else P2 : Nat)) : Int)) g (if sw then m1 else m2) mB)
    (hnh : ∀ a, nh a = true → ∀ p ∈ hitsBoth sc0 (-(((if sw then P1 else P2 : Nat)) : Int)) g (if sw then m1 else m2),
      properPair lo hi a p.1 = false) :
    PassOk lo hi g m1 m2 (-(P1 : Int)) (-(P2 : Int))
      (if sw then (stepR .two .one lo hi mA nh (fun _ => mB)).swap else stepR .one .two lo hi mA nh (fun _ => mB)) := by
  cases sw with
  | false =>
    simp only [Bool.false_eq_true, if_false] at hA hB hnh ⊢
    obtain ⟨hm, hu⟩ := stepR_ok .one (Mate.sel (-(P1 : Int)) (-(P2 : Int))) lo hi g (Mate.sel m1 m2) mA nh mB
      hA.1 hA.2 hB hnh
    simp only [Mate.other] at hm hu
    unfold PassOk
    cases ho : stepR .one .two lo hi mA nh (fun _ => mB) with
    | mapped x =>
      obtain ⟨ha, hb, hp⟩ := hm x ho
      show pairSpecT _ _ lo hi g m1 m2 = some x
      unfold pairSpecT
      simp only [Mate.sel] at ha hb
      rw [ha, hb]; simp [hp]
    | unmapped rs k =>
      obtain ⟨hnp, hok⟩ := hu rs k ho
      by_cases hr : rs = .notProper
      · subst hr; exact ⟨rfl, hnp rfl, trivial⟩
      · exact hok hr
  | true =>
    simp only [if_true] at hA hB hnh ⊢
    obtain ⟨hm, hu⟩ := stepR_ok .two (Mate.sel (-(P1 : Int)) (-(P2 : Int))) lo hi g (Mate.sel m1 m2) mA nh mB
      hA.1 hA.2 hB hnh
    simp only [Mate.other] at hm hu
    unfold PassOk
    cases ho : stepR .two .one lo hi mA nh (fun _ => mB) with
    | mapped x =>
      obtain ⟨ha, hb, hp⟩ := hm x ho
      show pairSpecT _ _ lo hi g m1 m2 = some (x.2, x.1)
      unfold pairSpecT
      simp only [Mate.sel] at ha hb
      have hp' : properPair lo hi x.2.1 x.1.1 = true := by rw [properPair_comm]; exact hp
      rw [ha, hb]; simp [hp']
    | unmapped rs k =>
      obtain ⟨hnp, hok⟩ := hu rs k ho
      by_cases hr : rs = .notProper
      · subst hr
        obtain ⟨a, b, ha, hb, hp⟩ := hnp rfl
        refine ⟨rfl, ⟨b, a, hb, ha, ?_⟩, trivial⟩
        rw [properPair_comm]; exact hp
      · exact hok hr

/-- `PassOk` at caps `c1`, `c2` is `Settled` there. -/
theorem passOk_settled (c1 c2 n : Nat) (o : Out) (h : PassOk lo hi g m1 m2 (-(c1 : Int)) (-(c2 : Int)) o) :
    Settled lo hi g m1 m2 R1 R2 ⟨o, n, c1, c2⟩ := by
  unfold Settled
  unfold PassOk at h
  cases o with
  | mapped x => exact h
  | unmapped rs k =>
    obtain ⟨hs, hr⟩ := h
    cases rs with
    | trimmedAway m => simp [Reason.searched] at hs
    | tooShort m => simp [Reason.searched] at hs
    | noHit m => exact hr
    | tie m => exact hr
    | noPartner m => exact hr
    | notProper => exact hr

variable (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (K : PassKer) (hK : KerOk lo hi g K)
include h1 h2 hK

/-- **Pass kernel = specification** at caps `P1`, `P2` (both mates on the fast path). -/
theorem passG_ok (P1 P2 : Nat) (ord : Option Bool) (hf1 : fastT P1 R1 = true) (hf2 : fastT P2 R2 = true) :
    PassOk lo hi g m1 m2 (-(P1 : Int)) (-(P2 : Int)) (passG K P1 P2 ord lo hi R1 R2) := by
  unfold passG
  simp only []
  generalize (match ord with
    | some o => o
    | none => decide (K.cost P2 (K.prep R2) < K.cost P1 (K.prep R1))) = sw
  obtain ⟨k1, r1⟩ := hK P1 R1 m1 h1 hf1
  obtain ⟨k2, r2⟩ := hK P2 R2 m2 h2 hf2
  cases sw with
  | true =>
    have := stepR_passOk lo hi g m1 m2 true P1 P2 _ _ _
      (by simpa using k2) (by simpa using k1) (by simpa using r1)
    simpa using this
  | false =>
    have := stepR_passOk lo hi g m1 m2 false P1 P2 _ _ _
      (by simpa using k1) (by simpa using k2) (by simpa using r2)
    simpa using this

/-- **Known mate = specification**: mate `ma`'s answer at its cap `PA` is `a`; mate
`ma.other` at cap `PB`. -/
theorem passKnownG_ok (ma : Mate) (PA PB : Nat) (a : Placement × Int)
    (ha : mapSpecBoth sc0 (-(PA : Int)) g (Mate.sel m1 m2 ma) = some a)
    (hf : fastT PB (Mate.sel R1 R2 ma.other) = true) :
    PassOk lo hi g m1 m2 (Mate.sel (-(PA : Int)) (-(PB : Int)) ma) (Mate.sel (-(PA : Int)) (-(PB : Int)) ma.other)
      (passKnownG K ma a PB lo hi (Mate.sel R1 R2 ma.other)) := by
  cases ma with
  | one =>
    obtain ⟨k, r⟩ := hK PB R2 m2 h2 hf
    have := stepR_passOk lo hi g m1 m2 false PA PB (some a, true) _ _
      ⟨by simpa using ha.symm, fun h => by cases h⟩ (by simpa using k) (by simpa using r)
    simpa [passKnownG, Mate.sel, Mate.other] using this
  | two =>
    obtain ⟨k, r⟩ := hK PB R1 m1 h1 hf
    have := stepR_passOk lo hi g m1 m2 true PB PA (some a, true) _ _
      ⟨by simpa using ha.symm, fun h => by cases h⟩ (by simpa using k) (by simpa using r)
    simpa [passKnownG, Mate.sel, Mate.other] using this

/-- A pass with its length reasons. -/
theorem passLenG_ok (P1 P2 : Nat) (ord : Option Bool) (n : Nat) :
    Settled lo hi g m1 m2 R1 R2 ⟨passLenG K P1 P2 ord lo hi R1 R2, n, P1, P2⟩ := by
  unfold passLenG
  by_cases hf1 : fastT P1 R1 = true
  · by_cases hf2 : fastT P2 R2 = true
    · simp only [hf1, hf2, Bool.not_true, Bool.false_eq_true, if_false]
      exact passOk_settled lo hi g m1 m2 R1 R2 P1 P2 n _
        (passG_ok lo hi g m1 m2 R1 R2 h1 h2 K hK P1 P2 ord hf1 hf2)
    · simp only [Bool.not_eq_true] at hf2
      simp only [hf1, hf2, Bool.not_true, Bool.not_false, Bool.false_eq_true, if_false, if_true]
      exact hf2
  · simp only [Bool.not_eq_true] at hf1
    simp only [hf1, Bool.not_false, if_true]
    exact hf1

/-- Pass 2 after pass 1 left the pair unmapped with reason `r` (and the other mate's
answer `k` for `noPartner`), settled at the pass-1 caps `A1`, `A2`. -/
theorem pass2G_ok (A1 A2 B1 B2 : Nat) (r : Reason) (k : Option (Placement × Int)) (n : Nat)
    (h : Settled lo hi g m1 m2 R1 R2 ⟨.unmapped r k, 1, A1, A2⟩) :
    Settled lo hi g m1 m2 R1 R2 ⟨pass2G K A1 A2 B1 B2 r lo hi R1 R2 k, n, B1, B2⟩ := by
  have pl := fun ord => passLenG_ok lo hi g m1 m2 R1 R2 h1 h2 K hK B1 B2 ord n
  unfold pass2G
  split
  · next a =>
    split
    · next hc =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      have ha : mapSpecBoth sc0 (-(A1 : Int)) g m1 = some a := h.2
      have ha' := mapSpecBoth_mono_some _ (-(B1 : Int)) (by omega) g m1 a ha
      have := passKnownG_ok lo hi g m1 m2 R1 R2 h1 h2 K hK .one B1 B2 a ha' hc.2
      exact passOk_settled lo hi g m1 m2 R1 R2 B1 B2 n _ this
    · exact pl none
  · next a =>
    split
    · next hc =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      have ha : mapSpecBoth sc0 (-(A2 : Int)) g m2 = some a := h.2
      have ha' := mapSpecBoth_mono_some _ (-(B2 : Int)) (by omega) g m2 a ha
      have := passKnownG_ok lo hi g m1 m2 R1 R2 h1 h2 K hK .two B2 B1 a ha' hc.2
      exact passOk_settled lo hi g m1 m2 R1 R2 B1 B2 n _ this
    · exact pl none
  · exact pl _
  · exact pl _
  · exact pl none

omit hK in
/-- **Router = specification**, for any pass-1 kernel `K1` and pass-2 kernel `K2`
meeting `KerOk`.  Every routed pair is settled at the caps of the pass that settled it:
mapped = `pairSpecT` there, a search reason holds of the specification there (so
`pairSpecT = none`, `settled_none`), `tooShort` = off the fast path there. -/
theorem routeG_ok (cfg : RouteCfg) (K1 K2 : PassKer) (hK1 : KerOk lo hi g K1) (hK2 : KerOk lo hi g K2) :
    Settled lo hi g m1 m2 R1 R2 (routeG cfg K1 K2 lo hi (some R1) (some R2)) := by
  have hp := passLenG_ok lo hi g m1 m2 R1 R2 h1 h2 K1 hK1 (cfg.cap1 R1.size) (cfg.cap1 R2.size) none 1
  unfold routeG
  simp only []
  generalize passLenG K1 (cfg.cap1 R1.size) (cfg.cap1 R2.size) none lo hi R1 R2 = o at hp ⊢
  cases o with
  | mapped x => exact hp
  | unmapped r k =>
    simp only []
    split
    · exact pass2G_ok lo hi g m1 m2 R1 R2 h1 h2 K2 hK2 _ _ _ _ r k 2 hp
    · exact hp

end generic

/-! ## Proofs: today's kernel on the packed genome -/

section packed
variable (lo hi : Nat) (g : Genome) (m1 m2 : List Char) (ix : Mz.MzIdx) (G : PGen)
  (offs ns : Array Nat) (R1 R2 : ByteArray) (hcut : cutOk G offs ns = true)
  (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2)
  (hchk : Mz.check2P ix G = true)

/-- The whole-genome search of one mate, any-hit flag included. -/
theorem mateKP_ok (P : Nat) (R : ByteArray) (m : List Char) (hr : Encodes R m)
    (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) g) (hcut : cutOk G offs ns = true)
    (hchk : Mz.check2P ix G = true) (hf : fastT P R = true) :
    MateOk (-(P : Int)) g m (mateKP P ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) R
      (prepMate ((ix, G) : PkMz) R)) := by
  have hG : ∀ R s base p, LookG.look ((ix, G) : PkMz) ByteArray.empty R s base p =
      LookG.look ((ix, G) : PkMz) (Mz.unpack G) R s base p := fun _ _ _ _ => rfl
  have hcat := catOk_cut G offs ns hcut
  have hlk := lookOk_pk ix G hchk
  have eb : mapChromsGBKG P ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) (cutAll G offs ns) R =
      mapChromsGB P ((ix, G) : PkMz) (Mz.unpack G) offs ((cutAll G offs ns).map Mz.unpack) R := by
    rw [mapChromsGBKG_unpack, mapChromsGBK_eq_rep P _ _ offs _ _ (repAllK_unpack _)]
    simp only [mapChromsGB, ilG_congrG ((ix, G) : PkMz) ByteArray.empty (Mz.unpack G) hG]
  have em : mapFastGBKP P ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) R = mapSpecBoth sc0 (-(P : Int)) g m := by
    rw [mapFastGBKP_eq, mapFastGB_congrG ((ix, G) : PkMz) ByteArray.empty (Mz.unpack G) hG]
    exact mapFastGB_eq_mapSpecBoth P g m _ R _ _ offs hg hr hcat hlk
  have e1 : (mateKP P ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) R (prepMate ((ix, G) : PkMz) R)) =
      (decodeP (cutAll G offs ns).size P (mapChromsGBKG P ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns)
        (cutAll G offs ns) R),
       decide ((mapChromsGBKG P ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) (cutAll G offs ns) R).pen ≤ P)) := rfl
  have e2 : mapFastGBKP P ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) R =
      decodeP (cutAll G offs ns).size P (mapChromsGBKG P ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns)
        (cutAll G offs ns) R) := by
    unfold mapFastGBKP; rw [if_pos hf]
  rw [e1]
  refine ⟨by simp only []; rw [← e2, em], fun _ => ?_⟩
  simp only [decide_eq_true_eq]
  rw [eb]
  exact pen_le_iff P m g _ R hg hr _ _ offs hcat hlk hf

/-- Region miss: no hit of the read (cap `P`) is a proper partner of `a`. -/
theorem regionKP_ok (P : Nat) (R : ByteArray) (m : List Char) (hr : Encodes R m)
    (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) g) (hcut : cutOk G offs ns = true)
    (hchk : Mz.check2P ix G = true) :
    ∀ a, regionNoHitKP P lo hi (fun a b => ((((ix, G) : PkMz), a, b) : RgMz)) ByteArray.empty offs
        (cutAll G offs ns) R a = true →
      ∀ p ∈ hitsBoth sc0 (-(P : Int)) g m, properPair lo hi a p.1 = false := by
  intro a h p hp
  rw [mem_hitsBoth_T] at hp
  exact regionNoHitKP_sound P lo hi m g _ R hg hr _ ByteArray.empty (Mz.unpack G) offs
    (fun _ _ _ _ _ _ _ => rfl) (catOk_cut G offs ns hcut)
    (fun a b B hb hB hBi => lookOk_rg ix G hchk a b B hb hB hBi) a h p.1 p.2 hp.2.1 hp.2.2


include hcut hg hchk in
/-- Today's kernel meets `KerOk`. -/
theorem kpKer_ok : KerOk lo hi g (kpKer lo hi ((ix, G) : PkMz) (fun a b => ((((ix, G) : PkMz), a, b) : RgMz))
    ByteArray.empty offs (cutAll G offs ns)) :=
  fun P R m hr hf => ⟨mateKP_ok g ix G offs ns P R m hr hg hcut hchk hf,
    regionKP_ok lo hi g ix G offs ns P R m hr hg hcut hchk⟩

include hcut hg h1 h2 hchk in
/-- **Router (today's kernel) = specification.** -/
theorem routeKP_ok (cfg : RouteCfg) :
    Settled lo hi g m1 m2 R1 R2 (routeKP cfg lo hi ((ix, G) : PkMz)
      (fun a b => ((((ix, G) : PkMz), a, b) : RgMz)) ByteArray.empty offs (cutAll G offs ns) (some R1) (some R2)) :=
  have hK := kpKer_ok lo hi g ix G offs ns hcut hg hchk
  routeG_ok lo hi g m1 m2 R1 R2 h1 h2 cfg _ _ hK hK

end packed

end MapSpec.Fast

#print axioms MapSpec.Fast.pen_le_iff
#print axioms MapSpec.Fast.mateKP_ok
#print axioms MapSpec.Fast.kpKer_ok
#print axioms MapSpec.Fast.passG_ok
#print axioms MapSpec.Fast.passKnownG_ok
#print axioms MapSpec.Fast.passLenG_ok
#print axioms MapSpec.Fast.pass2G_ok
#print axioms MapSpec.Fast.routeG_ok
#print axioms MapSpec.Fast.routeKP_ok
#print axioms MapSpec.Fast.settled_none
