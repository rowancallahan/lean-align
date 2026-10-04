import MzCheckFast
import MapperPGen

/-!
# Minimizer index checker and builder over a packed genome

The checker `Mz.check2` and the builder `Mz.buildW` read the genome only
through `G.get!` and `G.size`.  `check2P` / `buildWP` are copies reading a
`PGen` (pool/mapper/MapperPGen.lean).  `check2P_eq`: under `Rep P G`,
`check2P ix P = check2 ix G`.  `unpack P` (never run) is the byte genome a
`PGen` spells, and `Rep P (unpack P)` always holds (`rep_unpack`), so a packed
genome and its index are checked without the byte genome in memory.
-/

namespace MapSpec.Mz

open MapSpec.Fast (PGen Rep)

/-- The bytes a packed genome spells (for statements only). -/
def unpack (P : PGen) : ByteArray := ⟨(Array.range P.n).map P.get⟩

theorem rep_unpack (P : PGen) : Rep P (unpack P) := by
  refine ⟨by simp [unpack, ByteArray.size], fun i => ?_⟩
  by_cases hi : i < P.n
  · simp [unpack, ByteArray.get!, hi]
  · rw [Fast.get!_out _ i (by simp [unpack, ByteArray.size]; omega)]
    exact Fast.get_out P i (by omega)

/-! ## Copies reading a `PGen` -/

def wcUP (B : PGen) (i stop : Nat) (x : UInt64) : UInt64 :=
  if i < stop then
    let b := B.get i
    if acgt b then wcUP B (i + 1) stop (x * 4 + (byteCode b).toUInt64) else BADU
  else x
termination_by stop - i

def allAP (B : PGen) (i stop : Nat) : Bool :=
  if i < stop then acgt (B.get i) && allAP B (i + 1) stop else true
termination_by stop - i

def allNotP (B : PGen) (i stop : Nat) : Bool :=
  if i < stop then !acgt (B.get i) && allNotP B (i + 1) stop else true
termination_by stop - i

def wcGoP (B : PGen) (i stop x : Nat) : Nat :=
  if i < stop then wcGoP B (i + 1) stop (x * 4 + byteCode (B.get i)) else x
termination_by stop - i

def rollToP (G : PGen) : (e : Nat) → UInt64 × Nat
  | 0 => (0, 0)
  | e + 1 => roll (G.get e) (rollToP G e).1 (rollToP G e).2

def compRP (ix : MzIdx) (G : PGen) (fill : ByteArray) (last : Nat) :
    (n p : Nat) → (x : UInt64) → (g : Nat) → Bool
  | 0, _, _, _ => true
  | n + 1, p, x, g =>
    let s := roll (G.get (p + q - 1)) x g
    if q ≤ s.2 then
      let v := s.1.toNat
      let o := ix.mini v
      let pm := p + o
      if pm + 1 = last then compRP ix G fill last n (p + 1) s.1 s.2
      else
        let b := ix.hsh (ix.sub v o) >>> ix.kb
        let t := getU32 fill b
        decide (ix.loB b ≤ t) && decide (t < ix.hiB b) && ix.posOf (ix.slot t) == pm &&
          compRP ix G (setU32 fill b (t + 1)) (pm + 1) n (p + 1) s.1 s.2
    else compRP ix G fill last n (p + 1) s.1 s.2

def entryOkP (ix : MzIdx) (G : PGen) (b hi t : Nat) : Bool :=
  let e := (ix.slot t)
  let pos := ix.posOf e
  let tg := ix.tagOf e
  let x := wcUP G pos (pos + ix.k) 0
  let h := ix.hsh x.toNat
  let w1 := ix.c
  decide (pos + ix.k ≤ G.n) && x != BADU && (h >>> ix.kb) == b &&
    ix.keyF tg == (h &&& ix.kbM) &&
    (ix.flagF tg != 0 ||
      (decide (w1 ≤ pos) && decide (pos + ix.k + w1 ≤ G.n) &&
        (let bf := wcUP G (pos - w1) pos 0
         let af := wcUP G (pos + ix.k) (pos + ix.k + w1) 0
         bf != BADU && af != BADU && ix.befF tg == bf.toNat && ix.aftF tg == af.toNat))) &&
    (decide (hi ≤ t + 1) || decide (pos < ix.posOf (ix.slot (t + 1))))

def checkBucketP (ix : MzIdx) (G : PGen) (b hi : Nat) : (n t : Nat) → Bool
  | 0, _ => true
  | n + 1, t => entryOkP ix G b hi t && checkBucketP ix G b hi n (t + 1)

def checkSoundP (ix : MzIdx) (G : PGen) : (n b : Nat) → Bool
  | 0, _ => true
  | n + 1, b =>
    checkBucketP ix G b (ix.hiB b) (ix.hiB b - ix.loB b) (ix.loB b) && checkSoundP ix G n (b + 1)

def runOkP (ix : MzIdx) (G : PGen) (i : Nat) : Bool :=
  let a := ix.ra i
  let b := ix.rb i
  decide (a < b) && decide (b ≤ G.n) && allNotP G a b &&
    (decide (b = G.n) || acgt (G.get b)) && (decide (a = 0) || acgt (G.get (a - 1))) &&
    (decide (ix.nr ≤ i + 1) || decide (b < ix.ra (i + 1)))

def checkRunsP (ix : MzIdx) (G : PGen) : (n i : Nat) → Bool
  | 0, _ => true
  | n + 1, i => runOkP ix G i && checkRunsP ix G n (i + 1)

def checkCoverP (ix : MzIdx) (G : PGen) (c : Nat) : (n x : Nat) → Bool
  | 0, _ => true
  | n + 1, x =>
    if acgt (G.get x) then checkCoverP ix G c n (x + 1)
    else
      let c := advance ix x ix.nr c
      decide (c < ix.nr) && decide (ix.ra c ≤ x) && decide (x < ix.rb c) && checkCoverP ix G c n (x + 1)

/-- `check2` reading a packed genome. -/
def check2P (ix : MzIdx) (G : PGen) : Bool :=
  checkParams ix && checkSoundP ix G (2 ^ ix.B) 0 &&
    (let s := rollToP G (q - 1); compRP ix G ix.offs 0 (G.n + 1 - q) 0 s.1 s.2) &&
    checkRunsP ix G ix.nr 0 && checkCoverP ix G 0 G.n 0

/-! ## Builder (not trusted; copy of `buildW`) -/

def slotAtP (ix : MzIdx) (G : PGen) (pm h : Nat) : UInt64 :=
  let c := ix.c
  let good := decide (c ≤ pm) && decide (pm + ix.k + c ≤ G.n) &&
    allAP G (pm - c) pm && allAP G (pm + ix.k) (pm + ix.k + c)
  let key := (h &&& ix.kbM).toUInt64
  let tag := if good then
      key ||| ((wcGoP G (pm - c) pm 0).toUInt64 <<< ix.bsh.toUInt64) |||
        ((wcGoP G (pm + ix.k) (pm + ix.k + c) 0).toUInt64 <<< ix.ash.toUInt64)
    else key ||| ((1 : UInt64) <<< ix.fsh.toUInt64)
  (pm.toUInt64 <<< ix.T.toUInt64) ||| tag

@[specialize] def foldMinsP {α : Type} (ix0 : MzIdx) (G : PGen) (f : α → Nat → Nat → α)
    (p : Nat) (x : UInt64) (good last : Nat) (acc : α) : α :=
  if p < G.n then
    let c := G.get p
    let ok := acgt c
    let x := if ok then (x <<< 2 ||| (byteCode c).toUInt64) &&& 0x3FFFFFFFFFFFF else x
    let good := if ok then good + 1 else 0
    if good ≥ q then
      let v := x.toNat
      let o := ix0.mini v
      let pm := p + 1 - q + o
      if pm + 1 != last then foldMinsP ix0 G f (p + 1) x good (pm + 1) (f acc pm (ix0.hsh (ix0.sub v o)))
      else foldMinsP ix0 G f (p + 1) x good last acc
    else foldMinsP ix0 G f (p + 1) x good last acc
  else acc
termination_by G.n - p

def buildWP (G : PGen) (k B c sw t : Nat) : MzIdx := Id.run do
  let pb := G.n.log2 + 1
  if 2 * k < B || 32 < B || k = 0 || q < k || q - k < c || t = 0 || k < t || (k - t) % (q + 1 - k) != 0 ||
      !(sw = 4 || sw = 5 || sw = 6 || sw = 8) || 8 * sw < pb + 4 * c + 1 then
    return panic! s!"Mz.buildWP: unsupported k={k} B={B} c={c} sw={sw} t={t} (genome {G.n} letters)"
  let ix0 := mkIdx k B c sw pb t
  let nb := 2 ^ B
  let mut cnt := foldMinsP ix0 G (fun cnt _ h =>
    let b := h >>> ix0.kb
    setU32 cnt (b + 1) (getU32 cnt (b + 1) + 1)) 0 0 0 0 (zeros (4 * (nb + 1)))
  for b in [0:nb] do cnt := setU32 cnt (b + 1) (getU32 cnt (b + 1) + getU32 cnt b)
  let total := getU32 cnt nb
  let (_, sl) := foldMinsP ix0 G (fun (fill, sl) pm h =>
    let b := h >>> ix0.kb
    let t := getU32 fill b
    (setU32 fill b (t + 1), wrLE sl (sw * t) (slotAtP ix0 G pm h) sw)) 0 0 0 0 (cnt, zeros (sw * total))
  let mut runs : Array Nat := #[]
  for p in [0:G.n] do
    let odd := !acgt (G.get p)
    if odd && (p == 0 || acgt (G.get (p - 1))) then runs := runs.push p
    if odd && (p + 1 == G.n || acgt (G.get (p + 1))) then runs := runs.push (p + 1)
  return { ix0 with offs := cnt, sl, runs }

/-! ## Proof: the checker copy computes `check2` -/

section
variable {P : PGen} {G : ByteArray} (h : Rep P G)
include h

theorem wcUP_eq (stop : Nat) : ∀ d i x, stop - i = d → wcUP P i stop x = wcU G i stop x := by
  intro d
  induction d with
  | zero => intro i x hd; unfold wcUP wcU; rw [if_neg (by omega), if_neg (by omega)]
  | succ d ih =>
    intro i x hd
    unfold wcUP wcU
    have ih' := fun x => ih (i + 1) x (by omega)
    simp only [show i < stop from by omega, if_true, h.2, ih']

theorem allNotP_eq (stop : Nat) : ∀ d i, stop - i = d → allNotP P i stop = allNot G i stop := by
  intro d
  induction d with
  | zero => intro i hd; unfold allNotP allNot; rw [if_neg (by omega), if_neg (by omega)]
  | succ d ih =>
    intro i hd
    unfold allNotP allNot
    simp only [show i < stop from by omega, if_true, h.2, ih (i + 1) (by omega)]

theorem rollToP_eq : ∀ e, rollToP P e = rollTo G e := by
  intro e
  induction e with
  | zero => rfl
  | succ e ih => simp only [rollToP, rollTo, h.2, ih]

theorem compRP_eq (ix : MzIdx) : ∀ n fill last p x g, compRP ix P fill last n p x g = compR ix G fill last n p x g := by
  intro n
  induction n with
  | zero => intro fill last p x g; rfl
  | succ n ih => intro fill last p x g; simp only [compRP, compR, h.2, ih]

theorem checkSoundP_eq (ix : MzIdx) : ∀ n b, checkSoundP ix P n b = checkSound ix G n b := by
  have eo : ∀ b hi t, entryOkP ix P b hi t = entryOk ix G b hi t := fun b hi t => by
    simp only [entryOkP, entryOk, h.1, fun i stop x => wcUP_eq h stop _ i x rfl]
  have cb : ∀ b hi n t, checkBucketP ix P b hi n t = checkBucket ix G b hi n t := fun b hi n => by
    induction n with
    | zero => intro t; rfl
    | succ n ih => intro t; simp only [checkBucketP, checkBucket, eo, ih]
  intro n
  induction n with
  | zero => intro b; rfl
  | succ n ih => intro b; simp only [checkSoundP, checkSound, cb, ih]

theorem checkRunsP_eq (ix : MzIdx) : ∀ n i, checkRunsP ix P n i = checkRuns ix G n i := by
  intro n
  induction n with
  | zero => intro i; rfl
  | succ n ih =>
    intro i
    simp only [checkRunsP, checkRuns, runOkP, runOk, h.1, h.2, ih, fun i stop => allNotP_eq h stop _ i rfl]

theorem checkCoverP_eq (ix : MzIdx) : ∀ n c x, checkCoverP ix P c n x = checkCover ix G c n x := by
  intro n
  induction n with
  | zero => intro c x; rfl
  | succ n ih => intro c x; simp only [checkCoverP, checkCover, h.2, ih]

theorem check2P_eq (ix : MzIdx) : check2P ix P = check2 ix G := by
  simp only [check2P, check2, checkSoundP_eq h, rollToP_eq h, compRP_eq h, checkRunsP_eq h,
    checkCoverP_eq h, h.1]

end

end MapSpec.Mz

#print axioms MapSpec.Mz.check2P_eq
