import PairConcat
import PairPacked

/-!
# Codec `pairFastCP`: one packed concatenated genome, one index

`pairFastC` (codecs/PairConcat.lean: one index over the concatenated genome `G`,
windows scored on each chromosome) with `G` a `PGen` and the chromosomes views
into it (`cutAll G offs ns`: chromosome `c` is `G[offs[c], offs[c] + ns[c])`,
sharing `G`'s arrays), so the genome is held once, at 2 bits per letter.

    … → pairFastCP lk lp lo hi ix G offs gbs R1 R2 = pairFastC lk lo hi ix G' offs gbs' R1 R2   (pairFastCP_eq)
    cutOk G offs ns → Mz.check2P ix G → GenomeBytes ((cutAll G offs ns).map Mz.unpack) g → …
      pairFastCP mzL mzLookP lo hi ix G offs (cutAll G offs ns) R1 R2 = pairSpec …    (pairFastCP_mz_eq_pairSpec)
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-! ## Algorithm (copies of `PairConcat` reading `PGen`s) -/

@[inline] def lzStepAP (R : ByteArray) (G : PGen) (c : Nat) (lj : Array Nat) (k : Nat) (as : Array Nat)
    (looked : Nat) (b : Best) : Array Nat × Best :=
  let fresh := newOnly as lj 0 0 #[]
  let as := merge as lj 0 0 #[]
  let b := fresh.foldl (sameStep2P R G c) b
  (as, if 2 ≤ k && 8 ≤ b.pen then gapAll2P R G c as looked as.size 0 b else b)

@[inline] def stepC1P (R : ByteArray) (gbs : Array PGen) (offs : Array Nat) (base : Nat) (a : Array Nat)
    (j k looked : Nat) (r : Array (Array Nat) × Best) (c : Nat) : Array (Array Nat) × Best :=
  let sl := sliceA a j offs[c]! gbs[c]!.n
  if sl.isEmpty && r.1[c]!.isEmpty then r
  else
    let x := lzStepAP R gbs[c]! (base + c) sl k r.1[c]! looked r.2
    (r.1.set! c x.1, x.2)

@[inline] def stepCP (R : ByteArray) (gbs : Array PGen) (offs : Array Nat) (base : Nat) (a : Array Nat)
    (j k looked : Nat) (ass : Array (Array Nat)) (b : Best) : Array (Array Nat) × Best :=
  (List.range gbs.size).foldl (stepC1P R gbs offs base a j k looked) (ass, b)

@[inline] def CS.advP {L P : Type} [Inhabited P] (lp : LookPk L P) (ix : L) (G : PGen) (R : ByteArray)
    (gbs : Array PGen) (offs : Array Nat) (base : Nat) (ps : Array P) (s : CS) (b : Best) : CS × Best :=
  match s.ord with
  | [] => (s, b)
  | j :: rest =>
    let r := stepCP R gbs offs base (lp ix G R j ps[j]!) j s.k (s.looked + pow2 j) s.as b
    (⟨rest, s.k + 1, s.looked + pow2 j, r.1⟩, r.2)

@[specialize] def ilCP {L P : Type} [Inhabited P] (lk : Look L P) (lp : LookPk L P) (ix : L) (G : PGen)
    (gbs : Array PGen) (offs : Array Nat) (R1 R2 : ByteArray) (c1 c2 : Nat) (ps1 ps2 : Array P) :
    Nat → CS → CS → Best → Best
  | 0, _, _, b => b
  | f + 1, s1, s2, b =>
    let l2 := s2.live b
    if s1.live b && (!l2 || s1.k < s2.k || (s1.k == s2.k && s1.next lk ix ps1 ≤ s2.next lk ix ps2)) then
      let r := s1.advP lp ix G R1 gbs offs c1 ps1 b
      ilCP lk lp ix G gbs offs R1 R2 c1 c2 ps1 ps2 f r.1 s2 r.2
    else if l2 then
      let r := s2.advP lp ix G R2 gbs offs c2 ps2 b
      ilCP lk lp ix G gbs offs R1 R2 c1 c2 ps1 ps2 f s1 r.1 r.2
    else b

@[specialize] def mapChromsCP {L P : Type} [Inhabited P] (lk : Look L P) (lp : LookPk L P) (ix : L) (G : PGen)
    (offs : Array Nat) (gbs : Array PGen) (R : ByteArray) (rf : Bool := false) : Best :=
  let n := gbs.size
  let Rr := revCompB R
  let ps := prepAll lk ix (seedHashes R)
  let pr := prepAll lk ix (seedHashes Rr)
  if rf then ilCP lk lp ix G gbs offs Rr R n 0 pr ps 8 (CS.init lk ix pr n) (CS.init lk ix ps n) {}
  else ilCP lk lp ix G gbs offs R Rr 0 n ps pr 8 (CS.init lk ix ps n) (CS.init lk ix pr n) {}

def mapFastCP {L P : Type} [Inhabited P] (lk : Look L P) (lp : LookPk L P) (ix : L) (G : PGen) (offs : Array Nat)
    (gbs : Array PGen) (R : ByteArray) (rf : Bool := false) : Option (Placement × Int) :=
  decodeJ gbs.size (mapChromsCP lk lp ix G offs gbs R rf)

def pairFastCP {L P : Type} [Inhabited P] (lk : Look L P) (lp : LookPk L P) (lo hi : Nat) (ix : L) (G : PGen)
    (offs : Array Nat) (gbs : Array PGen) (R1 R2 : ByteArray) :
    Option ((Placement × Int) × (Placement × Int)) :=
  match mapFastCP lk lp ix G offs gbs R1 false with
  | none => none
  | some a =>
    match mapFastCP lk lp ix G offs gbs R2 (a.1.2 == Strand.fwd) with
    | some b => if properPair lo hi a.1 b.1 then some (a, b) else none
    | none => none

/-- Chromosome views: `c` is `G[offs[c], offs[c] + ns[c])`. -/
def cutAll (G : PGen) (offs ns : Array Nat) : Array PGen := (Array.range ns.size).map fun c => view G offs[c]! ns[c]!

/-- `G` is a whole packed genome and every chromosome lies inside it. -/
def cutOk (G : PGen) (offs ns : Array Nat) : Bool :=
  G.o == 0 && (List.range ns.size).all fun c => decide (offs[c]! + ns[c]! ≤ G.n)

/-! ## Proofs -/

theorem lzStepAP_eq {P : PGen} {G : ByteArray} (h : Rep P G) (R : ByteArray) (c : Nat) (lj : Array Nat) (k : Nat)
    (as : Array Nat) (looked : Nat) (b : Best) : lzStepAP R P c lj k as looked b = lzStepA R G c lj k as looked b := by
  simp only [lzStepAP, lzStepA, sameStep2P_eq h, gapAll2P_eq h]

section
variable {gbs : Array PGen} {gbsB : Array ByteArray} (hs : gbs.size = gbsB.size) (h : ∀ c : Nat, Rep gbs[c]! gbsB[c]!)
include hs h

theorem stepCP_eq (R : ByteArray) (offs : Array Nat) (base : Nat) (a : Array Nat) (j k looked : Nat)
    (ass : Array (Array Nat)) (b : Best) : stepCP R gbs offs base a j k looked ass b = stepC R gbsB offs base a j k looked ass b := by
  have e : stepC1P R gbs offs base a j k looked = stepC1 R gbsB offs base a j k looked := by
    funext r c; simp only [stepC1P, stepC1, (h c).1, lzStepAP_eq (h c)]
  simp only [stepCP, stepC, e, hs]

variable {L Q : Type} [Inhabited Q] (lk : Look L Q) (lp : LookPk L Q) {G : PGen} {GB : ByteArray}
  (hlp : ∀ ix R j p, lp ix G R j p = lk.look ix GB R j p)
include hlp

theorem ilCP_eq (ix : L) (offs : Array Nat) (R1 R2 : ByteArray) (c1 c2 : Nat) (ps1 ps2 : Array Q) :
    ∀ f s1 s2 b, ilCP lk lp ix G gbs offs R1 R2 c1 c2 ps1 ps2 f s1 s2 b = ilC lk ix GB gbsB offs R1 R2 c1 c2 ps1 ps2 f s1 s2 b := by
  have adv : ∀ R c ps (s : CS) b, s.advP lp ix G R gbs offs c ps b = s.adv lk ix GB R gbsB offs c ps b := by
    intro R c ps s b
    unfold CS.advP CS.adv
    split <;> simp only [hlp, stepCP_eq hs h] <;> simp only [*]
  intro f
  induction f with
  | zero => intro s1 s2 b; rfl
  | succ f ih => intro s1 s2 b; simp only [ilCP, ilC, adv, ih]

theorem pairFastCP_eq (lo hi : Nat) (ix : L) (offs : Array Nat) (R1 R2 : ByteArray) :
    pairFastCP lk lp lo hi ix G offs gbs R1 R2 = pairFastC lk lo hi ix GB offs gbsB R1 R2 := by
  have e : ∀ R rf, mapFastCP lk lp ix G offs gbs R rf = mapFastC lk ix GB offs gbsB R rf := fun R rf => by
    simp only [mapFastCP, mapFastC, mapChromsCP, mapChromsC, hs, ilCP_eq hs h lk lp hlp]
  simp only [pairFastCP, pairFastC, e] <;> rfl

end

theorem cutAll_get (G : PGen) (offs ns : Array Nat) (c : Nat) (hc : c < ns.size) :
    (cutAll G offs ns)[c]! = view G offs[c]! ns[c]! := by
  simp [cutAll, hc]

/-- **Packed concatenated genome + one minimizer index.**  A packed genome whose
chromosome views spell `g`, cut by `cutOk`, and an index that passes the checker
on the packed genome give the specification's answer. -/
theorem pairFastCP_mz_eq_pairSpec (lo hi : Nat) (ix : Mz.MzIdx) (G : PGen) (offs ns : Array Nat) (g : Genome)
    (m1 m2 : List Char) (R1 R2 : ByteArray) (hcut : cutOk G offs ns = true)
    (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) g)
    (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hchk : Mz.check2P ix G = true)
    (hok1 : fastOk R1 = true) (hok2 : fastOk R2 = true) :
    pairFastCP mzL mzLookP lo hi ix G offs (cutAll G offs ns) R1 R2 = pairSpec sc0 (-12) lo hi g m1 m2 := by
  have hrep : ∀ c : Nat, Rep (cutAll G offs ns)[c]! ((cutAll G offs ns).map Mz.unpack)[c]! := fun c => by
    by_cases hc : c < (cutAll G offs ns).size
    · rw [show ((cutAll G offs ns).map Mz.unpack)[c]! = Mz.unpack (cutAll G offs ns)[c]! by simp [hc]]
      exact Mz.rep_unpack _
    · rw [getElem!_neg _ c (by omega), getElem!_neg _ c (by simp at hc ⊢; omega)]
      exact ⟨rfl, fun i => by rw [get!_out _ i (Nat.zero_le _)]; rfl⟩
  rw [pairFastCP_eq (by simp) hrep mzL mzLookP (fun ix R j p => mzLookP_eq (Mz.rep_unpack G) ix R j p)]
  refine pairFastC_mz_eq_pairSpec lo hi ix _ offs g m1 m2 _ R1 R2 hg h1 h2 ?_
    (by rw [← Mz.check2P_eq (Mz.rep_unpack G)]; exact hchk) hok1 hok2
  -- every view spells its slice of `G`
  simp only [cutOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hcut
  have hu : ∀ P : PGen, (Mz.unpack P).size = P.n := fun P => (Mz.rep_unpack P).1.symm
  have hg' : ∀ P : PGen, ∀ i, (Mz.unpack P).get! i = P.get i := fun P i => ((Mz.rep_unpack P).2 i).symm
  unfold catOk
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, Array.size_map]
  intro c hc
  have hc' : c < ns.size := by simpa [cutAll] using hc
  rw [show ((cutAll G offs ns).map Mz.unpack)[c]! = Mz.unpack (view G offs[c]! ns[c]!) by
    simp [cutAll, hc']]
  refine ⟨by rw [hu, hu]; exact hcut.2 c hc', (eqRun_spec _ _ _ _ _).2 fun m hm => ?_⟩
  rw [hu] at hm
  rw [hg', hg']
  have hb := hcut.2 c hc'
  simp only [PGen.get, view, Nat.zero_add] at hm ⊢
  rw [if_pos (by omega), if_pos hm, Nat.add_assoc]
  rfl

end MapSpec.Fast

#print axioms MapSpec.Fast.pairFastCP_eq
#print axioms MapSpec.Fast.pairFastCP_mz_eq_pairSpec
