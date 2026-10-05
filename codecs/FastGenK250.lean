import FastGenPair
import FastGenProof
import MapperK250Words
import MapperK250Seed

/-!
# Codec `pairFastGBK`: `pairFastGB` with the word kernels

`pairFastGB` (codecs/FastGenPair.lean) with its window kernel `kerH` replaced by
`kerHK`: the word kernel `kerGK` (pool/mapper/MapperK250.lean) up to `15`, and at `16`
`ker16K`, which decides the one-gap penalty-16 windows in closed form (first/last
three mismatches) instead of the banded kernel; the banded kernel is left only for
two-gap candidates.  The genome is read through the packed copy `pvs` (`Rep`).

The search code is copied with the kernel as a parameter (`…F`); with `kerH` it is
`pairFastGB` itself.

    kerHK R (packRP R) gbs pvs c st len l = kerH R gbs c st len l          (kerHK_eq)
    pairFastGBK … = pairFastGB …                                           (pairFastGBK_eq)
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-! ## Kernels -/

/-- Reverse complement, one pass. -/
def revCompLoop (R : ByteArray) : (i : Nat) → ByteArray → ByteArray
  | 0, acc => acc
  | i + 1, acc => revCompLoop R i (acc.push (complTab.get! (R.get! i).toNat))

@[inline] def revCompK (R : ByteArray) : ByteArray := revCompLoop R R.size (ByteArray.emptyWithCapacity R.size)

/-- The two-gap candidates (necessary for an exact two-gap walk). -/
@[inline] def twoGapC (R G : ByteArray) (st len : Nat) : Bool :=
  let n := R.size
  let A := fwdMis R G st n 0 1
  let B := bwdMis R G st len 0 n 1
  (len == n || len == n + 2 || len + 2 == n) &&
    (hamming R G (st + 1) 0 (A + 1) (B - 1) 0 == 0 || st == 0 || hamming R G (st - 1) 0 (A + 1) (B - 1) 0 == 0)

/-- Two-gap windows (penalty `> 15`, not four mismatches): the necessary test first. -/
@[inline] def twoGap16 (R : ByteArray) (gbs : Array ByteArray) (c st len : Nat) : Nat :=
  let G := gbs[c]!
  if !twoGapC R G st len then 17
  else if twoGapB R G st len then 16
  else bandPen 16 R gbs ⟨c, st, len⟩

/-- `twoGapC` with the first / last mismatch `A` / `B` passed in. -/
@[inline] def twoGapCAB (R G : ByteArray) (st len A B : Nat) : Bool :=
  let n := R.size
  (len == n || len == n + 2 || len + 2 == n) &&
    (hamming R G (st + 1) 0 (A + 1) (B - 1) 0 == 0 || st == 0 || hamming R G (st - 1) 0 (A + 1) (B - 1) 0 == 0)

/-- `twoGap16` with the first / last mismatch found once, by the word scans (`twoGap16K_eq`). -/
@[inline] def twoGap16K (R : ByteArray) (K : RP) (gbs : Array ByteArray) (pvs : Array PGen) (c st len : Nat) : Nat :=
  let G := gbs[c]!
  let A := fwdL R G K pvs[c]! st R.size 1
  let B := bwdL R G K pvs[c]! st len 0 1
  if !twoGapCAB R G st len A B then 17
  else if twoGapBP R G st len A B then 16
  else bandPen 16 R gbs ⟨c, st, len⟩

/-- `ker16`: the word kernel capped at `17` (exact one-gap formula), then the two-gap
tests for lengths `n`, `n ± 2` (a chromosome out of range: `ker16` itself). -/
def ker16K (R : ByteArray) (K : RP) (gbs : Array ByteArray) (pvs : Array PGen) (c st len : Nat) : Nat :=
  if gbs.size ≤ c then ker16 R gbs c st len
  else if st + len ≤ gbs[c]!.size then
    let r := kerGK R K gbs[c]! pvs[c]! st len 16
    if r ≤ 16 then r
    else if len = R.size ∨ len = R.size + 2 ∨ len + 2 = R.size then twoGap16K R K gbs pvs c st len
    else 17
  else 17

/-- `kerH` with the word kernels. -/
@[inline] def kerHK (R : ByteArray) (K : RP) (gbs : Array ByteArray) (pvs : Array PGen) (c st len l : Nat) : Nat :=
  if l ≤ 15 then kerGK R K gbs[c]! pvs[c]! st len l else ker16K R K gbs pvs c st len

/-! ## The search with the kernel as a parameter (copied from `pairFastGB`) -/

/-- A window kernel: chromosome, start, length, cap `l` ↦ penalty capped at `l + 1`. -/
abbrev Ker := Nat → Nat → Nat → Nat → Nat

@[inline] def addKF (kf : Ker) (c lim : Nat) (st len : Int) (b : Best) : Best :=
  if 0 ≤ st ∧ 0 ≤ len then
    if b.pen ≤ lim ∧ b.chr = c ∧ b.st = st.toNat ∧ b.len = len.toNat then b else
    let l := min lim b.pen
    let r := kf c st.toNat len.toNat l
    if r ≤ l then b.add c st.toNat len.toNat r else b
  else b

def stageKF (kf : Ker) (n c lim : Nat) (shs : List (Int × Int)) (ds : List Nat) (b : Best) : Best :=
  ds.foldl (fun b D => shs.foldl (fun b sh => addKF kf c lim (dst n D sh) (wlen n sh) b) b) b

def chromKBF (kf : Ker) (R : ByteArray) (gbs : Array ByteArray) (c P : Nat) (acc : List (Array Nat))
    (J : List Nat) (b1 : Best) : Best :=
  let lim := min P 16
  let Q1 := min b1.pen P
  let b2 := if 0 < gapBound sc0 (-(Q1 : Int)) then
      stageKS (fun D b => stageKF kf R.size c lim (shapesKT Q1) [D] b)
        R gbs[c]! acc (unseen (R.size / 25) J) (R.size / (R.size / 25)) lim (diags acc) b1 else b1
  let Q2 := min b2.pen P
  if lim < Q2 then
    stageKS (fun D b => stageB P R gbs c (shapesT Q2) (shifts (gapBound sc0 (-(Q2 : Int)))) [D] b)
      R gbs[c]! acc (unseen (R.size / 25) J) (R.size / (R.size / 25)) P
      (diagsB acc (acc.length - sbound P) (2 * gapBound sc0 (-(Q2 : Int)))) b2
  else b2

@[inline] def advCF (kf : Ker) (n : Nat) (gbs2 : Array ByteArray) (offs : Array Nat) (t P bs : Nat) (a : Array Nat)
    (r : Array (List (Array Nat)) × Best) (c : Nat) : Array (List (Array Nat)) × Best :=
  let sl := sliceG a bs offs[c]! gbs2[t + c]!.size
  (r.1.set! c (sl :: r.1[c]!),
    sl.foldl (fun b e => addKF kf (t + c) (min P 16) ((e / 16 : Nat) - (n : Int)) n b) r.2)

@[inline] def GS.advF {L Pp : Type} [LookG L Pp] [Inhabited Pp] (kf : Ker) (ix : L) (G R : ByteArray)
    (gbs2 : Array ByteArray) (offs : Array Nat) (n t P Ls : Nat) (ps : Array Pp) (s : GS) (b : Best) : GS × Best :=
  match s.ord with
  | [] => (s, b)
  | j :: rest =>
    let r := (List.range n).foldl (advCF kf R.size gbs2 offs t P (R.size - j * Ls)
      (LookG.look ix G R (j * Ls) (R.size - j * Ls) ps[j]!)) (s.acc, b)
    (⟨rest, j :: s.J, r.1⟩, r.2)

@[specialize] def ilGF {L Pp : Type} [LookG L Pp] [Inhabited Pp] (kf1 kf2 : Ker) (ix : L) (G R1 R2 : ByteArray)
    (gbs2 : Array ByteArray) (offs : Array Nat) (n P Ls : Nat) (ps1 ps2 : Array Pp) :
    Nat → GS → GS → Best → GS × GS × Best
  | 0, s1, s2, b => (s1, s2, b)
  | f + 1, s1, s2, b =>
    let l2 := s2.live P b
    if s1.live P b && (!l2 || decide (s1.J.length ≤ s2.J.length)) then
      let r := s1.advF kf1 ix G R1 gbs2 offs n 0 P Ls ps1 b
      ilGF kf1 kf2 ix G R1 R2 gbs2 offs n P Ls ps1 ps2 f r.1 s2 r.2
    else if l2 then
      let r := s2.advF kf2 ix G R2 gbs2 offs n n P Ls ps2 b
      ilGF kf1 kf2 ix G R1 R2 gbs2 offs n P Ls ps1 ps2 f s1 r.1 r.2
    else (s1, s2, b)

/-- `mapChromsGB` with the kernels `kf1` (read) and `kf2` (reverse complement) and
the prepared seeds `ps`, `pr`. -/
@[specialize] def mapChromsGBF {L Pp : Type} [LookG L Pp] [Inhabited Pp] (kf1 kf2 : Ker) (P : Nat) (ix : L)
    (G : ByteArray) (offs : Array Nat) (gbs : Array ByteArray) (R Rr : ByteArray) (ps pr : Array Pp) : Best :=
  let n := gbs.size
  let gbs2 := gbs ++ gbs
  let m := R.size / 25
  let Ls := R.size / m
  let x := ilGF kf1 kf2 ix G R Rr gbs2 offs n P Ls ps pr (2 * m + 1)
    ⟨ordG (ps.map (LookG.size ix)) m, [], Array.replicate n []⟩
    ⟨ordG (pr.map (LookG.size ix)) m, [], Array.replicate n []⟩ (initP P)
  let b := (List.range n).foldl (fun b c => chromKBF kf1 R gbs2 c P x.1.acc[c]! x.1.J b) x.2.2
  (List.range n).foldl (fun b c => chromKBF kf2 Rr gbs2 (n + c) P x.2.1.acc[c]! x.2.1.J b) b

/-! ## With the word kernels -/

/-- Prepared seeds, hashes from the packed read (`seedHashK`). -/
@[inline] def prepGK {L Pp : Type} [LookG L Pp] (ix : L) (R : ByteArray) (K : RP) (m Ls : Nat) : Array Pp :=
  (Array.range m).map fun j => LookG.prep ix (seedHashK R K (j * Ls))

/-- Both strands with the word kernels; `pvs` spells `gbs` (packed). -/
@[specialize] def mapChromsGBK {L Pp : Type} [LookG L Pp] [Inhabited Pp] (P : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (gbs : Array ByteArray) (pvs : Array PGen) (R : ByteArray) : Best :=
  let gbs2 := gbs ++ gbs
  let pvs2 := pvs ++ pvs
  let Rr := revCompK R
  let K1 := packRP R
  let K2 := packRP Rr
  let m := R.size / 25
  let Ls := R.size / m
  mapChromsGBF (kerHK R K1 gbs2 pvs2) (kerHK Rr K2 gbs2 pvs2) P ix G offs gbs R Rr
    (prepGK ix R K1 m Ls) (prepGK ix Rr K2 m Ls)

def mapFastGBK {L Pp : Type} [LookG L Pp] [Inhabited Pp] (P : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (gbs : Array ByteArray) (pvs : Array PGen) (R : ByteArray) : Option (Placement × Int) :=
  if fastT P R then decodeP gbs.size P (mapChromsGBK P ix G offs gbs pvs R)
  else mapSpecBoth sc0 (-(P : Int)) (decodeGenomeB gbs) (decodeBytes R)

/-- A proper pair at `T = −P`, word kernels. -/
def pairFastGBK {L Pp : Type} [LookG L Pp] [Inhabited Pp] (P lo hi : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (gbs : Array ByteArray) (pvs : Array PGen) (R1 R2 : ByteArray) :
    Option ((Placement × Int) × (Placement × Int)) :=
  match mapFastGBK P ix G offs gbs pvs R1, mapFastGBK P ix G offs gbs pvs R2 with
  | some a, some b => if properPair lo hi a.1 b.1 then some (a, b) else none
  | _, _ => none

/-! ## Proofs: kernels -/

theorem revCompLoop_data (R : ByteArray) : ∀ (i : Nat) (acc : ByteArray),
    (revCompLoop R i acc).data.toList = acc.data.toList ++ (List.range i).reverse.map fun k => complB (R.get! k) := by
  intro i
  induction i with
  | zero => intro acc; simp [revCompLoop]
  | succ i ih =>
    intro acc
    have e : complTab.get! (R.get! i).toNat = complB (R.get! i) := by
      exact complTab_get _
    simp only [revCompLoop, ih, ByteArray.data_push, Array.toList_push, e, List.range_succ,
      List.reverse_append, List.map_append, List.append_assoc]
    rfl

theorem revCompK_eq (R : ByteArray) : revCompK R = revCompB R := by
  apply ByteArray.ext
  apply Array.ext'
  have e1 : (revCompK R).data.toList = (List.range R.size).reverse.map fun k => complB (R.get! k) := by
    rw [revCompK, revCompLoop_data]; rfl
  have e2 : (revCompB R).data.toList = (R.data.toList.map complB).reverse := by simp [revCompB]
  rw [e1, e2]
  have hs : R.data.toList.length = R.size := by simp
  apply List.ext_getElem
  · simp only [List.length_map, List.length_reverse, List.length_range, hs]
  · intro j h1 h2
    simp only [List.length_map, List.length_reverse, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_reverse, List.getElem_range, List.length_range]
    simp only [ByteArray.get!]
    rw [getElem!_pos R.data _ (by show _ < R.size; omega)]
    simp only [Array.getElem_toList, List.length_map, hs]

/-- The packed chromosomes spell the byte chromosomes. -/
def RepAllK (pvs : Array PGen) (gbs : Array ByteArray) : Prop := ∀ c : Nat, Rep pvs[c]! gbs[c]!

theorem twoGap16K_eq (R : ByteArray) (gbs : Array ByteArray) (pvs : Array PGen) (c : Nat) (hP : Rep pvs[c]! gbs[c]!)
    (st len : Nat) : twoGap16K R (packRP R) gbs pvs c st len = twoGap16 R gbs c st len := by
  unfold twoGap16K twoGap16 twoGapC twoGapB twoGapCAB twoGapBP
  simp only [fwdL_eq _ _ _ hP _ _ _ (Nat.le_refl 1), bwdL_eq _ _ _ hP _ _ _ _ (Nat.le_refl 1)]

/-! ### `ker16K_eq`: helpers -/

section
variable {R G : ByteArray} {xs seq : List Char} (hr : Encodes R xs) (hg : Encodes G seq)
include hr hg

/-- The formula `fB` bounds the capped penalty from above. -/
theorem penQ_le_fB (Q : Nat) (st len : Nat) (hfit : st + len ≤ seq.length) (hQ : fB R G st len ≤ Q) :
    penQ Q xs ((seq.drop st).take len) ≤ fB R G st len := by
  have hn : R.size = xs.length := hr.1
  generalize hys : (seq.drop st).take len = ys
  have hyl : ys.length = len := by rw [← hys]; simp; omega
  have hyk : ∀ k (h : k < ys.length), ys[k] = seq[st + k]'(by omega) := by
    intro k h; subst hys; simp
  have hpre : ∀ i, i ≤ xs.length → i ≤ len →
      MapSpec.hamming (xs.take i) (ys.take i) = preB R G st i := by
    intro i h1 h2; rw [← hys]; exact ham_take_bytes hr hg st len hfit i h1 h2
  revert hQ
  unfold fB
  by_cases hsame : len = R.size
  · rw [if_pos hsame]
    have := hpre xs.length (Nat.le_refl _) (by omega)
    rw [List.take_length, List.take_of_length_le (by omega)] at this
    rw [hn, ← this]
    exact (penQ_same Q xs ys (by omega)).1
  rw [if_neg hsame]
  unfold minMis gapLen skipOf
  by_cases hlt : R.size < len
  · simp only [hlt, if_true, show ¬ len < R.size by omega, if_false]
    have hM : minUpTo (misIns xs ys (len - R.size)) xs.length =
        minUpTo (misB R G st len 0) (R.size - 0) := by
      rw [Nat.sub_zero, hn]
      apply minUpTo_congr
      intro i hi
      unfold misIns misB
      rw [hpre i hi (by omega), Nat.add_zero]
      congr 1
      unfold sufB
      rw [hamming_cnt _ _ (fun k => R.get! (i + k) != G.get! (st + len + (i + k) - R.size)) (fun k h1 h2 => by
        simp only [List.getElem_drop]
        simp at h1 h2
        rw [neq_bytes hr hg (i + k) (st + len + (i + k) - R.size) (by omega) (by omega),
          hyk _ (by omega)]
        have e : st + (i + (len - xs.length) + k) = st + len + (i + k) - R.size := by omega
        simp only [e])]
      rw [cntP_shift (fun k => R.get! k != G.get! (st + len + k - R.size)) i 0]
      congr 1 <;> simp <;> omega
    rw [← hM]
    exact (penQ_ins Q xs ys (len - R.size) (by omega) (by omega)).1
  · have hlt' : len < R.size := by omega
    simp only [hlt, hlt', if_true, if_false]
    have hM : minUpTo (misDel xs ys (R.size - len)) ys.length =
        minUpTo (misB R G st len (R.size - len)) (R.size - (R.size - len)) := by
      rw [show R.size - (R.size - len) = ys.length by omega]
      apply minUpTo_congr
      intro i hi
      unfold misDel misB
      rw [hpre i (by omega) (by omega)]
      congr 1
      unfold sufB
      rw [hamming_cnt _ _ (fun k => R.get! (i + (R.size - len) + k) !=
          G.get! (st + len + (i + (R.size - len) + k) - R.size)) (fun k h1 h2 => by
        simp only [List.getElem_drop]
        simp at h1 h2
        rw [neq_bytes hr hg _ _ (by omega) (by omega), hyk (i + k) (by omega)]
        have e : st + (i + k) = st + len + (i + (R.size - len) + k) - R.size := by omega
        simp only [e])]
      rw [cntP_shift (fun k => R.get! k != G.get! (st + len + k - R.size)) (i + (R.size - len)) 0]
      congr 1 <;> simp <;> omega
    rw [← hM]
    exact (penQ_del Q xs ys (R.size - len) (by omega) (by omega)).1

/-- Penalty `16` above the one-gap formula: a two-gap candidate. -/
theorem twoGapC_of (Q : Nat) (hQ : 16 ≤ Q) (st len : Nat) (hfit : st + len ≤ seq.length)
    (h : penQ Q xs ((seq.drop st).take len) = 16) (hf : 16 < fB R G st len) : twoGapC R G st len = true := by
  have hn : R.size = xs.length := hr.1
  generalize hys : (seq.drop st).take len = ys at h
  have hyl : ys.length = len := by rw [← hys]; simp; omega
  have hyk : ∀ k (h : k < ys.length), ys[k] = seq[st + k]'(by omega) := by
    intro k h; subst hys; simp
  have hpre : ∀ i, i ≤ xs.length → i ≤ len →
      MapSpec.hamming (xs.take i) (ys.take i) = preB R G st i := by
    intro i h1 h2; rw [← hys]; exact ham_take_bytes hr hg st len hfit i h1 h2
  unfold twoGapC
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc]
  rcases penQ16 Q hQ xs ys h with ⟨hl, hh⟩ | ⟨L, i, hl, hL1, hL5, hi, hm⟩ | ⟨L, i, hl, hL1, hL5, hi, hm⟩ |
      ⟨i, j, k, x1, x2, hx, hy, d1, d2, p1, p2, p3⟩
  · exfalso
    have := hpre xs.length (Nat.le_refl _) (by omega)
    rw [List.take_length, List.take_of_length_le (by omega)] at this
    unfold fB at hf
    rw [if_pos (by omega), hn, ← this, hh] at hf
    omega
  · exfalso
    have hmis : misIns xs ys L i = misB R G st len 0 i := by
      unfold misIns misB
      rw [hpre i hi (by omega), Nat.add_zero]
      congr 1
      unfold sufB
      rw [hamming_cnt _ _ (fun k => R.get! (i + k) != G.get! (st + len + (i + k) - R.size)) (fun k h1 h2 => by
        simp only [List.getElem_drop]
        simp at h1 h2
        rw [neq_bytes hr hg (i + k) (st + len + (i + k) - R.size) (by omega) (by omega),
          hyk _ (by omega)]
        have e : st + (i + L + k) = st + len + (i + k) - R.size := by omega
        simp only [e])]
      rw [cntP_shift (fun k => R.get! k != G.get! (st + len + k - R.size)) i 0]
      congr 1 <;> simp <;> omega
    have hsk : skipOf R.size len = 0 := by unfold skipOf; split <;> omega
    have hgl : gapLen R.size len = L := by unfold gapLen; split <;> omega
    have hle := minUpTo_le (misB R G st len 0) (R.size - 0) i (by omega)
    unfold fB minMis at hf
    rw [if_neg (by omega), hsk, hgl] at hf
    omega
  · exfalso
    have hmis : misDel xs ys L i = misB R G st len L i := by
      unfold misDel misB
      rw [hpre i (by omega) (by omega)]
      congr 1
      unfold sufB
      rw [hamming_cnt _ _ (fun k => R.get! (i + L + k) !=
          G.get! (st + len + (i + L + k) - R.size)) (fun k h1 h2 => by
        simp only [List.getElem_drop]
        simp at h1 h2
        rw [neq_bytes hr hg _ _ (by omega) (by omega), hyk (i + k) (by omega)]
        have e : st + (i + k) = st + len + (i + L + k) - R.size := by omega
        simp only [e])]
      rw [cntP_shift (fun k => R.get! k != G.get! (st + len + k - R.size)) (i + L) 0]
      congr 1 <;> simp <;> omega
    have hsk : skipOf R.size len = L := by unfold skipOf; split <;> omega
    have hgl : gapLen R.size len = L := by unfold gapLen; split <;> omega
    have hle := minUpTo_le (misB R G st len L) (R.size - L) i (by omega)
    unfold fB minMis at hf
    rw [if_neg (by omega), hsk, hgl] at hf
    omega
  · -- two gaps
    refine ⟨by omega, ?_⟩
    obtain ⟨-, -, f1⟩ := fwdMis_spec R G st R.size _ 0 1 rfl (Nat.zero_le _) (Nat.le_refl _)
    obtain ⟨-, -, e1⟩ := bwdMis_spec R G st len 0 _ R.size 1 rfl (Nat.zero_le _) (Nat.le_refl _)
    have hA : i ≤ fwdMis R G st R.size 0 1 := by
      apply (f1 i (Nat.zero_le _) (by omega)).1
      rw [cntP_zero_of _ _ _ (fun u _ hu => clean_of hr hg u (st + u) (by omega) (by omega) (by
        rw [p1 u (by omega), hyk u (by omega)]))]
      omega
    have hB : bwdMis R G st len 0 R.size 1 ≤ R.size - k := by
      apply (e1 (R.size - k) (Nat.zero_le _) (by omega)).1
      rw [cntP_zero_of _ _ _ (fun u h1 hu => clean_of hr hg u (st + len + u - R.size) (by omega) (by omega) (by
        have := p3 (u - (R.size - k)) (by omega)
        have e1 : i + (1 - x1) + j + (1 - x2) + (u - (R.size - k)) = u := by omega
        have e2 : i + x1 + j + x2 + (u - (R.size - k)) = st + len + u - R.size - st := by omega
        simp only [e1, e2] at this
        rw [this, hyk _ (by omega)]
        congr 1; omega))]
      omega
    generalize fwdMis R G st R.size 0 1 = A at *
    generalize bwdMis R G st len 0 R.size 1 = B at *
    by_cases hx1 : x1 = 1
    · left
      subst hx1
      rw [hamming_spec R G (st + 1) 0 (B - 1) _ (A + 1) 0 rfl (Nat.le_refl _),
        cntP_zero_of _ _ _ (fun u h1 hu => clean_of hr hg u (st + 1 + u) (by omega) (by omega) (by
          have := p2 (u - i) (by omega)
          have e1 : i + (1 - 1) + (u - i) = u := by omega
          have e2 : i + 1 + (u - i) = st + 1 + u - st := by omega
          simp only [e1, e2] at this
          rw [this, hyk _ (by omega)]
          congr 1; omega))]
      rfl
    · right
      by_cases hst : st = 0
      · left; exact hst
      right
      rw [hamming_spec R G (st - 1) 0 (B - 1) _ (A + 1) 0 rfl (Nat.le_refl _),
        cntP_zero_of _ _ _ (fun u h1 hu => clean_of hr hg u (st - 1 + u) (by omega) (by omega) (by
          have := p2 (u - (i + 1)) (by omega)
          have e1 : i + (1 - x1) + (u - (i + 1)) = u := by omega
          have e2 : i + x1 + (u - (i + 1)) = st - 1 + u - st := by omega
          simp only [e1, e2] at this
          rw [this, hyk _ (by omega)]
          congr 1; omega))]
      rfl

end

theorem twoGapC_len (R G : ByteArray) (st len : Nat) (h : twoGapC R G st len = true) :
    len = R.size ∨ len = R.size + 2 ∨ len + 2 = R.size := by
  unfold twoGapC at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  omega

theorem encodes_decodeBytes (B : ByteArray) : Encodes B (decodeBytes B) :=
  ⟨(length_decodeBytes B).symm, fun i h => by rw [getElem_decodeBytes]; exact (toChar_val_toNat _).symm⟩

theorem genomeBytes_decode (gbs : Array ByteArray) : GenomeBytes gbs (decodeGenomeB gbs) := by
  refine ⟨by simp [decodeGenomeB], fun c h1 h2 => ?_⟩
  simp only [decodeGenomeB, Array.getElem_toList, List.getElem_map]
  exact encodes_decodeBytes _

/-- The capped penalty of a window that fits (or is `16`) is `penQ` of its letters. -/
theorem cwT_penQ (P : Nat) (read : List Char) (g : Genome) (gbs : Array ByteArray)
    (hg : GenomeBytes gbs g) (c st len : Nat) (hc : c < gbs.size)
    (h16 : cwT P read g ⟨c, st, len⟩ = 16 ∨ st + len ≤ gbs[c]!.size) (hP : 16 ≤ P) :
    ∃ (hc' : c < g.length), st + len ≤ g[c].seq.length ∧ Encodes gbs[c]! g[c].seq ∧
      cwT P read g ⟨c, st, len⟩ = penQ P read ((g[c].seq.drop st).take len) := by
  obtain ⟨hsz, henc⟩ := hg
  have hc' : c < g.length := by omega
  have he := henc c hc hc'
  rw [getElem!_pos gbs c hc] at h16 ⊢
  unfold cwT windowScore windowSeq
  unfold cwT windowScore windowSeq at h16
  simp only [List.getElem?_eq_getElem hc'] at h16 ⊢
  by_cases hfit : st + len ≤ g[c].seq.length
  · refine ⟨hc', hfit, he, ?_⟩
    rw [if_pos hfit]
    unfold penQ
    simp only []
    generalize getBestAlignment sc0 read (List.take len (List.drop st g[c].seq)) = r
    cases r with
    | none => rfl
    | some x => obtain ⟨path, bs⟩ := x; rfl
  · rw [if_neg hfit] at h16; simp only [] at h16
    rcases h16 with h16 | h16
    · omega
    · rw [he.1] at h16; omega

/-- **Penalty 16.** -/
theorem ker16K_eq (R : ByteArray) (gbs : Array ByteArray) (pvs : Array PGen) (hrep : RepAllK pvs gbs)
    (c st len : Nat) : ker16K R (packRP R) gbs pvs c st len = ker16 R gbs c st len := by
  unfold ker16K
  by_cases hc : gbs.size ≤ c
  · rw [if_pos hc]
  rw [if_neg hc]
  rw [twoGap16K_eq R gbs pvs c (hrep c)]
  have hc : c < gbs.size := by omega
  have hr := encodes_decodeBytes R
  have hg := genomeBytes_decode gbs
  generalize decodeBytes R = read at hr
  generalize decodeGenomeB gbs = g at hg
  rw [← cwT_ker16 16 (Nat.le_refl _) read g gbs R hg hr c st len hc, cwT_cap16 16 (Nat.le_refl _)]
  have hle := cwT_le 16 read g ⟨c, st, len⟩
  have hk := cwT_ker 16 read g gbs R hg hr c st len 15 hc (by omega) (by omega)
  rw [kerG_eq _ _ _ _ _ (by omega)] at hk
  generalize hX : cwT 16 read g ⟨c, st, len⟩ = X at hk hle
  split
  · next hfit =>
    rw [if_pos hfit] at hk
    obtain ⟨hc', hfit', he, hpq⟩ := cwT_penQ 16 read g gbs hg c st len hc (Or.inr hfit) (Nat.le_refl _)
    rw [hX] at hpq
    rw [kerGK_eq R gbs[c]! pvs[c]! (hrep c), kerG3_eq _ _ _ _ _ (by omega), if_pos hfit]
    dsimp only
    by_cases hf : fB R gbs[c]! st len ≤ 16
    · rw [if_pos (by omega)]
      have := penQ_le_fB hr he 16 st len hfit' hf
      omega
    rw [if_neg (by omega)]
    have hTG : X = 16 → twoGapC R gbs[c]! st len = true := fun h16 =>
      twoGapC_of hr he 16 (Nat.le_refl _) st len hfit' (by rw [← hpq, h16]) (by omega)
    split
    · unfold twoGap16
      dsimp only
      split
      · next hC =>
        have : X ≠ 16 := fun h16 => by rw [hTG h16] at hC; cases hC
        omega
      split
      · next hB =>
        have := twoGapB_pen hr he 16 (Nat.le_refl _) st len hfit' hB
        omega
      · rw [bandPen_eq 16 read g gbs R hg hr, hX]
    · next hl =>
      have : X ≠ 16 := fun h16 => hl (twoGapC_len R _ st len (hTG h16))
      omega
  · next hfit =>
    rw [if_neg hfit] at hk
    have : X ≠ 16 := fun h16 => by
      obtain ⟨hc', hfit', he, -⟩ := cwT_penQ 16 read g gbs hg c st len hc (Or.inl (hX ▸ h16)) (Nat.le_refl _)
      exact hfit (by rw [he.1]; exact hfit')
    omega

theorem kerHK_eq (R : ByteArray) (gbs : Array ByteArray) (pvs : Array PGen) (hrep : RepAllK pvs gbs)
    (c st len l : Nat) : kerHK R (packRP R) gbs pvs c st len l = kerH R gbs c st len l := by
  unfold kerHK kerH
  split
  · exact kerGK_kerG R gbs[c]! pvs[c]! (hrep c) st len l (by omega)
  · exact ker16K_eq R gbs pvs hrep c st len

/-! ## Proofs: the search -/

/-- The runtime check of the packed chromosomes. -/
def checkPGs (pvs : Array PGen) (gbs : Array ByteArray) : Bool :=
  pvs.size == gbs.size && (List.range gbs.size).all fun c => checkPG pvs[c]! gbs[c]!

theorem rep_default : Rep (default : PGen) (default : ByteArray) :=
  ⟨rfl, fun i => by rw [get_out _ i (Nat.zero_le _), get!_out _ i (Nat.zero_le _)]⟩

theorem checkPGs_ok (pvs : Array PGen) (gbs : Array ByteArray) (h : checkPGs pvs gbs = true) :
    RepAllK (pvs ++ pvs) (gbs ++ gbs) := by
  unfold checkPGs at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hs, hall⟩ := h
  have one : ∀ c, c < gbs.size → Rep pvs[c]! gbs[c]! := fun c hc => checkPG_ok _ _ (hall c hc)
  intro c
  by_cases h1 : c < gbs.size
  · rw [getElem!_pos (pvs ++ pvs) c (by simp; omega), getElem!_pos (gbs ++ gbs) c (by simp; omega),
      Array.getElem_append_left (by omega), Array.getElem_append_left (by omega),
      ← getElem!_pos pvs c (by omega), ← getElem!_pos gbs c h1]
    exact one c h1
  by_cases h2 : c < 2 * gbs.size
  · rw [getElem!_pos (pvs ++ pvs) c (by simp; omega), getElem!_pos (gbs ++ gbs) c (by simp; omega),
      Array.getElem_append_right (by omega), Array.getElem_append_right (by omega),
      ← getElem!_pos pvs (c - pvs.size) (by omega), ← getElem!_pos gbs (c - gbs.size) (by omega), hs]
    exact one _ (by omega)
  · rw [getElem!_neg (pvs ++ pvs) c (by simp; omega), getElem!_neg (gbs ++ gbs) c (by simp; omega)]
    exact rep_default

theorem stageKF_eq (R : ByteArray) (gbs : Array ByteArray) (c lim : Nat) (shs : List (Int × Int)) (ds : List Nat)
    (b : Best) : stageKF (kerH R gbs) R.size c lim shs ds b = stageK R gbs c lim shs ds b := rfl

theorem chromKBF_eq (R : ByteArray) (gbs : Array ByteArray) (c P : Nat) (acc : List (Array Nat)) (J : List Nat)
    (b : Best) : chromKBF (kerH R gbs) R gbs c P acc J b = chromKBS R gbs c P acc J b := by
  simp only [chromKBF, chromKBS]
  rw [show (if 16 ≤ min (min P 16) (min b.pen P) then stageKP else stageK) = stageK by split <;> first | rfl | (funext R gbs c lim shs ds b; exact stageKP_eq R gbs c lim shs ds b)]
  rfl

theorem advF_eq {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G R : ByteArray)
    (gbs2 : Array ByteArray) (offs : Array Nat) (n t P Ls : Nat) (ps : Array Pp) (s : GS) (b : Best) :
    s.advF (kerH R gbs2) ix G R gbs2 offs n t P Ls ps b = s.adv ix G R gbs2 offs n t P Ls ps b := rfl

theorem ilGF_eq {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G R1 R2 : ByteArray)
    (gbs2 : Array ByteArray) (offs : Array Nat) (n P Ls : Nat) (ps1 ps2 : Array Pp) :
    ∀ f s1 s2 b, ilGF (kerH R1 gbs2) (kerH R2 gbs2) ix G R1 R2 gbs2 offs n P Ls ps1 ps2 f s1 s2 b =
      ilG ix G R1 R2 gbs2 offs n P Ls ps1 ps2 f s1 s2 b := by
  intro f
  induction f with
  | zero => intro s1 s2 b; rfl
  | succ f ih =>
    intro s1 s2 b
    simp only [ilGF, ilG, advF_eq, ih]

theorem mapChromsGBF_eq {L Pp : Type} [LookG L Pp] [Inhabited Pp] (P : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (gbs : Array ByteArray) (R : ByteArray) :
    mapChromsGBF (kerH R (gbs ++ gbs)) (kerH (revCompB R) (gbs ++ gbs)) P ix G offs gbs R (revCompB R)
      (prepG ix R (R.size / 25) (R.size / (R.size / 25)))
      (prepG ix (revCompB R) (R.size / 25) (R.size / (R.size / 25))) =
      mapChromsGB P ix G offs gbs R := by
  unfold mapChromsGBF mapChromsGB
  simp only [ilGF_eq, chromKBF_eq, revCompB2_eq]

theorem prepGK_eq {L Pp : Type} [LookG L Pp] (ix : L) (R : ByteArray) (m Ls : Nat) :
    prepGK ix R (packRP R) m Ls = prepG ix R m Ls := by
  unfold prepGK prepG
  simp only [seedHashK_eq]

theorem mapChromsGBK_eq {L Pp : Type} [LookG L Pp] [Inhabited Pp] (P : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (gbs : Array ByteArray) (pvs : Array PGen) (hpg : checkPGs pvs gbs = true) (R : ByteArray) :
    mapChromsGBK P ix G offs gbs pvs R = mapChromsGB P ix G offs gbs R := by
  have hrep := checkPGs_ok pvs gbs hpg
  unfold mapChromsGBK
  simp only [revCompK_eq, prepGK_eq]
  rw [← mapChromsGBF_eq]
  congr 1
  · funext c st len l; exact kerHK_eq R _ _ hrep c st len l
  · funext c st len l; exact kerHK_eq (revCompB R) _ _ hrep c st len l

theorem pairFastGBK_eq {L Pp : Type} [LookG L Pp] [Inhabited Pp] (P lo hi : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (gbs : Array ByteArray) (pvs : Array PGen) (hpg : checkPGs pvs gbs = true) (R1 R2 : ByteArray) :
    pairFastGBK P lo hi ix G offs gbs pvs R1 R2 = pairFastGB P lo hi ix G offs gbs R1 R2 := by
  have h : ∀ R, mapFastGBK P ix G offs gbs pvs R = mapFastGB P ix G offs gbs R := fun R => by
    unfold mapFastGBK mapFastGB; rw [mapChromsGBK_eq P ix G offs gbs pvs hpg]
  unfold pairFastGBK pairFastGB
  rw [h R1, h R2]
  cases mapFastGB P ix G offs gbs R1 <;> cases mapFastGB P ix G offs gbs R2 <;> rfl

/-! ## Top theorems -/

/-- **Proper pairs, word kernels, hashed index over the concatenation.** -/
theorem pairFastGBK_hashed_eq_pairSpec (P lo hi : Nat) (g : Genome) (m1 m2 : List Char) (gbs : Array ByteArray)
    (pvs : Array PGen) (R1 R2 : ByteArray) (ix : HIdx) (G : ByteArray) (offs : Array Nat)
    (hg : GenomeBytes gbs g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hcat : catOk G offs gbs = true)
    (hchk : checkAll #[ix] #[G] = true) (hpg : checkPGs pvs gbs = true) :
    pairFastGBK P lo hi ix G offs gbs pvs R1 R2 = pairSpec sc0 (-(P : Int)) lo hi g m1 m2 := by
  rw [pairFastGBK_eq P lo hi ix G offs gbs pvs hpg]
  exact pairFastGB_hashed_eq_pairSpec P lo hi g m1 m2 gbs R1 R2 ix G offs hg h1 h2 hcat hchk

/-- **Proper pairs, word kernels, minimizer index over the concatenation.** -/
theorem pairFastGBK_mz_eq_pairSpec (P lo hi : Nat) (g : Genome) (m1 m2 : List Char) (gbs : Array ByteArray)
    (pvs : Array PGen) (R1 R2 : ByteArray) (ix : Mz.MzIdx) (G : ByteArray) (offs : Array Nat)
    (hg : GenomeBytes gbs g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hcat : catOk G offs gbs = true)
    (hchk : checkAllMz #[ix] #[G] = true) (hpg : checkPGs pvs gbs = true) :
    pairFastGBK P lo hi ix G offs gbs pvs R1 R2 = pairSpec sc0 (-(P : Int)) lo hi g m1 m2 := by
  rw [pairFastGBK_eq P lo hi ix G offs gbs pvs hpg]
  exact pairFastGB_mz_eq_pairSpec P lo hi g m1 m2 gbs R1 R2 ix G offs hg h1 h2 hcat hchk

end MapSpec.Fast

#print axioms MapSpec.Fast.kerHK_eq
#print axioms MapSpec.Fast.pairFastGBK_eq
#print axioms MapSpec.Fast.pairFastGBK_hashed_eq_pairSpec
#print axioms MapSpec.Fast.pairFastGBK_mz_eq_pairSpec
