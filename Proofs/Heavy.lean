import Proofs.GaveUp
import ParMap

/-! # The heavy 25-mer table: an O(log n) `highlyRepetitiveIn` witness

The index carries a table `H` of 25-letter words, 25 bytes each, sorted (Testing/notes/INDEX_COUNTS.md). The builder
(`Proofs/HeavyBuild.lean`) is not proved. What is proved is the check `heavyOk`, run once at build time inside
`indexOk`. For every entry it looks up the entry and the entry's reverse complement in the minimizer index and counts
in-chromosome places (`capCount`: among the first `gaveUpRepeats` places, a lower bound on `GaveUp.seedCount`). The
check passes when the two counts sum to at least `gaveUpRepeats`.

Query (`heavyMate`): binary-search each grid seed of the mate (letters `[25 j, 25 j + 25)`) in `H`. Soundness needs only
"found ⇒ equal to some entry" (no sortedness): the entry's check gives `occurrences ≥ gaveUpRepeats`, because
`occurrences w` = forward matches of `w` + forward matches of `reverseComplement w` (`GaveUp.occurrences_eq`).
-/

namespace Spec.Heavy

open GaveUp

/-! ## Counting with a cap -/

-- in-chromosome places among the first `gaveUpRepeats` places of the seed `R[s, s+25)`: a function of the exact
-- place list only (so two checked indexes of one genome agree on it), computed with a capped lookup (`capCount_eqF`)
def capCount (pk : MapSpec.Fast.PkMz) (offs ns : Array Nat) (R : ByteArray) (s : Nat) : Nat :=
  ((seedPlaces pk R s).extract 0 gaveUpRepeats).toList.countP (fun e => inChrom offs ns (e / 16))

def capCountF (pk : MapSpec.Fast.PkMz) (offs ns : Array Nat) (R : ByteArray) (s : Nat) : Nat :=
  let p := MapSpec.Fast.mzPrep pk.1 (MapSpec.Fast.seedHashAt R s)
  if p.ok then
    ((MapSpec.Fast.lookupPWk pk.1 pk.2 R s p 0 0 gaveUpRepeats).extract 0 gaveUpRepeats).toList.countP
      (fun e => inChrom offs ns (e / 16))
  else ((seedPlaces pk R s).extract 0 gaveUpRepeats).toList.countP (fun e => inChrom offs ns (e / 16))

@[csimp] theorem capCount_eqF : @capCount = @capCountF := by
  funext pk offs ns R s
  unfold capCount capCountF
  simp only []
  split
  · rename_i hok
    have hsp : seedPlaces pk R s = MapSpec.Fast.lookupPW pk.1 pk.2 R s
        (MapSpec.Fast.mzPrep pk.1 (MapSpec.Fast.seedHashAt R s)) 0 0 := by
      unfold seedPlaces MapSpec.Fast.mzLookSP; rw [if_pos hok]
    rw [MapSpec.Fast.lookupPWk_extract, hsp]
  · rfl

theorem capCount_le (pk : MapSpec.Fast.PkMz) (offs ns : Array Nat) (R : ByteArray) (s : Nat) :
    capCount pk offs ns R s ≤ seedCount pk offs ns R s := by
  unfold capCount seedCount
  have hsub : ((seedPlaces pk R s).extract 0 gaveUpRepeats).toList.Sublist (seedPlaces pk R s).toList := by
    rw [Array.toList_extract]
    simpa [List.extract] using List.take_sublist gaveUpRepeats _
  exact hsub.countP_le

/-! ## Reverse complement of bytes -/

def compB (b : UInt8) : UInt8 :=
  if b = 65 then 84 else if b = 84 then 65 else if b = 67 then 71 else if b = 71 then 67 else b

-- the reverse complement of the 25 bytes at `s`
def rcAt (R : ByteArray) (s : Nat) : ByteArray := ((R.extract s (s + 25)).toList.reverse.map compB).toByteArray

set_option maxRecDepth 100000 in
theorem compB_char (b : UInt8) : Char.ofNat (compB b).toNat = complement (Char.ofNat b.toNat) := by
  have key : ∀ n, n < 256 → Char.ofNat (compB (UInt8.ofNat n)).toNat = complement (Char.ofNat (UInt8.ofNat n).toNat) := by
    decide
  have := key b.toNat b.toNat_lt
  rwa [UInt8.ofNat_toNat] at this

theorem toList_extract (R : ByteArray) (a b : Nat) : (R.extract a b).toList = (R.toList.drop a).take (b - a) := by
  rw [Bridge.byteArray_toList, Bridge.byteArray_toList, ByteArray.data_extract, Array.toList_extract, List.extract]

theorem decodeRead_rcAt (R : ByteArray) (s : Nat) :
    decodeRead (rcAt R s) = reverseComplement (((decodeRead R).drop s).take seedLength) := by
  unfold rcAt decodeRead reverseComplement
  rw [Bridge.byteArray_toList (List.toByteArray _), List.toList_data_toByteArray, toList_extract,
    show s + 25 - s = seedLength from by unfold seedLength; omega]
  simp only [List.map_reverse, List.map_take, List.map_drop, List.map_map]
  congr 3
  apply List.map_congr_left
  intro b _
  exact compB_char b

theorem rcAt_size (R : ByteArray) (s : Nat) (h : s + 25 ≤ R.size) : (rcAt R s).size = 25 := by
  have := congrArg List.length (decodeRead_rcAt R s)
  simp only [GaveUp.decodeRead_length, reverseComplement, List.length_reverse, List.length_map, List.length_take,
    List.length_drop, seedLength] at this
  omega

/-! ## The table and its check -/

-- entry `i` (bytes `[25 i, 25 i + 25)` of `H`) and its reverse complement occur `gaveUpRepeats` times between them
def entryOk (pk : MapSpec.Fast.PkMz) (offs ns : Array Nat) (H : ByteArray) (i : Nat) : Bool :=
  gaveUpRepeats ≤ capCount pk offs ns H (25 * i) + capCount pk offs ns (rcAt H (25 * i)) 0

-- every entry the mask marks (byte 1) passes
def heavyOk (pk : MapSpec.Fast.PkMz) (offs ns : Array Nat) (H M : ByteArray) : Bool :=
  (List.range (H.size / 25)).all fun i => M.get! i != 1 || entryOk pk offs ns H i

-- the builder's mask: which entries pass (computed once, with the built index)
def heavyMask (pk : MapSpec.Fast.PkMz) (offs ns : Array Nat) (H : ByteArray) : ByteArray :=
  ((List.range (H.size / 25)).map fun i => if entryOk pk offs ns H i then (1 : UInt8) else 0).toByteArray

/-! ## Two checked indexes of one genome agree on the counts -/

theorem eq_of_sorted_mem : ∀ (l1 l2 : List Nat), l1.Pairwise (· < ·) → l2.Pairwise (· < ·) →
    (∀ x, x ∈ l1 ↔ x ∈ l2) → l1 = l2
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).mpr List.mem_cons_self) (by simp)
  | a :: _, [], _, _, h => absurd ((h a).mp List.mem_cons_self) (by simp)
  | a :: t1, b :: t2, h1, h2, h => by
    rw [List.pairwise_cons] at h1 h2
    have hab : a = b := by
      have ha := (h a).mp List.mem_cons_self
      have hb := (h b).mpr List.mem_cons_self
      rcases List.mem_cons.mp ha with e | ha'
      · exact e
      rcases List.mem_cons.mp hb with e | hb'
      · exact e.symm
      have := h2.1 a ha'; have := h1.1 b hb'; omega
    subst hab
    congr 1
    refine eq_of_sorted_mem t1 t2 h1.2 h2.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · rcases List.mem_cons.mp ((h x).mp (List.mem_cons_of_mem _ hx)) with e | e
      · have := h1.1 x hx; omega
      · exact e
    · rcases List.mem_cons.mp ((h x).mpr (List.mem_cons_of_mem _ hx)) with e | e
      · have := h2.1 x hx; omega
      · exact e

theorem seedPlaces_congr {ix1 ix2 : MapSpec.Mz.MzIdx} {G1 G2 : MapSpec.Fast.PGen}
    (h1 : MapSpec.Mz.check2P ix1 G1 = true) (h2 : MapSpec.Mz.check2P ix2 G2 = true)
    (hu : MapSpec.Mz.unpack G1 = MapSpec.Mz.unpack G2) (R : ByteArray) (s : Nat) :
    seedPlaces (ix1, G1) R s = seedPlaces (ix2, G2) R s := by
  have hc1 : MapSpec.Mz.check ix1 (MapSpec.Mz.unpack G1) = true := by
    rw [← MapSpec.Mz.check2_eq, ← MapSpec.Mz.check2P_eq (MapSpec.Mz.rep_unpack G1) ix1]; exact h1
  have hc2 : MapSpec.Mz.check ix2 (MapSpec.Mz.unpack G2) = true := by
    rw [← MapSpec.Mz.check2_eq, ← MapSpec.Mz.check2P_eq (MapSpec.Mz.rep_unpack G2) ix2]; exact h2
  unfold seedPlaces
  simp only []
  rw [MapSpec.Fast.mzLookSP_eq (MapSpec.Mz.rep_unpack G1), MapSpec.Fast.mzLookS_eq,
    MapSpec.Fast.mzLookSP_eq (MapSpec.Mz.rep_unpack G2), MapSpec.Fast.mzLookS_eq]
  congr 1
  rw [hu] at hc1 ⊢
  apply Array.toList_inj.mp
  exact eq_of_sorted_mem _ _ (MapSpec.Mz.lookupSeed_sorted hc1 R s) (MapSpec.Mz.lookupSeed_sorted hc2 R s)
    fun p => (MapSpec.Mz.lookupSeed_mem hc1 R s p).trans (MapSpec.Mz.lookupSeed_mem hc2 R s p).symm

theorem entryOk_congr {ix1 ix2 : MapSpec.Mz.MzIdx} {G1 G2 : MapSpec.Fast.PGen}
    (h1 : MapSpec.Mz.check2P ix1 G1 = true) (h2 : MapSpec.Mz.check2P ix2 G2 = true)
    (hu : MapSpec.Mz.unpack G1 = MapSpec.Mz.unpack G2) (offs ns : Array Nat) (H : ByteArray) (i : Nat) :
    entryOk (ix1, G1) offs ns H i = entryOk (ix2, G2) offs ns H i := by
  unfold entryOk capCount
  rw [seedPlaces_congr h1 h2 hu, seedPlaces_congr h1 h2 hu]

theorem heavyMask_size (pk : MapSpec.Fast.PkMz) (offs ns : Array Nat) (H : ByteArray) :
    (heavyMask pk offs ns H).size = H.size / 25 := by
  simp [heavyMask, List.size_toByteArray]

theorem heavyMask_get (pk : MapSpec.Fast.PkMz) (offs ns : Array Nat) (H : ByteArray) (i : Nat)
    (hi : i < H.size / 25) :
    (heavyMask pk offs ns H).get! i = if entryOk pk offs ns H i then 1 else 0 := by
  have hs : i < (heavyMask pk offs ns H).size := by simp [heavyMask, List.size_toByteArray, hi]
  rw [ByteArray.get!, getElem!_pos (heavyMask pk offs ns H).data i (by simpa using hs)]
  unfold heavyMask
  simp [List.data_toByteArray]

/-- **The builder's mask passes the check on any checked index of the same genome** (the loaded one). -/
theorem heavyOk_mask {ix1 ix2 : MapSpec.Mz.MzIdx} {G1 G2 : MapSpec.Fast.PGen}
    (h1 : MapSpec.Mz.check2P ix1 G1 = true) (h2 : MapSpec.Mz.check2P ix2 G2 = true)
    (hu : MapSpec.Mz.unpack G1 = MapSpec.Mz.unpack G2) (offs ns : Array Nat) (H : ByteArray) :
    heavyOk (ix2, G2) offs ns H (heavyMask (ix1, G1) offs ns H) = true := by
  unfold heavyOk
  rw [List.all_eq_true]
  intro i hi
  rw [List.mem_range] at hi
  rw [heavyMask_get _ _ _ _ _ hi, ← entryOk_congr h1 h2 hu]
  split <;> simp_all

/-! ## The query: binary search over the entries -/

-- compare `R[s+k, s+25)` with entry `i`'s bytes from `k` on
def cmpGo (H R : ByteArray) (i s : Nat) : (k : Nat) → Ordering
  | 0 => .eq
  | k + 1 =>
    let a := R.get! (s + (24 - k))
    let b := H.get! (25 * i + (24 - k))
    if a < b then .lt else if b < a then .gt else cmpGo H R i s k

theorem cmpGo_eq (H R : ByteArray) (i s : Nat) : ∀ k, cmpGo H R i s k = .eq →
    ∀ j, 25 - k ≤ j → j < 25 → R.get! (s + j) = H.get! (25 * i + j)
  | 0, _, j, h1, h2 => by omega
  | k + 1, h, j, h1, h2 => by
    unfold cmpGo at h
    simp only [] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i ha hb
        by_cases hj : j = 24 - k
        · subst hj
          have := UInt8.le_antisymm (UInt8.not_lt.mp hb) (UInt8.not_lt.mp ha)
          exact this
        · exact cmpGo_eq H R i s k h j (by omega) h2

-- an entry equal to `R[s, s+25)`, searched in `[lo, hi)`
def findGo (H R : ByteArray) (s : Nat) : (fuel lo hi : Nat) → Option Nat
  | 0, _, _ => none
  | f + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      match cmpGo H R mid s 25 with
      | .eq => some mid
      | .lt => findGo H R s f lo mid
      | .gt => findGo H R s f (mid + 1) hi
    else none

theorem findGo_sound (H R : ByteArray) (s : Nat) : ∀ f lo hi i, findGo H R s f lo hi = some i →
    i < hi ∧ cmpGo H R i s 25 = .eq
  | 0, _, _, _, h => by simp [findGo] at h
  | f + 1, lo, hi, i, h => by
    unfold findGo at h
    split at h
    · simp only [] at h
      split at h
      · rename_i heq
        cases h
        exact ⟨by omega, heq⟩
      · have := findGo_sound H R s f _ _ i h; exact ⟨by omega, this.2⟩
      · exact findGo_sound H R s f _ _ i h
    · cases h

-- the grid seed at `s` is a marked entry of `H`
def seedHeavy (H M R : ByteArray) (s : Nat) : Bool :=
  s + 25 ≤ R.size &&
    match findGo H R s 64 0 (H.size / 25) with
    | some i => M.get! i == 1
    | none => false

-- the mate has at least `gaveUpSeeds` grid seeds in `H`
def heavyMate (H M R : ByteArray) : Bool :=
  gaveUpSeeds ≤ (List.range (R.size / seedLength)).countP fun j => seedHeavy H M R (seedLength * j)

/-! ## Compiled forms: the entries checked in parallel (`ParMap.parMap`, the same as a plain map) -/

def heavyMaskP (pk : MapSpec.Fast.PkMz) (offs ns : Array Nat) (H : ByteArray) : ByteArray :=
  ⟨ParMap.parMap 16 (fun i => if entryOk pk offs ns H i then (1 : UInt8) else 0) (Array.range (H.size / 25))⟩

@[csimp] theorem heavyMask_eqP : @heavyMask = @heavyMaskP := by
  funext pk offs ns H
  unfold heavyMask heavyMaskP
  rw [ParMap.parMap_eq_map]
  apply ByteArray.ext
  rw [List.data_toByteArray]
  apply Array.toList_inj.mp
  simp [Array.toList_map, Array.toList_range]

def heavyOkP (pk : MapSpec.Fast.PkMz) (offs ns : Array Nat) (H M : ByteArray) : Bool :=
  (ParMap.parMap 16 (fun i => M.get! i != 1 || entryOk pk offs ns H i) (Array.range (H.size / 25))).all id

@[csimp] theorem heavyOk_eqP : @heavyOk = @heavyOkP := by
  funext pk offs ns H M
  unfold heavyOk heavyOkP
  rw [ParMap.parMap_eq_map, ← Array.all_toList]
  simp [Array.toList_map, Array.toList_range, List.all_map]

/-! ## Soundness -/

theorem seedHeavy_sound {ix : MapSpec.Mz.MzIdx} {G : MapSpec.Fast.PGen} {offs ns : Array Nat} {genome : Genome}
    (hchk : MapSpec.Mz.check2P ix G = true)
    (hslice : ∀ (c : Nat) (chr : Chromosome), genome[c]? = some chr →
      offs[c]! + chr.seq.length ≤ (decodeRead (MapSpec.Mz.unpack G)).length ∧
      chr.seq = ((decodeRead (MapSpec.Mz.unpack G)).drop offs[c]!).take chr.seq.length)
    (hchr : ∀ c, c < ns.size → ∃ chr : Chromosome, genome[c]? = some chr ∧ chr.seq.length = ns[c]!)
    {H M : ByteArray} (hH : heavyOk (ix, G) offs ns H M = true)
    (R : ByteArray) (s : Nat) (h : seedHeavy H M R s = true) :
    gaveUpRepeats ≤ genome.occurrences (((decodeRead R).drop s).take seedLength) := by
  unfold seedHeavy at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hsR, hm⟩ := h
  split at hm
  case h_2 => cases hm
  rename_i i hf
  obtain ⟨hi, hc⟩ := findGo_sound H R s 64 0 _ i hf
  have he := cmpGo_eq H R i s 25 hc
  have hok : entryOk (ix, G) offs ns H i = true := by
    have := List.all_eq_true.mp hH i (List.mem_range.mpr hi)
    simp only [beq_iff_eq] at hm
    simpa [hm] using this
  unfold entryOk at hok
  simp only [decide_eq_true_eq] at hok
  have hHs : 25 * i + 25 ≤ H.size := by
    have := Nat.lt_div_iff_mul_lt (by decide : 0 < 25) |>.mp hi
    omega
  -- the entry's letters are the seed's letters
  have hword : ((decodeRead H).drop (25 * i)).take seedLength = ((decodeRead R).drop s).take seedLength := by
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_take, List.getElem?_take, List.getElem?_drop, List.getElem?_drop]
    split
    · rename_i hj
      have hsl : seedLength = 25 := rfl
      rw [hsl] at hj
      rw [decodeRead_getElem? _ _ (by omega), decodeRead_getElem? _ _ (by omega), he j (by omega) hj]
    · rfl
  have h1 := seedCount_le_occList (genome := genome) hchk hslice hchr H (25 * i) hHs
  have h2 := seedCount_le_occList (genome := genome) hchk hslice hchr (rcAt H (25 * i)) 0
    (by rw [rcAt_size H _ hHs]; omega)
  rw [hword] at h1
  have hrc : ((decodeRead (rcAt H (25 * i))).drop 0).take seedLength =
      reverseComplement (((decodeRead R).drop s).take seedLength) := by
    rw [List.drop_zero, decodeRead_rcAt, hword]
    unfold reverseComplement
    rw [List.take_of_length_le]
    simp [GaveUp.decodeRead_length, seedLength] <;> omega
  rw [hrc] at h2
  rw [occurrences_eq]
  have c1 := capCount_le (ix, G) offs ns H (25 * i)
  have c2 := capCount_le (ix, G) offs ns (rcAt H (25 * i)) 0
  omega

/-- **The table check is sound**: a mate that `heavyMate` flags is `highlyRepetitiveIn` the genome. -/
theorem heavyMate_sound {ix : MapSpec.Mz.MzIdx} {G : MapSpec.Fast.PGen} {offs ns : Array Nat} {genome : Genome}
    (hchk : MapSpec.Mz.check2P ix G = true)
    (hslice : ∀ (c : Nat) (chr : Chromosome), genome[c]? = some chr →
      offs[c]! + chr.seq.length ≤ (decodeRead (MapSpec.Mz.unpack G)).length ∧
      chr.seq = ((decodeRead (MapSpec.Mz.unpack G)).drop offs[c]!).take chr.seq.length)
    (hchr : ∀ c, c < ns.size → ∃ chr : Chromosome, genome[c]? = some chr ∧ chr.seq.length = ns[c]!)
    {H M : ByteArray} (hH : heavyOk (ix, G) offs ns H M = true)
    (R : ByteArray) (h : heavyMate H M R = true) : (decodeRead R).highlyRepetitiveIn genome := by
  unfold heavyMate at h
  simp only [decide_eq_true_eq] at h
  have hsl : seedLength = 25 := rfl
  unfold Read.highlyRepetitiveIn
  simp only [GaveUp.decodeRead_length, ge_iff_le]
  refine Nat.le_trans h (List.countP_mono_left fun j _ hc => ?_)
  simp only [decide_eq_true_eq]
  have := seedHeavy_sound hchk hslice hchr hH R _ hc
  rw [List.extract_eq_take_drop, show (j + 1) * seedLength - j * seedLength = seedLength by rw [hsl]; omega,
    show j * seedLength = seedLength * j from Nat.mul_comm _ _]
  exact this

end Spec.Heavy

#print axioms Spec.Heavy.heavyMate_sound
#print axioms Spec.Heavy.heavyOk_mask
#print axioms Spec.Heavy.heavyMask_eqP
#print axioms Spec.Heavy.heavyOk_eqP
