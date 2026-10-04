import FastMapper
import MzIndex
import MzCheckFast
import ParMap

/-!
# Codec `mapFastMz`: the fast mapper through a minimizer index

`mapFastG` (generic over the seed lookup) instantiated with `MzIndex`: seed `j`'s
places `Mz.lookupSeed ix G R (25j)` (certified by `Mz.check`: exactly the places
where the seed occurs, increasing) become packed anchors `(p + BIAS − 25j)·16 + 2^j`.
Seeds are looked up smallest minimizer bucket first (`mzSize`); `lookupSeedA`
(a copy of `Mz.lookupSeed` writing packed anchors, proved `= map`) avoids a
second pass over the places.

Measured (`FAST_MZ=k FAST_MZ_B=B lake exe fast_bench`, chr21, 100k reads, nproc 4;
answers identical to the hashed index and the prototype):

    index                 bytes        1 task       4 tasks
    hashed 25-mer         406.1 MB     235k–270k    381k–686k reads/s
    minimizer k=21 B=22   119.1 MB     176k
    minimizer k=22 B=22   140.7 MB     170k–199k    313k reads/s
    minimizer k=23 B=24   223.4 MB     204k

`Mz.check2` (= `Mz.check`, rolling completeness pass, `codecs/MzCheckFast.lean`) 17 s
(`Mz.check` 27–34 s), `Mz.build` 33–39 s.

    GenomeBytes gbs g → Encodes R read → checkAllMz idxs gbs = true →
      mapFastMz gbs idxs R = mapSpec sc0 (-12) g read                        (mapFastMz_eq_mapSpec)
-/

namespace MapSpec.Fast

open MapSpec

/-! ## Lookup writing packed anchors `(p + base)·16 + bit` directly
(copies of `Mz.scan`, …, `Mz.lookupSeed`; `lookupA_eq`: `= map` of the original) -/

section

@[inline] def anc (base bit p : Nat) : Nat := (p + base) * 16 + bit

def scanA (ix : Mz.MzIdx) (G R : ByteArray) (s o key bw aw pmo o2 n1 a2 n2 hi base bit : Nat) (t : Nat)
    (acc : Array Nat) : Array Nat :=
  if t < hi then
    scanA ix G R s o key bw aw pmo o2 n1 a2 n2 hi base bit (t + 1)
      (if Mz.okAt ix G R s o key bw aw pmo o2 n1 a2 n2 t then acc.push (anc base bit (ix.posOf (ix.slot t) - o)) else acc)
  else acc
termination_by hi - t

def scanEdgeA (ix : Mz.MzIdx) (G R : ByteArray) (side d s base bit : Nat) (i : Nat) (acc : Array Nat) :
    Array Nat :=
  if i < ix.nr then
    scanEdgeA ix G R side d s base bit (i + 1)
      (if Mz.okEdge ix G R side d s i then acc.push (anc base bit (ix.runs[2 * i + side]! - d)) else acc)
  else acc
termination_by ix.nr - i

def scanRangeA (G R : ByteArray) (s stop base bit : Nat) (p : Nat) (acc : Array Nat) : Array Nat :=
  if p < stop then scanRangeA G R s stop base bit (p + 1) (if Mz.okIn G R s p then acc.push (anc base bit p) else acc)
  else acc
termination_by stop - p

def scanInsideA (ix : Mz.MzIdx) (G R : ByteArray) (s base bit : Nat) (i : Nat) (acc : Array Nat) : Array Nat :=
  if i < ix.nr then
    scanInsideA ix G R s base bit (i + 1) (scanRangeA G R s (ix.rb i + 1 - Mz.q) base bit (ix.ra i) acc)
  else acc
termination_by ix.nr - i

def lookupCodeA (ix : Mz.MzIdx) (G R : ByteArray) (s v base bit : Nat) : Array Nat :=
  let o := ix.mini v
  let h := ix.hsh (ix.sub v o)
  let b := h >>> ix.kb
  let m1 := min o ix.c
  let m2 := min (ix.w - 1 - o) ix.c
  scanA ix G R s o (h &&& ix.kbM) ((v >>> (2 * (Mz.q - o))) &&& ix.pm[m1]!)
    ((v >>> (2 * (Mz.q - o - ix.k - m2))) &&& ix.pm[m2]!) ix.pm[m1]! (2 * (ix.c - m2))
    (o - m1) (ix.k + m2) (ix.w - 1 - o - m2)
    (ix.hiB b) base bit (ix.loB b) #[]

def lookupSeedA (ix : Mz.MzIdx) (G R : ByteArray) (s base bit : Nat) : Array Nat :=
  let u := Mz.firstOdd R s (s + Mz.q)
  if u = s + Mz.q then lookupCodeA ix G R s (Mz.wcGo R s (s + Mz.q) 0) base bit
  else if s < u then scanEdgeA ix G R 0 (u - s) s base bit 0 #[]
  else
    let u2 := Mz.firstAcgt R s (s + Mz.q)
    if u2 < s + Mz.q then scanEdgeA ix G R 1 (u2 - s) s base bit 0 #[]
    else scanInsideA ix G R s base bit 0 #[]

theorem scanA_eq (ix : Mz.MzIdx) (G R : ByteArray) (s o key bw aw pmo o2 n1 a2 n2 hi base bit : Nat) :
    ∀ d t acc, hi - t = d → scanA ix G R s o key bw aw pmo o2 n1 a2 n2 hi base bit t (acc.map (anc base bit)) =
      (Mz.scan ix G R s o key bw aw pmo o2 n1 a2 n2 hi t acc).map (anc base bit) := by
  intro d; induction d with
  | zero =>
    intro t acc h
    have hlt : ¬ t < hi := by omega
    unfold scanA Mz.scan; simp only [hlt, if_false]
  | succ d ih =>
    intro t acc h
    have hlt : t < hi := by omega
    unfold scanA Mz.scan; simp only [hlt, if_true]
    split
    · rw [← Array.map_push]; exact ih _ _ (by omega)
    · exact ih _ _ (by omega)

theorem scanEdgeA_eq (ix : Mz.MzIdx) (G R : ByteArray) (side d0 s base bit : Nat) :
    ∀ d i acc, ix.nr - i = d → scanEdgeA ix G R side d0 s base bit i (acc.map (anc base bit)) =
      (Mz.scanEdge ix G R side d0 s i acc).map (anc base bit) := by
  intro d; induction d with
  | zero =>
    intro t acc h
    have hlt : ¬ t < ix.nr := by omega
    unfold scanEdgeA Mz.scanEdge; simp only [hlt, if_false]
  | succ d ih =>
    intro t acc h
    have hlt : t < ix.nr := by omega
    unfold scanEdgeA Mz.scanEdge; simp only [hlt, if_true]
    split
    · rw [← Array.map_push]; exact ih _ _ (by omega)
    · exact ih _ _ (by omega)

theorem scanRangeA_eq (G R : ByteArray) (s stop base bit : Nat) :
    ∀ d p acc, stop - p = d → scanRangeA G R s stop base bit p (acc.map (anc base bit)) =
      (Mz.scanRange G R s stop p acc).map (anc base bit) := by
  intro d; induction d with
  | zero =>
    intro t acc h
    have hlt : ¬ t < stop := by omega
    unfold scanRangeA Mz.scanRange; simp only [hlt, if_false]
  | succ d ih =>
    intro t acc h
    have hlt : t < stop := by omega
    unfold scanRangeA Mz.scanRange; simp only [hlt, if_true]
    split
    · rw [← Array.map_push]; exact ih _ _ (by omega)
    · exact ih _ _ (by omega)

theorem scanInsideA_eq (ix : Mz.MzIdx) (G R : ByteArray) (s base bit : Nat) :
    ∀ d i acc, ix.nr - i = d → scanInsideA ix G R s base bit i (acc.map (anc base bit)) =
      (Mz.scanInside ix G R s i acc).map (anc base bit) := by
  intro d; induction d with
  | zero =>
    intro t acc h
    have hlt : ¬ t < ix.nr := by omega
    unfold scanInsideA Mz.scanInside; simp only [hlt, if_false]
  | succ d ih =>
    intro t acc h
    have hlt : t < ix.nr := by omega
    unfold scanInsideA Mz.scanInside; simp only [hlt, if_true]
    rw [scanRangeA_eq G R s _ base bit _ _ acc rfl]; exact ih _ _ (by omega)

theorem lookupA_eq (ix : Mz.MzIdx) (G R : ByteArray) (s base bit : Nat) :
    lookupSeedA ix G R s base bit = (Mz.lookupSeed ix G R s).map (anc base bit) := by
  have e : (#[] : Array Nat) = (#[] : Array Nat).map (anc base bit) := by simp
  unfold lookupSeedA Mz.lookupSeed lookupCodeA Mz.lookupCode
  dsimp only
  split
  · conv => lhs; rw [e]
    rw [scanA_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl]
  · split
    · conv => lhs; rw [e]
      rw [scanEdgeA_eq _ _ _ _ _ _ _ _ _ _ _ rfl]
    · split
      · conv => lhs; rw [e]
        rw [scanEdgeA_eq _ _ _ _ _ _ _ _ _ _ _ rfl]
      · conv => lhs; rw [e]
        rw [scanInsideA_eq _ _ _ _ _ _ _ _ _ rfl]

theorem lookupCodeA_eq (ix : Mz.MzIdx) (G R : ByteArray) (s v base bit : Nat) :
    lookupCodeA ix G R s v base bit = (Mz.lookupCode ix G R s v).map (anc base bit) := by
  have e : (#[] : Array Nat) = (#[] : Array Nat).map (anc base bit) := by simp
  unfold lookupCodeA Mz.lookupCode
  dsimp only
  conv => lhs; rw [e]
  rw [scanA_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl]

end

/-- The seed code from its hash: `mix⁻¹ y = y·MIXINV mod 2^50`. -/
@[inline] def unmix (y : UInt64) : Nat := ((y * MIXINV.toUInt64) &&& 0x3FFFFFFFFFFFF).toNat

/-- A prepared seed: for an ACGT seed its code `v`, minimizer offset `o`, k-word
hash `h` and bucket `b`, computed once (order hint and lookup share them). -/
structure MzP where
  ok : Bool
  v : Nat
  o : Nat
  h : Nat
  b : Nat
deriving Inhabited

@[inline] def mzPrep (ix : Mz.MzIdx) : Option UInt64 → MzP
  | some y =>
    let v := unmix y
    let o := ix.mini v
    let h := ix.hsh (ix.sub v o)
    ⟨true, v, o, h, h >>> ix.kb⟩
  | none => ⟨false, 0, 0, 0, 0⟩

/-- `lookupCodeA` with the prepared values. -/
@[inline] def lookupP (ix : Mz.MzIdx) (G R : ByteArray) (s : Nat) (p : MzP) (base bit : Nat) : Array Nat :=
  let o := p.o
  let v := p.v
  let m1 := min o ix.c
  let m2 := min (ix.w - 1 - o) ix.c
  scanA ix G R s o (p.h &&& ix.kbM) ((v >>> (2 * (Mz.q - o))) &&& ix.pm[m1]!)
    ((v >>> (2 * (Mz.q - o - ix.k - m2))) &&& ix.pm[m2]!) ix.pm[m1]! (2 * (ix.c - m2))
    (o - m1) (ix.k + m2) (ix.w - 1 - o - m2)
    (ix.hiB p.b) base bit (ix.loB p.b) #[]

/-- Seed `j`'s packed anchors from a minimizer index; an ACGT seed reuses its
prepared code and bucket instead of reading its letters again. -/
def mzLook (ix : Mz.MzIdx) (G R : ByteArray) (j : Nat) (p : MzP) : Array Nat :=
  if p.ok then lookupP ix G R (j * q) p (BIAS - j * q) (pow2 j)
  else lookupSeedA ix G R (j * q) (BIAS - j * q) (pow2 j)

theorem unmix_mix (x : UInt64) (hx : x.toNat < 2 ^ 50) : unmix (mix x) = x.toNat := by
  unfold unmix
  rw [UInt64.toNat_and, UInt64.toNat_mul, mix_toNat, show (0x3FFFFFFFFFFFF : UInt64).toNat = 2 ^ 50 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, show MIXINV.toUInt64.toNat = MIXINV from rfl,
    Nat.mod_mod_of_dvd _ (by decide : 2 ^ 50 ∣ 2 ^ 64), Nat.mod_mul_mod, Nat.mul_assoc, Nat.mul_mod,
    show MIXC.toNat * MIXINV % 2 ^ 50 = 1 by decide, Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt hx]

theorem c2N_eq (b : UInt8) : c2N b = byteCode b := by
  unfold c2N byteCode codeNat
  have e : ∀ c : UInt8, (b = c ↔ b.toNat = c.toNat) := fun c => by rw [UInt8.toNat_inj]
  simp only [e]; rfl

theorem wN_eq (B : ByteArray) : ∀ n i, wN B i n = Mz.wc B i n := by
  intro n
  induction n with
  | zero => intro i; rfl
  | succ n ih =>
    intro i
    rw [show n + 1 = 1 + n by omega, Mz.wc_add, show 1 + n = n + 1 by omega]
    simp only [wN, Mz.wc, Nat.zero_mul, Nat.zero_add, Nat.add_zero, c2N_eq, ih]

theorem acgt_mz (b : UInt8) (h : acgt b = true) : Mz.acgt b = true := by
  unfold acgt at h
  have := acgt_tab b.toNat (UInt8.toNat_lt b) (by simpa using h)
  have e : ∀ n : Nat, n < 256 → (b = n.toUInt8 ↔ b.toNat = n) := fun n hn => by
    constructor
    · rintro rfl; simp; omega
    · intro h; rw [← h]; simp
  unfold Mz.acgt
  rcases this with h | h | h | h <;>
    simp [show b = _ from (e _ (by omega)).2 h]

/-- Order hint: size of the bucket of the seed's minimizer; 0 for a seed with a
letter other than ACGT. -/
@[inline] def mzSize (ix : Mz.MzIdx) (p : MzP) : Nat := if p.ok then ix.hiB p.b - ix.loB p.b else 0

def mzL : Look Mz.MzIdx MzP := ⟨mzPrep, mzSize, mzLook⟩

def checkAllMz (idxs : Array Mz.MzIdx) (gbs : Array ByteArray) : Bool :=
  (List.range gbs.size).all fun c => Mz.check2 idxs[c]! gbs[c]!

def mapFastMz (gbs : Array ByteArray) (idxs : Array Mz.MzIdx) (R : ByteArray) : Option (Window × Int) :=
  mapFastG mzL gbs idxs R

theorem mzLook_eq (ix : Mz.MzIdx) (G R : ByteArray) (j : Nat) :
    mzLook ix G R j (mzPrep ix (seedHash R j)) =
      (Mz.lookupSeed ix G R (j * q)).map (anc (BIAS - j * q) (pow2 j)) := by
  rw [seedHash_spec]
  split
  · next ha =>
    have e : ∀ y, mzLook ix G R j (mzPrep ix (some y)) =
        lookupCodeA ix G R (j * q) (unmix y) (BIAS - j * q) (pow2 j) := fun y => by
      unfold mzLook mzPrep lookupP lookupCodeA
      dsimp only
      rw [if_pos rfl]
    rw [e]
    unfold hashAt
    rw [unmix_mix _ (by rw [hashWord_toNat]; exact Nat.lt_of_lt_of_le (wN_lt R (j * q) q) (by decide)),
      hashWord_toNat, wN_eq, lookupCodeA_eq, Mz.lookupSeed_eq_lookupCode ix G R (j * q)
        (fun i hi => acgt_mz _ ((allACGT_word R (j * q)).1 ha i hi))]
    rfl
  · show lookupSeedA ix G R (j * q) (BIAS - j * q) (pow2 j) = _
    rw [lookupA_eq]

theorem mzLook_ok (ix : Mz.MzIdx) (G R : ByteArray) (j : Nat) (hj : j < 4)
    (hc : Mz.check ix G = true) : LookOk G R j (mzLook ix G R j (mzPrep ix (seedHash R j))) := by
  have hf : anc (BIAS - j * q) (pow2 j) = anchorOf j := funext fun p => by
    unfold anc; rw [pow2_eq j hj]; rfl
  unfold LookOk
  rw [mzLook_eq, hf, Array.toList_map]
  refine ⟨List.Pairwise.map _ (fun (a b : Nat) (hab : a < b) => show anchorOf j a < anchorOf j b by
    unfold anchorOf; generalize 2 ^ j = w; omega) (Mz.lookupSeed_sorted hc R (j * q)), fun e => ?_⟩
  rw [List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, (Mz.lookupSeed_mem hc R (j * q) p).1 hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, (Mz.lookupSeed_mem hc R (j * q) p).2 hp, rfl⟩

/-- **Mapping.**  Through minimizer indexes that pass the checker, `mapFastMz` is
the specification's answer. -/
theorem mapFastMz_eq_mapSpec (g : Genome) (read : List Char) (gbs : Array ByteArray)
    (idxs : Array Mz.MzIdx) (R : ByteArray) (hg : GenomeBytes gbs g) (hr : Encodes R read)
    (hchk : checkAllMz idxs gbs = true) :
    mapFastMz gbs idxs R = mapSpec sc0 (-12) g read := by
  apply mapFastG_eq_mapSpec mzL g read gbs idxs R hg hr
  intro c hc R' j hj
  unfold checkAllMz at hchk
  simp only [List.all_eq_true, List.mem_range] at hchk
  exact mzLook_ok _ _ _ _ hj (by rw [← Mz.check2_eq]; exact hchk c hc)

/-- `n` tasks. -/
def mapFastMzPar (n : Nat) (gbs : Array ByteArray) (idxs : Array Mz.MzIdx) (Rs : Array ByteArray) :
    Array (Option (Window × Int)) := ParMap.parMap n (mapFastMz gbs idxs) Rs

theorem mapFastMzPar_eq_mapSpec (n : Nat) (g : Genome) (gbs : Array ByteArray) (idxs : Array Mz.MzIdx)
    (Rs : Array ByteArray) (reads : Array (List Char)) (hg : GenomeBytes gbs g)
    (hchk : checkAllMz idxs gbs = true) (hl : Rs.size = reads.size)
    (hr : ∀ i (h1 : i < Rs.size) (h2 : i < reads.size), Encodes Rs[i] reads[i]) :
    mapFastMzPar n gbs idxs Rs = reads.map (mapSpec sc0 (-12) g) := by
  unfold mapFastMzPar
  rw [ParMap.parMap_eq_map]
  apply Array.ext (by simp [hl])
  intro i h1 h2
  simp only [Array.getElem_map]
  exact mapFastMz_eq_mapSpec g _ gbs idxs _ hg (hr i (by simpa using h1) (by simpa [hl] using h1)) hchk

end MapSpec.Fast

#print axioms MapSpec.Fast.mapFastMz_eq_mapSpec
#print axioms MapSpec.Fast.mapFastMzPar_eq_mapSpec
