import PairHits
import WgPacked

/-!
# `hitsAtKP`: every hit of a read within a cap, packed genome, word filter, word kernels

`hitsAtB` (codecs/PairHits.lean) with the chromosomes held 2-bit (`PGen`), the word
filter `kfiltV` before the kernels and the word kernels `kerHKG`:

    hitsAtKP lim ix G offs pgs R = hitsAtB lim ix G offs (pgs.map Mz.unpack) R   (hitsAtKP_eq)

and, over the packed whole-genome index (`PkMz`),

    hitsAtKP … = some l → (x ∈ l ↔ x ∈ hitsBoth sc0 (−lim) g read)            (mem_hitsAtKP_mz)
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-- `hitsC` on packed chromosomes: the word filter, then the word kernels. -/
def hitsCK (K : RP) (R : ByteArray) (pgs2 : Array PGen) (c lim : Nat) (acc : List (Array Nat))
    (us : List Nat) (Ls : Nat) : List (Window × Nat) :=
  (diags acc).flatMap fun D =>
    if kfiltV K R pgs2[c]! acc us Ls lim (initP lim) D then
      (shapesAt lim).filterMap fun sh =>
        if 0 ≤ dst R.size D sh ∧ 0 ≤ wlen R.size sh then
          let k := kerHKG R K pgs2 pgs2 c (dst R.size D sh).toNat (wlen R.size sh).toNat lim
          if k ≤ lim then some (⟨c, (dst R.size D sh).toNat, (wlen R.size sh).toNat⟩, k) else none
        else none
    else []

/-- `hitsS` on packed chromosomes (the read packed once per strand). -/
def hitsSK {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G : ByteArray) (offs : Array Nat)
    (pgs2 : Array PGen) (n t lim : Nat) (Rs : ByteArray) : List (Window × Nat) :=
  let m := Rs.size / 25
  let Ls := Rs.size / m
  let K := packRP Rs
  let ps := prepG ix Rs m Ls
  let J := (ordG (ps.map (LookG.size ix)) m).take (sbound lim + 1)
  let lk := J.map fun j => (j, LookG.look ix G Rs (j * Ls) (Rs.size - j * Ls) ps[j]!)
  let us := unseen m J
  (List.range n).flatMap fun c =>
    hitsCK K Rs pgs2 (t + c) lim (slicesAt lk Rs.size Ls offs[c]! (GRead.size pgs2[t + c]!)) us Ls

/-- Every placement of a read within penalty `lim ≤ 16`, packed genome. -/
def hitsAtKP {L Pp : Type} [LookG L Pp] [Inhabited Pp] (lim : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (pgs : Array PGen) (R : ByteArray) : Option (List (Placement × Int)) :=
  if fastT lim R then
    let n := pgs.size
    let pgs2 := pgs ++ pgs
    some ((hitsSK ix G offs pgs2 n 0 lim R ++ hitsSK ix G offs pgs2 n n lim (revCompK R)).map
      fun x => (decB n x.1, -(x.2 : Int)))
  else none

theorem hitsCK_eq (pgs : Array PGen) (R : ByteArray) (c lim : Nat) (acc : List (Array Nat)) (us : List Nat)
    (Ls : Nat) :
    hitsCK (packRP R) R (pgs ++ pgs) c lim acc us Ls =
      hitsC R (pgs.map Mz.unpack ++ pgs.map Mz.unpack) c lim acc us Ls := by
  have hs := sameA_append (sameA_unpack pgs) sameG_default
  have hk : ∀ st len, kerHKG R (packRP R) (pgs ++ pgs) (pgs ++ pgs) c st len lim =
      kerH R (pgs.map Mz.unpack ++ pgs.map Mz.unpack) c st len lim := by
    intro st len
    rw [kerHKG_same hs, kerHKG_bytes, kerHK_eq R _ _ (repAllK_unpack pgs)]
  have hf : ∀ D, kfiltV (packRP R) R (pgs ++ pgs)[c]! acc us Ls lim (initP lim) D =
      kfilt R (pgs.map Mz.unpack ++ pgs.map Mz.unpack)[c]! acc us Ls lim (initP lim) D := by
    intro D; rw [kfiltV_eq, kfilt_same (hs.2 c)]
  unfold hitsCK hitsC
  simp only [hk, hf]

theorem hitsSK_eq {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G : ByteArray) (offs : Array Nat)
    (pgs : Array PGen) (n t lim : Nat) (Rs : ByteArray) :
    hitsSK ix G offs (pgs ++ pgs) n t lim Rs = hitsS ix G offs (pgs.map Mz.unpack ++ pgs.map Mz.unpack) n t lim Rs := by
  have hs := sameA_append (sameA_unpack pgs) sameG_default
  have hz : ∀ c, GRead.size (pgs ++ pgs)[c]! = ByteArray.size ((pgs.map Mz.unpack ++ pgs.map Mz.unpack)[c]!) :=
    fun c => (hs.2 c).1
  unfold hitsSK hitsS
  simp only [hitsCK_eq, hz]

theorem hitsAtKP_eq {L Pp : Type} [LookG L Pp] [Inhabited Pp] (lim : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (pgs : Array PGen) (R : ByteArray) :
    hitsAtKP lim ix G offs pgs R = hitsAtB lim ix G offs (pgs.map Mz.unpack) R := by
  unfold hitsAtKP hitsAtB
  simp only [hitsSK_eq, revCompK_eq, revCompB2_eq, Array.size_map]

theorem hitsAtB_congrG {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G G' : ByteArray)
    (hG : ∀ R s base p, LookG.look ix G R s base p = LookG.look ix G' R s base p) (lim : Nat)
    (offs : Array Nat) (gbs : Array ByteArray) (R : ByteArray) :
    hitsAtB lim ix G offs gbs R = hitsAtB lim ix G' offs gbs R := by
  simp only [hitsAtB, hitsS, hG]

/-- **Every hit, packed whole genome.** -/
theorem mem_hitsAtKP_mz (lim : Nat) (hl16 : lim ≤ 16) (g : Genome) (read : List Char) (ix : Mz.MzIdx)
    (G : PGen) (offs ns : Array Nat) (R : ByteArray) (hcut : cutOk G offs ns = true)
    (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) g) (hr : Encodes R read)
    (hchk : Mz.check2P ix G = true) (l : List (Placement × Int))
    (hl : hitsAtKP lim ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) R = some l)
    (x : Placement × Int) : x ∈ l ↔ x ∈ hitsBoth sc0 (-(lim : Int)) g read := by
  rw [hitsAtKP_eq, hitsAtB_congrG ((ix, G) : PkMz) ByteArray.empty (Mz.unpack G) (fun _ _ _ _ => rfl)] at hl
  exact mem_hitsAtB lim hl16 read g _ R hg hr _ _ offs (catOk_cut G offs ns hcut) (lookOk_pk ix G hchk) l hl x

end MapSpec.Fast

#print axioms MapSpec.Fast.hitsAtKP_eq
#print axioms MapSpec.Fast.mem_hitsAtKP_mz
