import Proofs.Bridge
import WgPacked

/-! # The index layer: build, save, load, check (helpers for `Proofs/Aligner.lean`).

* build: the packer of bench/WholeGenome.lean `pmap` mode (`PB.push` every letter in order, then
  `finish`) and the minimizer builder of its `build` mode (`Mz.buildWV`, k=22, B=26, c=0, w=5, t=6)
  over the view of the chromosomes; when the view is not right (chromosomes shorter than 2^20,
  `catOkV`) the same builder reading the packed genome (`Mz.buildWP`). Nothing here is trusted:
  `indexOk` checks the result.
* save / load: one `ByteArray`: magic, then every field (`Nat` as 8 LE bytes, arrays and bytes
  length-prefixed). Nothing about the format is proved; `roundTrips` checks it once at build time.
* check: `cutOk`, `check3P` (= `check2P`, 4 tasks), and every chromosome view spells the genome's
  bytes. -/

namespace Spec.Index

open MapSpec MapSpec.Fast

/-! ## Build -/

def kMz : Nat := 22
def bMz : Nat := 26
def cMz : Nat := 0
def swMz : Nat := 5
def tMz : Nat := 6

-- all chromosomes packed one after the other (as `loadPacked` pushes them)
def packAll (gbs : Array ByteArray) : PGen :=
  (gbs.foldl (fun s g => g.foldl PB.push s) (PB.init (gbs.foldl (· + ·.size) 0))).finish

-- where each chromosome starts (as `loadGenome`)
def offsOf (gbs : Array ByteArray) : Array Nat :=
  (gbs.foldl (fun (o, n) g => (o.push n, n + g.size)) ((#[] : Array Nat), 0)).1

def buildMz (gbs : Array ByteArray) (G : PGen) : Mz.MzIdx :=
  let V := GV.ofChroms gbs
  if catOkV V (offsOf gbs) gbs then Mz.buildWV V kMz bMz cMz swMz tMz
  else Mz.buildWP G kMz bMz cMz swMz tMz

/-! ## Save -/

def magic : UInt64 := 0x3158444941474C4C  -- "LLGAIDX1"

def putU64 (b : ByteArray) (x : UInt64) : ByteArray :=
  (List.range 8).foldl (fun b i => b.push (x >>> (8 * i).toUInt64).toUInt8) b

def putNat (b : ByteArray) (x : Nat) : ByteArray := putU64 b x.toUInt64

def putNats (b : ByteArray) (xs : Array Nat) : ByteArray := xs.foldl putNat (putNat b xs.size)

def putBytes (b : ByteArray) (x : ByteArray) : ByteArray := putNat b x.size ++ x

def putMz (b : ByteArray) (ix : Mz.MzIdx) : ByteArray :=
  let b := [ix.k, ix.B, ix.w, ix.c, ix.kb, ix.kf, ix.T].foldl putNat b
  let b := putU64 b ix.kmU
  let b := putNat b ix.t
  let b := putU64 b ix.tmU
  let b := [ix.kbM, ix.fM, ix.tM].foldl putNat b
  let b := putNats b ix.pm
  let b := [ix.bsh, ix.ash, ix.fsh].foldl putNat b
  let b := putBytes b ix.offs
  let b := putNat b ix.sw
  let b := putBytes b ix.sl
  putNats b ix.runs

def putPGen (b : ByteArray) (G : PGen) : ByteArray :=
  putBytes (putBytes (putNat (putNat b G.n) G.o) G.w) G.ex

/-! ## Load: a parser reading `bs` from a position -/

abbrev Rd := StateT Nat Option

def rdU64 (bs : ByteArray) : Rd UInt64 := fun p =>
  if p + 8 ≤ bs.size then
    some ((List.range 8).foldl (fun x i => x ||| ((bs.get! (p + i)).toUInt64 <<< (8 * i).toUInt64)) 0, p + 8)
  else none

def rdNat (bs : ByteArray) : Rd Nat := return (← rdU64 bs).toNat

def rdNatsGo (bs : ByteArray) : Nat → Array Nat → Rd (Array Nat)
  | 0, acc => pure acc
  | n + 1, acc => do rdNatsGo bs n (acc.push (← rdNat bs))

def rdNats (bs : ByteArray) : Rd (Array Nat) := do
  let n ← rdNat bs
  let p ← get
  if p + 8 * n ≤ bs.size then rdNatsGo bs n (Array.emptyWithCapacity n) else failure

-- copies the bytes (see the note in `Proofs/Aligner.lean`)
def rdBytes (bs : ByteArray) : Rd ByteArray := do
  let n ← rdNat bs
  let p ← get
  if p + n ≤ bs.size then set (p + n); return bs.extract p (p + n) else failure

def rdMz (bs : ByteArray) : Rd Mz.MzIdx := do
  let k ← rdNat bs; let B ← rdNat bs; let w ← rdNat bs; let c ← rdNat bs
  let kb ← rdNat bs; let kf ← rdNat bs; let T ← rdNat bs
  let kmU ← rdU64 bs; let t ← rdNat bs; let tmU ← rdU64 bs
  let kbM ← rdNat bs; let fM ← rdNat bs; let tM ← rdNat bs
  let pm ← rdNats bs
  let bsh ← rdNat bs; let ash ← rdNat bs; let fsh ← rdNat bs
  let offs ← rdBytes bs; let sw ← rdNat bs; let sl ← rdBytes bs; let runs ← rdNats bs
  return { k, B, w, c, kb, kf, T, kmU, t, tmU, kbM, fM, tM, pm, bsh, ash, fsh, offs, sw, sl, runs }

def rdPGen (bs : ByteArray) : Rd PGen := do
  let n ← rdNat bs; let o ← rdNat bs; let w ← rdBytes bs; let ex ← rdBytes bs
  return { n, o, w, ex }

/-! ## Equality, decided (only `roundTrips` runs it; `ByteArray` equality is `memcmp`) -/

deriving instance DecidableEq for PGen
deriving instance DecidableEq for Mz.MzIdx

/-! ## Check -/

-- `P` spells `b` at `[i, i + k)`
def eqRunP (P : PGen) (b : ByteArray) (i : Nat) : (k : Nat) → Bool
  | 0 => true
  | k + 1 => P.get i == b.get! i && eqRunP P b (i + 1) k

def chromOk (P : PGen) (b : ByteArray) : Bool := P.n == b.size && eqRunP P b 0 P.n

-- every chromosome view spells the genome's bytes
def chromsOk (byteGenome : GenomeFile) (G : PGen) (offs ns : Array Nat) : Bool :=
  let gs := cutAll G offs ns
  ns.size == byteGenome.size && (List.range ns.size).all fun c => chromOk gs[c]! byteGenome[c]!.2

theorem eqRunP_sound {P : PGen} {b : ByteArray} :
    ∀ {k i}, eqRunP P b i k = true → ∀ j, i ≤ j → j < i + k → P.get j = b.get! j
  | 0, _, _, j, h1, h2 => absurd h2 (by omega)
  | k + 1, i, h, j, h1, h2 => by
    simp only [eqRunP, Bool.and_eq_true, beq_iff_eq] at h
    rcases Nat.eq_or_lt_of_le h1 with e | e
    · exact e ▸ h.1
    · exact eqRunP_sound h.2 j (by omega) (by omega)

theorem chromOk_encodes {P : PGen} {b : ByteArray} (h : chromOk P b = true) :
    Encodes (Mz.unpack P) (decodeRead b) := by
  simp only [chromOk, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hs, he⟩ := Bridge.encodes_decodeRead b
  have hr := Mz.rep_unpack P
  refine ⟨by rw [← hr.1, h.1, hs], fun i hi => ?_⟩
  rw [← hr.2 i, eqRunP_sound h.2 i (by omega) (by omega), he i hi]

theorem chromsOk_sound {byteGenome : GenomeFile} {G : PGen} {offs ns : Array Nat}
    (h : chromsOk byteGenome G offs ns = true) :
    GenomeBytes ((cutAll G offs ns).map Mz.unpack) (Bridge.oldGenome byteGenome.decode) := by
  simp only [chromsOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hn, hc⟩ := h
  have hlen : (Bridge.oldGenome byteGenome.decode).length = byteGenome.size := by
    simp [Bridge.oldGenome, GenomeFile.decode]
  refine ⟨by simp [cutAll, hlen, hn], fun c h1 h2 => ?_⟩
  have hcn : c < ns.size := by simpa [cutAll] using h1
  have hcg : c < byteGenome.size := by omega
  have e : (Bridge.oldGenome byteGenome.decode)[c].seq = decodeRead byteGenome[c].2 := by
    simp [Bridge.oldGenome, GenomeFile.decode]
  have := hc c hcn
  rw [getElem!_pos _ c (by simpa [cutAll] using hcn), getElem!_pos _ c hcg] at this
  simpa [e] using chromOk_encodes this

end Spec.Index
