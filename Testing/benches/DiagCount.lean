import Proofs.Aligner
import Proofs.Sam

/-! Benchmark only (unproved IO): for the pairs that reach the final second look (`lookAt`, after the router,
the join, the short-mate stage and the gave-up hook), mate 1's candidate diagonals in the second look's hit search
(`hitsSK`: hits of the `sbound c + 1` rarest seeds, deduplicated) and how many keep `m − sbound c` distinct seeds
(of all `m`, looked up) within the band `2·gapBound c` (the pigeonhole count the seed filter needs).
  diag_count INDEX R1.fq R2.fq [PAIRS] -/

open MapSpec MapSpec.Fast

structure St where
  pairs : Nat := 0
  look : Nat := 0
  diagsJ : Nat := 0
  keep : Nat := 0
  hitsJ : Nat := 0
  hitsRest : Nat := 0
  zero : Nat := 0
  keepPair : Nat := 0
  minMate : Nat := 0
  mate2 : Nat := 0
  zeroPair : Nat := 0

def lowerBound (a : Array Nat) (x : Nat) : Nat := Id.run do
  let mut lo := 0
  let mut hi := a.size
  while lo < hi do
    let mid := (lo + hi) / 2
    if a[mid]! < x then lo := mid + 1 else hi := mid
  return lo

-- the second look's candidate diagonals of one strand (hits of the `sbound c + 1` rarest seeds), sorted, distinct
def candD (pk : PkMz) (Rs : ByteArray) (c : Nat) : Array Nat := Id.run do
  let m := Rs.size / 25
  if m == 0 then return #[]
  let Ls := Rs.size / m
  let ps : Array MzP := prepG pk Rs m Ls
  let J := (ordG (ps.map (LookG.size pk)) m).take (sbound c + 1)
  let ds := (J.foldl (fun acc j => acc ++
    (LookG.look pk ByteArray.empty Rs (j * Ls) (Rs.size - j * Ls) ps[j]!).map (· / 16)) #[]).qsort (· < ·)
  let mut uniq : Array Nat := #[]
  for d in ds do
    if uniq.isEmpty || uniq.back! != d then uniq := uniq.push d
  return uniq

-- candidates of `a` with an element of sorted `b` within `w`
def nearCount (a b : Array Nat) (w : Nat) : Nat :=
  a.foldl (fun t d => let i := lowerBound b (d - w); if i < b.size && b[i]! ≤ d + w then t + 1 else t) 0

-- one strand: (candidate diagonals, kept, hits of J, hits of the other seeds)
def strandStats (pk : PkMz) (Rs : ByteArray) (c : Nat) : Nat × Nat × Nat × Nat := Id.run do
  let m := Rs.size / 25
  if m == 0 then return (0, 0, 0, 0)
  let Ls := Rs.size / m
  let ps : Array MzP := prepG pk Rs m Ls
  let J := (ordG (ps.map (LookG.size pk)) m).take (sbound c + 1)
  let arrs : Array (Array Nat) := (Array.range m).map fun j =>
    ((LookG.look pk ByteArray.empty Rs (j * Ls) (Rs.size - j * Ls) ps[j]!).map (· / 16)).qsort (· < ·)
  let r := 2 * gapBound sc0 (-(c : Int))
  let need := m - sbound c
  let ds := (J.foldl (fun acc j => acc ++ arrs[j]!) #[]).qsort (· < ·)
  let mut uniq : Array Nat := #[]
  for d in ds do
    if uniq.isEmpty || uniq.back! != d then uniq := uniq.push d
  let mut keep := 0
  for d in uniq do
    let mut s := 0
    for j in [0:m] do
      let a := arrs[j]!
      let i := lowerBound a (d - r)
      if i < a.size && a[i]! ≤ d + r then s := s + 1
    if need ≤ s then keep := keep + 1
  let hJ := J.foldl (fun t j => t + arrs[j]!.size) 0
  let hAll := arrs.foldl (fun t a => t + a.size) 0
  return (uniq.size, keep, hJ, hAll - hJ)

def main (args : List String) : IO Unit := do
  let indexPath :: r1 :: r2 :: rest := args | throw (IO.userError "usage: diag_count INDEX R1 R2 [PAIRS]")
  let lim := (rest.head?.bind String.toNat?).getD 1000000000
  let iS : Spec.InsertSettings := { range := (100, 1000) }
  let index ← IO.FS.readBinFile indexPath
  let some setup := Spec.chunkSetup iS (Spec.readIndex index).2 | throw (IO.userError "no router index")
  let (iS, cfg, pk, pgs, offs, ns) := setup
  let reads1 ← Spec.FastqReader.ofHandle (← IO.FS.Handle.mk r1 .read)
  let reads2 ← Spec.FastqReader.ofHandle (← IO.FS.Handle.mk r2 .read)
  let mut st : St := {}
  let mut n := 0
  repeat
    if lim ≤ n then break
    let some a ← Spec.readFastqRecord reads1 | break
    let some b ← Spec.readFastqRecord reads2 | break
    n := n + 1
    let a := Spec.trimRecord a
    let b := Spec.trimRecord b
    if a.letters.isEmpty || b.letters.isEmpty then continue
    let R1 := a.letters
    let R2 := b.letters
    st := { st with pairs := st.pairs + 1 }
    let req := Spec.reqOf iS R1 R2
    let t := tierPair (Spec.pairCfg cfg pk R1 R2) pk #[0] pgs (some R1) (some R2)
    let a1 := Spec.answerWith iS req (Spec.fallbackFrom req) pk pgs offs ns R1 R2 t
    if !(decide (Spec.LastResort.Leftover req a1)) then continue
    let c := Spec.lookCap req
    match (Spec.joinAt cfg pk pgs c R1 R2).map (Spec.answerWith iS req none pk pgs offs ns R1 R2) with
    | some aj => if !(decide (Spec.LastResort.Leftover req aj)) then continue
    | none => pure ()
    if Spec.shortOk pk c R1 R2 then continue
    if (Spec.gaveUp req pk offs ns R1 R2 a1).isSome then continue
    let (d1, k1, h1, x1) := strandStats pk R1 c
    let (d2, k2, h2, x2) := strandStats pk (revCompK R1) c
    let c1 := candD pk R1 c ++ candD pk (revCompK R1) c
    let c2 := (candD pk R2 c ++ candD pk (revCompK R2) c).qsort (· < ·)
    let kp := nearCount c1 c2 (iS.range.2 + R1.size + R2.size)
    st := { st with minMate := st.minMate + min c1.size c2.size, mate2 := st.mate2 + c2.size }
    st := { st with keepPair := st.keepPair + kp, zeroPair := st.zeroPair + (if kp == 0 then 1 else 0) }
    st := { st with look := st.look + 1, diagsJ := st.diagsJ + d1 + d2, keep := st.keep + k1 + k2,
                    hitsJ := st.hitsJ + h1 + h2, hitsRest := st.hitsRest + x1 + x2,
                    zero := st.zero + (if k1 + k2 == 0 then 1 else 0) }
  IO.println s!"pairs {st.pairs}  reach lookAt {st.look}  mate-1 candidate diagonals {st.diagsJ}  keep (count filter) {st.keep}  zero-candidate pairs {st.zero}  hits of J {st.hitsJ}  extra hits (other seeds) {st.hitsRest}  keep (mate-2 seed hit within the fragment) {st.keepPair}  zero-candidate pairs (pair filter) {st.zeroPair}  mate-2 candidates {st.mate2}  min(mate1, mate2) candidates {st.minMate}"
