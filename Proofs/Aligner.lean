import Proofs.Index
import Proofs.Whole
import Proofs.LastResort
import Proofs.GaveUp
import Proofs.Heavy
import Proofs.HeavyBuild
import TierHeur
import ParMap

/-! # 3. The aligner, proved. `Spec/Aligner.lean`'s types are in `Proofs/Answer.lean` (unchanged);
this file fills in the two holes, `buildIndex` and `alignPairs`, and proves `alignPairs_correct`
from the bridge lemmas (`Proofs/Bridge.lean`) and the router's `tierPair_sound`.

The index is checked once, when it is built: `buildIndex` writes the index only if what it loads
to passes the router's checks (`indexOk`); otherwise it writes an empty index, and `alignPairs`
then answers every pair with the bound 0 (always true). So `alignPairs` never re-checks the index,
and the proof gets the checks from `hIndex`. -/

namespace Spec

open Bridge

/-! ## The index: the minimizer index, the packed genome, and where each chromosome starts -/

-- (the last two: the heavy 25-mer table and its mask, `Proofs/Heavy.lean`)
abbrev LoadedIndex := MapSpec.Mz.MzIdx × MapSpec.Fast.PGen × Array Nat × Array Nat × ByteArray × ByteArray

-- the heavy 25-mer table (unproved builder `HeavyBuild.table`), size-capped so that it can be saved
def heavyTable (gbs : Array ByteArray) : ByteArray :=
  let H0 := HeavyBuild.table gbs
  if H0.size < 2 ^ 63 then H0 else ByteArray.empty

theorem heavyTable_size (gbs : Array ByteArray) : (heavyTable gbs).size < 2 ^ 63 := by
  unfold heavyTable; dsimp only; split
  · assumption
  · simp

-- the fast builders the harness uses (bench/WholeGenome.lean `build` and `pmap` modes; `Proofs/Index.lean`)
def buildLoaded (byteGenome : GenomeFile) : LoadedIndex :=
  let gbs := byteGenome.map (·.2)
  let G := Index.packAll gbs
  let ix := Index.buildMz gbs G
  let offs := Index.offsOf gbs
  let ns := gbs.map (·.size)
  -- the heavy table and the entries that pass `Heavy.entryOk` on the built index
  let H := heavyTable gbs
  (ix, G, offs, ns, H, Heavy.heavyMask (ix, G) offs ns H)

-- one ByteArray: `G.w`, `ix.sl`, the bucket offsets, the small fields, where they start, magic
-- (`Proofs/Index.lean`). Slot `t` of the loaded index is slot `t - m` of `ix.sl`.
def saveIndex (loaded : LoadedIndex) : ByteArray :=
  let (ix, G, offs, ns, H, M) := loaded
  let b := ByteArray.emptyWithCapacity (G.w.size + ix.sl.size + ix.offs.size + ix.sw + 4 + G.ex.size +
    H.size + M.size + 8 * (42 + ix.pm.size + ix.runs.size + offs.size + ns.size))
  let b := Index.pad (b ++ G.w) ix.sw
  let m := b.size / ix.sw
  let b := Index.pad (b ++ ix.sl) 4
  let ob := b.size / 4
  let b := Index.putOffs b ix.offs m
  let hp := b.size
  let b := Index.putNats (Index.putNats (Index.putPGen (Index.putMz b ix ob) G) offs) ns
  let b := Index.putBytes (Index.putBytes b H) M
  Index.putU64 (Index.putNat b hp) Index.magic

-- copies nothing big: `ix.offs`, `ix.sl`, `G.w` are `index` itself; rebuilds `G.ex`, `ix.pm`,
-- `ix.runs`, `offs`, `ns` (small) on every call, i.e. once per `alignPairs` chunk
def loadIndex (index : ByteArray) : Option LoadedIndex :=
  if index.size < 16 then none else
  (do
    let hp ← Index.rdNat index
    if (← Index.rdU64 index) != Index.magic then failure
    set hp
    let ix ← Index.rdMz index
    let G ← Index.rdPGen index
    let offs ← Index.rdNats index
    let ns ← Index.rdNats index
    let H ← Index.rdBytes index
    let M ← Index.rdBytes index
    if (← get) != index.size - 16 then failure
    return (ix, G, offs, ns, H, M) : Index.Rd LoadedIndex).run' (index.size - 16)

-- the router's hypotheses, as one check run at build time
def indexOk (byteGenome : GenomeFile) (loaded : LoadedIndex) : Bool :=
  let (ix, G, offs, ns, H, M) := loaded
  MapSpec.Fast.cutOk G offs ns && MapSpec.Mz.check3P ix G 4 && Index.chromsOk byteGenome G offs ns &&
    Heavy.heavyOk (ix, G) offs ns H M

theorem loadIndex_empty : loadIndex ByteArray.empty = none := by
  simp [loadIndex]

theorem indexOk_sound {byteGenome : GenomeFile} {ix : MapSpec.Mz.MzIdx} {G : MapSpec.Fast.PGen}
    {offs ns : Array Nat} {H M : ByteArray} (h : indexOk byteGenome (ix, G, offs, ns, H, M) = true) :
    MapSpec.Fast.cutOk G offs ns = true ∧
    MapSpec.GenomeBytes ((MapSpec.Fast.cutAll G offs ns).map MapSpec.Mz.unpack) (oldGenome byteGenome.decode) ∧
    MapSpec.Mz.check2P ix G = true ∧ Heavy.heavyOk (ix, G) offs ns H M = true := by
  simp only [indexOk, Bool.and_eq_true, MapSpec.Mz.check3P_eq] at h
  exact ⟨h.1.1.1, Index.chromsOk_sound h.1.2, h.1.1.2, h.2⟩

-- the index holds everything the aligner needs, the genome included; the check runs on what
-- `saved` loads to (nothing about saving or loading is proved)
-- the genome as written when the build's check fails (only for genomes that do not fit the index format,
-- `IndexFinal.buildIndex_eq_saveIndex`): each chromosome's length, then its bytes, as numbers in the lengths
-- record (`LastResort.lensRecord`)
def genomeChroms (byteGenome : GenomeFile) : List (List Nat) := byteGenome.toList.map fun p => p.2.toList.map (·.toNat)

def chromsNats (chroms : List (List Nat)) : List Nat := chroms.flatMap fun l => l.length :: l

-- the chromosomes back from the numbers (`ungen_chromsNats`)
def ungen : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | _, [] => []
  | f + 1, n :: rest => rest.take n :: ungen f (rest.drop n)

theorem ungen_chromsNats : ∀ (chroms : List (List Nat)) (f : Nat), (chromsNats chroms).length ≤ f →
    ungen f (chromsNats chroms) = chroms
  | [], f, _ => by cases f <;> rfl
  | l :: rest, f, h => by
    simp only [chromsNats, List.flatMap_cons, List.cons_append, List.length_cons, List.length_append] at h ⊢
    cases f with
    | zero => omega
    | succ f =>
      simp only [ungen, List.take_left', List.drop_left']
      exact congrArg (l :: ·) (ungen_chromsNats rest f (by simp only [chromsNats]; omega))

def buildIndex (byteGenome : GenomeFile) : ByteArray :=
  let saved := saveIndex (buildLoaded byteGenome)
  let record := fun (_ : Unit) => LastResort.lensRecord (chromsNats (genomeChroms byteGenome))
  match LastResort.readLens saved with
  | some _ => record ()
  | none =>
    match loadIndex saved with
    | some loaded => if indexOk byteGenome loaded then saved else record ()
    | none => record ()

-- what an index holds: the genome's chromosomes (a failed build), or the router's structures
def readIndex (index : ByteArray) : Option (List (List Nat)) × Option LoadedIndex :=
  match LastResort.readLens index with
  | some ls => (some (ungen ls.length ls), none)
  | none => (none, loadIndex index)

/-! ## The aligner -/

-- Deeper caps (Testing/notes/DEEP_CAPS.md), OFF by default: pairs that pass 1 leaves without a hit
-- or partner get pass 2 at cap 20 (150–249 letters) / 28 (≥ 250 letters), only when both mates'
-- lookup cost at that cap is ≤ 3000 (bench: WG_PASS2=1 WG_T2=250:28,150:20 WG_P2BUDGET=3000).
-- Any setting is sound (`tierPair_sound` holds for every `TierCfg`).
def deepCaps : Bool := false

-- ties (T1gm / T1um): print one pair in hand, uniqueness unknown (false: unmapped, as M1)
def reportTies : Bool := true

-- (stage 5) no proper pair from the router and the bound not below the mates' `requiredMapBound`: a fallback
-- pair (anchor + mate aligned near it, re-checked); false: straight to the last resort (`LastResort.finalize`)
def fallbackOn : Bool := true

-- mate rescue: the fallback also runs on junk answers where a mate has a placement in hand
def mateRescue : Bool := true

def fallbackFrom (req : Int) : Option Int :=
  if fallbackOn then some req else none

-- the router's lookup budget per mate: a pair over it is given up at once (T3, bound 0) and, with the
-- fallback, printed as a pair in hand (uniqueness unknown); lower = less time on repeats and ties
def gateBudget : Nat := 60000

-- pass-2 cap by mate length (a mate keeps its pass-1 cap where this is not deeper: `cap2Of`)
def deepCap2 (n : Nat) : Nat := if 250 ≤ n then 28 else if 150 ≤ n then 20 else 0

-- pass-1 cap by mate length
def capOfLen (n : Nat) : Nat := if 150 ≤ n then 16 else if 100 ≤ n then 12 else if 75 ≤ n then 11 else 12

-- the router's settings for these insert settings (any settings are sound; these are for speed)
def tierCfg (insertSettings : InsertSettings) (pk : MapSpec.Fast.PkMz) (offs : Array Nat)
    (pgs : Array MapSpec.Fast.PGen) : MapSpec.Fast.TierCfg :=
  TierHeur.rtxCfg { cap1 := fun R => capOfLen R.size
                    pass2 := deepCaps
                    cap2 := deepCap2
                    gate2 := fun a b =>
                      MapSpec.Fast.costP pk (deepCap2 a.size) (MapSpec.Fast.prepMate pk a : MapSpec.Fast.PrepM MapSpec.Fast.MzP) ≤ 3000 &&
                      MapSpec.Fast.costP pk (deepCap2 b.size) (MapSpec.Fast.prepMate pk b : MapSpec.Fast.PrepM MapSpec.Fast.MzP) ≤ 3000 }
    pk offs pgs insertSettings.range.1 insertSettings.range.2 insertSettings.dovetailSlack false gateBudget

-- (n32) per-pair caps for short reads (< 200 letters): a mate whose rarest `sbound c + 1` seed buckets per
-- strand (`costP`) hold more than `capBudget` places is searched at a lower cap, 15 (one seed fewer), else 11
-- (two fewer); the gate then skips RT when even cap 11 is over `capBudget`. A lower cap only weakens what
-- RT claims (any `TierCfg` is sound): a unique best within 15 is still the unique best. Reads ≥ 200 letters
-- keep `cap1` and the gate as before.
def capBudget : Nat := 5000

-- the gate's budget by mate length
def budOf (n : Nat) : Nat := if n < 200 then capBudget else gateBudget

def capFor (pk : MapSpec.Fast.PkMz) (c0 : Nat) (R : ByteArray) : Nat :=
  if 200 ≤ R.size then c0 else
  let s : MapSpec.Fast.PrepM MapSpec.Fast.MzP := MapSpec.Fast.prepMate pk R
  if MapSpec.Fast.costP pk c0 s ≤ capBudget then c0
  else if MapSpec.Fast.costP pk (min c0 15) s ≤ capBudget then min c0 15
  else min c0 11

-- the router's settings for one pair: each mate's cap lowered by `capFor` (computed once per mate), the gate by
-- `budOf`
def pairCfg (cfg : MapSpec.Fast.TierCfg) (pk : MapSpec.Fast.PkMz) (a b : ByteArray) : MapSpec.Fast.TierCfg :=
  let ca := capFor pk (cfg.rcfg.cap1 a) a
  let cb := capFor pk (cfg.rcfg.cap1 b) b
  { cfg with
    rcfg := { cfg.rcfg with cap1 := fun R => if R == a then ca else if R == b then cb else capFor pk (cfg.rcfg.cap1 R) R }
    gate := (fun a b _ _ c1 c2 => budOf a.size < c1 || budOf b.size < c2) }

-- the mates' `requiredMapBound` (Spec's `.unknown` arm), on their letters. THE ONE PLACE that reads it.
def reqOf (insertSettings : InsertSettings) (read1 read2 : ByteArray) : Int :=
  requiredMapBound (decodeRead read1) (decodeRead read2)

-- compiled `reqOf`: the bound depends on the mates' lengths only (`decodeRead_length`)
def reqOfF (_ : InsertSettings) (read1 read2 : ByteArray) : Int :=
  -4 * ((min 4 ((min read1.size read2.size) / 25 - 1) : Nat) : Int)

@[csimp] theorem reqOf_eqF : @reqOf = @reqOfF := by
  funext insertSettings read1 read2
  unfold reqOf reqOfF requiredMapBound
  simp only [GaveUp.decodeRead_length]

-- the cap of the second look: `-requiredMapBound`, at most 16 (`LastResort.pairsAt_mem`); for Spec's default
-- `requiredMapBound` it is `LastResort.capOfLens` (`4 * errorsChecked` of the shorter mate)
def lookCap (req : Int) : Nat := min 16 (-req).toNat

-- the genome from its chromosomes' letters (names are not kept: `LastResort.correct_transfer`)
def chromGenome (chroms : List (List Nat)) : Genome := chroms.map fun l => ⟨"", l.map Char.ofNat⟩

-- without an index (a genome that does not fit the index format): every proper pair within the cap, searched
-- window by window over the whole genome (`LastResort.pairsSpec`; total, slow)
def lookSpec (insertSettings : InsertSettings) (chroms : List (List Nat)) (read1 read2 : ByteArray) : PairAnswer :=
  let g := oldGenome (chromGenome chroms)
  let req := reqOf insertSettings read1 read2
  let c := lookCap req
  LastResort.finalize insertSettings (LastResort.fitNs (chroms.map (·.length)).toArray) req
    (LastResort.lookAnswer c (LastResort.runsSp g (decodeRead read1)) (LastResort.runsSp g (decodeRead read2))
      (LastResort.pairsSpec insertSettings.dovetailSlack insertSettings.range.1 insertSettings.range.2 c g
        (decodeRead read1) (decodeRead read2)))

-- (stage 2) the walk: up to `walkK` anchors per strand, keeping the first pair at `junkScore` or better
def walkK : Nat := 3

def keepOf (insertSettings : InsertSettings) (p : PairReport) : Bool :=
  decide (insertSettings.junkScore ≤ LastResort.repScore p)

-- a walk step aligns the other mate only when the anchored mate alone is at `junkScore` or better: a pair's score is
-- the sum of its mates' scores, each at most 0, so a worse anchored mate gives no pair that `keepOf` keeps
def preOf (insertSettings : InsertSettings) (r : MateReport) : Bool :=
  decide (insertSettings.junkScore ≤ r.score)

-- the other mate's DP limit at a walk step: a partner with penalty `≥ r.score - junkScore + 1` puts the pair below
-- `junkScore` (`keepOf` drops it). At least 9: `TierHeur.nearY` runs its banded DP only for a limit above 8
def limOf (insertSettings : InsertSettings) (r : MateReport) : Nat :=
  max 9 (r.score - insertSettings.junkScore + 1).toNat

-- the answer from a router output `t`: the found pair re-checked (`Report`), the walk when `fb` allows it, then
-- the report floor (`LastResort.finalize`)
def answerWith (insertSettings : InsertSettings) (req : Int) (fb : Option Int) (pk : MapSpec.Fast.PkMz)
    (pgs : Array MapSpec.Fast.PGen) (offs ns : Array Nat) (read1 read2 : ByteArray) (t : MapSpec.Fast.TierOut) :
    PairAnswer :=
  LastResort.finalize insertSettings (LastResort.fitNs ns) req
    (Report.answerOfPair reportTies fb mateRescue (preOf insertSettings) (limOf insertSettings) (keepOf insertSettings) walkK pk insertSettings pgs offs ns
      read1 read2 t)

-- the second look at a leftover: every proper pair within the cap, on the chromosomes (`LastResort.lookAnswer`).
-- A mate without the seeds for the cap (`fastT`; under 25 letters for Spec's default) is searched window by
-- window (`hitsKPF`'s fallback; total, slow)
def lookAt (insertSettings : InsertSettings) (req : Int) (pk : MapSpec.Fast.PkMz) (offs ns : Array Nat)
    (read1 read2 : ByteArray) : PairAnswer :=
  let c := lookCap req
  let pgs := MapSpec.Fast.cutAll pk.2 offs ns
  LastResort.finalize insertSettings (LastResort.fitNs ns) req
    (LastResort.lookAnswer c (LastResort.runsIx pgs read1) (LastResort.runsIx pgs read2)
      (LastResort.pairsAtS insertSettings.dovetailSlack insertSettings.range.1 insertSettings.range.2 c pk offs pgs
        read1 read2))

-- the sum of the `k` rarest seed buckets of a mate, over both strands (what a lookup of those seeds costs)
def rareCost (pk : MapSpec.Fast.PkMz) (R : ByteArray) (k : Nat) : Nat :=
  let s : MapSpec.Fast.PrepM MapSpec.Fast.MzP := MapSpec.Fast.prepMate pk R
  TierHeur.smallK pk s.ps (R.size / 25) k + TierHeur.smallK pk s.pr (R.size / 25) k

-- (stage 3) the rarest-seed join (`tierNo`, join only) at cap `c`, skipped when its seeds hold more than
-- `joinBudget` places
def joinBudget : Nat := 20000

def joinAt (cfg : MapSpec.Fast.TierCfg) (pk : MapSpec.Fast.PkMz) (pgs : Array MapSpec.Fast.PGen) (c : Nat)
    (read1 read2 : ByteArray) : Option MapSpec.Fast.TierOut :=
  if rareCost pk read1 (MapSpec.Fast.sbound c + 1) + rareCost pk read2 (MapSpec.Fast.sbound c + 1) ≤ joinBudget then
    MapSpec.Fast.tierNo cfg pk #[0] pgs c false false read1 read2
  else none

-- (stage 4) the second look early, for short mates (< 125 letters) whose rarest `c / 4 + 1` buckets per strand
-- hold at most `shortBudget` places
def shortBudget : Nat := 1000

def shortOk (pk : MapSpec.Fast.PkMz) (c : Nat) (read1 read2 : ByteArray) : Bool :=
  decide (min read1.size read2.size < 125) &&
    decide (rareCost pk read1 (c / 4 + 1) + rareCost pk read2 (c / 4 + 1) ≤ shortBudget)

-- (stage 5) the gave-up answer: the router's answer `a`, still a leftover, with `.repetitiveUnknown` when a mate
-- has `gaveUpSeeds` grid seeds in the heavy 25-mer table (`Heavy.heavyMate`: binary searches, no lookups)
def gaveUpOn : Bool := true

def gaveUp (req : Int) (hv : ByteArray × ByteArray) (read1 read2 : ByteArray) (a : PairAnswer) :
    Option PairAnswer :=
  if LastResort.Leftover req a ∧ (gaveUpOn && (Heavy.heavyMate hv.1 hv.2 read1 || Heavy.heavyMate hv.1 hv.2 read2))
  then some { a with uniqueness := .repetitiveUnknown } else none

-- the stage's answer if it is not a leftover, else the next stage
def orElse (req : Int) (o : Option PairAnswer) (next : Unit → PairAnswer) : PairAnswer :=
  match o with
  | some a => if LastResort.Leftover req a then next () else a
  | none => next ()

theorem orElse_ok {P : PairAnswer → Prop} (req : Int) (o : Option PairAnswer) (next : Unit → PairAnswer)
    (ho : ∀ a, o = some a → P a ∨ LastResort.Leftover req a) (hn : P (next ())) : P (orElse req o next) := by
  unfold orElse
  cases o with
  | none => exact hn
  | some a =>
    simp only
    split
    · exact hn
    · rename_i hl; exact (ho a rfl).resolve_right hl

-- stages (3)-(6) of the pipeline, after the router and the walk
def afterRouter (insertSettings : InsertSettings) (cfg : MapSpec.Fast.TierCfg) (pk : MapSpec.Fast.PkMz)
    (pgs : Array MapSpec.Fast.PGen) (offs ns : Array Nat) (hv : ByteArray × ByteArray) (req : Int) (read1 read2 : ByteArray)
    (a1 : PairAnswer) (_ : Unit) :
    PairAnswer :=
  let c := lookCap req
  orElse req ((joinAt cfg pk pgs c read1 read2).map (answerWith insertSettings req none pk pgs offs ns read1 read2))
    fun _ =>
  orElse req (if shortOk pk c read1 read2 then some (lookAt insertSettings req pk offs ns read1 read2) else none)
    fun _ =>
  -- the gave-up answer is taken as it is (it has no pair and no bound below `requiredMapBound`: a leftover)
  (gaveUp req hv read1 read2 a1).getD (lookAt insertSettings req pk offs ns read1 read2)

-- the pipeline: (1) the router with the per-pair settings, its pair re-checked; (2) the walk; (3) the
-- rarest-seed join; (4) short mates: the second look; (5) the gave-up hook; (6) the second look (`lookAt`).
-- Each stage's answer is taken unless it is a leftover (`LastResort.Leftover`)
-- (option, OFF) witness-first: a pair with a mate that `Heavy.heavyMate` flags answers `.repetitiveUnknown` at once,
-- before the router (it then also gives up on pairs the router would place: Testing/notes/INDEX_COUNTS.md)
def witnessFirst : Bool := false

-- no pair, the bound 0 (every alignment scores at most 0), a mate highly repetitive
def witnessAnswer : PairAnswer :=
  { found := none, bestPossibleScore := 0, uniqueness := .repetitiveUnknown, tier := .boundsOnly }

def witnessHit (hv : ByteArray × ByteArray) (read1 read2 : ByteArray) : Bool :=
  witnessFirst && (Heavy.heavyMate hv.1 hv.2 read1 || Heavy.heavyMate hv.1 hv.2 read2)

def answerOfReads (insertSettings : InsertSettings) (cfg : MapSpec.Fast.TierCfg) (pk : MapSpec.Fast.PkMz)
    (pgs : Array MapSpec.Fast.PGen) (offs ns : Array Nat) (hv : ByteArray × ByteArray) (read1 read2 : ByteArray) :
    PairAnswer :=
  if witnessHit hv read1 read2 then witnessAnswer else
  let req := reqOf insertSettings read1 read2
  let t := MapSpec.Fast.tierPair (pairCfg cfg pk read1 read2) pk #[0] pgs (some read1) (some read2)
  let a1 := answerWith insertSettings req (fallbackFrom req) pk pgs offs ns read1 read2 t
  orElse req (some a1) (afterRouter insertSettings cfg pk pgs offs ns hv req read1 read2 a1)

def alignOne (insertSettings : InsertSettings) (chroms : List (List Nat)) (loaded : Option LoadedIndex)
    (bytes1 bytes2 : Option ByteArray) : PairResult :=
  match bytes1, bytes2 with
  | none, _ => .trimmedAway .one
  | some _, none => .trimmedAway .two
  | some read1, some read2 =>
      match loaded with
      | none => .aligned (lookSpec insertSettings chroms read1 read2)
      | some (ix, G, offs, ns, H, M) =>
          -- the router searches the packed genome as ONE sequence (offsets `#[0]`, lengths `#[G.n]`):
          -- its seed loop then does not pay per chromosome; `Proofs/Whole.lean` moves the answer
          -- back to the chromosomes, `Proofs/Report.lean` the found pair, `Proofs/LastResort.lean` the rest
          .aligned (answerOfReads insertSettings (tierCfg insertSettings (ix, G) #[0] (MapSpec.Fast.cutAll G #[0] #[G.n]))
            (ix, G) (MapSpec.Fast.cutAll G #[0] #[G.n]) offs ns (H, M) read1 read2)

-- tasks per chunk (any value gives the same results: `ParMap.parMap_eq_map`). Use at least the
-- machine's core count: each task runs on its own thread, so 16 tasks use at most 16 cores. On 4 cores,
-- 4..64 tasks cost within ~7% CPU of each other (Testing/notes/THREADS_2026-11-02.md)
def parTasks : Nat := 16

-- a chunk of pairs; the implementation may work across the chunk however it likes
def alignPairs (insertSettings : InsertSettings) (index : ByteArray)
    (pairs : List (Option ByteArray × Option ByteArray)) : List PairResult :=
  let (chroms, loaded) := readIndex index
  -- `parTasks` batches, one task each (ParMap.parMap_eq_map: the same as a plain map)
  (ParMap.parMap parTasks (fun (bytes1, bytes2) => alignOne insertSettings (chroms.getD []) loaded bytes1 bytes2)
    pairs.toArray).toList

-- the router's settings and genome view, computed once per chunk (`alignPairs_eqC`)
abbrev Setup := InsertSettings × MapSpec.Fast.TierCfg × MapSpec.Fast.PkMz × Array MapSpec.Fast.PGen × Array Nat × Array Nat ×
  (ByteArray × ByteArray)

def loadedSetup (insertSettings : InsertSettings) (loaded : Option LoadedIndex) : Option Setup :=
  loaded.map fun (ix, G, offs, ns, H, M) =>
    let pgs := MapSpec.Fast.cutAll G #[0] #[G.n]
    (insertSettings, tierCfg insertSettings (ix, G) #[0] pgs, (ix, G), pgs, offs, ns, (H, M))

-- `alignOne` from `loadedSetup`
def alignOneC (insertSettings : InsertSettings) (chroms : List (List Nat)) (setup : Option Setup)
    (bytes1 bytes2 : Option ByteArray) : PairResult :=
  match bytes1, bytes2 with
  | none, _ => .trimmedAway .one
  | some _, none => .trimmedAway .two
  | some read1, some read2 =>
      match setup with
      | none => .aligned (lookSpec insertSettings chroms read1 read2)
      | some (insertSettings, cfg, pk, pgs, offs, ns, hv) =>
          .aligned (answerOfReads insertSettings cfg pk pgs offs ns hv read1 read2)

-- `capFor` from the mate's bucket sizes (`capForZ_eq`: the sizes of `prepMate`'s seeds)
def capForZ (c0 : Nat) (R : ByteArray) (z1 z2 : Array Nat) : Nat :=
  if 200 ≤ R.size then c0
  else if MapSpec.Fast.costZ c0 z1 z2 ≤ capBudget then c0
  else if MapSpec.Fast.costZ (min c0 15) z1 z2 ≤ capBudget then min c0 15
  else min c0 11

theorem capForZ_eq (pk : MapSpec.Fast.PkMz) (c0 : Nat) (R : ByteArray) :
    capForZ c0 R ((MapSpec.Fast.prepMz pk R).ps.map (MapSpec.Fast.LookG.size pk))
      ((MapSpec.Fast.prepMz pk R).pr.map (MapSpec.Fast.LookG.size pk)) = capFor pk c0 R := by
  unfold capForZ capFor
  simp only [MapSpec.Fast.prepMz_eq, MapSpec.Fast.costZ_eq]

-- `capForZ` from the strands' sizes already sorted (`capForS_eq`)
def capForS (c0 : Nat) (R : ByteArray) (l1 l2 : List Nat) : Nat :=
  if 200 ≤ R.size then c0
  else if MapSpec.Fast.costZS c0 l1 l2 ≤ capBudget then c0
  else if MapSpec.Fast.costZS (min c0 15) l1 l2 ≤ capBudget then min c0 15
  else min c0 11

theorem capForS_eq (c0 : Nat) (R : ByteArray) (z1 z2 : Array Nat) :
    capForS c0 R (z1.foldr MapSpec.Fast.insN []) (z2.foldr MapSpec.Fast.insN []) = capForZ c0 R z1 z2 := rfl

-- `pairCfg` with the two mates' caps given (`pairCfg cfg pk a b = pairCfgZ cfg pk a b (capFor …) (capFor …)`)
def pairCfgZ (cfg : MapSpec.Fast.TierCfg) (pk : MapSpec.Fast.PkMz) (a b : ByteArray) (ca cb : Nat) : MapSpec.Fast.TierCfg :=
  { cfg with
    rcfg := { cfg.rcfg with cap1 := fun R => if R == a then ca else if R == b then cb else capFor pk (cfg.rcfg.cap1 R) R }
    gate := (fun a b _ _ c1 c2 => budOf a.size < c1 || budOf b.size < c2) }

-- `alignOneC` with each mate prepared once (`prepMz`): its bucket sizes give `capFor` and the router's costs, and
-- the router (`tierPairBP`) and the reporter (`answerOfPairP`: reverse complements, packed strands) get the
-- preparations (`alignOneP_eq`)
-- the setup with `Report.monoOk` of its chromosome offsets, computed once per chunk (the reporter's chromosome
-- lookup stops early when it holds: `Report.chromOfM_eq`)
abbrev SetupP := Setup × Bool

def withMono (st : Setup) : SetupP := (st, Report.monoOk st.2.2.2.2.1 st.2.2.2.2.2.1)

def alignOneP (insertSettings : InsertSettings) (chroms : List (List Nat)) (setup : Option SetupP)
    (bytes1 bytes2 : Option ByteArray) : PairResult :=
  match bytes1, bytes2 with
  | none, _ => .trimmedAway .one
  | some _, none => .trimmedAway .two
  | some read1, some read2 =>
      match setup with
      | none => .aligned (lookSpec insertSettings chroms read1 read2)
      | some ((insertSettings, cfg, pk, pgs, offs, ns, hv), ok) =>
          .aligned <| if witnessHit hv read1 read2 then witnessAnswer else
          let req := reqOf insertSettings read1 read2
          let s1 := MapSpec.Fast.prepMz pk read1
          let s2 := MapSpec.Fast.prepMz pk read2
          let za1 := s1.ps.map (MapSpec.Fast.LookG.size pk)
          let za2 := s1.pr.map (MapSpec.Fast.LookG.size pk)
          let zb1 := s2.ps.map (MapSpec.Fast.LookG.size pk)
          let zb2 := s2.pr.map (MapSpec.Fast.LookG.size pk)
          -- each strand's sizes sorted once: the caps tried by `capFor` and the router's pass-1 costs
          let sa1 := za1.foldr MapSpec.Fast.insN []
          let sa2 := za2.foldr MapSpec.Fast.insN []
          let sb1 := zb1.foldr MapSpec.Fast.insN []
          let sb2 := zb2.foldr MapSpec.Fast.insN []
          let ca := capForS (cfg.rcfg.cap1 read1) read1 sa1 sa2
          let cb := capForS (cfg.rcfg.cap1 read2) read2 sb1 sb2
          let cfg' := pairCfgZ cfg pk read1 read2 ca cb
          let ans := LastResort.finalize insertSettings (LastResort.fitNs ns) req
            (Report.answerOfPairP reportTies (fallbackFrom req) mateRescue (preOf insertSettings) (limOf insertSettings) (keepOf insertSettings) walkK pk insertSettings
              pgs offs ns ok read1 read2
              s1 s2 (MapSpec.Fast.tierUp cfg' pk #[0] pgs read1 read2
                (MapSpec.Fast.tierPairBP.tierPairBQ cfg' pk #[0] pgs read1 read2 s1 s2 za1 za2 zb1 zb2
                  (MapSpec.Fast.costZS ca sa1 sa2) (MapSpec.Fast.costZS cb sb1 sb2))))
          -- a leftover goes on to the later stages (`answerOfReads`)
          orElse req (some ans) (afterRouter insertSettings cfg pk pgs offs ns hv req read1 read2 ans)

-- the router's caps under `pairCfgZ` are the given ones (equal reads have equal caps)
theorem pairCfgZ_cap (cfg : MapSpec.Fast.TierCfg) (pk : MapSpec.Fast.PkMz) (a b : ByteArray) (f : ByteArray → Nat) :
    (pairCfgZ cfg pk a b (f a) (f b)).rcfg.cap1 a = f a ∧ (pairCfgZ cfg pk a b (f a) (f b)).rcfg.cap1 b = f b := by
  have hs : ∀ x : ByteArray, (x == x) = true := fun x => by
    show (x.data == x.data) = true; exact beq_self_eq_true _
  refine ⟨by simp [pairCfgZ, hs], ?_⟩
  simp only [pairCfgZ]
  by_cases h : (b == a) = true
  · have : b = a := ByteArray.ext (eq_of_beq (show (b.data == a.data) = true from h))
    subst this; simp [hs]
  · simp [h, hs]

theorem alignOneP_eq (insertSettings : InsertSettings) (chroms : List (List Nat)) (setup : Option Setup)
    (bytes1 bytes2 : Option ByteArray) :
    alignOneP insertSettings chroms (setup.map withMono) bytes1 bytes2 = alignOneC insertSettings chroms setup bytes1 bytes2 := by
  rcases bytes1 with _ | a <;> rcases bytes2 with _ | b <;> rcases setup with _ | ⟨iS, cfg, pk, pgs, offs, ns, hv⟩
  all_goals try rfl
  have hc := pairCfgZ_cap cfg pk a b (fun R => capFor pk (cfg.rcfg.cap1 R) R)
  simp only [Option.map, withMono, alignOneP, alignOneC, capForS_eq, capForZ_eq, Report.answerOfPairP_eq,
    ← MapSpec.Fast.costZ_eqS]
  have hq : ∀ (s1 s2 : MapSpec.Fast.PrepM MapSpec.Fast.MzP) (za1 za2 zb1 zb2 : Array Nat),
      MapSpec.Fast.tierPairBP.tierPairBQ (pairCfg cfg pk a b) pk #[0] pgs a b s1 s2 za1 za2 zb1 zb2
        (MapSpec.Fast.costZ (capFor pk (cfg.rcfg.cap1 a) a) za1 za2) (MapSpec.Fast.costZ (capFor pk (cfg.rcfg.cap1 b) b) zb1 zb2) =
      MapSpec.Fast.tierPairBP (pairCfg cfg pk a b) pk #[0] pgs a b s1 s2 za1 za2 zb1 zb2 := by
    intro s1 s2 za1 za2 zb1 zb2
    unfold MapSpec.Fast.tierPairBP
    rw [show pairCfg cfg pk a b = pairCfgZ cfg pk a b (capFor pk (cfg.rcfg.cap1 a) a) (capFor pk (cfg.rcfg.cap1 b) b) from rfl,
      hc.1, hc.2]
  rw [show pairCfgZ cfg pk a b (capFor pk (cfg.rcfg.cap1 a) a) (capFor pk (cfg.rcfg.cap1 b) b) = pairCfg cfg pk a b from rfl, hq]
  simp only [answerOfReads, answerWith, MapSpec.Fast.tierPair, MapSpec.Fast.tierPairB_eqP]

-- each task loads the index and builds the setup itself (`ParMap.parMapS`): its structures are
-- then that task's own, so their reference counts are not shared across threads; only the
-- index bytes are
def alignPairsC (insertSettings : InsertSettings) (index : ByteArray)
    (pairs : List (Option ByteArray × Option ByteArray)) : List PairResult :=
  let chroms := (readIndex index).1.getD []
  (ParMap.parMapS parTasks (fun _ => (loadedSetup insertSettings (readIndex index).2).map withMono)
    (fun setup (bytes1, bytes2) => alignOneP insertSettings chroms setup bytes1 bytes2) pairs.toArray).toList

theorem alignOneC_eq (insertSettings : InsertSettings) (chroms : List (List Nat)) (loaded : Option LoadedIndex)
    (bytes1 bytes2 : Option ByteArray) :
    alignOneC insertSettings chroms (loadedSetup insertSettings loaded) bytes1 bytes2 =
      alignOne insertSettings chroms loaded bytes1 bytes2 := by
  rcases bytes1 with _ | _ <;> rcases bytes2 with _ | _ <;> rcases loaded with _ | ⟨ix, G, _, _, _, _⟩ <;> rfl

-- compiled code runs `alignPairsC`
@[csimp] theorem alignPairs_eqC : @alignPairs = @alignPairsC := by
  funext insertSettings index pairs
  simp only [alignPairs, alignPairsC, ParMap.parMapS_eq, ParMap.parMap_eq_map, alignOneP_eq, alignOneC_eq]

/-! ## The proof -/

theorem alignPairs_eq_map (insertSettings : InsertSettings) (index : ByteArray)
    (pairs : List (Option ByteArray × Option ByteArray)) :
    alignPairs insertSettings index pairs =
      pairs.map fun (bytes1, bytes2) =>
        alignOne insertSettings ((readIndex index).1.getD []) (readIndex index).2 bytes1 bytes2 := by
  simp [alignPairs, ParMap.parMap_eq_map]

/-! ## The setup made once, for any number of chunks (used by `MapFast`: `alignPairsP_eq`) -/

def AlignSetup : Type := List (List Nat) × Option SetupP

def chunkSetup (insertSettings : InsertSettings) (index : ByteArray) : AlignSetup :=
  ((readIndex index).1.getD [], (loadedSetup insertSettings (readIndex index).2).map withMono)

def alignPairsP (insertSettings : InsertSettings) (setup : AlignSetup)
    (pairs : List (Option ByteArray × Option ByteArray)) : List PairResult :=
  pairs.map fun (bytes1, bytes2) => alignOneP insertSettings setup.1 setup.2 bytes1 bytes2

theorem alignPairsP_eq (insertSettings : InsertSettings) (index : ByteArray) :
    alignPairsP insertSettings (chunkSetup insertSettings index) = alignPairs insertSettings index := by
  funext pairs
  rw [alignPairs_eq_map]
  simp only [alignPairsP, chunkSetup, alignOneP_eq, alignOneC_eq]

-- what the index holds, when it was built from `byteGenome`: the genome's chromosomes, or something checked
theorem readIndex_buildIndex (byteGenome : GenomeFile) :
    readIndex (buildIndex byteGenome) = (some (genomeChroms byteGenome), none) ∨
    ∃ loaded, readIndex (buildIndex byteGenome) = (none, some loaded) ∧ indexOk byteGenome loaded = true := by
  have hrec : readIndex (LastResort.lensRecord (chromsNats (genomeChroms byteGenome))) =
      (some (genomeChroms byteGenome), none) := by
    unfold readIndex; rw [LastResort.readLens_record]; dsimp only; rw [ungen_chromsNats _ _ (Nat.le_refl _)]
  unfold buildIndex
  generalize saveIndex (buildLoaded byteGenome) = saved
  dsimp only
  cases h1 : LastResort.readLens saved with
  | some _ => exact .inl hrec
  | none =>
    cases h2 : loadIndex saved with
    | none => exact .inl hrec
    | some loaded =>
      by_cases hok : indexOk byteGenome loaded = true
      · refine .inr ⟨loaded, ?_, hok⟩
        simp only [hok, if_true]
        unfold readIndex; rw [h1, h2]
      · exact .inl (by simp only [hok, Bool.false_eq_true, if_false]; exact hrec)

-- the genome from the record has the decoded genome's letters, and its chromosome lengths
theorem chromGenome_seqs (byteGenome : GenomeFile) :
    (chromGenome (genomeChroms byteGenome)).map (·.seq) = byteGenome.decode.map (·.seq) := by
  simp only [chromGenome, genomeChroms, GenomeFile.decode, List.map_map]
  refine List.map_congr_left fun p _ => ?_
  simp [decodeRead]

theorem chromGenome_lens (chroms : List (List Nat)) :
    (chromGenome chroms).length = (chroms.map (·.length)).toArray.size ∧
    ∀ c, c < (chroms.map (·.length)).toArray.size → ∃ chr : Chromosome,
      (chromGenome chroms)[c]? = some chr ∧ chr.seq.length = (chroms.map (·.length)).toArray[c]! := by
  refine ⟨by simp [chromGenome], fun c hc => ?_⟩
  have hc' : c < chroms.length := by simpa using hc
  refine ⟨_, List.getElem?_eq_getElem (by simpa [chromGenome] using hc'), ?_⟩
  rw [getElem!_pos _ c hc]
  simp [chromGenome]

-- THE ONE SETTING CONDITION: `junkScore ≤ -16`, so a pair below `junkScore` is below Spec's `requiredMapBound`
-- (which is between -16 and 0). (Without it Spec has no correct answer for some reads: best proper pair at -12,
-- `junkScore` -10, `requiredMapBound` -16.)
def SettingsOk (insertSettings : InsertSettings) : Prop := insertSettings.junkScore ≤ -16

-- what the proofs use: the second look's cap (at most 16) reaches `requiredMapBound`, and `junkScore` is below it
theorem settings_reads {insertSettings : InsertSettings} (h : SettingsOk insertSettings) (m1 m2 : Read) :
    -16 ≤ requiredMapBound m1 m2 ∧ insertSettings.junkScore ≤ requiredMapBound m1 m2 := by
  unfold SettingsOk at h; unfold requiredMapBound; constructor <;> omega

-- the second look's cap for Spec's `requiredMapBound` is `LastResort.capOfLens`
theorem lookCap_default (m1 m2 : Read) :
    lookCap (requiredMapBound m1 m2) = LastResort.capOfLens m1.length m2.length := by
  unfold lookCap requiredMapBound LastResort.capOfLens LastResort.errorsChecked
  omega

theorem lookCap_ok {req : Int} (h : -16 ≤ req) : -((lookCap req : Int) + 1) < req := by
  unfold lookCap; omega

theorem alignOne_correct (insertSettings : InsertSettings) (hS : SettingsOk insertSettings) (genome : Genome)
    (byteGenome : GenomeFile) (hGenome : byteGenome.decode = genome)
    (chroms : List (List Nat)) (loaded : Option LoadedIndex)
    (hcase : (loaded = none ∧ chroms = genomeChroms byteGenome) ∨
      ∃ l, loaded = some l ∧ indexOk byteGenome l = true)
    (bytes1 bytes2 : Option ByteArray) :
    PairResult.Correct insertSettings genome (bytes1.map decodeRead) (bytes2.map decodeRead)
      (alignOne insertSettings chroms loaded bytes1 bytes2) := by
  match bytes1, bytes2 with
  | none, _ => simp [alignOne, PairResult.Correct]
  | some _, none => simp [alignOne, PairResult.Correct]
  | some read1, some read2 =>
    obtain ⟨hreq, hj⟩ := settings_reads hS (decodeRead read1) (decodeRead read2)
    have hc := lookCap_ok hreq
    match loaded, hcase with
    | none, hcase =>
      have hl : chroms = genomeChroms byteGenome := by
        rcases hcase with ⟨-, h⟩ | ⟨_, h, -⟩
        · exact h
        · cases h
      have hseq : (chromGenome chroms).map (·.seq) = genome.map (·.seq) := by
        rw [hl, chromGenome_seqs, hGenome]
      obtain ⟨hlen, hchr⟩ := chromGenome_lens chroms
      obtain ⟨-, hnone⟩ := LastResort.fitNs_ok insertSettings.range.1 hlen hchr
      have hu : (LastResort.lookAnswer (lookCap (reqOf insertSettings read1 read2))
          (LastResort.runsSp (oldGenome (chromGenome chroms)) (decodeRead read1))
          (LastResort.runsSp (oldGenome (chromGenome chroms)) (decodeRead read2))
          (LastResort.pairsSpec insertSettings.dovetailSlack insertSettings.range.1 insertSettings.range.2
            (lookCap (reqOf insertSettings read1 read2)) (oldGenome (chromGenome chroms))
            (decodeRead read1) (decodeRead read2))).uniqueness = .unknown := by
        unfold LastResort.lookAnswer; split <;> rfl
      rcases LastResort.finalize_correct (LastResort.fitNs (chroms.map (·.length)).toArray) hnone
          (LastResort.lookAnswer_correct insertSettings (chromGenome chroms) (decodeRead read1) (decodeRead read2)
            _ _ _ _ (LastResort.pairsSpec_mem _ _ _ _ _ _ _)
            (fun _ hx => LastResort.runsSp_ok hx) (fun _ hx => LastResort.runsSp_ok hx)) with h | h
      · exact LastResort.correct_transfer hseq (LastResort.finalize_unknown hu) h
      · exact absurd h.1 (LastResort.look_not_leftover hc hj)
    | some (ix, G, offs, ns, H, M), hcase =>
      have hLoaded : indexOk byteGenome (ix, G, offs, ns, H, M) = true := by
        rcases hcase with ⟨h, -⟩ | ⟨_, h, hok⟩
        · cases h
        · cases h; exact hok
      obtain ⟨hcut, hg, hchk, hheavy⟩ := indexOk_sound hLoaded
      rw [hGenome] at hg
      have h0 : G.o = 0 := by
        simp only [MapSpec.Fast.cutOk, Bool.and_eq_true, beq_iff_eq] at hcut; exact hcut.1
      -- the router's answer, for the whole genome as one chromosome
      have hok := fun cfg => MapSpec.Fast.tierPair_sound cfg
        (oldGenome (Whole.wholeOf G))
        (decodeRead read1) (decodeRead read2) ix G #[0] #[G.n] (Whole.cutOk_whole h0)
        (Whole.genomeBytes_whole G) hchk (some read1) (some read2)
        (fun R h => by cases h; exact encodes_decodeRead _) (fun R h => by cases h; exact encodes_decodeRead _)
      -- moved to the chromosomes: each is a slice of the whole
      have hslice := Whole.slice_of_cut hcut hg
      -- chromosome `c` has `ns[c]` letters
      have hchr : ∀ c, c < ns.size → ∃ chr : Chromosome, genome[c]? = some chr ∧ chr.seq.length = ns[c]! := by
        intro c hc
        have hsz := hg.1
        simp only [Array.size_map, oldGenome, List.length_map, MapSpec.Fast.cutAll, Array.size_range] at hsz
        have hcg : c < genome.length := by omega
        refine ⟨genome[c], List.getElem?_eq_getElem hcg, ?_⟩
        have henc := hg.2 c (by simp [MapSpec.Fast.cutAll]; omega) (by simp [oldGenome]; omega)
        simp only [oldGenome, List.getElem_map] at henc
        rw [← henc.1, Array.getElem_map, ← getElem!_pos (MapSpec.Fast.cutAll G offs ns) c
          (by simp [MapSpec.Fast.cutAll]; omega), MapSpec.Fast.cutAll_get G offs ns c hc, MapSpec.Fast.unpack_size]
        rfl
      have hlen : genome.length = ns.size := by
        have hsz := hg.1
        simp only [Array.size_map, oldGenome, List.length_map, MapSpec.Fast.cutAll, Array.size_range] at hsz
        omega
      obtain ⟨-, hnone⟩ := LastResort.fitNs_ok insertSettings.range.1 hlen hchr
      -- moved to the chromosomes: each is a slice of the whole; the found pair re-checked (`Report`);
      -- an answer without a pair is junk or gets one (`LastResort`)
      have key : ∀ fb t, MapSpec.Fast.TierOk insertSettings.dovetailSlack insertSettings.range.1 insertSettings.range.2
          (oldGenome (Whole.wholeOf G)) (decodeRead read1) (decodeRead read2) (some read1) (some read2) t →
          (answerWith insertSettings (reqOf insertSettings read1 read2) fb (ix, G) (MapSpec.Fast.cutAll G #[0] #[G.n])
            offs ns read1 read2 t).Correct insertSettings genome (decodeRead read1) (decodeRead read2) ∨
          (LastResort.Leftover (reqOf insertSettings read1 read2) (answerWith insertSettings (reqOf insertSettings read1 read2)
            fb (ix, G) (MapSpec.Fast.cutAll G #[0] #[G.n]) offs ns read1 read2 t) ∧
           CorrectU insertSettings genome (decodeRead read1) (decodeRead read2) (answerWith insertSettings
            (reqOf insertSettings read1 read2) fb (ix, G) (MapSpec.Fast.cutAll G #[0] #[G.n]) offs ns read1 read2 t)) :=
        fun fb t hok' => LastResort.finalize_correct (LastResort.fitNs ns) hnone
          (Report.answerOfPair_correct hslice hchr hlen reportTies fb mateRescue _ _ _ _ (ix, G) insertSettings read1 read2 _ hok'
            (Whole.correct_of_whole insertSettings _ _ hslice _ rfl rfl
              (answerOf_correct insertSettings (Whole.wholeOf G) _ _ read1 read2 _ hok')))
      -- the second look
      have hlook : (lookAt insertSettings (reqOf insertSettings read1 read2) (ix, G) offs ns read1 read2).Correct
          insertSettings genome (decodeRead read1) (decodeRead read2) := by
        unfold lookAt
        dsimp only
        have hc16 : lookCap (reqOf insertSettings read1 read2) ≤ 16 := Nat.min_le_left _ _
        rcases LastResort.finalize_correct (LastResort.fitNs ns) hnone
            (LastResort.lookAnswer_correct insertSettings genome _ _ _ _ _ _
              (LastResort.pairsAtS_mem hc16 hcut hg hchk (encodes_decodeRead _) (encodes_decodeRead _))
              (fun x hx => LastResort.runsIx_ok hg (encodes_decodeRead _) hx)
              (fun x hx => LastResort.runsIx_ok hg (encodes_decodeRead _) hx)) with h | h
        · exact h
        · exact absurd h.1 (LastResort.look_not_leftover hc hj)
      have hok0 := hok (pairCfg (tierCfg insertSettings (ix, G) #[0] (MapSpec.Fast.cutAll G #[0] #[G.n])) (ix, G) read1 read2)
      show PairAnswer.Correct _ _ _ _ (answerOfReads _ _ _ _ _ _ _ _ _)
      unfold answerOfReads
      -- witness-first (an option)
      split
      · rename_i hw
        simp only [witnessHit, Bool.and_eq_true, Bool.or_eq_true] at hw
        refine ⟨fun rep h => by simp [witnessAnswer] at h, fun pair _ => ?_, ⟨rfl, ?_⟩⟩
        · show pair.first.score + pair.second.score ≤ 0
          have := pair.first.score_nonpos; have := pair.second.score_nonpos; omega
        · rcases hw.2 with h | h
          · exact .inl (Heavy.heavyMate_sound hchk hslice hchr hheavy read1 h)
          · exact .inr (Heavy.heavyMate_sound hchk hslice hchr hheavy read2 h)
      dsimp only
      -- (1, 2) the router and the walk
      refine orElse_ok _ _ _ (fun a ha => by cases ha; exact (key _ _ hok0).imp id And.left) ?_
      unfold afterRouter
      dsimp only
      -- (3) the join
      refine orElse_ok _ _ _ (fun a ha => ?_) ?_
      · unfold joinAt at ha
        split at ha
        · obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp ha
          exact (key _ _ (MapSpec.Fast.tierNo_ok (tierCfg insertSettings (ix, G) #[0] (MapSpec.Fast.cutAll G #[0] #[G.n]))
            (oldGenome (Whole.wholeOf G)) (decodeRead read1) (decodeRead read2) ix G #[0] #[G.n]
            (Whole.cutOk_whole h0) (Whole.genomeBytes_whole G) hchk
            (encodes_decodeRead _) (encodes_decodeRead _) _ false false ht)).imp id And.left
        · cases ha
      -- (4) short mates: the second look
      refine orElse_ok _ _ _ (fun a ha => ?_) ?_
      · split at ha
        · cases ha; exact .inl hlook
        · cases ha
      -- (5) the gave-up hook (a no-op for now)
      cases hgv : gaveUp (reqOf insertSettings read1 read2) (H, M) read1 read2
          (answerWith insertSettings (reqOf insertSettings read1 read2) (fallbackFrom (reqOf insertSettings read1 read2))
            (ix, G) (MapSpec.Fast.cutAll G #[0] #[G.n]) offs ns read1 read2
            (MapSpec.Fast.tierPair (pairCfg (tierCfg insertSettings (ix, G) #[0] (MapSpec.Fast.cutAll G #[0] #[G.n]))
              (ix, G) read1 read2) (ix, G) #[0] (MapSpec.Fast.cutAll G #[0] #[G.n]) (some read1) (some read2))) with
      | none => exact hlook
      | some a =>
        show PairAnswer.Correct _ _ _ _ a
        have ha := hgv
        unfold gaveUp at ha
        split at ha
        · rename_i hg
          cases ha
          obtain ⟨hleft, hrep⟩ := hg
          have hb := (key (fallbackFrom (reqOf insertSettings read1 read2)) _ hok0).elim (fun h => h.2.1) (fun h => h.2.2.1)
          simp only [Bool.and_eq_true, Bool.or_eq_true] at hrep
          refine ⟨fun rep h => absurd (hleft.1.symm.trans h) (by simp), hb, ?_⟩
          have hw : (decodeRead read1).highlyRepetitiveIn genome ∨ (decodeRead read2).highlyRepetitiveIn genome := by
            rcases hrep.2 with h | h
            · exact .inl (Heavy.heavyMate_sound hchk hslice hchr hheavy read1 h)
            · exact .inr (Heavy.heavyMate_sound hchk hslice hchr hheavy read2 h)
          exact ⟨hleft.1, hw⟩
        · cases ha

-- For any genome and trimmed mates: run on their bytes, with the index built from the genome's
-- bytes, there is one result per pair, and the i-th result proves its claim about the i-th pair.
-- `hSettings` (`SettingsOk`) is the ONE assumption beyond Spec's statement, on the settings only.
theorem alignPairs_correct (insertSettings : InsertSettings)
    (genome : Genome) (trimmedPairs : List (Option Read × Option Read))
    (byteGenome : GenomeFile) (hGenome : byteGenome.decode = genome)
    (index : ByteArray) (hIndex : index = buildIndex byteGenome)
    (bytePairs : List (Option ByteArray × Option ByteArray))
    (hMates : bytePairs.map decodePair = trimmedPairs)
    (hSettings : SettingsOk insertSettings) :
    (alignPairs insertSettings index bytePairs).length = trimmedPairs.length ∧
    ∀ (i : Nat) (result : PairResult) (mates : Option Read × Option Read),
      (alignPairs insertSettings index bytePairs)[i]? = some result →
      trimmedPairs[i]? = some mates →
      PairResult.Correct insertSettings genome mates.1 mates.2 result := by
  subst hMates index
  have hcase : ((readIndex (buildIndex byteGenome)).2 = none ∧
      (readIndex (buildIndex byteGenome)).1.getD [] = genomeChroms byteGenome) ∨
      ∃ l, (readIndex (buildIndex byteGenome)).2 = some l ∧ indexOk byteGenome l = true := by
    rcases readIndex_buildIndex byteGenome with h | ⟨l, h, hok⟩
    · exact .inl ⟨by rw [h], by rw [h]; rfl⟩
    · exact .inr ⟨l, by rw [h], hok⟩
  refine ⟨by simp [alignPairs_eq_map], ?_⟩
  intro i result mates hResult hMatesAt
  simp only [alignPairs_eq_map, List.getElem?_map] at hResult hMatesAt
  cases hAt : bytePairs[i]? with
  | none => simp [hAt] at hResult
  | some bytes =>
    simp only [hAt, Option.map_some, Option.some.injEq] at hResult hMatesAt
    subst hResult hMatesAt
    exact alignOne_correct insertSettings hSettings genome byteGenome hGenome _ _ hcase bytes.1 bytes.2

/-! ## End to end from the pure objects: the byte round trip for A, C, G, T, N -/

theorem decodeRead_encodeRead {read : Read} (h : ReadIsDNA read) : decodeRead (encodeRead read) = read := by
  simp only [decodeRead, encodeRead, Bridge.byteArray_toList, List.map_map]
  conv => rhs; rw [← List.map_id read]
  refine List.map_congr_left fun letter hl => ?_
  have hb : letter.toNat < 256 := by
    have := h letter hl
    simp only [nucleotides, List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl <;> decide
  have : (UInt8.ofNat letter.toNat).toNat = letter.toNat := by
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt hb]
  simp [Nat.toUInt8, this, Char.ofNat_toNat]

theorem Genome.decode_encode {genome : Genome} (h : GenomeIsDNA genome) : genome.encode.decode = genome := by
  simp only [Genome.encode, GenomeFile.decode, List.toList_toArray, List.map_map]
  conv => rhs; rw [← List.map_id genome]
  refine List.map_congr_left fun chromosome hc => ?_
  show ({ name := chromosome.name, seq := decodeRead (encodeRead chromosome.seq) } : Chromosome) = chromosome
  rw [decodeRead_encodeRead (h chromosome hc)]

theorem decodePair_encodePair {mates : Option Read × Option Read} (h : MatesAreDNA mates) :
    decodePair (encodePair mates) = mates := by
  obtain ⟨m1, m2⟩ := mates
  obtain ⟨h1, h2⟩ := h
  cases m1 <;> cases m2 <;>
    simp_all [decodePair, encodePair, decodeRead_encodeRead]

-- The same, end to end from the pure objects: write the genome and the trimmed mates as bytes,
-- build the index from the genome's bytes, align the pairs' bytes. Only assumption: every letter
-- is A, C, G, T or N. `hSettings`: as in `alignPairs_correct`.
theorem alignPairs_end_to_end (insertSettings : InsertSettings)
    (genome : Genome) (trimmedPairs : List (Option Read × Option Read))
    (hGenome : GenomeIsDNA genome) (hPairs : ∀ mates ∈ trimmedPairs, MatesAreDNA mates)
    (hSettings : SettingsOk insertSettings) :
    (alignPairs insertSettings (buildIndex genome.encode) (trimmedPairs.map encodePair)).length =
      trimmedPairs.length ∧
    ∀ (i : Nat) (result : PairResult) (mates : Option Read × Option Read),
      (alignPairs insertSettings (buildIndex genome.encode) (trimmedPairs.map encodePair))[i]? =
        some result →
      trimmedPairs[i]? = some mates →
      PairResult.Correct insertSettings genome mates.1 mates.2 result := by
  have hMates : (trimmedPairs.map encodePair).map decodePair = trimmedPairs := by
    rw [List.map_map]
    conv => rhs; rw [← List.map_id trimmedPairs]
    exact List.map_congr_left fun mates hm => decodePair_encodePair (hPairs mates hm)
  exact alignPairs_correct insertSettings genome trimmedPairs genome.encode
    (Genome.decode_encode hGenome) _ rfl _ hMates hSettings

end Spec

#print axioms Spec.alignPairs_correct
#print axioms Spec.alignPairs_end_to_end
