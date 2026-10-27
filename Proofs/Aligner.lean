import Proofs.Index
import TierHeur
import ParMap

/-! # 3. The aligner, proved. `Spec/Aligner.lean`'s types are in `Proofs/Answer.lean` (unchanged);
this file fills in the two holes, `buildIndex` and `alignPairs`, and proves `alignPairs_correct`
from the bridge lemmas (`Proofs/Bridge.lean`) and the router's `tierPair_sound`.

The index is checked once, when it is built: `buildIndex` writes the index only if it loads back
to exactly what was built and passes the router's checks (`IndexOk`); otherwise it writes an empty
index, and `alignPairs` then answers every pair with the bound 0 (always true). So `alignPairs`
never re-checks the index, and the proof gets the checks from `hIndex`. -/

namespace Spec

open Bridge

/-! ## The index: the minimizer index, the packed genome, and where each chromosome starts -/

abbrev LoadedIndex := MapSpec.Mz.MzIdx × MapSpec.Fast.PGen × Array Nat × Array Nat

-- the fast builders the harness uses (bench/WholeGenome.lean `build` and `pmap` modes; `Proofs/Index.lean`)
def buildLoaded (byteGenome : GenomeFile) : LoadedIndex :=
  let gbs := byteGenome.map (·.2)
  let G := Index.packAll gbs
  (Index.buildMz gbs G, G, Index.offsOf gbs, gbs.map (·.size))

-- one ByteArray: magic, then the four parts
def saveIndex (loaded : LoadedIndex) : ByteArray :=
  let (ix, G, offs, ns) := loaded
  Index.putNats (Index.putNats (Index.putPGen (Index.putMz (Index.putU64 (ByteArray.emptyWithCapacity (Index.savedSize ix G offs ns)) Index.magic) ix) G) offs) ns

-- Note (speed): `loadIndex` copies `ix.offs`, `ix.sl`, `G.w`, `G.ex` out of `index` (`extract`) and
-- rebuilds `ix.pm`, `ix.runs`, `offs`, `ns`, on every call, i.e. once per `alignPairs` chunk.
def loadIndex (index : ByteArray) : Option LoadedIndex :=
  if index.size < 8 then none else
  (do
    if (← Index.rdU64 index) != Index.magic then failure
    let ix ← Index.rdMz index
    let G ← Index.rdPGen index
    let offs ← Index.rdNats index
    let ns ← Index.rdNats index
    if (← get) != index.size then failure
    return (ix, G, offs, ns) : Index.Rd LoadedIndex).run' 0

-- the router's hypotheses, as one check run at build time
def indexOk (byteGenome : GenomeFile) (loaded : LoadedIndex) : Bool :=
  let (ix, G, offs, ns) := loaded
  MapSpec.Fast.cutOk G offs ns && MapSpec.Mz.check3P ix G 4 && Index.chromsOk byteGenome G offs ns

-- saving then loading gives back what was saved (checked at build time)
def roundTrips (saved : ByteArray) (loaded : LoadedIndex) : Bool :=
  decide (loadIndex saved = some loaded)

theorem loadIndex_empty : loadIndex ByteArray.empty = none := by
  simp [loadIndex]

theorem roundTrips_load {saved : ByteArray} {loaded : LoadedIndex} (h : roundTrips saved loaded = true) :
    loadIndex saved = some loaded :=
  of_decide_eq_true h

theorem indexOk_sound {byteGenome : GenomeFile} {ix : MapSpec.Mz.MzIdx} {G : MapSpec.Fast.PGen}
    {offs ns : Array Nat} (h : indexOk byteGenome (ix, G, offs, ns) = true) :
    MapSpec.Fast.cutOk G offs ns = true ∧
    MapSpec.GenomeBytes ((MapSpec.Fast.cutAll G offs ns).map MapSpec.Mz.unpack) (oldGenome byteGenome.decode) ∧
    MapSpec.Mz.check2P ix G = true := by
  simp only [indexOk, Bool.and_eq_true, MapSpec.Mz.check3P_eq] at h
  exact ⟨h.1.1, Index.chromsOk_sound h.2, h.1.2⟩

-- the index holds everything the aligner needs, the genome included
def buildIndex (byteGenome : GenomeFile) : ByteArray :=
  let loaded := buildLoaded byteGenome
  let saved := saveIndex loaded
  if roundTrips saved loaded && indexOk byteGenome loaded then saved else ByteArray.empty

/-! ## The aligner -/

-- the router's settings for these insert settings (any settings are sound; these are for speed)
def tierCfg (insertSettings : InsertSettings) (pk : MapSpec.Fast.PkMz) (offs : Array Nat)
    (pgs : Array MapSpec.Fast.PGen) : MapSpec.Fast.TierCfg :=
  TierHeur.rtxCfg { cap1 := fun n => if 150 ≤ n then 16 else if 100 ≤ n then 12 else if 75 ≤ n then 11 else 12 }
    pk offs pgs insertSettings.range.1 insertSettings.range.2 insertSettings.dovetailSlack

-- the bound that always holds: every score is ≤ 0
def noIndexAnswer : PairAnswer :=
  { found := none, bestPossibleScore := 0, uniqueness := .unknown, tier := .boundsOnly }

def alignOne (insertSettings : InsertSettings) (loaded : Option LoadedIndex)
    (bytes1 bytes2 : Option ByteArray) : PairResult :=
  match bytes1, bytes2 with
  | none, _ => .trimmedAway .one
  | some _, none => .trimmedAway .two
  | some read1, some read2 =>
      match loaded with
      | none => .aligned noIndexAnswer
      | some (ix, G, offs, ns) =>
          .aligned (answerOf (MapSpec.Fast.tierPair (tierCfg insertSettings (ix, G) offs (MapSpec.Fast.cutAll G offs ns)) (ix, G) offs
            (MapSpec.Fast.cutAll G offs ns) (some read1) (some read2)))

-- a chunk of pairs; the implementation may work across the chunk however it likes
def alignPairs (insertSettings : InsertSettings) (index : ByteArray)
    (pairs : List (Option ByteArray × Option ByteArray)) : List PairResult :=
  let loaded := loadIndex index
  -- 16 batches, one task each (ParMap.parMap_eq_map: the same as a plain map)
  (ParMap.parMap 16 (fun (bytes1, bytes2) => alignOne insertSettings loaded bytes1 bytes2) pairs.toArray).toList

/-! ## The proof -/

theorem alignPairs_eq_map (insertSettings : InsertSettings) (index : ByteArray)
    (pairs : List (Option ByteArray × Option ByteArray)) :
    alignPairs insertSettings index pairs =
      pairs.map fun (bytes1, bytes2) => alignOne insertSettings (loadIndex index) bytes1 bytes2 := by
  simp [alignPairs, ParMap.parMap_eq_map]


theorem noIndexAnswer_correct (insertSettings : InsertSettings) (genome : Genome) (mate1 mate2 : Read) :
    noIndexAnswer.Correct insertSettings genome mate1 mate2 := by
  refine ⟨fun _ h => by simp [noIndexAnswer] at h, fun pair _ => ?_, by simp [noIndexAnswer]⟩
  have := pair.first.score_nonpos
  have := pair.second.score_nonpos
  simp only [noIndexAnswer, PairAlignment.score]
  omega

-- what the index loads to, when it was built from `byteGenome`: nothing, or something checked
theorem loadIndex_buildIndex (byteGenome : GenomeFile) :
    loadIndex (buildIndex byteGenome) = none ∨
    ∃ loaded, loadIndex (buildIndex byteGenome) = some loaded ∧ indexOk byteGenome loaded = true := by
  unfold buildIndex
  simp only
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    exact .inr ⟨_, roundTrips_load h.1, h.2⟩
  · exact .inl loadIndex_empty

theorem alignOne_correct (insertSettings : InsertSettings) (genome : Genome)
    (byteGenome : GenomeFile) (hGenome : byteGenome.decode = genome)
    (loaded : Option LoadedIndex) (hLoaded : ∀ l, loaded = some l → indexOk byteGenome l = true)
    (bytes1 bytes2 : Option ByteArray) :
    PairResult.Correct insertSettings genome (bytes1.map decodeRead) (bytes2.map decodeRead)
      (alignOne insertSettings loaded bytes1 bytes2) := by
  match bytes1, bytes2 with
  | none, _ => simp [alignOne, PairResult.Correct]
  | some _, none => simp [alignOne, PairResult.Correct]
  | some read1, some read2 =>
    match loaded, hLoaded with
    | none, _ => exact noIndexAnswer_correct insertSettings genome _ _
    | some (ix, G, offs, ns), hLoaded =>
      obtain ⟨hcut, hg, hchk⟩ := indexOk_sound (hLoaded _ rfl)
      rw [hGenome] at hg
      have hok := MapSpec.Fast.tierPair_sound (tierCfg insertSettings (ix, G) offs (MapSpec.Fast.cutAll G offs ns)) (oldGenome genome)
        (decodeRead read1) (decodeRead read2) ix G offs ns hcut hg hchk (some read1) (some read2)
        (fun R h => by cases h; exact encodes_decodeRead _) (fun R h => by cases h; exact encodes_decodeRead _)
      exact answerOf_correct insertSettings genome _ _ read1 read2 _ hok

-- For any genome and trimmed mates: run on their bytes, with the index built from the genome's
-- bytes, there is one result per pair, and the i-th result proves its claim about the i-th pair.
theorem alignPairs_correct (insertSettings : InsertSettings)
    (genome : Genome) (trimmedPairs : List (Option Read × Option Read))
    (byteGenome : GenomeFile) (hGenome : byteGenome.decode = genome)
    (index : ByteArray) (hIndex : index = buildIndex byteGenome)
    (bytePairs : List (Option ByteArray × Option ByteArray))
    (hMates : bytePairs.map decodePair = trimmedPairs) :
    (alignPairs insertSettings index bytePairs).length = trimmedPairs.length ∧
    ∀ (i : Nat) (result : PairResult) (mates : Option Read × Option Read),
      (alignPairs insertSettings index bytePairs)[i]? = some result →
      trimmedPairs[i]? = some mates →
      PairResult.Correct insertSettings genome mates.1 mates.2 result := by
  subst hMates hIndex
  have hLoaded : ∀ l, loadIndex (buildIndex byteGenome) = some l → indexOk byteGenome l = true := by
    intro l hl
    rcases loadIndex_buildIndex byteGenome with h | ⟨l', h, hok⟩
    · rw [h] at hl; cases hl
    · rw [h] at hl; cases hl; exact hok
  refine ⟨by simp [alignPairs_eq_map], ?_⟩
  intro i result mates hResult hMatesAt
  simp only [alignPairs_eq_map, List.getElem?_map] at hResult hMatesAt
  cases hAt : bytePairs[i]? with
  | none => simp [hAt] at hResult
  | some bytes =>
    simp only [hAt, Option.map_some, Option.some.injEq] at hResult hMatesAt
    subst hResult hMatesAt
    exact alignOne_correct insertSettings genome byteGenome hGenome _ hLoaded bytes.1 bytes.2

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
-- is A, C, G, T or N.
theorem alignPairs_end_to_end (insertSettings : InsertSettings)
    (genome : Genome) (trimmedPairs : List (Option Read × Option Read))
    (hGenome : GenomeIsDNA genome) (hPairs : ∀ mates ∈ trimmedPairs, MatesAreDNA mates) :
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
    (Genome.decode_encode hGenome) _ rfl _ hMates

end Spec
