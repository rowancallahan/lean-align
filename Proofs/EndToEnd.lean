import Proofs.Aligner
namespace Spec

/-! ## End to end from the pure objects

`alignPairs_correct` with every hypothesis discharged: start from a `Genome` and trimmed pairs,
write them as bytes (one byte per letter), index the genome's bytes, run the pairs' bytes. The
answers are correct for the original genome and pairs. The one assumption: every letter is an
upper-case nucleotide A, C, G, T or N (`Read` is `List Char`, and only letters below 256 survive the byte round trip). -/

def nucleotides : List Char := ['A', 'C', 'G', 'T', 'N']

def ReadIsDNA (read : Read) : Prop := ∀ letter ∈ read, letter ∈ nucleotides

def GenomeIsDNA (genome : Genome) : Prop := ∀ chromosome ∈ genome, ReadIsDNA chromosome.seq

def encodeRead (read : Read) : ByteArray :=
  ⟨(read.map fun letter => letter.toNat.toUInt8).toArray⟩

def Genome.encode (genome : Genome) : GenomeFile :=
  (genome.map fun chromosome => (chromosome.name, encodeRead chromosome.seq)).toArray

def encodePair (mates : Option Read × Option Read) : Option ByteArray × Option ByteArray :=
  (mates.1.map encodeRead, mates.2.map encodeRead)

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

def MatesAreDNA (mates : Option Read × Option Read) : Prop :=
  (∀ read ∈ mates.1, ReadIsDNA read) ∧ (∀ read ∈ mates.2, ReadIsDNA read)

theorem decodePair_encodePair {mates : Option Read × Option Read} (h : MatesAreDNA mates) :
    decodePair (encodePair mates) = mates := by
  obtain ⟨m1, m2⟩ := mates
  obtain ⟨h1, h2⟩ := h
  cases m1 <;> cases m2 <;>
    simp_all [decodePair, encodePair, decodeRead_encodeRead]

-- Index the genome, align the pairs; one answer per pair, each correct for the genome and pair.
theorem alignPairs_end_to_end (insertSettings : InsertSettings) (genome : Genome)
    (trimmedPairs : List (Option Read × Option Read))
    (hGenome : GenomeIsDNA genome) (hPairs : ∀ mates ∈ trimmedPairs, MatesAreDNA mates) :
    let results := alignPairs insertSettings (buildIndex genome.encode) (trimmedPairs.map encodePair)
    results.length = trimmedPairs.length ∧
    ∀ (i : Nat) (result : PairResult) (mates : Option Read × Option Read),
      results[i]? = some result → trimmedPairs[i]? = some mates →
      PairResult.Correct insertSettings genome mates.1 mates.2 result := by
  have hMates : (trimmedPairs.map encodePair).map decodePair = trimmedPairs := by
    rw [List.map_map]
    conv => rhs; rw [← List.map_id trimmedPairs]
    exact List.map_congr_left fun mates hm => decodePair_encodePair (hPairs mates hm)
  exact alignPairs_correct insertSettings genome trimmedPairs genome.encode
    (Genome.decode_encode hGenome) _ rfl _ hMates

end Spec
