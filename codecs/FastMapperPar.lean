import FastMapper
import ParMap

/-!
# `mapFastPar`: the fast mapper over `n` tasks

The reads are cut into `n` batches mapped by `Task.spawn` (`parMap`); the
answer is read by read the specification's.

    GenomeBytes gbs g → checkAll idxs gbs = true → (∀ i, Encodes Rs[i] reads[i]) →
      (mapFastPar n gbs idxs Rs)[i] = mapSpec sc0 (-12) g reads[i]          (mapFastPar_eq_mapSpec)
-/

namespace MapSpec.Fast

open MapSpec ParMap

def mapFastPar (n : Nat) (gbs : Array ByteArray) (idxs : Array HIdx) (Rs : Array ByteArray) :
    Array (Option (Window × Int)) :=
  parMap n (mapFast gbs idxs) Rs

theorem mapFastPar_eq_map (n : Nat) (gbs : Array ByteArray) (idxs : Array HIdx) (Rs : Array ByteArray) :
    mapFastPar n gbs idxs Rs = Rs.map (mapFast gbs idxs) :=
  parMap_eq_map n _ Rs

/-- **Parallel.**  Every read gets the specification's answer. -/
theorem mapFastPar_eq_mapSpec (n : Nat) (g : Genome) (gbs : Array ByteArray) (idxs : Array HIdx)
    (Rs : Array ByteArray) (reads : Array (List Char)) (hg : GenomeBytes gbs g)
    (hchk : checkAll idxs gbs = true) (hl : Rs.size = reads.size)
    (hr : ∀ i (h1 : i < Rs.size) (h2 : i < reads.size), Encodes Rs[i] reads[i]) :
    mapFastPar n gbs idxs Rs = reads.map (mapSpec sc0 (-12) g) := by
  rw [mapFastPar_eq_map]
  apply Array.ext
  · simp [hl]
  · intro i h1 h2
    simp only [Array.getElem_map]
    exact mapFast_eq_mapSpec g _ gbs idxs _ hg (hr i (by simpa using h1) (by simpa [hl] using h1)) hchk

end MapSpec.Fast

#print axioms MapSpec.Fast.mapFastPar_eq_mapSpec
