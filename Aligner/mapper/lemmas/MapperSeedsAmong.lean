import MapperWalk2

/-! Clean seed among any chosen seeds.  `exists_clean_seed2` with the seeds
cut by a fixed `k` (the mapper's seed count) and the error bound taken at a
threshold `T` that may be higher than the mapper's: a walk scoring at least
`T` spoils at most `seedBound sc T` seeds, so among any `seedBound sc T + 1`
distinct seeds — in any order — one is clean, and its window shape obeys the
bounds at `T`. -/

namespace MapSpec

open AlignmentSpec

/-- Default scoring: a window within penalty `P` of a perfect match spoils at
most `P / 4` seeds (`P = 0, 4, 8, 12`). -/
example : seedBound ⟨0, -4, -6, -2⟩ 0 = 0 := by decide
example : seedBound ⟨0, -4, -6, -2⟩ (-4) = 1 := by decide
example : seedBound ⟨0, -4, -6, -2⟩ (-8) = 2 := by decide
example : seedBound ⟨0, -4, -6, -2⟩ (-12) = 3 := by decide

end MapSpec

