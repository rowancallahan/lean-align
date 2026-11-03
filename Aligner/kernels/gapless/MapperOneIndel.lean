import MapperGapless

/-! Walks scoring exactly `gapOpen + gapExtend` with a gap (when
`matchScore = 0`): one gap column, every other column a match.  So the two
lists differ by deleting one letter from the longer (`delOk`). -/

namespace MapSpec

open AlignmentSpec

/-! ## Soundness: a one-letter deletion gives a walk scoring `gapOpen + gapExtend` -/

end MapSpec

