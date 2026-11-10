import PairNear
open MapSpec.Fast MapSpec AlignmentSpec
def spec (sl hi n gb : Nat) (ys : List (Placement × Int)) (vc nR D : Nat) : Bool :=
  ys.any fun y => y.1.1.chr == (if vc < n then vc else vc - n) &&
    decide (D ≤ y.1.1.start + y.1.1.len + hi + sl + nR + gb) && decide (y.1.1.start + nR ≤ D + hi + sl + gb)
def mkP (c s l : Nat) : Placement := by
  first | exact (⟨c, s, l⟩, .fwd) | exact ⟨⟨c, s, l⟩, .fwd⟩
def main : IO Unit := do
  let mut bad := 0
  for trial in [0:3000] do
    let k ← IO.rand 0 30
    let n ← IO.rand 1 4
    let mut ys : List (Placement × Int) := []
    for _ in [0:k] do
      ys := (mkP (← IO.rand 0 3) (← IO.rand 0 400) (← IO.rand 0 200), 0) :: ys
    let sl ← IO.rand 0 20; let hi ← IO.rand 0 300; let gb ← IO.rand 0 30
    let t := keepTab ys; let f := keepQ (hi + sl + gb) n t
    for _ in [0:200] do
      let vc ← IO.rand 0 (2*n); let nR ← IO.rand 25 300; let D ← IO.rand 0 1500
      if f vc nR D != spec sl hi n gb ys vc nR D then
        bad := bad + 1
        if bad < 4 then IO.println s!"MISMATCH trial {trial} vc {vc} nR {nR} D {D}"
  IO.println s!"mismatches {bad} of 600000"
