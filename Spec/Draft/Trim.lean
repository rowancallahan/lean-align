import Spec.Fastq

namespace Spec.Trim
open Spec.FQ

def adapter   : List UInt8 := "AGATCGGAAGAGC".toUTF8.toList

-- cut the read where the adapter starts: all 13 letters with ≤ 1 mismatch,
-- or at least its first 6 letters exactly, running off the read's end
def cut (r : FQ.Read) : FQ.Read :=
  let adapterAt (i : Nat) : Bool :=
    let rest := r.sequence.extract i
    match decide (adapter.length ≤ rest.length) with
    | true =>
      ((adapter.zip rest).filter fun (a, b) => a != b).length ≤ 1
    | false =>
      6 ≤ rest.length && rest == adapter.extract 0 rest.length
  let c := ((List.range r.sequence.length).find? adapterAt).getD r.sequence.length
  ⟨r.name, r.sequence.extract 0 c, r.quality.extract 0 c⟩

-- the score of the window [start, stop) of a read: each base scores Phred - 25,
-- and an N rules the window out
def windowScore (r : FQ.Read) (start stop : Nat) : Int :=
  let baseScore (b q : UInt8) : Int :=
    match b with
    | 0x41 | 0x43 | 0x47 | 0x54 =>
      (min (q.toNat - 33) 93 : Nat) - 25
    | _ =>
      -1000000
  (List.zipWith baseScore (r.sequence.extract start stop) (r.quality.extract start stop)).sum

def minLength : Nat := 25

def trim (r : FQ.Read) : FQ.Read := sorry

-- the kept part is a best window [start, stop): no proposed window scores higher;
-- it is dropped if shorter than `minLength`
theorem trim_correct (r : FQ.Read) (h : r.sequence.length = r.quality.length) :
    (r.sequence = [] ∧
     trim r = ⟨r.name, [], []⟩)
    ∨
    ∃ start stop,
      let windowLength := stop - start
      start < stop ∧
      stop ≤ r.sequence.length ∧
      (∀ proposedStart proposedStop,
        proposedStart < proposedStop →
        proposedStop ≤ r.sequence.length →
        windowScore r proposedStart proposedStop ≤ windowScore r start stop) ∧
      trim r =
        match decide (minLength ≤ windowLength) with
        | true =>
          ⟨r.name, r.sequence.extract start stop, r.quality.extract start stop⟩
        | false =>
          ⟨r.name, [], []⟩ := by
  sorry

end Spec.Trim
