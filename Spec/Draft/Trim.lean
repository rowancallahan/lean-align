import Spec.Fastq

namespace Spec.Trim
open Spec.FQ

def adapter   : List UInt8 := "AGATCGGAAGAGC".toUTF8.toList
def minLength : Nat := 25

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

-- Phred - 25 for A C G T; N rules a window out
def baseScore (b q : UInt8) : Int :=
  match b with
  | 0x41 | 0x43 | 0x47 | 0x54 =>
    (min (q.toNat - 33) 93 : Nat) - 25
  | _ =>
    -1000000

def windowScore (scores : List Int) (lo hi : Nat) : Int :=
  (scores.extract lo hi).sum

def trim (r : FQ.Read) : FQ.Read := sorry

-- the kept part is a best window [lo, hi): no window scores higher;
-- it is dropped if shorter than `minLength`
theorem trim_correct (r : FQ.Read) :
    let scores := List.zipWith baseScore r.sequence r.quality
    (scores = [] ∧ trim r = ⟨r.name, [], []⟩) ∨
    ∃ lo hi, lo < hi ∧ hi ≤ scores.length ∧
      (∀ a b, a < b → b ≤ scores.length → windowScore scores a b ≤ windowScore scores lo hi) ∧
      trim r =
        match decide (minLength ≤ hi - lo) with
        | true =>
          ⟨r.name, r.sequence.extract lo hi, r.quality.extract lo hi⟩
        | false =>
          ⟨r.name, [], []⟩ := by
  sorry

end Spec.Trim
