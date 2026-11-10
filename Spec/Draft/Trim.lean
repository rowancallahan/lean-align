import Spec.Fastq

namespace Spec.Trim
open Spec.FQ

def adapter   : List UInt8 := "AGATCGGAAGAGC".toUTF8.toList
def minLength : Nat := 25

-- the first position where the adapter starts (≤ 1 mismatch), or where at least 6 of its first letters run
-- off the read's end exactly; the read's length if there is none
def cut (s : List UInt8) : Nat :=
  let adapterAt (i : Nat) : Bool :=
    let rest := s.drop i
    match decide (adapter.length ≤ rest.length) with
    | true  => ((adapter.zip rest).filter fun (a, b) => a != b).length ≤ 1
    | false => 6 ≤ rest.length && rest == adapter.take rest.length
  ((List.range s.length).find? adapterAt).getD s.length

-- Phred - 25 for A C G T; anything else (N) rules a window out
def baseScore (b q : UInt8) : Int :=
  match b with
  | 0x41 | 0x43 | 0x47 | 0x54 => (min (q.toNat - 33) 93 : Nat) - 25
  | _ => -1000000

def windowScore (scores : List Int) (lo hi : Nat) : Int := ((scores.drop lo).take (hi - lo)).sum

-- [lo, hi) is a window of `scores` and no window scores higher
def best (scores : List Int) (lo hi : Nat) : Prop :=
  lo < hi ∧ hi ≤ scores.length ∧
  ∀ a b, a < b → b ≤ scores.length → windowScore scores a b ≤ windowScore scores lo hi

def trim (r : FQ.Read) : FQ.Read := sorry

-- the name is kept; the sequence and quality are a best window of the read cut at the adapter, at least
-- `minLength` long, or nothing (when the read was cut to nothing, or a best window is shorter than `minLength`)
theorem trim_correct (r : FQ.Read) :
    let c := cut r.sequence
    let scores := List.zipWith baseScore (r.sequence.take c) (r.quality.take c)
    (trim r).name = r.name ∧
    ((∃ lo hi, best scores lo hi ∧ minLength ≤ hi - lo ∧
        (trim r).sequence = (r.sequence.drop lo).take (hi - lo) ∧
        (trim r).quality = (r.quality.drop lo).take (hi - lo)) ∨
     ((trim r).sequence = [] ∧ (trim r).quality = [] ∧
        (scores = [] ∨ ∃ lo hi, best scores lo hi ∧ hi - lo < minLength))) := by
  sorry

end Spec.Trim
