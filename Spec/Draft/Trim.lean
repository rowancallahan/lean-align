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

-- every window [lo, hi) with lo < hi ≤ n, and its score
def windows (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun lo => (List.range (n - lo)).map fun k => (lo, lo + k + 1)

def windowScore (scores : List Int) (w : Nat × Nat) : Int := ((scores.drop w.1).take (w.2 - w.1)).sum

def bestWindow (scores : List Int) : Option (Nat × Nat) := (windows scores.length).maxOn? (windowScore scores)

-- cut at the adapter, keep the best-scoring window, and drop it if it is shorter than `minLength`
def trim (r : FQ.Read) : FQ.Read :=
  let c := cut r.sequence
  let scores := List.zipWith baseScore (r.sequence.take c) (r.quality.take c)
  match (bestWindow scores).filter fun (lo, hi) => minLength ≤ hi - lo with
  | some (lo, hi) => ⟨r.name, (r.sequence.drop lo).take (hi - lo), (r.quality.drop lo).take (hi - lo)⟩
  | none          => ⟨r.name, [], []⟩

theorem best_window (scores : List Int) (best : Nat × Nat) (h : bestWindow scores = some best) :
    ∀ w ∈ windows scores.length, windowScore scores w ≤ windowScore scores best := by
  sorry

end Spec.Trim
