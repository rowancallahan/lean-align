import Spec.Fastq

namespace Spec.Trim
open Spec.FQ

def adapter   : List UInt8 := "AGATCGGAAGAGC".toUTF8.toList
def minLength : Nat := 25

def cut (s : List UInt8) : Nat :=
  let adapterAt (i : Nat) : Bool :=
    let rest := s.drop i
    match decide (adapter.length ≤ rest.length) with
    | true  => ((adapter.zip rest).filter fun (a, b) => a != b).length ≤ 1
    | false => 6 ≤ rest.length && rest == adapter.take rest.length
  ((List.range s.length).find? adapterAt).getD s.length

def baseScore (b q : UInt8) : Int :=
  match b with
  | 0x41 | 0x43 | 0x47 | 0x54 => (min (q.toNat - 33) 93 : Nat) - 25
  | _ => -1000000

def windows (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun lo => (List.range (n - lo)).map fun k => (lo, lo + k + 1)

def windowScore (scores : List Int) (w : Nat × Nat) : Int := ((scores.drop w.1).take (w.2 - w.1)).sum

def bestWindow (scores : List Int) : Option (Nat × Nat) := (windows scores.length).maxOn? (windowScore scores)

def scoresOf (r : FQ.Read) : List Int :=
  List.zipWith baseScore (r.sequence.take (cut r.sequence)) (r.quality.take (cut r.sequence))

def trim (r : FQ.Read) : FQ.Read :=
  match bestWindow (scoresOf r) with
  | some (lo, hi) =>
    match decide (minLength ≤ hi - lo) with
    | true  => ⟨r.name, (r.sequence.drop lo).take (hi - lo), (r.quality.drop lo).take (hi - lo)⟩
    | false => ⟨r.name, [], []⟩
  | none => ⟨r.name, [], []⟩

theorem best_window (scores : List Int) (best : Nat × Nat) (h : bestWindow scores = some best) :
    ∀ w ∈ windows scores.length, windowScore scores w ≤ windowScore scores best := by
  sorry

end Spec.Trim
