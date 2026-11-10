import Spec.Fastq
import ReadWindowTrimmer

namespace Spec.Trim
open Spec.FQ

def adapter      : List UInt8 := "AGATCGGAAGAGC".toUTF8.toList
def minAdapter   : Nat := 6
def minLength    : Nat := 25
def neutralPhred : Int := 25

def mismatches (a b : List UInt8) : Nat := ((a.zip b).filter fun (x, y) => x != y).length

def adapterAt (s : List UInt8) (i : Nat) : Bool :=
  let rest := s.drop i
  if adapter.length ≤ rest.length then mismatches adapter rest ≤ 1
  else minAdapter ≤ rest.length && rest == adapter.take rest.length

def cutPoint (s : List UInt8) : Nat := ((List.range s.length).find? (adapterAt s)).getD s.length

def baseScore (b q : UInt8) : Int :=
  if b ∈ [0x41, 0x43, 0x47, 0x54] then (min (q.toNat - 33) 93 : Nat) - neutralPhred else -1000000

def window (lo hi : Nat) (xs : List UInt8) : List UInt8 := (xs.drop lo).take (hi - lo)

def trim (r : FQ.Read) : FQ.Read :=
  let s := r.sequence.take (cutPoint r.sequence)
  let q := r.quality.take (cutPoint r.sequence)
  match get_best_window [] (List.zipWith baseScore s q) id with
  | some (lo, hi) => if minLength ≤ hi - lo then ⟨r.name, window lo hi s, window lo hi q⟩ else ⟨r.name, [], []⟩
  | none          => ⟨r.name, [], []⟩

theorem cut_correct (s : List UInt8) :
    cutPoint s ≤ s.length ∧ (∀ i < cutPoint s, adapterAt s i = false) ∧
    (cutPoint s < s.length → adapterAt s (cutPoint s) = true) := by
  sorry

theorem trim_correct (r : FQ.Read) (lo hi : Nat) (hr : (trim r).sequence ≠ []) :
    let s := r.sequence.take (cutPoint r.sequence)
    let scores := List.zipWith baseScore s (r.quality.take (cutPoint r.sequence))
    get_best_window [] scores id = some (lo, hi) →
      (trim r).sequence = window lo hi s ∧ minLength ≤ hi - lo ∧
      ∀ a b, a < b → b ≤ scores.length → window_score scores id (a, b) ≤ window_score scores id (lo, hi) := by
  sorry

end Spec.Trim
