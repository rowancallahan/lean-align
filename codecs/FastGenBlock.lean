import FastGenCoverE
import MapperK250Seed

/-!
# Block choice: any 25-letter subwindow of a seed block

The event pigeonhole (`coverLE`) leaves a whole block `[j·L, j·L + L)` of a window
within penalty `P` clean, not only its first `l` letters.  So each block may be
seeded by any `l`-letter subwindow at offset `off j ≤ L − l` (`coverLE_blk`), e.g.
the one with the smallest index bucket (`blkOff`, a choice: no proof needed beyond
`blkOff_le`).
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-- **Coverage with block offsets**: as `coverLE`, the clean seed taken at offset `off j`
of its block (`off j + l ≤ L`). -/
theorem coverLE_blk (g : Genome) (read : List Char) (gbs : Array ByteArray) (R : ByteArray)
    (hg : GenomeBytes gbs g) (hr : Encodes R read) (S : Int)
    (l : Nat) (k : Nat) (hl2 : 2 ≤ read.length / (k + 1))
    (off : Nat → Nat) (hoff : ∀ j, off j + l ≤ read.length / (k + 1))
    (J : List Nat) (hJn : J.Nodup) (hJk : ∀ j ∈ J, j ≤ k) (hJl : seedBoundE sc0 S < J.length)
    (w : Window) (s : Int) (hs : windowScore sc0 read g w = some s) (hS : S ≤ s) :
    ∃ j ∈ J, ∃ (p : Nat) (a b : Int), w.chr < gbs.size ∧
      MatchAtL gbs[w.chr]! (p + off j) R (j * (read.length / (k + 1)) + off j) l ∧
      shapeOk (gapBound sc0 S) (gapBound2 sc0 S) a b ∧
      ((j * (read.length / (k + 1)) : Nat) : Int) + a ≤ p ∧ 0 ≤ (read.length : Int) + a + b ∧
      w.start = ((p : Int) - (j * (read.length / (k + 1)) : Nat) - a).toNat ∧
      w.len = ((read.length : Int) + a + b).toNat := by
  obtain ⟨j, hj, p, a, b, hc, hm, h1, h2, h3, h4, h5⟩ :=
    coverLE g read gbs R hg hr S (read.length / (k + 1)) (by omega) k (Nat.le_refl _) hl2 J hJn hJk hJl w s hs hS
  refine ⟨j, hj, p, a, b, hc, ⟨?_, fun i hi => ?_⟩, h1, h2, h3, h4, h5⟩
  · have := hm.1; have := hoff j; omega
  · have := hm.2 (off j + i) (by have := hoff j; omega)
    rw [show p + off j + i = p + (off j + i) by omega,
      show j * (read.length / (k + 1)) + off j + i = j * (read.length / (k + 1)) + (off j + i) by omega]
    exact this

/-- The offset `d ≤ Ls − q` of block `j` whose seed has the least `size` (first of equals). -/
def blkOff (size : Option UInt64 → Nat) (R : ByteArray) (K : RP) (Ls j : Nat) : Nat :=
  ((List.range (Ls - q + 1)).foldl (fun (a : Nat × Nat) d =>
    let z := size (seedHashK R K (j * Ls + d))
    if z < a.2 then (d, z) else a) (0, size (seedHashK R K (j * Ls)))).1

theorem blkOff_le (size : Option UInt64 → Nat) (R : ByteArray) (K : RP) (Ls j : Nat) :
    blkOff size R K Ls j + q ≤ max Ls q := by
  unfold blkOff
  suffices h : ∀ (l : List Nat) (a : Nat × Nat), a.1 ≤ Ls - q → (∀ d ∈ l, d ≤ Ls - q) →
      (l.foldl (fun (a : Nat × Nat) d =>
        let z := size (seedHashK R K (j * Ls + d))
        if z < a.2 then (d, z) else a) a).1 ≤ Ls - q by
    have := h (List.range (Ls - q + 1)) (0, size (seedHashK R K (j * Ls))) (Nat.zero_le _) (fun d hd => by
      have := List.mem_range.1 hd; omega)
    omega
  intro l
  induction l with
  | nil => intro a ha _; exact ha
  | cons d l ih =>
    intro a ha hl
    simp only [List.foldl_cons]
    apply ih _ _ (fun d' hd' => hl d' (List.mem_cons_of_mem _ hd'))
    split
    · exact hl d (List.mem_cons_self ..)
    · exact ha

end MapSpec.Fast

#print axioms MapSpec.Fast.coverLE_blk
#print axioms MapSpec.Fast.blkOff_le
