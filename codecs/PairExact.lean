import PairNear
import PairGuarFast

/-!
# `pairGXE`: the best proper pair at pair score `≥ −Gc`, `Gc ≤ 16` (gapped mates)

One mate (`swap`: mate 2) is enumerated within `Gc` (`hitsKPF`, exact for `Gc ≤ 16`), the other
only near its hits (`hitsKPFN`, `NearOk`); the proper pairs at pair score `≥ −Gc` and their unique
best (`bestOfPairs`).  A pair at score `≥ −Gc` has both mates within `Gc` (scores ≤ 0, distance cost
≥ 0), so these are all such proper pairs at any caps `≥ Gc` (`pairGXE_sound`, the statement of
`pairGF_sound`).  Runs only when both mates are on the fast path at `Gc` (`fastT`), so neither list
falls back to the specification.
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-- **The exact pair search at `Gc`**: `(best, a proper pair at score ≥ −Gc seen)`; `none` when a
mate is too short for `Gc` (`fastT`). -/
def pairGXE {L Pp : Type} [LookG L Pp] [Inhabited Pp] (dc : Nat → Nat) (sl lo hi Gc : Nat) (swap : Bool)
    (ix : L) (offs : Array Nat) (pgs : Array PGen) (R1 R2 : ByteArray) : Option (Option PairHit × Bool) :=
  let RX := if swap then R2 else R1
  let RY := if swap then R1 else R2
  if fastT Gc RX && fastT Gc RY then
    let lX := hitsKPF ix ByteArray.empty offs pgs RX Gc
    let lY := hitsKPFN sl hi ix ByteArray.empty offs pgs RY Gc lX
    let ps := (properPairsF sl lo hi (if swap then lY else lX) (if swap then lX else lY)).filter
      fun p => decide (-(Gc : Int) ≤ pairScoreD dc p)
    some (bestOfPairs dc ps, !ps.isEmpty)
  else none

theorem pairGXE_some {L Pp : Type} [LookG L Pp] [Inhabited Pp] (dc : Nat → Nat) (sl lo hi Gc : Nat)
    (swap : Bool) (ix : L) (offs : Array Nat) (pgs : Array PGen) (R1 R2 : ByteArray)
    (h1 : fastT Gc R1 = true) (h2 : fastT Gc R2 = true) :
    ∃ v, pairGXE dc sl lo hi Gc swap ix offs pgs R1 R2 = some v := by
  unfold pairGXE
  cases swap <;> simp [h1, h2]

/-- Within a pair score `≥ −Gc`, a mate's hit within `Gc` is a hit at any cap `P ≥ Gc`. -/
theorem hitsBoth_capped {g : Genome} {m : List Char} {Gc P : Nat} (hP : Gc ≤ P) (x : Placement × Int)
    (hx : -(Gc : Int) ≤ x.2) : x ∈ hitsBoth sc0 (-(Gc : Int)) g m ↔ x ∈ hitsBoth sc0 (-(P : Int)) g m := by
  obtain ⟨p, s⟩ := x
  rw [mem_hitsBoth_T, mem_hitsBoth_T]
  simp only at hx
  constructor
  · rintro ⟨a, b, -⟩; exact ⟨a, b, by omega⟩
  · rintro ⟨a, b, -⟩; exact ⟨a, b, hx⟩

section top
variable (dc : Nat → Nat) (sl lo hi Gc : Nat) (g : Genome) (m1 m2 : List Char) (ix : Mz.MzIdx) (G : PGen)
  (offs ns : Array Nat) (R1 R2 : ByteArray)
  (hcut : cutOk G offs ns = true) (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) g)
  (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hchk : Mz.check2P ix G = true)

include hcut hg h1 h2 hchk in
/-- **The exact pair search is the specification** (`Gc ≤ 16`, any caps `P1, P2 ≥ Gc`): a pair is
seen iff some proper pair has pair score `≥ −Gc`; then the answer is `pairSpecUT`, and `none` is a
pair-level tie. -/
theorem pairGXE_sound (hG : Gc ≤ 16) (swap : Bool) (P1 P2 : Nat) (hP1 : Gc ≤ P1) (hP2 : Gc ≤ P2)
    (r : Option PairHit) (seen : Bool)
    (h : pairGXE dc sl lo hi Gc swap ((ix, G) : PkMz) offs (cutAll G offs ns) R1 R2 = some (r, seen)) :
    (seen = true ↔ ∃ w ∈ properPairs sl lo hi (hitsBoth sc0 (-(P1 : Int)) g m1) (hitsBoth sc0 (-(P2 : Int)) g m2),
      -(Gc : Int) ≤ pairScoreD dc w) ∧
    (seen = true → r = pairSpecUT sc0 dc sl lo hi (-(P1 : Int)) (-(P2 : Int)) g m1 m2) ∧
    (seen = true → r = none → PairTieOk dc sl lo hi (-(P1 : Int)) (-(P2 : Int)) g m1 m2) := by
  unfold pairGXE at h
  by_cases hf : (fastT Gc (if swap then R2 else R1) && fastT Gc (if swap then R1 else R2)) = true
  · rw [if_pos hf] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    -- the two hit lists, as the mates' hits within `Gc`
    have K1 := hitsKPF_mem g ix G offs ns hcut hg hchk R1 m1 h1 Gc hG
    have K2 := hitsKPF_mem g ix G offs ns hcut hg hchk R2 m2 h2 Gc hG
    have hpp : ∀ p, p ∈ properPairsF sl lo hi
        (if swap then hitsKPFN sl hi ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) (if swap then R1 else R2) Gc
          (hitsKPF ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) (if swap then R2 else R1) Gc)
         else hitsKPF ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) (if swap then R2 else R1) Gc)
        (if swap then hitsKPF ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) (if swap then R2 else R1) Gc
         else hitsKPFN sl hi ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) (if swap then R1 else R2) Gc
          (hitsKPF ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) (if swap then R2 else R1) Gc)) ↔
        p ∈ properPairs sl lo hi (hitsKPF ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) R1 Gc)
          (hitsKPF ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) R2 Gc) := by
      intro p
      rw [properPairsF_eq]
      cases swap
      · exact pp_near_right (hitsKPFN_near sl lo hi _ _ _ _ _ Gc _) p
      · exact pp_near_left (hitsKPFN_near sl lo hi _ _ _ _ _ Gc _) p
    generalize hps : List.filter _ _ = ps
    have HP : ∀ p, p ∈ ps ↔ p ∈ properPairs sl lo hi (hitsBoth sc0 (-(P1 : Int)) g m1)
        (hitsBoth sc0 (-(P2 : Int)) g m2) ∧ -(Gc : Int) ≤ pairScoreD dc p := by
      intro p
      rw [← hps, List.mem_filter, hpp, decide_eq_true_eq, mem_properPairs, mem_properPairs, K1, K2]
      obtain ⟨x, y⟩ := p
      simp only
      constructor
      · rintro ⟨⟨hx, hy, hp⟩, hs⟩
        have nx := hitsBoth_nonpos _ _ _ _ hx
        have ny := hitsBoth_nonpos _ _ _ _ hy
        have hd : (0 : Int) ≤ (dc (fragLen x.1 y.1) : Int) := Int.natCast_nonneg _
        unfold pairScoreD at hs
        simp only at hs
        exact ⟨⟨(hitsBoth_capped hP1 x (by omega)).mp hx, (hitsBoth_capped hP2 y (by omega)).mp hy, hp⟩, hs⟩
      · rintro ⟨⟨hx, hy, hp⟩, hs⟩
        have nx := hitsBoth_nonpos _ _ _ _ hx
        have ny := hitsBoth_nonpos _ _ _ _ hy
        have hd : (0 : Int) ≤ (dc (fragLen x.1 y.1) : Int) := Int.natCast_nonneg _
        unfold pairScoreD at hs
        simp only at hs
        exact ⟨⟨(hitsBoth_capped hP1 x (by omega)).mpr hx, (hitsBoth_capped hP2 y (by omega)).mpr hy, hp⟩, hs⟩
    have hseen : (!ps.isEmpty) = true ↔
        ∃ w ∈ properPairs sl lo hi (hitsBoth sc0 (-(P1 : Int)) g m1) (hitsBoth sc0 (-(P2 : Int)) g m2),
          -(Gc : Int) ≤ pairScoreD dc w := by
      rw [Bool.not_eq_true', List.isEmpty_eq_false_iff_exists_mem]
      constructor
      · rintro ⟨w, hw⟩; exact ⟨w, ((HP w).1 hw).1, ((HP w).1 hw).2⟩
      · rintro ⟨w, hw, hs⟩; exact ⟨w, (HP w).2 ⟨hw, hs⟩⟩
    have hbest : (!ps.isEmpty) = true → bestOfPairs dc ps = pairSpecUT sc0 dc sl lo hi (-(P1 : Int)) (-(P2 : Int)) g m1 m2 := by
      intro hs
      rw [Bool.not_eq_true', List.isEmpty_eq_false_iff_exists_mem] at hs
      obtain ⟨w, hw⟩ := hs
      exact bestOfPairs_restrict dc sl lo hi _ _ (hitsBoth_scoreFun _ _ _ _) (hitsBoth_scoreFun _ _ _ _) _ _ HP
        (List.ne_nil_of_mem hw)
    refine ⟨hseen, hbest, fun hs hn => ⟨?_, ?_⟩⟩
    · rw [← hbest hs]; exact hn
    · obtain ⟨w, hw, -⟩ := hseen.1 hs; exact ⟨w, hw⟩
  · rw [if_neg hf] at h; cases h

end top

end MapSpec.Fast

#print axioms MapSpec.Fast.pairGXE_sound
