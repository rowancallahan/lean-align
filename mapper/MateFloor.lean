import FastGenCoverE
import FastGenPair

/-!
# Mate floors from seeds with no exact copy

The read is cut into `k + 1` blocks of `L = read.length / (k + 1)` letters.  If the first `l`
letters of block `j` occur nowhere in the genome, every window has an edit (mismatch 4, gap ≥ 8
with `sc0`) touching that block, and the event pigeonhole (`exists_clean_seed_amongE`, through
`coverLE`) turns `|J|` such blocks into a penalty of at least `4·|J|`:

    (∀ j ∈ J, block j's first l letters occur in no chromosome) →
      windowScore sc0 read g w = some s → 4·|J| ≤ −s                     (floor_absent)

`floor_look`: the same from lookups in one index over the concatenated genome (`catOk`) that
return no places (`LookOkS`), as the whole-genome mapper's seeds (`l = q = 25`, `L = n / m`).
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

theorem seedBoundE_sc0 (s : Int) : seedBoundE sc0 s = ((-s) / 4).toNat := by
  unfold seedBoundE sc0
  rfl

/-- **Floor from absent blocks.** -/
theorem floor_absent (g : Genome) (read : List Char) (gbs : Array ByteArray) (R : ByteArray)
    (hg : GenomeBytes gbs g) (hr : Encodes R read)
    (l : Nat) (hl0 : 0 < l) (k : Nat) (hk : l ≤ read.length / (k + 1)) (hl2 : 2 ≤ read.length / (k + 1))
    (J : List Nat) (hJn : J.Nodup) (hJk : ∀ j ∈ J, j ≤ k)
    (habs : ∀ j ∈ J, ∀ c p, c < gbs.size → ¬ MatchAtL gbs[c]! p R (j * (read.length / (k + 1))) l)
    (w : Window) (s : Int) (hs : windowScore sc0 read g w = some s) :
    4 * (J.length : Int) ≤ -s := by
  have h0 := windowScore_nonpos read g w s hs
  refine Int.not_lt.mp fun hc => ?_
  have hJl : seedBoundE sc0 s < J.length := by
    rw [seedBoundE_sc0]
    have : (-s) / 4 < (J.length : Int) := by omega
    omega
  obtain ⟨j, hj, p, a, b, hcg, hm, -⟩ :=
    coverLE g read gbs R hg hr s l hl0 k hk hl2 J hJn hJk hJl w s hs (Int.le_refl _)
  exact habs j hj w.chr p hcg hm

/-- A lookup that returns no places: the seed occurs in no chromosome. -/
theorem absent_of_look (G : ByteArray) (offs : Array Nat) (gbs : Array ByteArray)
    (hcat : catOk G offs gbs = true) (R : ByteArray) (s base : Nat) (a : Array Nat)
    (hl : LookOkS G R s base 0 a) (he : a = #[]) :
    ∀ c p, c < gbs.size → ¬ MatchAtL gbs[c]! p R s q := by
  intro c p hc hm
  obtain ⟨hfit, heq⟩ := catOk_spec G offs gbs hcat c hc
  have hM : MatchAt G (offs[c]! + p) R s :=
    ⟨by have := hm.1; omega, fun i hi => by
      rw [Nat.add_assoc, heq _ (by have := hm.1; omega)]; exact hm.2 i hi⟩
  have := (hl.2 ((offs[c]! + p + base) * 16 + 0)).mpr ⟨_, hM, rfl⟩
  rw [he] at this
  simp at this

/-- **Floor from empty lookups** (the whole-genome mapper's seeds: `m = n / 25` blocks of
`n / m` letters, a 25-letter seed at each block start). -/
theorem floor_look {L Pp : Type} [LookG L Pp] (ix : L) (G : ByteArray) (offs : Array Nat)
    (g : Genome) (read : List Char) (gbs : Array ByteArray) (R : ByteArray)
    (hg : GenomeBytes gbs g) (hr : Encodes R read) (hcat : catOk G offs gbs = true)
    (hm : 0 < read.length / 25)
    (J : List Nat) (hJn : J.Nodup) (hJk : ∀ j ∈ J, j < read.length / 25)
    (base : Nat → Nat)
    (hlk : ∀ j ∈ J, LookOkS G R (j * (read.length / (read.length / 25))) (base j) 0
      (LookG.look ix G R (j * (read.length / (read.length / 25))) (base j)
        (LookG.prep ix (seedHashAt R (j * (read.length / (read.length / 25)))))))
    (hempty : ∀ j ∈ J, LookG.look ix G R (j * (read.length / (read.length / 25))) (base j)
        (LookG.prep ix (seedHashAt R (j * (read.length / (read.length / 25))))) = #[])
    (w : Window) (s : Int) (hs : windowScore sc0 read g w = some s) :
    4 * (J.length : Int) ≤ -s := by
  have hk1 : read.length / 25 - 1 + 1 = read.length / 25 := by omega
  have hL : 25 ≤ read.length / (read.length / 25) := by
    rw [Nat.le_div_iff_mul_le hm, Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  refine floor_absent g read gbs R hg hr q (by decide) (read.length / 25 - 1) (by rw [hk1]; exact hL)
    (by rw [hk1]; omega) J hJn (fun j hj => by have := hJk j hj; omega) (fun j hj => ?_) w s hs
  rw [hk1]
  exact absent_of_look G offs gbs hcat R _ (base j) _ (hlk j hj) (hempty j hj)

theorem gapBound_sc0_zero (S : Int) (hS : -8 < S) : gapBound sc0 S = 0 ∧ gapBound2 sc0 S = 0 := by
  unfold gapBound gapBound2 sc0
  exact ⟨Int.toNat_eq_zero.mpr (by simp only [Int.neg_neg]; omega),
    Int.toNat_eq_zero.mpr (by simp only [Int.neg_neg]; omega)⟩

theorem length_filter_split (J : List Nat) (f : Nat → Bool) :
    J.length = (J.filter f).length + (J.filter fun j => !f j).length := by
  induction J with
  | nil => rfl
  | cons a t ih => cases h : f a <;> simp [List.filter_cons, h] <;> omega

open Classical in
/-- **Floor from a completed enumeration.**  Above `−8` every window scoring at least `S` is
gapless (`best_gapless`) and keeps all but `seedBoundE sc0 S` blocks of any `J` exact on its own
diagonal (`coverLE` with no room for a gap).  So if every window of the read's length with that many
exact blocks of `J` has a gapless score below `S` (what an enumeration of those diagonals checks),
every window scores below `S`.  With `sc0`: `S = −3`, all of `J` exact, no window with Hamming 0 →
penalty ≥ 4; `S = −7`, all but one of `J` (`|J| ≥ 2`) exact, no window with Hamming ≤ 1 → penalty ≥ 8. -/
theorem floor_enum (g : Genome) (read : List Char) (gbs : Array ByteArray) (R : ByteArray)
    (hg : GenomeBytes gbs g) (hr : Encodes R read)
    (l : Nat) (hl0 : 0 < l) (k : Nat) (hk : l ≤ read.length / (k + 1)) (hl2 : 2 ≤ read.length / (k + 1))
    (J : List Nat) (hJn : J.Nodup) (hJk : ∀ j ∈ J, j ≤ k)
    (S : Int) (hS8 : -8 < S) (hJl : seedBoundE sc0 S < J.length)
    (hchk : ∀ w : Window, w.chr < gbs.size → w.len = read.length →
      J.length - seedBoundE sc0 S ≤
        (J.filter fun j => decide (MatchAtL gbs[w.chr]! (w.start + j * (read.length / (k + 1))) R
          (j * (read.length / (k + 1))) l)).length →
      ∀ ys, windowSeq g w = some ys → -4 * (MapSpec.hamming read ys : Int) < S)
    (w : Window) (s : Int) (hs : windowScore sc0 read g w = some s) : s < S := by
  refine Int.not_le.mp fun hSs => ?_
  have hs0 := hs
  unfold windowScore at hs
  cases hseq : windowSeq g w with
  | none => rw [hseq] at hs; cases hs
  | some ys =>
    rw [hseq] at hs
    simp only at hs
    cases hbest : getBestAlignment sc0 read ys with
    | none => rw [hbest] at hs; cases hs
    | some best =>
      rw [hbest] at hs
      obtain ⟨path, bs⟩ := best
      have hsb : bs = s := by simpa using hs
      subst hsb
      obtain ⟨hlen, -, hgs⟩ := best_gapless sc0 valid_sc0 read ys path bs hbest
        (by unfold gapCost1 sc0; simp only; omega)
      rw [gaplessScore_match_zero sc0 rfl] at hgs
      -- the window lies in a chromosome and has the read's length
      have hwin : w.chr < gbs.size ∧ w.len = read.length := by
        unfold windowSeq at hseq
        cases hc : g[w.chr]? with
        | none => rw [hc] at hseq; cases hseq
        | some ch =>
          rw [hc] at hseq
          simp only at hseq
          split at hseq
          · have hys : ys = (ch.seq.drop w.start).take w.len := by simpa using hseq.symm
            have hc' : w.chr < g.length := by
              rcases Nat.lt_or_ge w.chr g.length with h | h
              · exact h
              · rw [List.getElem?_eq_none h] at hc; cases hc
            refine ⟨by rw [hg.1]; exact hc', ?_⟩
            rw [hlen, hys, List.length_take, List.length_drop]; omega
          · cases hseq
      generalize hL : read.length / (k + 1) = L at hk hl2 hchk
      -- at most `seedBoundE` blocks of `J` are not exact on the window's diagonal
      have hbad : (J.filter fun j => !decide (MatchAtL gbs[w.chr]! (w.start + j * L) R (j * L) l)).length ≤
          seedBoundE sc0 bs := by
        refine Nat.not_lt.mp fun hlt => ?_
        have hle : seedBoundE sc0 bs ≤ seedBoundE sc0 S := by
          rw [seedBoundE_sc0, seedBoundE_sc0]; omega
        obtain ⟨j, hj, p, a, b, -, hm, hsh, hja, -, hst, -⟩ :=
          coverLE g read gbs R hg hr bs l hl0 k (by rw [hL]; exact hk) (by rw [hL]; exact hl2)
            _ (hJn.filter _) (fun j hj => hJk j (List.mem_filter.mp hj).1) hlt w bs hs0 (Int.le_refl _)
        rw [hL] at hm hja hst
        obtain ⟨g1, g2⟩ := gapBound_sc0_zero bs (by omega)
        rw [g1, g2] at hsh
        have ha : a = 0 := by have := hsh.1; omega
        subst ha
        have hp : p = w.start + j * L := by omega
        rw [List.mem_filter] at hj
        rw [hp] at hm
        simp [hm] at hj
      have hsplit := length_filter_split J
        (fun j => decide (MatchAtL gbs[w.chr]! (w.start + j * L) R (j * L) l))
      have hle : seedBoundE sc0 bs ≤ seedBoundE sc0 S := by
        rw [seedBoundE_sc0, seedBoundE_sc0]; omega
      have := hchk w hwin.1 hwin.2 (by omega) ys hseq
      have hm4 : sc0.mismatchScore = -4 := rfl
      rw [hm4] at hgs
      omega

/-- The pair floor: a pair's penalty is at least the sum of its mates' floors. -/
theorem pair_floor (pA pB fA fB : Nat) (hA : fA ≤ pA) (hB : fB ≤ pB) : fA + fB ≤ pA + pB :=
  Nat.add_le_add hA hB

end MapSpec.Fast

#print axioms MapSpec.Fast.floor_absent
#print axioms MapSpec.Fast.absent_of_look
#print axioms MapSpec.Fast.floor_look
#print axioms MapSpec.Fast.floor_enum
