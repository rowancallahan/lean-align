import AlignmentWfaOff

/-!
# Layer O, the loop: the corner level determines the optimal score

`wfaLoopO` runs the offsets-only levels and returns the level `L` at
which the corner is first reached.  `wfaLoopO_spec` (an adaptation of
`wfaLoop_opt`'s induction) shows the model's loop reaches its corner
cell at the same step and that this cell's walk has penalty exactly
`L`; `wfaRunO_spec` turns that into the score identity
`2 * score + L = matchScore * (m + n)` for the score `wfaRun` returns.
-/

namespace AlignmentSpec

def wfaLoopO (m n : Nat) (xs ys : List Char) (len pe po px : Nat) :
    Nat → List OLevelW → Nat → Option Nat
  | 0, _, _ => none
  | fuel + 1, hist, p =>
      let lv := nextLevelO m n xs ys len pe po px hist
      if cornerO m n lv then some p
      else wfaLoopO m n xs ys len pe po px fuel
        ((lv :: hist).take (max pe (max po px))) (p + 1)

theorem wfaLoopO_spec (sc : Scoring) (hr : ReasonableScoring sc)
    (hpe1 : 1 ≤ wfaPe sc) (hpx1 : 1 ≤ wfaPx sc) (xs ys : List Char) :
    ∀ (fuel : Nat) (p : Nat) (hist : List WLevel),
      HistOK sc xs ys p hist → HistComplete sc xs ys p hist →
      1 ≤ p →
      hist.length = min p (max (wfaPe sc).toNat
        (max (wfaPo sc).toNat (wfaPx sc).toNat)) →
      (∀ w2, IsMonotoneWalk w2 xs ys →
        (p : Int) ≤ penOf sc w2 xs ys) →
      ∀ L, wfaLoopO xs.length ys.length xs ys (xs.length + ys.length + 1)
        (wfaPe sc).toNat (wfaPo sc).toNat (wfaPx sc).toNat fuel
        (hist.map projL) p = some L →
      ∃ c, wfaLoop xs ys (xs.length + ys.length + 1) ys.length
        (wfaPe sc).toNat (wfaPo sc).toNat (wfaPx sc).toNat fuel hist =
          some c ∧ penOf sc c.walk.reverse xs ys = L := by
  intro fuel
  induction fuel with
  | zero =>
      intro p hist _ _ _ _ _ L h
      simp [wfaLoopO] at h
  | succ fuel ih =>
      intro p hist hh hhc hp1 hwin hinv L h
      have hlv := nextLevel_sound sc hr hpe1 hpx1 xs ys p hist hh
      have hlvC := nextLevel_complete sc hr hpe1 hpx1 xs ys p hist hh
        hhc hp1 hwin
      have hproj := projL_nextLevel sc hr xs ys p (xs.length + ys.length + 1)
        (wfaPe sc).toNat (wfaPo sc).toNat (wfaPx sc).toNat hist hh
      simp only [wfaLoopO] at h
      rw [← hproj] at h
      rw [← cornerOf_iff_cornerO sc xs ys _ _ hlv] at h
      simp only [wfaLoop]
      cases hcorner : cornerOf ys.length
          (nextLevel xs ys (xs.length + ys.length + 1)
            (wfaPe sc).toNat (wfaPo sc).toNat (wfaPx sc).toNat hist)
        with
      | some c0 =>
          rw [hcorner] at h
          simp at h
          subst h
          refine ⟨c0, rfl, ?_⟩
          obtain ⟨hvalid, hpenc⟩ := cornerOf_sound sc xs ys _ _ hlv c0 hcorner
          have := hinv _ hvalid
          omega
      | none =>
          rw [hcorner] at h
          simp only [Option.isSome_none, Bool.false_eq_true, if_false] at h
          have hinv' : ∀ w2, IsMonotoneWalk w2 xs ys →
              ((p + 1 : Nat) : Int) ≤ penOf sc w2 xs ys := by
            intro w2 hw2
            have hge := hinv w2 hw2
            rcases Int.lt_or_le (p : Int) (penOf sc w2 xs ys) with
              hlt | hle
            · omega
            · exfalso
              have hpeq : penOf sc w2 xs ys = (p : Int) := by omega
              obtain ⟨hcM, _, _⟩ := hlvC w2 xs ys [] [] (by simp)
                (by simp) hw2 hpeq
              have ht : ys.length + (xs.length - xs.length) =
                  ys.length := by omega
              rw [ht] at hcM
              obtain ⟨cq, hcq⟩ := cornerOf_of_covered sc xs ys _ _
                hlv hcM
              rw [hcorner] at hcq
              simp at hcq
          have hmap : ((nextLevel xs ys (xs.length + ys.length + 1)
              (wfaPe sc).toNat (wfaPo sc).toNat (wfaPx sc).toNat hist :: hist).take
                (max (wfaPe sc).toNat (max (wfaPo sc).toNat (wfaPx sc).toNat))).map projL =
              (projL (nextLevel xs ys (xs.length + ys.length + 1)
                (wfaPe sc).toNat (wfaPo sc).toNat (wfaPx sc).toNat hist) :: hist.map projL).take
                (max (wfaPe sc).toNat (max (wfaPo sc).toNat (wfaPx sc).toNat)) := by
            rw [List.map_take, List.map_cons]
          rw [← hmap] at h
          exact ih (p + 1)
            ((nextLevel xs ys (xs.length + ys.length + 1)
                (wfaPe sc).toNat (wfaPo sc).toNat (wfaPx sc).toNat
                hist :: hist).take
              (max (wfaPe sc).toNat (max (wfaPo sc).toNat
                (wfaPx sc).toNat)))
            (histOK_take sc xs ys (p + 1) _ _
              (histOK_cons sc xs ys p hist _ hh hlv))
            (histComplete_take sc xs ys (p + 1) _ _
              (histComplete_cons sc xs ys p hist _ hhc hlvC))
            (by omega)
            (by rw [List.length_take, List.length_cons, hwin]; omega)
            hinv' L h

/-- Offsets-only run: the level of the optimum, or `none` on fuel exhaustion. -/
def wfaRunO (sc : Scoring) (xs ys : List Char) : Option Nat :=
  let m := xs.length
  let n := ys.length
  let len := m + n + 1
  let pe := (wfaPe sc).toNat
  let po := (wfaPo sc).toNat
  let px := (wfaPx sc).toNat
  let lv0 := seedO m len xs ys
  if cornerO m n lv0 then some 0
  else wfaLoopO m n xs ys len pe po px ((m + n + 2) * po + 1) [lv0] 1

theorem penOf_eq_score (sc : Scoring) (xs ys : List Char) (w : List Step) :
    penOf sc w xs ys = sc.matchScore * ((xs.length : Int) + ys.length) - 2 * walkScore sc xs ys w := rfl

/-- The model returns a score `s` with `2 s + L = matchScore (m + n)`
whenever the offsets-only run reports level `L`. -/
theorem wfaRunO_spec (sc : Scoring) (hr : ReasonableScoring sc)
    (hpe1 : 1 ≤ wfaPe sc) (hpx1 : 1 ≤ wfaPx sc) (xs ys : List Char) (L : Nat)
    (h : wfaRunO sc xs ys = some L) :
    ∃ w s, wfaRun sc xs ys = some (w, s) ∧
      2 * s + (L : Int) = sc.matchScore * ((xs.length : Int) + ys.length) := by
  have hseed := seedLevel_sound sc xs ys
  have hproj := projL_seedLevel xs.length (xs.length + ys.length + 1) xs ys
  simp only [wfaRunO] at h
  rw [← hproj, ← cornerOf_iff_cornerO sc xs ys _ _ hseed] at h
  simp only [wfaRun]
  cases hc0 : cornerOf ys.length
      (seedLevel xs.length (xs.length + ys.length + 1) xs ys) with
  | some c =>
      rw [hc0] at h
      simp at h
      subst h
      refine ⟨c.walk.reverse, walkScore sc xs ys c.walk.reverse, rfl, ?_⟩
      obtain ⟨hvalid, hpen⟩ := cornerOf_sound sc xs ys 0 _ hseed c hc0
      have hnn := penOf_nonneg sc hr _ xs ys hvalid
      have hz : penOf sc c.walk.reverse xs ys = 0 := by omega
      rw [penOf_eq_score] at hz
      push_cast
      omega
  | none =>
      rw [hc0] at h
      simp only [Option.isSome_none, Bool.false_eq_true, if_false] at h
      obtain ⟨c, hl, hpen⟩ := wfaLoopO_spec sc hr hpe1 hpx1 xs ys _ 1 _
        (histOK_singleton sc xs ys _ hseed)
        (histComplete_singleton sc xs ys _
          (seedLevel_complete sc hr hpe1 hpx1 xs ys))
        (by omega)
        (by simp; omega)
        (by intro w2 hw2
            have hnn := penOf_nonneg sc hr w2 xs ys hw2
            rcases Int.lt_or_le 0 (penOf sc w2 xs ys) with
              hlt | hle
            · omega
            · exfalso
              have hpeq : penOf sc w2 xs ys = 0 := by omega
              obtain ⟨hcM, _, _⟩ := (seedLevel_complete sc hr
                hpe1 hpx1 xs ys) w2 xs ys [] [] (by simp)
                (by simp) hw2 hpeq
              have ht : ys.length + (xs.length - xs.length) =
                  ys.length := by omega
              rw [ht] at hcM
              obtain ⟨cq, hcq⟩ := cornerOf_of_covered sc xs ys 0
                _ hseed hcM
              rw [hc0] at hcq
              simp at hcq)
        L h
      rw [hl]
      refine ⟨c.walk.reverse, walkScore sc xs ys c.walk.reverse, rfl, ?_⟩
      rw [penOf_eq_score] at hpen
      omega

#print axioms wfaRunO_spec

end AlignmentSpec
