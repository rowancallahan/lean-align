import FastGenCoverL
import MapperEvents

/-!
Coverage with the event-based pigeonhole (`exists_clean_seed_amongE`): a window
within penalty `P` leaves at most `seedBoundE sc0 (−P) = P / 4` of any chosen
seeds (of at least 2 letters) without a clean copy in the window.
-/

namespace MapSpec

open AlignmentSpec

theorem mem_seedCands_amongE (keep : List Char → Nat × Nat → Bool) (lookup : List Char → List (Nat × Nat))
    (l0 : Nat) (sc : Scoring) (hv : ValidScoring sc) (hO : sc.gapOpen < 0) (S : Int) (g : Genome)
    (hl : LookupComplete g l0 lookup) (hk : KeepComplete g keep)
    (read : List Char) (k d d2 : Nat) (hcond : 0 < l0 ∧ l0 ≤ read.length / (k + 1)) (hl2 : 2 ≤ read.length / (k + 1))
    (hd : gapBound sc S ≤ d) (hd2 : gapBound2 sc S ≤ d2)
    (J : List Nat) (hJn : J.Nodup) (hJk : ∀ j ∈ J, j ≤ k) (hJl : seedBoundE sc S < J.length)
    (w : Window) (s : Int) (hscore : windowScore sc read g w = some s) (hS : S ≤ s) :
    w ∈ J.flatMap (seedCands keep lookup l0 read k d d2) := by
  unfold windowScore at hscore
  cases hseq : windowSeq g w with
  | none => rw [hseq] at hscore; cases hscore
  | some ys =>
    rw [hseq] at hscore
    simp only at hscore
    cases hbest : getBestAlignment sc read ys with
    | none => rw [hbest] at hscore; cases hscore
    | some best =>
      rw [hbest] at hscore
      obtain ⟨path, bs⟩ := best
      have hsb : bs = s := by simpa using hscore
      subst hsb
      obtain ⟨hwalk, hws⟩ := getBestAlignment_returns_a_valid_walk sc read ys path bs hbest
      obtain ⟨j, hjJ, o, ho, hseed, hshape⟩ :=
        exists_clean_seed_amongE sc hv hO S read ys path hwalk (by rw [hws]; exact hS) k hl2 J hJn hJk hJl
      have hj := hJk j hjJ
      have hshape' := shapeOk_mono _ _ _ _ _ _ hshape hd hd2
      unfold windowSeq at hseq
      cases hc : g[w.chr]? with
      | none => rw [hc] at hseq; cases hseq
      | some chromosome =>
        rw [hc] at hseq
        simp only at hseq
        split at hseq
        · next hfit =>
          have hys : ys = (chromosome.seq.drop w.start).take w.len := by
            simpa using hseq.symm
          have hyl : ys.length = w.len := by
            rw [hys, List.length_take, List.length_drop]; omega
          generalize hq : read.length / (k + 1) = q at *
          have hjq : j * q + q ≤ read.length := by
            have h1 : (k + 1) * q ≤ read.length := by
              rw [← hq, Nat.mul_comm]; exact Nat.div_mul_le_self _ _
            have : j * q ≤ k * q := Nat.mul_le_mul_right q hj
            rw [Nat.add_mul] at h1; omega
          have hseedlen : ((read.drop (j * q)).take q).length = q := by
            simp; omega
          have hgen : (chromosome.seq.drop (w.start + o)).take q = (read.drop (j * q)).take q := by
            rw [← hseed, hys, take_drop_window _ _ _ _ _ (by omega)]
          rw [List.mem_flatMap]
          refine ⟨j, hjJ, ?_⟩
          simp only [seedCands, hq]
          rw [List.mem_flatMap]
          refine ⟨(w.chr, w.start + o), ?_, ?_⟩
          · rw [List.mem_filter]
            constructor
            · have hkey : ((read.drop (j * q)).take q).take l0 =
                  (chromosome.seq.drop (w.start + o)).take l0 := by
                rw [← hgen, List.take_take, Nat.min_eq_left hcond.2]
              rw [hkey]
              exact hl w.chr chromosome (w.start + o) hc (by omega)
            · exact hk w.chr chromosome (w.start + o) _ hc (by rw [hseedlen]; omega)
                (by rw [hseedlen]; exact hgen)
          · rw [List.mem_filterMap]
            refine ⟨_, mem_shapes _ _ _ _ hshape', ?_⟩
            rw [if_pos (by constructor <;> omega)]
            cases w
            simp only [Option.some.injEq, Window.mk.injEq] at *
            refine ⟨trivial, by omega, by omega⟩
        · cases hseq

end MapSpec

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-- **Coverage**, events counted (`seedBoundE`), seeds of at least 2 letters. -/
theorem coverLE (g : Genome) (read : List Char) (gbs : Array ByteArray) (R : ByteArray)
    (hg : GenomeBytes gbs g) (hr : Encodes R read) (S : Int)
    (l : Nat) (hl0 : 0 < l) (k : Nat) (hk : l ≤ read.length / (k + 1)) (hl2 : 2 ≤ read.length / (k + 1))
    (J : List Nat) (hJn : J.Nodup) (hJk : ∀ j ∈ J, j ≤ k) (hJl : seedBoundE sc0 S < J.length)
    (w : Window) (s : Int) (hs : windowScore sc0 read g w = some s) (hS : S ≤ s) :
    ∃ j ∈ J, ∃ (p : Nat) (a b : Int), w.chr < gbs.size ∧
      MatchAtL gbs[w.chr]! p R (j * (read.length / (k + 1))) l ∧
      shapeOk (gapBound sc0 S) (gapBound2 sc0 S) a b ∧
      ((j * (read.length / (k + 1)) : Nat) : Int) + a ≤ p ∧ 0 ≤ (read.length : Int) + a + b ∧
      w.start = ((p : Int) - (j * (read.length / (k + 1)) : Nat) - a).toNat ∧
      w.len = ((read.length : Int) + a + b).toNat := by
  have hm := mem_seedCands_amongE (fun _ _ => true) (scanLookup g l) l sc0 valid_sc0 (by decide) S g
    (scanLookup_complete g l) (keepAll_complete g) read k (gapBound sc0 S) (gapBound2 sc0 S)
    ⟨hl0, hk⟩ hl2 (Nat.le_refl _) (Nat.le_refl _) J hJn hJk hJl w s hs hS
  rw [List.mem_flatMap] at hm
  obtain ⟨j, hj, hw⟩ := hm
  unfold seedCands at hw
  simp only [List.mem_filter, List.mem_flatMap, List.mem_filterMap, Option.ite_none_right_eq_some,
    Option.some.injEq] at hw
  obtain ⟨⟨c, p⟩, ⟨hplace, -⟩, st, hst, ⟨h1, h2⟩, rfl⟩ := hw
  obtain ⟨ch, hch, hword⟩ := scanLookup_sound g l _ c p hplace
  clear hs hplace
  dsimp only at h1 ⊢
  generalize hL : read.length / (k + 1) = L at hk hword h1 ⊢
  have hjk := hJk j hj
  have hjL : j * L + L ≤ read.length := by
    have := Nat.div_mul_le_self read.length (k + 1)
    rw [hL] at this
    have : j * L + L ≤ (k + 1) * L := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
    have h3 : (k + 1) * L = L * (k + 1) := Nat.mul_comm _ _
    omega
  have hc : c < g.length := by
    rcases Nat.lt_or_ge c g.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hch; cases hch
  have hch' : g[c] = ch := by rw [List.getElem?_eq_getElem hc] at hch; cases hch; rfl
  have hcg : c < gbs.size := by rw [hg.1]; exact hc
  have henc := hg.2 c hcg hc
  rw [hch'] at henc
  have hlen : ((read.drop (j * L)).take L).take l = (read.drop (j * L)).take l := by
    rw [List.take_take, Nat.min_eq_left (by omega)]
  rw [hlen] at hword
  have hwl : ((ch.seq.drop p).take l).length = l := by
    rw [hword, List.length_take, List.length_drop]; omega
  have hfit : p + l ≤ ch.seq.length := by
    rw [List.length_take, List.length_drop] at hwl; omega
  refine ⟨j, hj, p, st.1, st.2, hcg, ⟨?_, fun i hi => ?_⟩, shapes_ok _ _ st hst, h1, h2, rfl, rfl⟩
  · rw [getElem!_pos gbs c hcg, henc.1]; exact hfit
  · rw [getElem!_pos gbs c hcg]
    have e1 : ((ch.seq.drop p).take l)[i]'(by rw [hwl]; exact hi) = ch.seq[p + i]'(by omega) := by simp
    have e2 : ((read.drop (j * L)).take l)[i]'(by simp; omega) = read[j * L + i]'(by omega) := by simp
    have he : ch.seq[p + i]'(by omega) = read[j * L + i]'(by omega) := by
      rw [← e1, ← e2]; congr 1
    apply UInt8.toNat_inj.mp
    rw [henc.2 (p + i) (by omega), hr.2 (j * L + i) (by omega), he]

end MapSpec.Fast

#print axioms MapSpec.Fast.coverLE
