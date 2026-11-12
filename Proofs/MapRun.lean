import Proofs.MapProcess
import Proofs.MapPending
import Proofs.MapJobs
/-! # The stream (`MapFast.step`) against `mapReads`: invariant, a successful step, a failing step, the end. -/
namespace Spec.FQ.MapStream
open Spec Spec.MapFast Spec.MapCopy Spec.MapCopy.Jobs

/-! ## List helpers -/

theorem mapM_id_some {α : Type} : ∀ (xs : List (Option α)) (ps : List α), xs.mapM id = some ps ↔ xs = ps.map some
  | [], ps => by
    simp only [List.mapM_nil]
    constructor
    · intro h; have := Option.some.inj h; subst this; rfl
    · intro h; cases ps with
      | nil => rfl
      | cons p ps => simp at h
  | x :: xs, ps => by
    rw [List.mapM_cons]
    cases x with
    | none => cases ps <;> simp
    | some a =>
      cases hr : xs.mapM id with
      | none =>
        simp only [id, Option.bind_some, Option.bind_none]
        constructor
        · intro h; cases h
        · intro h
          cases ps with
          | nil => simp at h
          | cons p ps =>
            simp only [List.map_cons, List.cons.injEq] at h
            have := (mapM_id_some xs ps).2 h.2
            rw [hr] at this; cases this
      | some qs =>
        have := (mapM_id_some xs qs).1 hr
        simp only [id, Option.bind_some, pure]
        constructor
        · intro h
          have h' := Option.some.inj h
          subst h'; simp [this]
        · intro h
          cases ps with
          | nil => simp at h
          | cons p ps =>
            simp only [List.map_cons, List.cons.injEq, Option.some.injEq] at h
            obtain ⟨rfl, h2⟩ := h
            have := (mapM_id_some xs ps).2 h2
            rw [hr] at this
            have := Option.some.inj this
            subst this; rfl

theorem mapM_id_append {α : Type} (xs ys : List (Option α)) :
    (xs ++ ys).mapM id = (xs.mapM id).bind fun a => (ys.mapM id).map (a ++ ·) := by
  induction xs with
  | nil => cases h : ys.mapM id <;> simp [h]
  | cons x xs ih =>
    rw [List.cons_append, List.mapM_cons, List.mapM_cons, ih]
    cases x with
    | none => simp
    | some a =>
      cases hx : xs.mapM id with
      | none => simp
      | some ys' => cases hy : ys.mapM id <;> simp

/-! ## The jobs add up -/

theorem chain (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList) :
    ∀ (SP : List (List UInt8 × List UInt8)), (∀ p ∈ SP, IsSlice need p.1 ∧ IsSlice need p.2) → ∀ R1 R2 : List UInt8,
    mapReads settings index chrs ((SP.map (·.1)).flatten ++ R1) ((SP.map (·.2)).flatten ++ R2) =
      ((SP.map fun p => mapReads settings index chrs p.1 p.2).mapM id).bind fun os =>
        (mapReads settings index chrs R1 R2).map (os.flatten ++ ·)
  | [], _, R1, R2 => by
    cases h : mapReads settings index chrs R1 R2 <;> simp [h]
  | (a, b) :: SP, hSP, R1, R2 => by
    obtain ⟨ha, hb⟩ := hSP (a, b) (by simp)
    have ih := chain settings index chrs SP (fun p hp => hSP p (List.mem_cons_of_mem _ hp)) R1 R2
    have hcut := mapReads_cut settings index chrs jobPairs (a ++ ((SP.map (·.1)).flatten ++ R1))
      (b ++ ((SP.map (·.2)).flatten ++ R2)) a ((SP.map (·.1)).flatten ++ R1) b ((SP.map (·.2)).flatten ++ R2)
      (by simpa [need, IsSlice] using cutLines_extend _ a a [] ((SP.map (·.1)).flatten ++ R1) ha)
      (by simpa [need, IsSlice] using cutLines_extend _ b b [] ((SP.map (·.2)).flatten ++ R2) hb)
    simp only [List.map_cons, List.flatten_cons, List.append_assoc]
    rw [hcut, ih, List.mapM_cons]
    cases hx : mapReads settings index chrs a b with
    | none => simp
    | some o =>
      cases hm : (SP.map fun p => mapReads settings index chrs p.1 p.2).mapM id with
      | none => simp
      | some os => cases hr : mapReads settings index chrs R1 R2 <;> simp [List.append_assoc]

/-! ## The invariant -/

abbrev bl (b : ByteArray) : List UInt8 := b.data.toList

-- what a state says about the bytes read so far (`F1`, `F2`) and the lines written (`W`); `spec` is `mapReads`
def InvG (spec : List UInt8 → List UInt8 → Option (List UInt8)) (job : ByteArray → ByteArray → Option ByteArray)
    (st : State) (W F1 F2 : List UInt8) : Prop :=
  ∃ (SP : List (List UInt8 × List UInt8)) (K : Nat) (pieces : List (List UInt8)),
    st.job = job ∧ ScanOk st.file1 ∧ ScanOk st.file2 ∧
    (∀ p ∈ SP, IsSlice need p.1 ∧ IsSlice need p.2) ∧
    (∀ s ∈ st.queue1.toList.map bl, IsSlice need s) ∧ (∀ s ∈ st.queue2.toList.map bl, IsSlice need s) ∧
    F1 = (SP.map (·.1)).flatten ++ (st.queue1.toList.map bl).flatten ++ bl st.file1.carry ∧
    F2 = (SP.map (·.2)).flatten ++ (st.queue2.toList.map bl).flatten ++ bl st.file2.carry ∧
    (st.queue1.size = 0 ∨ st.queue2.size = 0) ∧
    K ≤ SP.length ∧ (SP.take K).map (fun p => spec p.1 p.2) = pieces.map some ∧ W = pieces.flatten ∧
    vals st.pending = (SP.drop K).map (fun p => spec p.1 p.2)

def FInv (spec : List UInt8 → List UInt8 → Option (List UInt8)) (job : ByteArray → ByteArray → Option ByteArray)
    (st : State) (W F1 F2 : List UInt8) : Prop :=
  InvG spec job st W F1 F2 ∧ st.pending.size ≤ inFlight

theorem finv_init (spec : List UInt8 → List UInt8 → Option (List UInt8)) (job : ByteArray → ByteArray → Option ByteArray) :
    FInv spec job (init job) [] [] [] := by
  refine ⟨⟨[], 0, [], rfl, ⟨by simp [init], by simp [init], by simp [init, need]; unfold jobPairs; omega⟩,
    ⟨by simp [init], by simp [init], by simp [init, need]; unfold jobPairs; omega⟩, by simp, by simp [init], by simp [init],
    by simp [init], by simp [init], Or.inl (by simp [init]), by simp, by simp, by simp, by simp [vals, init]⟩, by simp [init]⟩

/-! ## One step: append, cut, spawn (before `collect`) -/

theorem range_getElem (A : Array ByteArray) : ∀ n, n ≤ A.size → (List.range n).map (fun k => bl A[k]!) = (A.toList.map bl).take n
  | 0, _ => by simp
  | n + 1, h => by
    rw [List.range_succ, List.map_append, range_getElem A n (by omega)]
    have hn : n < A.size := by omega
    have : (A.toList.map bl).take (n + 1) = (A.toList.map bl).take n ++ [bl A[n]!] := by
      rw [List.take_succ]
      have : (A.toList.map bl)[n]? = some (bl A[n]!) := by
        rw [List.getElem?_map, List.getElem?_eq_getElem (by simpa using hn)]
        simp [getElem!_pos A n hn]
      rw [this]; rfl
    rw [this]; rfl

theorem spawn_inv (spec : List UInt8 → List UInt8 → Option (List UInt8)) (job : ByteArray → ByteArray → Option ByteArray)
    (hjob : ∀ a b, (job a b).map bl = spec (bl a) (bl b)) (st : State) (W F1 F2 : List UInt8) (a b : ByteArray)
    (hI : InvG spec job st W F1 F2) :
    let q1 := st.queue1 ++ (cutSlices st.file1 a).2
    let q2 := st.queue2 ++ (cutSlices st.file2 b).2
    let n := min q1.size q2.size
    InvG spec job ⟨st.job, (cutSlices st.file1 a).1, (cutSlices st.file2 b).1, q1.extract n q1.size, q2.extract n q2.size,
      spawnPaired st.job q1 q2 st.pending⟩ W (F1 ++ bl a) (F2 ++ bl b) := by
  intro q1 q2 n
  obtain ⟨SP, K, pieces, hj, ok1, ok2, hSP, hq1, hq2, hF1, hF2, hqs, hK, hpieces, hW, hvals⟩ := hI
  obtain ⟨ss1, hss1, hcs1, hcar1, hcnt1, hok1'⟩ := cutSlices_spec st.file1 a ok1
  obtain ⟨ss2, hss2, hcs2, hcar2, hcnt2, hok2'⟩ := cutSlices_spec st.file2 b ok2
  have hQ1 : q1.toList.map bl = st.queue1.toList.map bl ++ ss1 := by simp [q1, Array.toList_append, hcs1.symm]
  have hQ2 : q2.toList.map bl = st.queue2.toList.map bl ++ ss2 := by simp [q2, Array.toList_append, hcs2.symm]
  have hn1 : n ≤ q1.size := Nat.min_le_left _ _
  have hn2 : n ≤ q2.size := Nat.min_le_right _ _
  have hmap1 := range_getElem q1 n hn1
  have hmap2 := range_getElem q2 n hn2
  have hall1 : ∀ s ∈ q1.toList.map bl, IsSlice need s := by
    rw [hQ1]; intro s hs
    rcases List.mem_append.1 hs with h | h
    · exact hq1 s h
    · exact hss1 s h
  have hall2 : ∀ s ∈ q2.toList.map bl, IsSlice need s := by
    rw [hQ2]; intro s hs
    rcases List.mem_append.1 hs with h | h
    · exact hq2 s h
    · exact hss2 s h
  have hex1 : (q1.extract n q1.size).toList.map bl = (q1.toList.map bl).drop n := by
    rw [Array.toList_extract, List.extract_eq_drop_take, List.map_take, List.map_drop,
      List.take_of_length_le (by simp)]
  have hex2 : (q2.extract n q2.size).toList.map bl = (q2.toList.map bl).drop n := by
    rw [Array.toList_extract, List.extract_eq_drop_take, List.map_take, List.map_drop,
      List.take_of_length_le (by simp)]
  refine ⟨SP ++ (List.range n).map (fun k => (bl q1[k]!, bl q2[k]!)), K, pieces, hj, hok1', hok2', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hW, ?_⟩
  -- 1: the jobs' slices
  · intro p hp
    rcases List.mem_append.1 hp with h | h
    · exact hSP p h
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 h
      have m1 : bl q1[k]! ∈ q1.toList.map bl := by
        have := List.mem_map_of_mem (f := fun k => bl q1[k]!) hk
        rw [hmap1] at this; exact List.mem_of_mem_take this
      have m2 : bl q2[k]! ∈ q2.toList.map bl := by
        have := List.mem_map_of_mem (f := fun k => bl q2[k]!) hk
        rw [hmap2] at this; exact List.mem_of_mem_take this
      exact ⟨hall1 _ m1, hall2 _ m2⟩
  -- 2, 3: the queues
  · intro s hs; simp only [] at hs; rw [hex1] at hs; exact hall1 s (List.mem_of_mem_drop hs)
  · intro s hs; simp only [] at hs; rw [hex2] at hs; exact hall2 s (List.mem_of_mem_drop hs)
  -- 4, 5: the bytes
  · simp only [List.map_append, List.flatten_append, List.map_map, Function.comp_def]
    rw [hex1]
    have e : (List.map (fun k => bl q1[k]!) (List.range n)).flatten = ((q1.toList.map bl).take n).flatten := by rw [hmap1]
    rw [e]
    have hc : bl st.file1.carry ++ bl a = ss1.flatten ++ bl (cutSlices st.file1 a).1.carry := hcar1
    have hQf : (q1.toList.map bl).flatten = (st.queue1.toList.map bl).flatten ++ ss1.flatten := by rw [hQ1, List.flatten_append]
    have hsplit : (q1.toList.map bl).flatten = ((q1.toList.map bl).take n).flatten ++ ((q1.toList.map bl).drop n).flatten := by
      rw [← List.flatten_append, List.take_append_drop]
    rw [hF1]
    simp only [List.append_assoc]
    congr 1
    rw [hc, ← List.append_assoc, ← hQf, hsplit, List.append_assoc]
  · simp only [List.map_append, List.flatten_append, List.map_map, Function.comp_def]
    rw [hex2]
    have e : (List.map (fun k => bl q2[k]!) (List.range n)).flatten = ((q2.toList.map bl).take n).flatten := by rw [hmap2]
    rw [e]
    have hc : bl st.file2.carry ++ bl b = ss2.flatten ++ bl (cutSlices st.file2 b).1.carry := hcar2
    have hQf : (q2.toList.map bl).flatten = (st.queue2.toList.map bl).flatten ++ ss2.flatten := by rw [hQ2, List.flatten_append]
    have hsplit : (q2.toList.map bl).flatten = ((q2.toList.map bl).take n).flatten ++ ((q2.toList.map bl).drop n).flatten := by
      rw [← List.flatten_append, List.take_append_drop]
    rw [hF2]
    generalize bl (cutSlices st.file2 b).1.carry = c' at hc ⊢
    simp only [List.append_assoc]
    refine congrArg ((List.map (fun x => x.snd) SP).flatten ++ ·) ?_
    rw [hc, ← List.append_assoc, ← hQf, hsplit, List.append_assoc]
  · simp only [Array.size_extract]
    omega
  · simp only [List.length_append]; omega
  · rw [List.take_append_of_le_length hK]; exact hpieces
  · rw [spawnPaired_vals, hvals, List.drop_append_of_le_length hK, List.map_append, List.map_map]
    refine congrArg (_ ++ ·) ?_
    apply List.map_congr_left
    intro k hk
    show Option.map bl (st.job q1[k]! q2[k]!) = spec (bl q1[k]!) (bl q2[k]!)
    rw [hj]; exact hjob _ _

/-! ## `collect` -/

theorem collect_inv (spec : List UInt8 → List UInt8 → Option (List UInt8)) (job : ByteArray → ByteArray → Option ByteArray)
    (st : State) (W F1 F2 : List UInt8) (keep : Nat) (pd : Array (Task (Option ByteArray))) (o : ByteArray)
    (hI : InvG spec job st W F1 F2) (h : collect keep st.pending ByteArray.empty = some (pd, o)) :
    InvG spec job { st with pending := pd } (W ++ bl o) F1 F2 ∧ pd.size ≤ keep := by
  have hv := collect_vals keep st.pending ByteArray.empty
  rw [h] at hv
  simp only [Option.map_some] at hv
  obtain ⟨SP, K, pieces, hj, ok1, ok2, hSP, hq1, hq2, hF1, hF2, hqs, hK, hpieces, hW, hvals⟩ := hI
  unfold collectL at hv
  rw [hvals] at hv
  have hlen : ((SP.drop K).map fun p => spec p.1 p.2).length = SP.length - K := by simp
  cases hm : (List.take (((SP.drop K).map fun p => spec p.1 p.2).length - keep)
      ((SP.drop K).map fun p => spec p.1 p.2)).mapM id with
  | none => rw [hm] at hv; simp at hv
  | some ps =>
    rw [hm] at hv
    simp only [Option.some.injEq, Prod.mk.injEq] at hv
    obtain ⟨hpd, ho⟩ := hv
    generalize ht : ((SP.drop K).map fun p => spec p.1 p.2).length - keep = t at hm hpd
    have hps := (mapM_id_some _ _).1 hm
    have htl : t ≤ SP.length - K := by omega
    refine ⟨⟨SP, K + t, pieces ++ ps, hj, ok1, ok2, hSP, hq1, hq2, hF1, hF2, hqs, by omega, ?_, ?_, ?_⟩, ?_⟩
    · rw [List.take_add, List.map_append, hpieces, List.map_take, hps, List.map_append]
    · have ho' : bl o = ps.flatten := by simpa [bl] using ho
      rw [hW, ho']; simp
    · simp only []
      rw [hpd, ← List.map_drop, List.drop_drop, Nat.add_comm]
    · have : pd.size = (vals pd).length := by simp [vals]
      rw [this, hpd]; simp; omega

-- if some result that `collect` would take is none, the files (whatever follows) are not valid
theorem failing_job (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList)
    (job : ByteArray → ByteArray → Option ByteArray) (st : State) (W F1 F2 : List UInt8) (keep : Nat)
    (hI : InvG (mapReads settings index chrs) job st W F1 F2) (h : collect keep st.pending ByteArray.empty = none)
    (T1 T2 : List UInt8) : mapReads settings index chrs (F1 ++ T1) (F2 ++ T2) = none := by
  have hv := collect_vals keep st.pending ByteArray.empty
  rw [h] at hv
  simp only [Option.map_none] at hv
  obtain ⟨SP, K, pieces, hj, ok1, ok2, hSP, hq1, hq2, hF1, hF2, hqs, hK, hpieces, hW, hvals⟩ := hI
  unfold collectL at hv
  cases hm : (List.take ((vals st.pending).length - keep) (vals st.pending)).mapM id with
  | some ps => rw [hm] at hv; simp at hv
  | none =>
    rw [hF1, hF2]
    simp only [List.append_assoc]
    rw [chain settings index chrs SP hSP]
    have hmap : SP.map (fun p => mapReads settings index chrs p.1 p.2) = pieces.map some ++ vals st.pending := by
      rw [← List.take_append_drop K SP, List.map_append, hpieces, ← hvals]
    have : (SP.map fun p => mapReads settings index chrs p.1 p.2).mapM id = none := by
      rw [hmap, mapM_id_append, (mapM_id_some _ _).2 rfl]
      simp only [Option.bind_some]
      rw [← List.take_append_drop ((vals st.pending).length - keep) (vals st.pending), mapM_id_append, hm]
      simp
    rw [this]; rfl

/-! ## `step` -/

theorem step_some_inv (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList)
    (job : ByteArray → ByteArray → Option ByteArray)
    (hjob : ∀ a b, (job a b).map bl = mapReads settings index chrs (bl a) (bl b))
    (st st' : State) (W F1 F2 : List UInt8) (a b out : ByteArray)
    (hI : FInv (mapReads settings index chrs) job st W F1 F2) (h : MapFast.step st (some (a, b)) = some (st', out)) :
    FInv (mapReads settings index chrs) job st' (W ++ bl out) (F1 ++ bl a) (F2 ++ bl b) := by
  have hmid := spawn_inv (mapReads settings index chrs) job hjob st W F1 F2 a b hI.1
  obtain ⟨jb, f1, f2, q1, q2, pend⟩ := st
  simp only [MapFast.step] at h
  cases hc : collect inFlight (spawnPaired jb (q1 ++ (cutSlices f1 a).2) (q2 ++ (cutSlices f2 b).2) pend) ByteArray.empty with
  | none => rw [hc] at h; simp at h
  | some r =>
    obtain ⟨pd, o⟩ := r
    rw [hc] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact collect_inv (mapReads settings index chrs) job _ _ _ _ inFlight pd o hmid hc

theorem step_some_fail (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList)
    (job : ByteArray → ByteArray → Option ByteArray)
    (hjob : ∀ a b, (job a b).map bl = mapReads settings index chrs (bl a) (bl b))
    (st : State) (W F1 F2 : List UInt8) (a b : ByteArray)
    (hI : FInv (mapReads settings index chrs) job st W F1 F2) (h : MapFast.step st (some (a, b)) = none) (T1 T2 : List UInt8) :
    mapReads settings index chrs (F1 ++ bl a ++ T1) (F2 ++ bl b ++ T2) = none := by
  have hmid := spawn_inv (mapReads settings index chrs) job hjob st W F1 F2 a b hI.1
  obtain ⟨jb, f1, f2, q1, q2, pend⟩ := st
  simp only [MapFast.step] at h
  cases hc : collect inFlight (spawnPaired jb (q1 ++ (cutSlices f1 a).2) (q2 ++ (cutSlices f2 b).2) pend) ByteArray.empty with
  | none => exact failing_job settings index chrs job _ _ _ _ inFlight hmid hc T1 T2
  | some r => rw [hc] at h; simp at h

/-! ## The end: pair what is left, then one last job -/

theorem pair_inv (spec : List UInt8 → List UInt8 → Option (List UInt8)) (job : ByteArray → ByteArray → Option ByteArray)
    (hjob : ∀ a b, (job a b).map bl = spec (bl a) (bl b)) (st : State) (W F1 F2 : List UInt8)
    (hI : InvG spec job st W F1 F2) :
    let n := min st.queue1.size st.queue2.size
    InvG spec job ⟨st.job, st.file1, st.file2, st.queue1.extract n st.queue1.size, st.queue2.extract n st.queue2.size,
      spawnPaired st.job st.queue1 st.queue2 st.pending⟩ W F1 F2 := by
  intro n
  obtain ⟨SP, K, pieces, hj, ok1, ok2, hSP, hq1, hq2, hF1, hF2, hqs, hK, hpieces, hW, hvals⟩ := hI
  have hn1 : n ≤ st.queue1.size := Nat.min_le_left _ _
  have hn2 : n ≤ st.queue2.size := Nat.min_le_right _ _
  have hmap1 := range_getElem st.queue1 n hn1
  have hmap2 := range_getElem st.queue2 n hn2
  have hex1 : (st.queue1.extract n st.queue1.size).toList.map bl = (st.queue1.toList.map bl).drop n := by
    rw [Array.toList_extract, List.extract_eq_drop_take, List.map_take, List.map_drop,
      List.take_of_length_le (by simp)]
  have hex2 : (st.queue2.extract n st.queue2.size).toList.map bl = (st.queue2.toList.map bl).drop n := by
    rw [Array.toList_extract, List.extract_eq_drop_take, List.map_take, List.map_drop,
      List.take_of_length_le (by simp)]
  refine ⟨SP ++ (List.range n).map (fun k => (bl st.queue1[k]!, bl st.queue2[k]!)), K, pieces, hj, ok1, ok2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hW, ?_⟩
  · intro p hp
    rcases List.mem_append.1 hp with h | h
    · exact hSP p h
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 h
      have m1 : bl st.queue1[k]! ∈ st.queue1.toList.map bl := by
        have := List.mem_map_of_mem (f := fun k => bl st.queue1[k]!) hk
        rw [hmap1] at this; exact List.mem_of_mem_take this
      have m2 : bl st.queue2[k]! ∈ st.queue2.toList.map bl := by
        have := List.mem_map_of_mem (f := fun k => bl st.queue2[k]!) hk
        rw [hmap2] at this; exact List.mem_of_mem_take this
      exact ⟨hq1 _ m1, hq2 _ m2⟩
  · intro s hs; simp only [] at hs; rw [hex1] at hs; exact hq1 s (List.mem_of_mem_drop hs)
  · intro s hs; simp only [] at hs; rw [hex2] at hs; exact hq2 s (List.mem_of_mem_drop hs)
  · simp only [List.map_append, List.flatten_append, List.map_map, Function.comp_def]
    rw [hex1]
    have e : (List.map (fun k => bl st.queue1[k]!) (List.range n)).flatten = ((st.queue1.toList.map bl).take n).flatten := by rw [hmap1]
    rw [e, hF1]
    have hsplit : (st.queue1.toList.map bl).flatten = ((st.queue1.toList.map bl).take n).flatten ++ ((st.queue1.toList.map bl).drop n).flatten := by
      rw [← List.flatten_append, List.take_append_drop]
    rw [hsplit]
    simp only [List.append_assoc]
  · simp only [List.map_append, List.flatten_append, List.map_map, Function.comp_def]
    rw [hex2]
    have e : (List.map (fun k => bl st.queue2[k]!) (List.range n)).flatten = ((st.queue2.toList.map bl).take n).flatten := by rw [hmap2]
    rw [e, hF2]
    have hsplit : (st.queue2.toList.map bl).flatten = ((st.queue2.toList.map bl).take n).flatten ++ ((st.queue2.toList.map bl).drop n).flatten := by
      rw [← List.flatten_append, List.take_append_drop]
    rw [hsplit]
    simp only [List.append_assoc]
  · simp only [Array.size_extract]
    omega
  · simp only [List.length_append]; omega
  · rw [List.take_append_of_le_length hK]; exact hpieces
  · rw [spawnPaired_vals, hvals, List.drop_append_of_le_length hK, List.map_append, List.map_map]
    refine congrArg (_ ++ ·) ?_
    apply List.map_congr_left
    intro k hk
    show Option.map bl (st.job st.queue1[k]! st.queue2[k]!) = spec (bl st.queue1[k]!) (bl st.queue2[k]!)
    rw [hj]; exact hjob _ _

theorem collectL_zero (res : List (Option (List UInt8))) (out : List UInt8) :
    (collectL 0 res out).map (·.2) = (res.mapM id).map fun ps => out ++ ps.flatten := by
  unfold collectL
  simp only [Nat.sub_zero, List.take_length]
  cases res.mapM id <;> simp

theorem foldl_append_bl : ∀ (L : List ByteArray) (acc : ByteArray), bl (L.foldl (· ++ ·) acc) = bl acc ++ (L.map bl).flatten
  | [], acc => by simp
  | x :: xs, acc => by
    rw [List.foldl_cons, foldl_append_bl xs]
    have : bl (acc ++ x) = bl acc ++ bl x := data_toList_append' acc x
    rw [this]
    simp [List.append_assoc]

theorem mapReads_nil (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList) :
    mapReads settings index chrs [] [] = some [] := by
  rw [mapReads_eq, parse_nil]
  simp only []
  unfold R
  rw [prep_eq]
  simp [alignPairs_eq_map, SamSpec.body]

theorem collect_zero_out (pend : Array (Task (Option ByteArray))) (out : ByteArray) :
    (collect 0 pend out).map (fun r => bl r.2) = ((vals pend).mapM id).map fun ps => bl out ++ ps.flatten := by
  have hv := collect_vals 0 pend out
  have := congrArg (Option.map (·.2)) hv
  rw [Option.map_map] at this
  rw [collectL_zero] at this
  rw [← this]
  rfl

theorem end_correct (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList)
    (job : ByteArray → ByteArray → Option ByteArray)
    (hjob : ∀ a b, (job a b).map bl = mapReads settings index chrs (bl a) (bl b))
    (st : State) (W F1 F2 : List UInt8) (hI : FInv (mapReads settings index chrs) job st W F1 F2) :
    (∀ st' out, MapFast.step st none = some (st', out) → mapReads settings index chrs F1 F2 = some (W ++ bl out)) ∧
    (MapFast.step st none = none → mapReads settings index chrs F1 F2 = none) := by
  have hP := pair_inv (mapReads settings index chrs) job hjob st W F1 F2 hI.1
  obtain ⟨SP, K, pieces, hj, ok1, ok2, hSP, hq1, hq2, hF1, hF2, hqs, hK, hpieces, hW, hvals⟩ := hP
  obtain ⟨jb, f1, f2, q1, q2, pend⟩ := st
  simp only [] at hj hF1 hF2 hvals
  subst hj
  -- the last job's input
  have hr1 : bl ((q1.extract (min q1.size q2.size) q1.size).foldl (· ++ ·) ByteArray.empty ++ f1.carry) =
      ((q1.extract (min q1.size q2.size) q1.size).toList.map bl).flatten ++ bl f1.carry := by
    rw [show ∀ a b : ByteArray, bl (a ++ b) = bl a ++ bl b from fun a b => data_toList_append' a b,
      ← Array.foldl_toList, foldl_append_bl]; simp
  have hr2 : bl ((q2.extract (min q1.size q2.size) q2.size).foldl (· ++ ·) ByteArray.empty ++ f2.carry) =
      ((q2.extract (min q1.size q2.size) q2.size).toList.map bl).flatten ++ bl f2.carry := by
    rw [show ∀ a b : ByteArray, bl (a ++ b) = bl a ++ bl b from fun a b => data_toList_append' a b,
      ← Array.foldl_toList, foldl_append_bl]; simp
  generalize hrest1 : (q1.extract (min q1.size q2.size) q1.size).foldl (· ++ ·) ByteArray.empty ++ f1.carry = rest1 at hr1
  generalize hrest2 : (q2.extract (min q1.size q2.size) q2.size).foldl (· ++ ·) ByteArray.empty ++ f2.carry = rest2 at hr2
  generalize hpaired : spawnPaired jb q1 q2 pend = paired at hvals
  have hF1' : F1 = (SP.map (·.1)).flatten ++ bl rest1 := by rw [hF1, hr1]; simp only [List.append_assoc]
  have hF2' : F2 = (SP.map (·.2)).flatten ++ bl rest2 := by rw [hF2, hr2]; simp only [List.append_assoc]
  have hCH := chain settings index chrs SP hSP (bl rest1) (bl rest2)
  rw [← hF1', ← hF2'] at hCH
  have hmap : SP.map (fun p => mapReads settings index chrs p.1 p.2) = pieces.map some ++ vals paired := by
    rw [← List.take_append_drop K SP, List.map_append, hpieces, ← hvals]
  have hMres : (SP.map fun p => mapReads settings index chrs p.1 p.2).mapM id =
      ((vals paired).mapM id).map (pieces ++ ·) := by
    rw [hmap, mapM_id_append, (mapM_id_some _ _).2 rfl]
    simp only [Option.bind_some]
  have hCH' : mapReads settings index chrs F1 F2 = ((vals paired).mapM id).bind fun ps =>
      (mapReads settings index chrs (bl rest1) (bl rest2)).map ((pieces ++ ps).flatten ++ ·) := by
    rw [hCH, hMres]
    cases (vals paired).mapM id <;> simp
  have hCOL : ((collect 0 (if rest1.isEmpty && rest2.isEmpty then paired
        else paired.push (Task.spawn fun _ => jb rest1 rest2)) ByteArray.empty).map fun r => bl r.2) =
      ((vals paired).mapM id).bind fun ps => (mapReads settings index chrs (bl rest1) (bl rest2)).map (ps.flatten ++ ·) := by
    by_cases hE : (rest1.isEmpty && rest2.isEmpty) = true
    · rw [if_pos hE, collect_zero_out]
      have h1 : bl rest1 = [] := by
        have := (Bool.and_eq_true _ _ ▸ hE : _ ∧ _).1
        have hs : rest1.size = 0 := by simpa [ByteArray.isEmpty] using this
        exact List.length_eq_zero_iff.1 (by rw [← size_eq_length']; exact hs)
      have h2 : bl rest2 = [] := by
        have := (Bool.and_eq_true _ _ ▸ hE : _ ∧ _).2
        have hs : rest2.size = 0 := by simpa [ByteArray.isEmpty] using this
        exact List.length_eq_zero_iff.1 (by rw [← size_eq_length']; exact hs)
      rw [h1, h2, mapReads_nil]
      cases (vals paired).mapM id <;> simp [bl]
    · rw [if_neg hE, collect_zero_out]
      have hv : vals (paired.push (Task.spawn fun _ => jb rest1 rest2)) =
          vals paired ++ [mapReads settings index chrs (bl rest1) (bl rest2)] := by
        simp only [vals, Array.toList_push, List.map_append, List.map_cons, List.map_nil, spawn_get]
        rw [hjob]
      rw [hv, mapM_id_append]
      cases (vals paired).mapM id with
      | none => simp
      | some ps => cases hx : mapReads settings index chrs (bl rest1) (bl rest2) <;> simp [bl]
  constructor
  · intro st' out h
    simp only [MapFast.step] at h
    simp only [hrest1, hrest2, hpaired] at h
    cases hc : collect 0 (if rest1.isEmpty && rest2.isEmpty then paired
        else paired.push (Task.spawn fun _ => jb rest1 rest2)) ByteArray.empty with
    | none => rw [hc] at h; simp at h
    | some r =>
      obtain ⟨pd, o⟩ := r
      rw [hc] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      rw [hc] at hCOL
      simp only [Option.map_some] at hCOL
      rw [hCH', hW]
      cases hM : (vals paired).mapM id with
      | none => rw [hM] at hCOL; simp at hCOL
      | some ps =>
        rw [hM] at hCOL
        cases hX : mapReads settings index chrs (bl rest1) (bl rest2) with
        | none => rw [hX] at hCOL; simp at hCOL
        | some x =>
          rw [hX] at hCOL
          simp only [Option.bind_some, Option.map_some, Option.some.injEq] at hCOL
          simp only [Option.bind_some, Option.map_some, hCOL, List.flatten_append, List.append_assoc]
  · intro h
    simp only [MapFast.step] at h
    simp only [hrest1, hrest2, hpaired] at h
    cases hc : collect 0 (if rest1.isEmpty && rest2.isEmpty then paired
        else paired.push (Task.spawn fun _ => jb rest1 rest2)) ByteArray.empty with
    | some r => rw [hc] at h; simp at h
    | none =>
      rw [hc] at hCOL
      simp only [Option.map_none] at hCOL
      rw [hCH']
      cases hM : (vals paired).mapM id with
      | none => simp
      | some ps =>
        rw [hM] at hCOL
        cases hX : mapReads settings index chrs (bl rest1) (bl rest2) with
        | none => simp
        | some x => rw [hX] at hCOL; simp at hCOL

/-! ## The whole run -/

theorem fold_correct (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList)
    (job : ByteArray → ByteArray → Option ByteArray)
    (hjob : ∀ a b, (job a b).map bl = mapReads settings index chrs (bl a) (bl b)) :
    ∀ (chunks : List (ByteArray × ByteArray)) (st : State) (W F1 F2 : List UInt8),
    FInv (mapReads settings index chrs) job st W F1 F2 →
    Spec.Total.MapProcess.fold MapFast.step st W chunks =
      mapReads settings index chrs (F1 ++ chunks.flatMap fun c => bl c.1) (F2 ++ chunks.flatMap fun c => bl c.2)
  | [], st, W, F1, F2, hI => by
    obtain ⟨hs, hn⟩ := end_correct settings index chrs job hjob st W F1 F2 hI
    simp only [Spec.Total.MapProcess.fold, List.foldlM_nil, List.flatMap_nil, List.append_nil]
    cases hst : MapFast.step st none with
    | none => rw [hn hst]; simp [hst]
    | some r => obtain ⟨st', out⟩ := r; rw [hs st' out hst]; simp [hst, bl]
  | (a, b) :: rest, st, W, F1, F2, hI => by
    simp only [Spec.Total.MapProcess.fold, List.foldlM_cons, List.flatMap_cons]
    cases hst : MapFast.step st (some (a, b)) with
    | none =>
      simp only [Option.map_none, Option.bind_none]
      have := step_some_fail settings index chrs job hjob st W F1 F2 a b hI hst
        (rest.flatMap fun c => bl c.1) (rest.flatMap fun c => bl c.2)
      simp only [List.append_assoc] at this
      exact this.symm
    | some r =>
      obtain ⟨st', piece⟩ := r
      simp only [Option.map_some, Option.bind_some]
      have ih := fold_correct settings index chrs job hjob rest st' (W ++ bl piece) (F1 ++ bl a) (F2 ++ bl b)
        (step_some_inv settings index chrs job hjob st st' W F1 F2 a b piece hI hst)
      simp only [Spec.Total.MapProcess.fold] at ih
      simp only [List.append_assoc] at ih
      exact ih

end Spec.FQ.MapStream
