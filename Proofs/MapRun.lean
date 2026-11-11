import Proofs.MapProcess
import Proofs.MapPending
import Proofs.MapJobs
/-! # The stream (`MapFast.step`) against `mapReads`: invariant, a successful step, a failing step, the end. -/
namespace Spec.FQ.MapStream
open Spec Spec.MapFast Spec.MapCopy Spec.MapCopy.Jobs

abbrev bl (b : ByteArray) : List UInt8 := b.data.toList

/-! ## List helpers -/

theorem foldl_append_bl : ∀ (L : List ByteArray) (acc : ByteArray), bl (L.foldl (· ++ ·) acc) = bl acc ++ (L.map bl).flatten
  | [], acc => by simp
  | x :: xs, acc => by
    rw [List.foldl_cons, foldl_append_bl xs]
    have : bl (acc ++ x) = bl acc ++ bl x := data_toList_append' acc x
    rw [this]
    simp [List.append_assoc]



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

def sl (a : Array ByteArray) : List (List UInt8) := a.toList.map bl

-- the bytes of a file that are not in the queue yet: the last cut's slices, its carry, the chunks buffered since
def rem (cut : Task (Carry × Array ByteArray)) (buf : Array ByteArray) : List UInt8 :=
  (sl cut.get.2).flatten ++ bl cut.get.1.carry ++ (sl buf).flatten

-- what a state says about the bytes read so far (`F1`, `F2`: the bytes of the queue are followed by `R1`, `R2`) and the
-- lines written (`W`); `spec` is `mapReads`
def InvG (spec : List UInt8 → List UInt8 → Option (List UInt8)) (job : ByteArray → ByteArray → Option ByteArray)
    (st : State) (W F1 F2 R1 R2 : List UInt8) : Prop :=
  ∃ (SP : List (List UInt8 × List UInt8)) (K : Nat) (pieces : List (List UInt8)),
    st.job = job ∧
    (∀ p ∈ SP, IsSlice need p.1 ∧ IsSlice need p.2) ∧
    (∀ s ∈ sl st.queue1, IsSlice need s) ∧ (∀ s ∈ sl st.queue2, IsSlice need s) ∧
    F1 = (SP.map (·.1)).flatten ++ (sl st.queue1).flatten ++ R1 ∧
    F2 = (SP.map (·.2)).flatten ++ (sl st.queue2).flatten ++ R2 ∧
    K ≤ SP.length ∧ (SP.take K).map (fun p => spec p.1 p.2) = pieces.map some ∧ W = pieces.flatten ∧
    vals st.pending = (SP.drop K).map (fun p => spec p.1 p.2)

-- the cuts: scan state of the carries, slices of the finished cuts
def FileInv (st : State) : Prop :=
  ScanOk st.cut1.get.1 ∧ ScanOk st.cut2.get.1 ∧
  (∀ s ∈ sl st.cut1.get.2, IsSlice need s) ∧ (∀ s ∈ sl st.cut2.get.2, IsSlice need s)

def FInv (spec : List UInt8 → List UInt8 → Option (List UInt8)) (job : ByteArray → ByteArray → Option ByteArray)
    (st : State) (W F1 F2 : List UInt8) : Prop :=
  InvG spec job st W F1 F2 (rem st.cut1 st.buf1) (rem st.cut2 st.buf2) ∧ FileInv st ∧ st.pending.size ≤ inFlight

theorem finv_init (spec : List UInt8 → List UInt8 → Option (List UInt8)) (job : ByteArray → ByteArray → Option ByteArray) :
    FInv spec job (init job) [] [] [] := by
  have hn : 0 < need := by unfold need jobPairs; omega
  refine ⟨⟨[], 0, [], rfl, by simp, by simp [sl, init], by simp [sl, init], by simp [sl, init, rem],
    by simp [sl, init, rem], by simp, by simp, by simp, by simp [vals, init]⟩,
    ⟨⟨by simp [init], by simp [init], hn⟩, ⟨by simp [init], by simp [init], hn⟩, by simp [sl, init], by simp [sl, init]⟩,
    by simp [init]⟩

/-! ## `feed`: one file's chunk is buffered, or flushed into the cut chain -/

theorem join_bl (b : Array ByteArray) : bl (join b) = (sl b).flatten := by
  unfold join sl
  rw [← Array.foldl_toList, foldl_append_bl]
  simp

theorem feed_noflush (cut : Task (Carry × Array ByteArray)) (buf : Array ByteArray) (size : Nat) (queue : Array ByteArray)
    (chunk : ByteArray) (h : ¬ flushBytes ≤ size + chunk.size) :
    feed cut buf size queue chunk = (cut, buf.push chunk, size + chunk.size, queue) := by
  unfold feed; exact if_neg h

theorem feed_flush (cut : Task (Carry × Array ByteArray)) (buf : Array ByteArray) (size : Nat) (queue : Array ByteArray)
    (chunk : ByteArray) (h : flushBytes ≤ size + chunk.size) :
    feed cut buf size queue chunk =
      (cut.map (prio := .dedicated) (fun (c, _) => cutSlices c (join (buf.push chunk))), #[], 0, queue ++ cut.get.2) := by
  unfold feed; exact if_pos h

theorem feed_spec (cut : Task (Carry × Array ByteArray)) (buf : Array ByteArray) (size : Nat) (queue : Array ByteArray)
    (chunk : ByteArray) (hok : ScanOk cut.get.1) (hc : ∀ s ∈ sl cut.get.2, IsSlice need s)
    (hq : ∀ s ∈ sl queue, IsSlice need s) :
    ScanOk (feed cut buf size queue chunk).1.get.1 ∧ (∀ s ∈ sl (feed cut buf size queue chunk).1.get.2, IsSlice need s) ∧
    (∀ s ∈ sl (feed cut buf size queue chunk).2.2.2, IsSlice need s) ∧
    (sl queue).flatten ++ rem cut buf ++ bl chunk =
      (sl (feed cut buf size queue chunk).2.2.2).flatten ++ rem (feed cut buf size queue chunk).1 (feed cut buf size queue chunk).2.1 := by
  by_cases hfl : flushBytes ≤ size + chunk.size
  · rw [feed_flush cut buf size queue chunk hfl]
    have hget : (cut.map (prio := .dedicated) (fun (c, _) => cutSlices c (join (buf.push chunk)))).get =
        cutSlices cut.get.1 (join (buf.push chunk)) := rfl
    obtain ⟨ss, hss, hcs, hcar, -, hok'⟩ := cutSlices_spec cut.get.1 (join (buf.push chunk)) hok
    simp only [hget]
    refine ⟨hok', ?_, ?_, ?_⟩
    · intro s hs
      unfold sl at hs
      rw [hcs] at hs
      exact hss s hs
    · intro s hs
      unfold sl at hs
      rw [Array.toList_append, List.map_append] at hs
      rcases List.mem_append.1 hs with h | h
      · exact hq s h
      · exact hc s h
    · have hb : bl (join (buf.push chunk)) = (sl buf).flatten ++ bl chunk := by
        rw [join_bl]; simp [sl, Array.toList_push, List.map_append]
      have hcar' : bl cut.get.1.carry ++ bl (join (buf.push chunk)) =
          ss.flatten ++ bl (cutSlices cut.get.1 (join (buf.push chunk))).1.carry := hcar
      rw [hb] at hcar'
      have hs2 : (cutSlices cut.get.1 (join (buf.push chunk))).2.toList.map bl = ss := hcs
      unfold rem
      rw [hget]
      simp only [hs2, sl, Array.toList_append, List.map_append, List.flatten_append, List.map_nil,
        List.flatten_nil, List.append_nil, Array.toList_empty]
      simp only [sl] at hcar'
      rw [List.append_assoc, List.append_assoc, ← hcar']
      simp [List.append_assoc]
  · rw [feed_noflush cut buf size queue chunk hfl]
    refine ⟨hok, hc, hq, ?_⟩
    simp only [rem, sl, Array.toList_push, List.map_append, List.flatten_append, List.map_cons, List.map_nil,
      List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]

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

/-! ## `collect` -/

theorem collect_inv (spec : List UInt8 → List UInt8 → Option (List UInt8)) (job : ByteArray → ByteArray → Option ByteArray)
    (st : State) (W F1 F2 R1 R2 : List UInt8) (keep : Nat) (pd : Array (Task (Option ByteArray))) (o : ByteArray)
    (hI : InvG spec job st W F1 F2 R1 R2) (h : collect keep st.pending ByteArray.empty = some (pd, o)) :
    InvG spec job { st with pending := pd } (W ++ bl o) F1 F2 R1 R2 ∧ pd.size ≤ keep := by
  have hv := collect_vals keep st.pending ByteArray.empty
  rw [h] at hv
  simp only [Option.map_some] at hv
  obtain ⟨SP, K, pieces, hj, hSP, hq1, hq2, hF1, hF2, hK, hpieces, hW, hvals⟩ := hI
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
    refine ⟨⟨SP, K + t, pieces ++ ps, hj, hSP, hq1, hq2, hF1, hF2, by omega, ?_, ?_, ?_⟩, ?_⟩
    · rw [List.take_add, List.map_append, hpieces, List.map_take, hps, List.map_append]
    · have ho' : bl o = ps.flatten := by simpa [bl] using ho
      rw [hW, ho']; simp
    · simp only []
      rw [hpd, ← List.map_drop, List.drop_drop, Nat.add_comm]
    · have : pd.size = (vals pd).length := by simp [vals]
      rw [this, hpd]; simp; omega

-- if some result that `collect` would take is none, the files (whatever follows) are not valid
theorem failing_job (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList)
    (job : ByteArray → ByteArray → Option ByteArray) (st : State) (W F1 F2 R1 R2 : List UInt8) (keep : Nat)
    (hI : InvG (mapReads settings index chrs) job st W F1 F2 R1 R2) (h : collect keep st.pending ByteArray.empty = none)
    (T1 T2 : List UInt8) : mapReads settings index chrs (F1 ++ T1) (F2 ++ T2) = none := by
  have hv := collect_vals keep st.pending ByteArray.empty
  rw [h] at hv
  simp only [Option.map_none] at hv
  obtain ⟨SP, K, pieces, hj, hSP, hq1, hq2, hF1, hF2, hK, hpieces, hW, hvals⟩ := hI
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

theorem pair_inv (spec : List UInt8 → List UInt8 → Option (List UInt8)) (job : ByteArray → ByteArray → Option ByteArray)
    (hjob : ∀ a b, (job a b).map bl = spec (bl a) (bl b)) (st : State) (W F1 F2 R1 R2 : List UInt8)
    (hI : InvG spec job st W F1 F2 R1 R2) :
    let n := min st.queue1.size st.queue2.size
    InvG spec job { st with queue1 := (st.queue1.extract n st.queue1.size), queue2 := (st.queue2.extract n st.queue2.size), pending := (spawnPaired st.job st.queue1 st.queue2 st.pending) } W F1 F2 R1 R2 := by
  intro n
  obtain ⟨SP, K, pieces, hj, hSP, hq1, hq2, hF1, hF2, hK, hpieces, hW, hvals⟩ := hI
  have hn1 : n ≤ st.queue1.size := Nat.min_le_left _ _
  have hn2 : n ≤ st.queue2.size := Nat.min_le_right _ _
  have hmap1 := range_getElem st.queue1 n hn1
  have hmap2 := range_getElem st.queue2 n hn2
  have hex1 : sl (st.queue1.extract n st.queue1.size) = (sl st.queue1).drop n := by
    unfold sl
    rw [Array.toList_extract, List.extract_eq_drop_take, List.map_take, List.map_drop,
      List.take_of_length_le (by simp)]
  have hex2 : sl (st.queue2.extract n st.queue2.size) = (sl st.queue2).drop n := by
    unfold sl
    rw [Array.toList_extract, List.extract_eq_drop_take, List.map_take, List.map_drop,
      List.take_of_length_le (by simp)]
  refine ⟨SP ++ (List.range n).map (fun k => (bl st.queue1[k]!, bl st.queue2[k]!)), K, pieces, hj, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hW, ?_⟩
  · intro p hp
    rcases List.mem_append.1 hp with h | h
    · exact hSP p h
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 h
      have m1 : bl st.queue1[k]! ∈ sl st.queue1 := by
        have := List.mem_map_of_mem (f := fun k => bl st.queue1[k]!) hk
        rw [hmap1] at this; exact List.mem_of_mem_take this
      have m2 : bl st.queue2[k]! ∈ sl st.queue2 := by
        have := List.mem_map_of_mem (f := fun k => bl st.queue2[k]!) hk
        rw [hmap2] at this; exact List.mem_of_mem_take this
      exact ⟨hq1 _ m1, hq2 _ m2⟩
  · intro s hs; simp only [] at hs; rw [hex1] at hs; exact hq1 s (List.mem_of_mem_drop hs)
  · intro s hs; simp only [] at hs; rw [hex2] at hs; exact hq2 s (List.mem_of_mem_drop hs)
  · simp only [List.map_append, List.flatten_append, List.map_map, Function.comp_def]
    rw [hex1]
    have e : (List.map (fun k => bl st.queue1[k]!) (List.range n)).flatten = ((sl st.queue1).take n).flatten := by rw [hmap1]; rfl
    rw [e, hF1]
    have hsplit : (sl st.queue1).flatten = ((sl st.queue1).take n).flatten ++ ((sl st.queue1).drop n).flatten := by
      rw [← List.flatten_append, List.take_append_drop]
    rw [hsplit]
    simp only [List.append_assoc]
  · simp only [List.map_append, List.flatten_append, List.map_map, Function.comp_def]
    rw [hex2]
    have e : (List.map (fun k => bl st.queue2[k]!) (List.range n)).flatten = ((sl st.queue2).take n).flatten := by rw [hmap2]; rfl
    rw [e, hF2]
    have hsplit : (sl st.queue2).flatten = ((sl st.queue2).take n).flatten ++ ((sl st.queue2).drop n).flatten := by
      rw [← List.flatten_append, List.take_append_drop]
    rw [hsplit]
    simp only [List.append_assoc]
  · simp only [List.length_append]; omega
  · rw [List.take_append_of_le_length hK]; exact hpieces
  · rw [spawnPaired_vals, hvals, List.drop_append_of_le_length hK, List.map_append, List.map_map]
    refine congrArg (_ ++ ·) ?_
    apply List.map_congr_left
    intro k hk
    show Option.map bl (st.job st.queue1[k]! st.queue2[k]!) = spec (bl st.queue1[k]!) (bl st.queue2[k]!)
    rw [hj]; exact hjob _ _


-- the state after `feed` on both files
def fedState (st : State) (a b : ByteArray) : State :=
  let r1 := feed st.cut1 st.buf1 st.size1 st.queue1 a
  let r2 := feed st.cut2 st.buf2 st.size2 st.queue2 b
  ⟨st.job, r1.1, r2.1, r1.2.1, r2.2.1, r1.2.2.1, r2.2.2.1, r1.2.2.2, r2.2.2.2, st.pending⟩

theorem fed_inv (spec : List UInt8 → List UInt8 → Option (List UInt8)) (job : ByteArray → ByteArray → Option ByteArray)
    (st : State) (W F1 F2 : List UInt8) (a b : ByteArray) (hI : FInv spec job st W F1 F2) :
    InvG spec job (fedState st a b) W (F1 ++ bl a) (F2 ++ bl b)
      (rem (fedState st a b).cut1 (fedState st a b).buf1) (rem (fedState st a b).cut2 (fedState st a b).buf2) ∧
    FileInv (fedState st a b) := by
  obtain ⟨hG, ⟨ok1, ok2, hc1, hc2⟩, -⟩ := hI
  obtain ⟨SP, K, pieces, hj, hSP, hq1, hq2, hF1, hF2, hK, hpieces, hW, hvals⟩ := hG
  obtain ⟨o1, c1', q1', e1⟩ := feed_spec st.cut1 st.buf1 st.size1 st.queue1 a ok1 hc1 hq1
  obtain ⟨o2, c2', q2', e2⟩ := feed_spec st.cut2 st.buf2 st.size2 st.queue2 b ok2 hc2 hq2
  refine ⟨⟨SP, K, pieces, hj, hSP, q1', q2', ?_, ?_, hK, hpieces, hW, hvals⟩, ⟨o1, o2, c1', c2'⟩⟩
  · rw [hF1]; simp only [List.append_assoc] at e1 ⊢; exact congrArg _ e1
  · rw [hF2]; simp only [List.append_assoc] at e2 ⊢; exact congrArg _ e2

theorem step_some_inv (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList)
    (job : ByteArray → ByteArray → Option ByteArray)
    (hjob : ∀ a b, (job a b).map bl = mapReads settings index chrs (bl a) (bl b))
    (st st' : State) (W F1 F2 : List UInt8) (a b out : ByteArray)
    (hI : FInv (mapReads settings index chrs) job st W F1 F2) (h : MapFast.step st (some (a, b)) = some (st', out)) :
    FInv (mapReads settings index chrs) job st' (W ++ bl out) (F1 ++ bl a) (F2 ++ bl b) := by
  obtain ⟨hF, hFile⟩ := fed_inv (mapReads settings index chrs) job st W F1 F2 a b hI
  have hpair := pair_inv (mapReads settings index chrs) job hjob _ _ _ _ _ _ hF
  obtain ⟨jb, c1, c2, b1, b2, z1, z2, q1, q2, pend⟩ := st
  simp only [MapFast.step] at h
  cases hc : collect inFlight (spawnPaired jb (feed c1 b1 z1 q1 a).2.2.2 (feed c2 b2 z2 q2 b).2.2.2 pend) ByteArray.empty with
  | none => rw [hc] at h; simp at h
  | some r =>
    obtain ⟨pd, o⟩ := r
    rw [hc] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hI', hpd⟩ := collect_inv (mapReads settings index chrs) job _ _ _ _ _ _ inFlight pd o hpair hc
    exact ⟨hI', hFile, hpd⟩

theorem step_some_fail (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList)
    (job : ByteArray → ByteArray → Option ByteArray)
    (hjob : ∀ a b, (job a b).map bl = mapReads settings index chrs (bl a) (bl b))
    (st : State) (W F1 F2 : List UInt8) (a b : ByteArray)
    (hI : FInv (mapReads settings index chrs) job st W F1 F2) (h : MapFast.step st (some (a, b)) = none) (T1 T2 : List UInt8) :
    mapReads settings index chrs (F1 ++ bl a ++ T1) (F2 ++ bl b ++ T2) = none := by
  obtain ⟨hF, hFile⟩ := fed_inv (mapReads settings index chrs) job st W F1 F2 a b hI
  have hpair := pair_inv (mapReads settings index chrs) job hjob _ _ _ _ _ _ hF
  obtain ⟨jb, c1, c2, b1, b2, z1, z2, q1, q2, pend⟩ := st
  simp only [MapFast.step] at h
  cases hc : collect inFlight (spawnPaired jb (feed c1 b1 z1 q1 a).2.2.2 (feed c2 b2 z2 q2 b).2.2.2 pend) ByteArray.empty with
  | none => exact failing_job settings index chrs job _ _ _ _ _ _ inFlight hpair hc T1 T2
  | some r => rw [hc] at h; simp at h

/-! ## The end: pair what is left, then one last job -/

theorem collectL_zero (res : List (Option (List UInt8))) (out : List UInt8) :
    (collectL 0 res out).map (·.2) = (res.mapM id).map fun ps => out ++ ps.flatten := by
  unfold collectL
  simp only [Nat.sub_zero, List.take_length]
  cases res.mapM id <;> simp

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

def endState (st : State) : State :=
  let l1 := cutSlices st.cut1.get.1 (join st.buf1)
  let l2 := cutSlices st.cut2.get.1 (join st.buf2)
  ⟨st.job, Task.pure (l1.1, #[]), Task.pure (l2.1, #[]), #[], #[], 0, 0,
    st.queue1 ++ st.cut1.get.2 ++ l1.2, st.queue2 ++ st.cut2.get.2 ++ l2.2, st.pending⟩

theorem end_inv (spec : List UInt8 → List UInt8 → Option (List UInt8)) (job : ByteArray → ByteArray → Option ByteArray)
    (st : State) (W F1 F2 : List UInt8) (hI : FInv spec job st W F1 F2) :
    InvG spec job (endState st) W F1 F2 (bl (cutSlices st.cut1.get.1 (join st.buf1)).1.carry)
      (bl (cutSlices st.cut2.get.1 (join st.buf2)).1.carry) := by
  obtain ⟨hG, ⟨ok1, ok2, hc1, hc2⟩, -⟩ := hI
  obtain ⟨SP, K, pieces, hj, hSP, hq1, hq2, hF1, hF2, hK, hpieces, hW, hvals⟩ := hG
  obtain ⟨ss1, hss1, hcs1, hcar1, -, -⟩ := cutSlices_spec st.cut1.get.1 (join st.buf1) ok1
  obtain ⟨ss2, hss2, hcs2, hcar2, -, -⟩ := cutSlices_spec st.cut2.get.1 (join st.buf2) ok2
  have hcar1' : bl st.cut1.get.1.carry ++ (sl st.buf1).flatten = ss1.flatten ++ bl (cutSlices st.cut1.get.1 (join st.buf1)).1.carry := by
    rw [← join_bl]; exact hcar1
  have hcar2' : bl st.cut2.get.1.carry ++ (sl st.buf2).flatten = ss2.flatten ++ bl (cutSlices st.cut2.get.1 (join st.buf2)).1.carry := by
    rw [← join_bl]; exact hcar2
  have hs1 : sl (cutSlices st.cut1.get.1 (join st.buf1)).2 = ss1 := hcs1
  have hs2 : sl (cutSlices st.cut2.get.1 (join st.buf2)).2 = ss2 := hcs2
  refine ⟨SP, K, pieces, hj, hSP, ?_, ?_, ?_, ?_, hK, hpieces, hW, hvals⟩
  · intro s hs
    simp only [endState, sl, Array.toList_append, List.map_append] at hs
    rcases List.mem_append.1 hs with h | h
    · rcases List.mem_append.1 h with h | h
      · exact hq1 s h
      · exact hc1 s h
    · have : s ∈ ss1 := by rw [← hs1]; exact h
      exact hss1 s this
  · intro s hs
    simp only [endState, sl, Array.toList_append, List.map_append] at hs
    rcases List.mem_append.1 hs with h | h
    · rcases List.mem_append.1 h with h | h
      · exact hq2 s h
      · exact hc2 s h
    · have : s ∈ ss2 := by rw [← hs2]; exact h
      exact hss2 s this
  · rw [hF1]
    simp only [endState, sl, Array.toList_append, List.map_append, List.flatten_append] at hs1 ⊢
    unfold rem sl at *
    rw [hs1] at *
    simp only [List.append_assoc]
    rw [hcar1']
  · rw [hF2]
    simp only [endState, sl, Array.toList_append, List.map_append, List.flatten_append] at hs2 ⊢
    unfold rem sl at *
    rw [hs2] at *
    simp only [List.append_assoc]
    rw [hcar2']

theorem end_correct (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList)
    (job : ByteArray → ByteArray → Option ByteArray)
    (hjob : ∀ a b, (job a b).map bl = mapReads settings index chrs (bl a) (bl b))
    (st : State) (W F1 F2 : List UInt8) (hI : FInv (mapReads settings index chrs) job st W F1 F2) :
    (∀ st' out, MapFast.step st none = some (st', out) → mapReads settings index chrs F1 F2 = some (W ++ bl out)) ∧
    (MapFast.step st none = none → mapReads settings index chrs F1 F2 = none) := by
  have hE := end_inv _ job st W F1 F2 hI
  have hP := pair_inv (mapReads settings index chrs) job hjob (endState st) W F1 F2 _ _ hE
  obtain ⟨SP, K, pieces, hj, hSP, hq1, hq2, hF1, hF2, hK, hpieces, hW, hvals⟩ := hP
  clear hE hI
  obtain ⟨jb, c1, c2, b1, b2, z1, z2, qq1, qq2, pend⟩ := st
  simp only [endState] at hj hF1 hF2 hvals
  generalize hl1 : cutSlices c1.get.1 (join b1) = l1 at *
  generalize hl2 : cutSlices c2.get.1 (join b2) = l2 at *
  generalize hQ1 : qq1 ++ c1.get.2 ++ l1.2 = q1 at *
  generalize hQ2 : qq2 ++ c2.get.2 ++ l2.2 = q2 at *
  subst hj
  -- the last job's input
  have hr1 : bl ((q1.extract (min q1.size q2.size) q1.size).foldl (· ++ ·) ByteArray.empty ++ l1.1.carry) =
      ((q1.extract (min q1.size q2.size) q1.size).toList.map bl).flatten ++ bl l1.1.carry := by
    rw [show ∀ a b : ByteArray, bl (a ++ b) = bl a ++ bl b from fun a b => data_toList_append' a b,
      ← Array.foldl_toList, foldl_append_bl]; simp
  have hr2 : bl ((q2.extract (min q1.size q2.size) q2.size).foldl (· ++ ·) ByteArray.empty ++ l2.1.carry) =
      ((q2.extract (min q1.size q2.size) q2.size).toList.map bl).flatten ++ bl l2.1.carry := by
    rw [show ∀ a b : ByteArray, bl (a ++ b) = bl a ++ bl b from fun a b => data_toList_append' a b,
      ← Array.foldl_toList, foldl_append_bl]; simp
  generalize hrest1 : (q1.extract (min q1.size q2.size) q1.size).foldl (· ++ ·) ByteArray.empty ++ l1.1.carry = rest1 at hr1
  generalize hrest2 : (q2.extract (min q1.size q2.size) q2.size).foldl (· ++ ·) ByteArray.empty ++ l2.1.carry = rest2 at hr2
  generalize hpaired : spawnPaired jb q1 q2 pend = paired at hvals
  have hF1' : F1 = (SP.map (·.1)).flatten ++ bl rest1 := by rw [hF1, hr1]; simp only [List.append_assoc]; try rfl
  have hF2' : F2 = (SP.map (·.2)).flatten ++ bl rest2 := by rw [hF2, hr2]; simp only [List.append_assoc]; try rfl
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
    simp only [hl1, hl2, hQ1, hQ2] at h
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
    simp only [hl1, hl2, hQ1, hQ2] at h
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
