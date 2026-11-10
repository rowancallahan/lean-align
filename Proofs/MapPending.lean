import Proofs.MapSlices
/-! # `spawnPaired` and `collect` (Proofs/MapFast.lean), on the values of the tasks. A pure `Task.spawn f` has value `f ()`. -/
namespace Spec.FQ.MapStream
open Spec Spec.MapFast

abbrev Val := Option ByteArray

def vals (p : Array (Task (Option ByteArray))) : List (Option (List UInt8)) :=
  p.toList.map fun t => t.get.map (·.data.toList)

theorem spawn_get {α : Type} (f : Unit → α) : (Task.spawn f).get = f () := rfl

-- the jobs `spawnPaired` starts, by value
theorem spawnPaired_vals (job : ByteArray → ByteArray → Option ByteArray) (q1 q2 : Array ByteArray)
    (pending : Array (Task (Option ByteArray))) :
    vals (spawnPaired job q1 q2 pending) =
      vals pending ++ (List.range (min q1.size q2.size)).map fun k => (job q1[k]! q2[k]!).map (·.data.toList) := by
  unfold spawnPaired
  generalize List.range (min q1.size q2.size) = ks
  induction ks generalizing pending with
  | nil => simp
  | cons k ks ih =>
    simp only [List.foldl_cons, ih, vals, List.map_cons, List.map_append]
    simp [Array.toList_push, spawn_get]

-- `collect`, on the values: the oldest `res.length - keep` results, in order, appended to `out`; none if one of them is none
def collectL (keep : Nat) (res : List (Option (List UInt8))) (out : List UInt8) :
    Option (List (Option (List UInt8)) × List UInt8) :=
  match (res.take (res.length - keep)).mapM id with
  | some ps => some (res.drop (res.length - keep), out ++ ps.flatten)
  | none => none

theorem getElem!_vals (pending : Array (Task (Option ByteArray))) (i : Nat) (h : i < pending.size) :
    (vals pending)[i]'(by simp [vals]; exact h) = (pending[i]!).get.map (·.data.toList) := by
  simp [vals, getElem!_pos pending i h]

theorem collect_go (keep : Nat) (pending : Array (Task (Option ByteArray))) :
    ∀ (fuel i : Nat) (out : ByteArray), i ≤ pending.size → pending.size ≤ i + fuel →
    ((collect.go keep pending fuel i out).map fun (j, o) => (j, o.data.toList)) =
      match ((vals pending).drop i |>.take (pending.size - keep - i)).mapM id with
      | some ps => some (max i (pending.size - keep), out.data.toList ++ ps.flatten)
      | none => none
  | 0, i, out, hi, hf => by
    have : pending.size - keep - i = 0 := by omega
    simp [collect.go, this]
    omega
  | fuel + 1, i, out, hi, hf => by
    rw [collect.go]
    by_cases hlt : keep < pending.size - i
    · rw [if_pos hlt]
      have hi' : i < pending.size := by omega
      have hres : (vals pending)[i]'(by simp [vals]; exact hi') = (pending[i]!).get.map (·.data.toList) := getElem!_vals pending i hi'
      have hdrop : (vals pending).drop i = (vals pending)[i]'(by simp [vals]; exact hi') :: (vals pending).drop (i + 1) :=
        List.drop_eq_getElem_cons _
      have hlen : pending.size - keep - i = (pending.size - keep - (i + 1)) + 1 := by omega
      rw [hdrop, hlen, List.take_succ_cons, hres]
      cases hg : (pending[i]!).get with
      | none => simp [hg]
      | some piece =>
        have ih := collect_go keep pending fuel (i + 1) (out ++ piece) hi' (by omega)
        simp only [hg, Option.map_some, List.mapM_cons]
        simp only [Option.map_some] at ih
        rw [ih]
        have hmax : max (i + 1) (pending.size - keep) = max i (pending.size - keep) := by omega
        cases hm : List.mapM id (List.take (pending.size - keep - (i + 1)) (List.drop (i + 1) (vals pending))) with
        | none => simp [hm]
        | some ps => simp [hm, hmax, data_toList_append', List.append_assoc]
    · rw [if_neg hlt]
      have : pending.size - keep - i = 0 := by omega
      simp [this]
      omega

theorem collect_vals (keep : Nat) (pending : Array (Task (Option ByteArray))) (out : ByteArray) :
    (collect keep pending out).map (fun (pd, o) => (vals pd, o.data.toList)) = collectL keep (vals pending) out.data.toList := by
  have h := collect_go keep pending pending.size 0 out (Nat.zero_le _) (by omega)
  have hv : (vals pending).length = pending.size := by simp [vals]
  unfold collect collectL
  rw [hv]
  simp only [Nat.sub_zero, List.drop_zero] at h
  cases hg : collect.go keep pending pending.size 0 out with
  | none =>
    rw [hg] at h
    cases hm : (List.take (pending.size - keep) (vals pending)).mapM id with
    | none => simp [hm]
    | some ps => rw [hm] at h; simp at h
  | some r =>
    obtain ⟨j, o⟩ := r
    rw [hg] at h
    cases hm : (List.take (pending.size - keep) (vals pending)).mapM id with
    | none => rw [hm] at h; simp at h
    | some ps =>
      rw [hm] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hj, ho⟩ := h
      have : j = pending.size - keep := by omega
      simp only [Option.map_some, hm, this, ho, vals, Array.toList_extract, List.map_drop]
      congr 2
      rw [List.extract_eq_drop_take, List.map_take, List.map_drop, List.take_of_length_le (by simp)]

end Spec.FQ.MapStream
