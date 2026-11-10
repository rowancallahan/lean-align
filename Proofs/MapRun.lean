import Proofs.MapPending
import Proofs.MapJobs
/-! # The stream (`MapFast.step`) against `mapReads`: invariant, a successful step, a failing step, the end. -/
namespace Spec.FQ.MapStream
open Spec Spec.MapFast Spec.Total Spec.Total.Jobs

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

end Spec.FQ.MapStream
