import Proofs.MapDefs
import Proofs.MapStream
/-! # `mapReads` is additive over record-aligned slices: the stream's jobs add up to the whole.
(Layer A of the proof of `process_correct`, Proofs/MapFiles.lean.) -/
namespace Spec.MapCopy.Jobs
open Spec Spec.FQ Spec.FQ.MapStream Spec.MapCopy

-- `mapReads` once the files are parsed
def R (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList) (r1 r2 : List FQ.Read) :
    Option (List UInt8) :=
  (prepPairs r1 r2).map fun pairs => SamSpec.body chrs pairs (alignPairs settings index (pairs.map mateLetters))

theorem mapReads_eq (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList) (f1 f2 : List UInt8) :
    mapReads settings index chrs f1 f2 =
      match FQ.parse f1, FQ.parse f2 with
      | some a, some b => R settings index chrs a b
      | _, _ => none := rfl

theorem prep_eq (r1 r2 : List FQ.Read) :
    prepPairs r1 r2 =
      if (r1.map (SamSpec.qname ∘ FQ.Read.name) = r2.map (SamSpec.qname ∘ FQ.Read.name) ∧
          (r1.map (SamSpec.qname ∘ FQ.Read.name)).all SamSpec.qnameOk = true) then
        some (List.zip (r1.map (Trim.trim ∘ Trim.cut)) (r2.map (Trim.trim ∘ Trim.cut)))
      else none := by
  unfold prepPairs
  simp only []
  rcases Decidable.em (r1.map (SamSpec.qname ∘ FQ.Read.name) = r2.map (SamSpec.qname ∘ FQ.Read.name) ∧
          (r1.map (SamSpec.qname ∘ FQ.Read.name)).all SamSpec.qnameOk = true) with h | h
  · rw [if_pos h, decide_eq_true h]
  · rw [if_neg h, decide_eq_false h]

theorem alignPairs_length (settings : InsertSettings) (index : ByteArray) (xs : List (Option ByteArray × Option ByteArray)) :
    (alignPairs settings index xs).length = xs.length := by
  rw [alignPairs_eq_map]; simp

theorem alignPairs_append (settings : InsertSettings) (index : ByteArray) (xs ys : List (Option ByteArray × Option ByteArray)) :
    alignPairs settings index (xs ++ ys) = alignPairs settings index xs ++ alignPairs settings index ys := by
  rw [alignPairs_eq_map, alignPairs_eq_map, alignPairs_eq_map, List.map_append]

theorem body_pairs_append (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList)
    (P1 P2 : List (FQ.Read × FQ.Read)) :
    SamSpec.body chrs (P1 ++ P2) (alignPairs settings index ((P1 ++ P2).map mateLetters)) =
      SamSpec.body chrs P1 (alignPairs settings index (P1.map mateLetters)) ++
      SamSpec.body chrs P2 (alignPairs settings index (P2.map mateLetters)) := by
  rw [List.map_append, alignPairs_append]
  exact SamFast.body_append chrs P1 P2 _ _ (by rw [alignPairs_length]; simp)

theorem R_append (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList)
    (a1 a2 b1 b2 : List FQ.Read) (hl : a1.length = a2.length) :
    R settings index chrs (a1 ++ b1) (a2 ++ b2) =
      (R settings index chrs a1 a2).bind fun o => (R settings index chrs b1 b2).map (o ++ ·) := by
  unfold R
  rw [prep_eq, prep_eq a1 a2, prep_eq b1 b2]
  simp only [List.map_append, List.all_append, Bool.and_eq_true]
  have hl' : (a1.map (SamSpec.qname ∘ FQ.Read.name)).length = (a2.map (SamSpec.qname ∘ FQ.Read.name)).length := by simp [hl]
  have key : ∀ (A B A' B' : List (List UInt8)), A.length = A'.length → (A ++ B = A' ++ B' ↔ A = A' ∧ B = B') := by
    intro A B A' B' h
    constructor
    · intro e; exact List.append_inj e h
    · rintro ⟨rfl, rfl⟩; rfl
  by_cases cw : ((a1.map (SamSpec.qname ∘ FQ.Read.name) ++ b1.map (SamSpec.qname ∘ FQ.Read.name) =
            a2.map (SamSpec.qname ∘ FQ.Read.name) ++ b2.map (SamSpec.qname ∘ FQ.Read.name)) ∧
          ((a1.map (SamSpec.qname ∘ FQ.Read.name)).all SamSpec.qnameOk = true ∧
            (b1.map (SamSpec.qname ∘ FQ.Read.name)).all SamSpec.qnameOk = true))
  · obtain ⟨he, hoa, hob⟩ := cw
    obtain ⟨hea, heb⟩ := (key _ _ _ _ hl').1 he
    rw [if_pos ⟨he, hoa, hob⟩, if_pos ⟨hea, hoa⟩, if_pos ⟨heb, hob⟩]
    simp only [Option.map_some, Option.bind_some, Option.some.injEq]
    have hz : List.zip (a1.map (Trim.trim ∘ Trim.cut) ++ b1.map (Trim.trim ∘ Trim.cut))
        (a2.map (Trim.trim ∘ Trim.cut) ++ b2.map (Trim.trim ∘ Trim.cut)) =
        List.zip (a1.map (Trim.trim ∘ Trim.cut)) (a2.map (Trim.trim ∘ Trim.cut)) ++
        List.zip (b1.map (Trim.trim ∘ Trim.cut)) (b2.map (Trim.trim ∘ Trim.cut)) :=
      List.zip_append (by simp [hl])
    rw [hz, body_pairs_append]
  · rw [if_neg cw]
    simp only [Option.map_none]
    by_cases ca : (a1.map (SamSpec.qname ∘ FQ.Read.name) = a2.map (SamSpec.qname ∘ FQ.Read.name) ∧
          (a1.map (SamSpec.qname ∘ FQ.Read.name)).all SamSpec.qnameOk = true)
    · by_cases cb : (b1.map (SamSpec.qname ∘ FQ.Read.name) = b2.map (SamSpec.qname ∘ FQ.Read.name) ∧
          (b1.map (SamSpec.qname ∘ FQ.Read.name)).all SamSpec.qnameOk = true)
      · exact absurd ⟨(key _ _ _ _ hl').2 ⟨ca.1, cb.1⟩, ca.2, cb.2⟩ cw
      · rw [if_pos ca, if_neg cb]; simp
    · rw [if_neg ca]; simp

/-! ## Cutting at `4 n` newlines cuts between records -/

theorem count_flatMap_toBytes : ∀ rs : List Record, (∀ r ∈ rs, r.valid) → (rs.flatMap toBytes).count newline = 4 * rs.length
  | [], _ => by simp
  | r :: rs, h => by
    rw [List.flatMap_cons, List.count_append, count_toBytes r (h r (by simp)),
      count_flatMap_toBytes rs (fun x m => h x (List.mem_cons_of_mem _ m))]
    simp; omega

theorem parse_count (c : List UInt8) (rs : List FQ.Read) (h : FQ.parse c = some rs) : c.count newline = 4 * rs.length := by
  obtain ⟨rs', hv, hb, hm⟩ := parse_some c rs h
  rw [← hb, count_flatMap_toBytes rs' hv, ← hm]; simp

-- a valid file cut after `4 n` newlines: both parts parse, the first has `n` reads
theorem parse_cut (n : Nat) (X x y : List UInt8) (R : List FQ.Read) (hc : cutLines (4 * n) X = some (x, y))
    (hp : FQ.parse X = some R) :
    ∃ a M, FQ.parse x = some a ∧ FQ.parse y = some M ∧ R = a ++ M ∧ a.length = n := by
  obtain ⟨rs, hv, hb, hm⟩ := parse_some X R hp
  rw [← hb] at hc
  obtain ⟨rs1, rs2, e, e1, e2⟩ := cutLines_valid n rs hv x y hc
  have p1 := parse_of_records rs1 (fun r m => hv r (by rw [e]; exact List.mem_append_left _ m))
  have p2 := parse_of_records rs2 (fun r m => hv r (by rw [e]; exact List.mem_append_right _ m))
  rw [← e1] at p1
  rw [← e2] at p2
  refine ⟨rs1.map toRead, rs2.map toRead, p1, p2, ?_, ?_⟩
  · rw [← hm, e]; simp
  · have h1 := cutLines_count _ _ _ _ hc
    rw [e1, count_flatMap_toBytes rs1 (fun r m => hv r (by rw [e]; exact List.mem_append_left _ m))] at h1
    simpa using (by omega : rs1.length = n)

-- THE additivity: cut both files after `4 n` newlines (`n` reads each), and the jobs add up
theorem mapReads_cut (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList) (n : Nat)
    (X1 X2 x1 y1 x2 y2 : List UInt8) (h1 : cutLines (4 * n) X1 = some (x1, y1)) (h2 : cutLines (4 * n) X2 = some (x2, y2)) :
    mapReads settings index chrs X1 X2 =
      (mapReads settings index chrs x1 x2).bind fun o => (mapReads settings index chrs y1 y2).map (o ++ ·) := by
  have e1 := cutLines_spec _ _ _ _ h1
  have e2 := cutLines_spec _ _ _ _ h2
  cases hp1 : FQ.parse X1 with
  | some R1 =>
    cases hp2 : FQ.parse X2 with
    | some R2 =>
      obtain ⟨a1, M1, pa1, pm1, hR1, hl1⟩ := parse_cut n X1 x1 y1 R1 h1 hp1
      obtain ⟨a2, M2, pa2, pm2, hR2, hl2⟩ := parse_cut n X2 x2 y2 R2 h2 hp2
      rw [mapReads_eq, hp1, hp2, mapReads_eq settings index chrs x1 x2, pa1, pa2, mapReads_eq settings index chrs y1 y2, pm1, pm2, hR1, hR2]
      simp only []
      exact R_append settings index chrs a1 a2 M1 M2 (by omega)
    | none =>
      rw [mapReads_eq, hp1, hp2]
      simp only []
      symm
      rcases Option.eq_none_or_eq_some (mapReads settings index chrs x1 x2) with hx | ⟨o, hx⟩
      · rw [hx]; rfl
      · rw [hx]
        -- x2 and y2 would both parse, so X2 would
        simp only [Option.bind_some]
        rcases Option.eq_none_or_eq_some (mapReads settings index chrs y1 y2) with hy | ⟨o', hy⟩
        · rw [hy]; rfl
        · exfalso
          rw [mapReads_eq] at hx hy
          cases hq1 : FQ.parse x2 with
          | none => cases hq : FQ.parse x1 <;> simp [hq1, hq] at hx
          | some q1 =>
          cases hq2 : FQ.parse y2 with
          | none => rw [hq2] at hy; cases hq : FQ.parse y1 <;> simp [hq] at hy
          | some q2 =>
            have := parse_append x2 y2 q1 hq1
            rw [e2, this, hq2] at hp2
            simp at hp2
  | none =>
    rw [mapReads_eq, hp1]
    simp only []
    symm
    rcases Option.eq_none_or_eq_some (mapReads settings index chrs x1 x2) with hx | ⟨o, hx⟩
    · rw [hx]; rfl
    · simp only [hx, Option.bind_some]
      rcases Option.eq_none_or_eq_some (mapReads settings index chrs y1 y2) with hy | ⟨o', hy⟩
      · rw [hy]; rfl
      · exfalso
        rw [mapReads_eq] at hx hy
        cases hq1 : FQ.parse x1 with
        | none => simp [hq1] at hx
        | some q1 =>
        cases hq2 : FQ.parse y1 with
        | none => rw [hq2] at hy; cases hq : FQ.parse y2 <;> simp [hq] at hy
        | some q2 =>
          have := parse_append x1 y1 q1 hq1
          rw [e1, this, hq2] at hp1
          simp at hp1

#print axioms mapReads_cut

end Spec.MapCopy.Jobs
