import Proofs.MapDefs
import Proofs.SamFast
import Proofs.TrimFast

/-! # `job_eq`: one job of the stream is `mapReads` of its two slices

`MapFast.job` (parse with `parseFastqB`, pair with `prepPairsB`, align with `alignPairsP`, write with `samChunkS`)
gives exactly the bytes of `mapReads` (stated against `MapCopy`, the copies of Proofs/MapFiles.lean's definitions
that the stream proof uses). Pieces: `FQ.parseFastqB_eq` (parsing), `SamFast.bl_qname` / `qnameOkB_eq` (QNAME),
`Trim.trimB_eq` (cut and trim), `alignPairsP_eq` (the setup), `SamFast.samChunkS_eq` (the SAM lines). -/

namespace Spec.MapCopy
open Spec

theorem readOfB_eq (r : ReadB) : FQ.readOfB r = r.toRead := rfl

theorem ba_beq (a b : ByteArray) : (a == b) = true ↔ a.data.toList = b.data.toList := by
  show (a.data == b.data) = true ↔ _
  rw [beq_iff_eq, Array.toList_inj]

-- the pairing check on lists: equal lengths and pairwise equal names that pass `g` = equal name lists that pass `g`
theorem zip_all_iff {α : Type} (F : α → List UInt8) (g : List UInt8 → Bool) : ∀ l1 l2 : List α,
    (l1.length = l2.length ∧ (l1.zip l2).all (fun x => decide (F x.1 = F x.2) && g (F x.1)) = true) ↔
      (l1.map F = l2.map F ∧ (l1.map F).all g = true)
  | [], [] => by simp
  | [], _ :: _ => by simp
  | _ :: _, [] => by simp
  | a :: l1, b :: l2 => by
    have ih := zip_all_iff F g l1 l2
    simp only [List.length_cons, Nat.add_right_cancel_iff, List.zip_cons_cons, List.all_cons, Bool.and_eq_true,
      decide_eq_true_eq, List.map_cons, List.cons.injEq] at ih ⊢
    constructor
    · rintro ⟨hl, ⟨he, hg⟩, hr⟩
      obtain ⟨h1, h2⟩ := ih.mp ⟨hl, hr⟩
      exact ⟨⟨he, h1⟩, hg, h2⟩
    · rintro ⟨⟨he, h1⟩, hg, h2⟩
      obtain ⟨hl, hr⟩ := ih.mpr ⟨h1, h2⟩
      exact ⟨hl, ⟨he, hg⟩, hr⟩

-- a read cut and trimmed by `TrimCore.trimB` is `trim (cut ·)` of the spec's read
theorem trimmed_eq (a : ReadB) :
    ({ a with seq := (TrimCore.trimB a.seq a.qual).1, qual := (TrimCore.trimB a.seq a.qual).2 } : ReadB).toRead =
      Trim.trim (Trim.cut a.toRead) := by
  have h := Trim.trimB_eq a.toRead
  have e1 : (⟨a.toRead.sequence.toArray⟩ : ByteArray) = a.seq := by
    apply ByteArray.ext; simp [ReadB.toRead]
  have e2 : (⟨a.toRead.quality.toArray⟩ : ByteArray) = a.qual := by
    apply ByteArray.ext; simp [ReadB.toRead]
  simp only [e1, e2, Prod.mk.injEq] at h
  have hn : (Trim.trim (Trim.cut a.toRead)).name = a.toRead.name := rfl
  show (⟨a.name.data.toList, _, _⟩ : FQ.Read) = _
  rw [h.1, h.2]
  rcases ht : Trim.trim (Trim.cut a.toRead) with ⟨n, s, q⟩
  rw [ht] at hn
  simp only at hn ⊢
  rw [hn]; rfl

theorem qname_ok_eq (q : ByteArray) : qnameOkB q = SamSpec.qnameOk q.data.toList := by
  rw [qnameOkB_eq]; rfl

theorem zip_trim : ∀ l1 l2 : List ReadB,
    ((l1.zip l2).map (fun x => match x with
      | (a, b) =>
        have t1 := TrimCore.trimB a.seq a.qual
        have t2 := TrimCore.trimB b.seq b.qual
        (({ name := a.name, seq := t1.fst, qual := t1.snd } : ReadB), ({ name := b.name, seq := t2.fst, qual := t2.snd } : ReadB)))).map
      SamFast.toReads =
    (l1.map ReadB.toRead |>.map (Trim.trim ∘ Trim.cut)).zip (l2.map ReadB.toRead |>.map (Trim.trim ∘ Trim.cut))
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: l1, b :: l2 => by
    simp only [List.zip_cons_cons, List.map_cons, List.cons.injEq]
    refine ⟨?_, zip_trim l1 l2⟩
    simp only [SamFast.toReads, Function.comp]
    exact Prod.ext (trimmed_eq a) (trimmed_eq b)

-- `prepPairsB` is `prepPairs` on the spec's reads
theorem prepPairsB_eq (r1 r2 : Array ReadB) :
    (MapFast.prepPairsB r1 r2).map (fun P => P.toList.map SamFast.toReads) =
      prepPairs (r1.toList.map FQ.readOfB) (r2.toList.map FQ.readOfB) := by
  unfold MapFast.prepPairsB prepPairs
  rw [show FQ.readOfB = ReadB.toRead from funext readOfB_eq]
  -- the check
  have hc : (r1.size == r2.size && (r1.zip r2).all (fun (a, b) => let q := qnameB a.name; q == qnameB b.name && qnameOkB q))
      = decide ((r1.toList.map ReadB.toRead).map (SamSpec.qname ∘ FQ.Read.name) =
          (r2.toList.map ReadB.toRead).map (SamSpec.qname ∘ FQ.Read.name) ∧
        ((r1.toList.map ReadB.toRead).map (SamSpec.qname ∘ FQ.Read.name)).all SamSpec.qnameOk) := by
    have hF : ∀ a : ReadB, (SamSpec.qname ∘ FQ.Read.name) a.toRead = (qnameB a.name).data.toList := by
      intro a; exact (SamFast.bl_qname a.name).symm
    have hp : ∀ a b : ReadB, (let q := qnameB a.name; q == qnameB b.name && qnameOkB q) =
        (decide ((qnameB a.name).data.toList = (qnameB b.name).data.toList) &&
          SamSpec.qnameOk (qnameB a.name).data.toList) := by
      intro a b
      simp only []
      rw [qname_ok_eq]
      congr 1
      exact Bool.eq_iff_iff.mpr ((ba_beq _ _).trans decide_eq_true_iff.symm)
    have hz := zip_all_iff (fun a : ReadB => (qnameB a.name).data.toList) SamSpec.qnameOk r1.toList r2.toList
    simp only [List.map_map]
    rw [show (SamSpec.qname ∘ FQ.Read.name) ∘ ReadB.toRead = fun a : ReadB => (qnameB a.name).data.toList from
      funext hF]
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_iff, ← hz, Bool.and_eq_true, beq_iff_eq, Array.size_eq_length_toList,
      Array.size_eq_length_toList, ← Array.all_toList, Array.toList_zip]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [← h2]; congr 1; funext x; rw [hp]
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [← h2]; congr 1; funext x; rw [hp]
  rw [hc]
  split
  · rename_i h
    dsimp only
    rw [h]
    simp only [Option.map_some, Option.some.injEq]
    rw [Array.toList_map, Array.toList_zip]
    exact zip_trim r1.toList r2.toList
  · rename_i h
    dsimp only
    rw [Bool.not_eq_true] at h
    rw [h]
    simp

theorem letters_eq (r : ReadB) (o : Option ByteArray)
    (h : o = match r.seq.data.toList with
      | [] => none
      | s => some (⟨s.toArray⟩ : ByteArray)) : o = if r.seq.isEmpty then none else some r.seq := by
  rw [h]
  split
  · rename_i hn
    have : r.seq.isEmpty = true := by
      simp only [ByteArray.isEmpty, beq_iff_eq]
      have := congrArg List.length hn; simpa using this
    rw [if_pos this]
  · rename_i s hs
    have hne : r.seq.data.toList ≠ [] := by
      intro e; exact hs e
    have : r.seq.isEmpty = false := by
      simp only [ByteArray.isEmpty, beq_eq_false_iff_ne, ne_eq]
      intro e; apply hne; apply List.eq_nil_of_length_eq_zero; simpa using e
    rw [if_neg (by simp [this])]

theorem mateLetters_eq (p : ReadB × ReadB) : mateLetters (SamFast.toReads p) = MapFast.mateLettersB p := by
  obtain ⟨a, b⟩ := p
  unfold mateLetters
  simp only [SamFast.toReads, ReadB.toRead, MapFast.mateLettersB]
  exact Prod.ext (letters_eq a _ rfl) (letters_eq b _ rfl)

/-- **One job of the stream is `mapReads` of its two slices.** -/
theorem job_eq (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList) (s1 s2 : ByteArray) :
    (MapFast.job settings index chrs s1 s2).map bytes = mapReads settings index chrs (bytes s1) (bytes s2) := by
  have h1 := FQ.parseFastqB_eq s1
  have h2 := FQ.parseFastqB_eq s2
  unfold MapFast.job mapReads bytes
  rw [← h1, ← h2]
  cases parseFastqB s1 with
  | error _ => simp [Except.toOption]
  | ok r1 =>
    cases parseFastqB s2 with
    | error _ => simp [Except.toOption]
    | ok r2 =>
      simp only [Except.toOption, Option.map_some]
      rw [← prepPairsB_eq]
      cases MapFast.prepPairsB r1 r2 with
      | none => rfl
      | some P =>
        simp only [Option.map_some, Option.some.injEq]
        rw [alignPairsP_eq]
        have hm : (P.toList.map SamFast.toReads).map mateLetters = P.toList.map MapFast.mateLettersB := by
          rw [List.map_map]; congr 1; funext p; exact mateLetters_eq p
        rw [hm]
        exact SamFast.samChunkS_eq chrs P _

end Spec.MapCopy

#print axioms Spec.MapCopy.job_eq
