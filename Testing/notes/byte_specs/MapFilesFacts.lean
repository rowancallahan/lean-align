import Spec.Draft.MapFiles
/-! Two facts about Spec/Draft/Sam.lean and MapFiles.lean (checked against the Spec lib; `lake env lean <file>`):
1. the SAM body is additive over lists of pairs, so a stream may write it chunk by chunk (`bodyOf_append`);
2. a successful `mapFiles` means the two files have the same number of reads, pairwise with equal valid QNAMEs (`mapFiles_some`).
Proofs/Draft mirrors (S-G, spec/mapfiles) need the same text with their import. -/
namespace Spec.Total
open Spec

theorem body_append (chrs : ChromosomeList) (p1 p2 : List (FQ.Read × FQ.Read)) (r1 r2 : List PairResult)
    (h : p1.length = r1.length) :
    SamSpec.body chrs (p1 ++ p2) (r1 ++ r2) = SamSpec.body chrs p1 r1 ++ SamSpec.body chrs p2 r2 := by
  unfold SamSpec.body
  rw [List.zip_append h, List.map_append, List.flatten_append]

-- `body` of the aligner's results for a list of pairs, whatever `align` is, as long as it works pair by pair
def bodyOf (align : List (Option ByteArray × Option ByteArray) → List PairResult) (chrs : ChromosomeList)
    (pairs : List (FQ.Read × FQ.Read)) : List UInt8 :=
  SamSpec.body chrs pairs (align (pairs.map mateLetters))

theorem bodyOf_append (align : List (Option ByteArray × Option ByteArray) → List PairResult) (chrs : ChromosomeList)
    (happ : ∀ a b, align (a ++ b) = align a ++ align b) (hlen : ∀ xs, (align xs).length = xs.length)
    (p1 p2 : List (FQ.Read × FQ.Read)) :
    bodyOf align chrs (p1 ++ p2) = bodyOf align chrs p1 ++ bodyOf align chrs p2 := by
  unfold bodyOf
  rw [List.map_append, happ, body_append chrs _ _ _ _ (by rw [hlen]; simp)]

theorem zip_of_map_eq {α β γ : Type} (f : α → γ) (g : β → γ) :
    ∀ (xs : List α) (ys : List β), xs.map f = ys.map g → ∀ p ∈ xs.zip ys, f p.1 = g p.2
  | [], [], _, p, hp => by simp at hp
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h
  | x :: xs, y :: ys, h, p, hp => by
    simp only [List.map_cons, List.cons.injEq] at h
    rcases List.mem_cons.1 (by simpa using hp : p ∈ (x, y) :: xs.zip ys) with rfl | hp'
    · exact h.1
    · exact zip_of_map_eq f g xs ys h.2 p hp'

-- if the files map, they have the same number of reads, with pairwise equal valid QNAMEs
theorem mapFiles_some (settings : InsertSettings) (index : ByteArray) (chrs : ChromosomeList)
    (file1 file2 out : List UInt8) (h : mapFiles settings index chrs file1 file2 = some out) :
    ∃ reads1 reads2, FQ.parse file1 = some reads1 ∧ FQ.parse file2 = some reads2 ∧
      reads1.length = reads2.length ∧
      (∀ p ∈ reads1.zip reads2, SamSpec.qname p.1.name = SamSpec.qname p.2.name) ∧
      ∀ r ∈ reads1, SamSpec.qnameOk (SamSpec.qname r.name) = true := by
  unfold mapFiles at h
  cases h1 : FQ.parse file1 with
  | none => simp [h1] at h
  | some reads1 =>
  cases h2 : FQ.parse file2 with
  | none => simp [h1, h2] at h
  | some reads2 =>
  simp only [h1, h2] at h
  unfold prepPairs at h
  simp only [] at h
  split at h
  · rename_i hd
    have hd' := of_decide_eq_true hd
    obtain ⟨heq, hall⟩ := hd'
    refine ⟨reads1, reads2, rfl, rfl, ?_, ?_, ?_⟩
    · have := congrArg List.length heq
      simpa using this
    · exact zip_of_map_eq _ _ reads1 reads2 heq
    · intro r hr
      simp only [List.all_eq_true, List.mem_map] at hall
      exact hall _ ⟨r, hr, rfl⟩
  · simp at h

#print axioms body_append
#print axioms bodyOf_append
#print axioms mapFiles_some

end Spec.Total
