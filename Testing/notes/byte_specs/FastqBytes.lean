import Proofs.Fastq
/-! DRAFT for Rowan (not built by lake, not part of Spec/). A whole-file FASTQ spec over bytes:
what the records of a file ARE, independent of how they are read. Every reader (block reader,
parallel slice parser) is then proved to return exactly `parseFastq bytes`.
PROOF STATUS (this file has no `sorry`; `lake env lean` checks it): `parseFastq_append`, `parseSlices_eq`,
`cutLinesL_spec` / `cutLinesL_boundary`. `pairsOfFiles` is stated, not yet connected to a reader. -/
namespace Spec.Draft

theorem toList_loop (bs : ByteArray) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  fun_induction ByteArray.toList.loop bs i r with
  | case1 i r h ih =>
    rw [ih]
    have hi : i < bs.data.toList.length := by simpa using h
    rw [List.drop_eq_getElem_cons hi]
    simp [ByteArray.get!, Array.get!Internal_eq_getElem!, h]
  | case2 i r h =>
    have : bs.data.toList.length ≤ i := by simpa using h
    simp [List.drop_eq_nil_of_le this]

theorem toList_eq (bs : ByteArray) : bs.toList = bs.data.toList := by
  unfold ByteArray.toList
  simp [toList_loop]

def lines (bytes : ByteArray) : List ByteArray :=
  let ls := (bytes.toList.splitOn 10).map fun l =>
    ByteArray.mk (if l.getLast? = some 13 then l.dropLast else l).toArray
  if ls.getLast?.map (·.size) = some 0 then ls.dropLast else ls

def stripCR (l : List UInt8) : ByteArray := ByteArray.mk (if l.getLast? = some 13 then l.dropLast else l).toArray

theorem lines_eq (bytes : ByteArray) :
    lines bytes = (let ls := (bytes.toList.splitOn 10).map stripCR
      if ls.getLast?.map (·.size) = some 0 then ls.dropLast else ls) := rfl

theorem toList_mk (l : List UInt8) : (ByteArray.mk l.toArray).toList = l := by
  rw [toList_eq]

theorem toList_append' (a b : ByteArray) : (a ++ b).toList = a.toList ++ b.toList := by
  rw [toList_eq, toList_eq, toList_eq]; simp

theorem lines_append_of_end (c b : List UInt8) :
    lines (ByteArray.mk (c ++ [10]).toArray ++ ByteArray.mk b.toArray) =
      lines (ByteArray.mk (c ++ [10]).toArray) ++ lines (ByteArray.mk b.toArray) := by
  rw [lines_eq, lines_eq, lines_eq]
  simp only [toList_append', toList_mk]
  rw [show c ++ [10] ++ b = c ++ 10 :: b by simp, List.splitOn_append_cons_self,
    show c ++ [10] = c ++ 10 :: [] from rfl, List.splitOn_append_cons_self]
  simp only [List.splitOn_nil, List.map_append, List.map_cons, List.map_nil]
  have hY : (List.splitOn 10 b).map stripCR ≠ [] := by simp [List.splitOn_ne_nil]
  have he : (stripCR []).size = 0 := by unfold stripCR; simp [ByteArray.size]
  generalize (List.splitOn 10 c).map stripCR = X
  generalize (List.splitOn 10 b).map stripCR = Y at hY ⊢
  rcases List.eq_nil_or_concat Y with rfl | ⟨Y0, y, rfl⟩
  · exact absurd rfl hY
  · by_cases hy : y.size = 0 <;> simp [hy, he, List.dropLast_append_of_ne_nil]


def parseLines : List ByteArray → Except String (List FastqRecord)
  | [] => .ok []
  | header :: letters :: plus :: quality :: rest => do
      let record ← parseRecord header letters plus quality
      let records ← parseLines rest
      pure (record :: records)
  | _ => .error "file ends inside a record"

def parseFastq (bytes : ByteArray) : Except String (List FastqRecord) := parseLines (lines bytes)

theorem parseLines_append : ∀ (n : Nat) (L1 L2 : List ByteArray), L1.length = 4 * n →
    parseLines (L1 ++ L2) = (parseLines L1).bind fun ra => (parseLines L2).map (ra ++ ·)
  | 0, L1, L2, h => by
    have : L1 = [] := List.length_eq_zero_iff.1 (by omega)
    subst this
    cases hL : parseLines L2 <;> simp [parseLines, hL, Except.bind, Except.map]
  | n + 1, L1, L2, h => by
    match L1, h with
    | a :: b :: c :: d :: rest, h =>
      have hr : rest.length = 4 * n := by simp at h; omega
      simp only [List.cons_append, parseLines]
      rw [parseLines_append n rest L2 hr]
      cases hp : parseRecord a b c d with
      | error e => simp [hp, bind, Except.bind]
      | ok r =>
        cases hr1 : parseLines rest <;> cases hr2 : parseLines L2 <;>
          simp [hp, hr1, hr2, bind, Except.bind, Functor.map, Except.map, pure, Except.pure]


theorem lines_empty : lines ByteArray.empty = [] := by
  rw [lines_eq]
  have : ByteArray.empty.toList = [] := by rw [toList_eq]; rfl
  have he : (stripCR []).size = 0 := by unfold stripCR; simp [ByteArray.size]
  simp [this, List.splitOn_nil, he]

-- THE lemma for parallel parsing
theorem parseFastq_append (a b : ByteArray) (hEnd : a.size = 0 ∨ a[a.size - 1]! = 10)
    (hRec : (lines a).length % 4 = 0) :
    parseFastq (a ++ b) = (parseFastq a).bind fun ra => (parseFastq b).map (ra ++ ·) := by
  unfold parseFastq
  by_cases hsz : a.size = 0
  · have ha : a = ByteArray.empty := by
      apply ByteArray.ext
      have : a.data.size = 0 := hsz
      rw [ByteArray.data_empty]
      exact Array.eq_empty_of_size_eq_zero this
    subst ha
    rw [ByteArray.empty_append, lines_empty]
    cases hb : parseLines (lines b) with
    | error e => rfl
    | ok v => rfl
  · have h10 : a[a.size - 1]! = 10 := hEnd.resolve_left hsz
    have hne : a.data.toList ≠ [] := by
      intro h
      apply hsz
      have : a.data.size = 0 := by rw [← Array.length_toList, h]; rfl
      exact this
    have hlast : a.data.toList.getLast hne = 10 := by
      have hi : a.size - 1 < a.size := by omega
      rw [getElem!_pos a _ hi] at h10
      rw [List.getLast_eq_getElem]
      simp only [Array.length_toList, Array.getElem_toList]
      exact h10
    have hl : a.data.toList = a.data.toList.dropLast ++ [10] := by
      have h := List.dropLast_concat_getLast hne
      rw [hlast] at h
      exact h.symm
    have ha : a = ByteArray.mk (a.data.toList.dropLast ++ [10]).toArray := by
      obtain ⟨d⟩ := a
      simp only at hl ⊢
      rw [← hl]
    have hb : b = ByteArray.mk b.data.toList.toArray := by obtain ⟨d⟩ := b; simp
    have key := lines_append_of_end a.data.toList.dropLast b.data.toList
    rw [← ha, ← hb] at key
    rw [key]
    exact parseLines_append ((lines a).length / 4) (lines a) (lines b) (by omega)


-- ## The parallel parser: parse slices on separate tasks, join the results in slice order

-- a slice that may be followed by more bytes: ends a line (or is empty) and holds whole records
def Boundary (s : ByteArray) : Prop := (s.size = 0 ∨ s[s.size - 1]! = 10) ∧ (lines s).length % 4 = 0

-- all slices but the last are at record boundaries
def Boundaries : List ByteArray → Prop
  | [] => True
  | [_] => True
  | s :: rest@(_ :: _) => Boundary s ∧ Boundaries rest

def concatBytes : List ByteArray → ByteArray
  | [] => ByteArray.empty
  | s :: rest => s ++ concatBytes rest

-- what the task join computes: each slice parsed on its own, results in slice order, the first error in slice order wins
def parseSlices : List ByteArray → Except String (List FastqRecord)
  | [] => .ok []
  | s :: rest => (parseFastq s).bind fun ra => (parseSlices rest).map (ra ++ ·)

theorem parseSlices_eq : ∀ (slices : List ByteArray), Boundaries slices →
    parseSlices slices = parseFastq (concatBytes slices)
  | [], _ => by simp [parseSlices, concatBytes, parseFastq, lines_empty, parseLines]
  | [s], _ => by
    simp only [parseSlices, concatBytes, ByteArray.append_empty]
    cases h : parseFastq s <;> simp [parseSlices, Except.bind, Except.map, h]
  | s :: t :: rest, hb => by
    simp only [Boundaries] at hb
    obtain ⟨hs, hrest⟩ := hb
    have ih := parseSlices_eq (t :: rest) hrest
    rw [concatBytes, parseFastq_append s _ hs.1 hs.2, ← ih]
    simp only [parseSlices]


-- ## The record-boundary finder (list-level spec of the serial scan: cut after the k-th newline)

-- one line: the bytes before the first '\n', and what follows it (none if there is no '\n')
def takeLine : List UInt8 → List UInt8 × Option (List UInt8)
  | [] => ([], none)
  | x :: xs => if x == 10 then ([], some xs) else
      let r := takeLine xs
      (x :: r.1, r.2)

theorem takeLine_spec : ∀ (l c rest : List UInt8), takeLine l = (c, some rest) →
    l = c ++ 10 :: rest ∧ ∀ x ∈ c, x != 10
  | [], c, rest, h => by simp [takeLine] at h
  | x :: xs, c, rest, h => by
    unfold takeLine at h
    by_cases hx : x == 10
    · simp only [hx, if_true, Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have : x = 10 := by simpa using hx
      subst this
      exact ⟨rfl, by simp⟩
    · simp only [hx, Bool.false_eq_true, if_false, Prod.mk.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      have ih := takeLine_spec xs _ rest (Prod.ext rfl h2)
      refine ⟨by simpa using congrArg (x :: ·) ih.1, fun y hy => ?_⟩
      rcases List.mem_cons.1 hy with rfl | hy'
      · simpa using hx
      · exact ih.2 y hy'

-- `cutLinesL k l` = (the first k lines of `l` with their '\n', the rest), if `l` has k newlines
def cutLinesL : Nat → List UInt8 → Option (List UInt8 × List UInt8)
  | 0, l => some ([], l)
  | k + 1, l =>
    match takeLine l with
    | (c, some rest) => (cutLinesL k rest).map fun (pre, post) => (c ++ 10 :: pre, post)
    | _ => none

theorem lines_one_line (c : List UInt8) (h : ∀ x ∈ c, x != 10) :
    (lines (ByteArray.mk (c ++ [10]).toArray)).length = 1 := by
  rw [lines_eq, toList_mk, show c ++ [10] = c ++ 10 :: [] from rfl, List.splitOn_append_cons_self,
    List.splitOn_eq_singleton (fun h10 => by simpa using h 10 h10), List.splitOn_nil]
  have he : (stripCR []).size = 0 := by unfold stripCR; simp [ByteArray.size]
  simp [he]


theorem cutLinesL_spec : ∀ (k : Nat) (l pre post : List UInt8), cutLinesL k l = some (pre, post) →
    l = pre ++ post ∧ (lines (ByteArray.mk pre.toArray)).length = k ∧ (pre = [] ∨ pre.getLast? = some 10)
  | 0, l, pre, post, h => by
    simp only [cutLinesL, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, ?_, Or.inl rfl⟩
    have : ByteArray.mk ([] : List UInt8).toArray = ByteArray.empty := rfl
    rw [this, lines_empty]; rfl
  | k + 1, l, pre, post, h => by
    unfold cutLinesL at h
    split at h
    · rename_i c rest hs
      simp only [Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at h
      obtain ⟨pre', post', hrec, rfl, rfl⟩ := h
      obtain ⟨hl, hlen, hend⟩ := cutLinesL_spec k rest pre' post' hrec
      obtain ⟨hsplit, hc10⟩ := takeLine_spec l c rest hs
      refine ⟨by rw [hsplit, hl]; simp, ?_, Or.inr ?_⟩
      · have key := lines_append_of_end c pre'
        rw [show c ++ 10 :: pre' = (c ++ [10]) ++ pre' by simp]
        have e : ByteArray.mk ((c ++ [10]) ++ pre').toArray =
            ByteArray.mk (c ++ [10]).toArray ++ ByteArray.mk pre'.toArray := by
          apply ByteArray.ext; simp
        rw [e, key, List.length_append, lines_one_line c hc10, hlen]; omega
      · rcases hend with rfl | hend
        · simp
        · rw [List.getLast?_append]
          cases pre' with
          | nil => simp at hend
          | cons y ys => simpa [List.getLast?_cons_cons] using hend
    · simp at h


-- THE finder lemma: cutting after 4n lines gives a slice at a record boundary, so `parseFastq_append` applies to it
theorem cutLinesL_boundary (n : Nat) (l pre post : List UInt8) (h : cutLinesL (4 * n) l = some (pre, post)) :
    Boundary (ByteArray.mk pre.toArray) := by
  obtain ⟨_, hlen, hend⟩ := cutLinesL_spec (4 * n) l pre post h
  refine ⟨?_, by omega⟩
  rcases hend with rfl | hend
  · exact Or.inl rfl
  · right
    have hne : pre ≠ [] := by rintro rfl; simp at hend
    have hi : (ByteArray.mk pre.toArray).size - 1 < (ByteArray.mk pre.toArray).size := by
      have : 0 < pre.length := List.length_pos_iff.2 hne
      simp [ByteArray.size]; omega
    rw [getElem!_pos (ByteArray.mk pre.toArray) _ hi]
    have h1 : pre[pre.length - 1]? = some 10 := by rw [← List.getLast?_eq_getElem?]; exact hend
    obtain ⟨_, hget⟩ := List.getElem?_eq_some_iff.1 h1
    exact hget

-- pairing: the two files have the same number of records and mate names agree, record by record
def pairUp (r1 r2 : List FastqRecord) : Except String (List (FastqRecord × FastqRecord)) :=
  if r1.length != r2.length then .error "FASTQ files out of step: different numbers of reads"
  else (r1.zip r2).mapM fun (x, y) =>
    if mateName x.name == mateName y.name then .ok (x, y) else .error s!"mate names {x.name} / {y.name}"

-- what the shim's reading must produce (trusted today, provable later): the pairs of the two files, in order
def pairsOfFiles (f1 f2 : ByteArray) : Except String (List (FastqRecord × FastqRecord)) := do
  pairUp (← parseFastq f1) (← parseFastq f2)

#print axioms parseFastq_append
#print axioms parseSlices_eq
#print axioms cutLinesL_spec
#print axioms cutLinesL_boundary

end Spec.Draft
