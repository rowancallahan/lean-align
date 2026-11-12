import Proofs.Fastq
/-! DRAFT for Rowan (not built by lake, not part of Spec/). A whole-file FASTQ spec over bytes:
what the records of a file ARE, independent of how they are read. Every reader (block reader,
parallel slice parser) is then proved to return exactly `parseFastq bytes`.
PROOF STATUS (this file has no `sorry`; `lake env lean` checks it): `parseFastq_append`, `parseSlices_eq`,
`cutLinesL_spec` / `cutLinesL_boundary`; and, for the byte scan, `findNewlineU_eq` (the USize loop computes `nl`),
`cutLinesL_scanK` / `scanK_boundary` (the serial scan on the buffer = `cutLinesL`, so it cuts at record boundaries),
`linesFrom_eq` / `parseFastq_slice` (reading lines by position from the shared buffer = `lines` / `parseFastq` of the slice).
`pairsOfFiles` is stated, not yet connected to a reader. The record type here is today's (String name/quality); the proposal over
bytes is `ProvisionalSpec.lean`, whose `lines` / `parseLines` / `parseFastq` are textually these. -/
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

-- ## The byte scan: the fast newline search, the serial boundary scan, and reading lines by position

-- from research/io `shim_speed.patch`: the USize newline search the shim would use
theorem usize_le' (a : ByteArray) : a.usize.toNat ≤ a.size := by
  show a.size.toUSize.toNat ≤ a.size
  rw [Nat.toUSize_eq, USize.toNat_ofNat']; exact Nat.mod_le _ _

def findNewlineU (bytes : @& ByteArray) (j : USize) : USize :=
  if h : j < bytes.usize then
    if bytes.uget j (Nat.lt_of_lt_of_le h (usize_le' bytes)) != 10 then findNewlineU bytes (j + 1) else j
  else j
termination_by bytes.usize.toNat - j.toNat
decreasing_by
  have h' : j.toNat < bytes.usize.toNat := h
  have := USize.toNat_lt_size bytes.usize
  have hs : USize.size = 2 ^ System.Platform.numBits := rfl
  rw [USize.toNat_add, USize.toNat_one, Nat.mod_eq_of_lt (by omega)]; omega

-- the spec of "the first newline at or after i (or the end)", by plain recursion (the `while` loop of Spec/Fastq.lean is
-- `partial` underneath and cannot be unfolded in a proof; stating the scan by recursion is what makes it provable)
def nl (b : ByteArray) (i : Nat) : Nat :=
  if h : i < b.size then (if b[i] != 10 then nl b (i + 1) else i) else i
termination_by b.size - i

theorem nl_ge (b : ByteArray) : ∀ n i, b.size - i = n → i ≤ nl b i
  | n, i, hn => by
    unfold nl
    split
    · rename_i h
      split
      · have := nl_ge b (n - 1) (i + 1) (by omega); omega
      · exact Nat.le_refl _
    · exact Nat.le_refl _
termination_by n => n
decreasing_by all_goals omega

theorem nl_le (b : ByteArray) : ∀ n i, b.size - i = n → i ≤ b.size → nl b i ≤ b.size
  | n, i, hn, hi => by
    unfold nl
    split
    · rename_i h
      split
      · exact nl_le b (n - 1) (i + 1) (by omega) (by omega)
      · omega
    · exact hi
termination_by n => n
decreasing_by all_goals omega

-- what `nl` finds: a newline at `nl b i` (when inside), none before it
theorem nl_spec (b : ByteArray) : ∀ n i, b.size - i = n →
    (nl b i < b.size → b.data.toList[nl b i]? = some 10) ∧
    (∀ k, i ≤ k → k < nl b i → b.data.toList[k]? ≠ some 10)
  | n, i, hn => by
    have hnl : nl b i = if h : i < b.size then (if b[i] != 10 then nl b (i + 1) else i) else i := by rw [nl]
    by_cases h : i < b.size
    · rw [dif_pos h] at hnl
      by_cases h10 : b[i] != 10
      · rw [if_pos h10] at hnl
        have ih := nl_spec b (n - 1) (i + 1) (by omega)
        have hb : b.data.toList[i]? ≠ some 10 := by
          simp only [Array.getElem?_toList]
          rw [Array.getElem?_eq_getElem (by simpa using h)]
          simpa [ByteArray.getElem_eq_getElem_data] using h10
        refine ⟨fun hlt => by rw [hnl] at hlt ⊢; exact ih.1 hlt, fun k hk hk2 => ?_⟩
        rw [hnl] at hk2
        rcases Nat.eq_or_lt_of_le hk with rfl | hk'
        · exact hb
        · exact ih.2 k hk' hk2
      · rw [if_neg h10] at hnl
        have : b[i] = 10 := by simpa using h10
        refine ⟨fun _ => ?_, fun k hk hk2 => by omega⟩
        rw [hnl]
        simp only [Array.getElem?_toList]
        rw [Array.getElem?_eq_getElem (by simpa using h)]
        simpa [ByteArray.getElem_eq_getElem_data] using this
    · rw [dif_neg h] at hnl
      exact ⟨fun hlt => by omega, fun k hk hk2 => by omega⟩
termination_by n => n
decreasing_by all_goals omega

-- THE bridge for the fast scan: the USize loop computes `nl` (needs the size guard the shim has: size < 2^32 - 1)
theorem findNewlineU_eq (b : ByteArray) (hs : b.size < 4294967295) :
    ∀ n (j : USize), b.size - j.toNat = n → j.toNat ≤ b.size → (findNewlineU b j).toNat = nl b j.toNat
  | n, j, hn, hj => by
    have hsz : 4294967296 ≤ USize.size := by
      rcases USize.size_eq with h | h <;> omega
    have hP : USize.size = 2 ^ System.Platform.numBits := rfl
    have hus : b.usize.toNat = b.size := by
      show b.size.toUSize.toNat = b.size
      rw [Nat.toUSize_eq, USize.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
    rw [findNewlineU]
    by_cases hlt : j < b.usize
    · have hj' : j.toNat < b.size := by
        have := USize.lt_iff_toNat_lt.1 hlt; omega
      rw [dif_pos hlt]
      have hnl : nl b j.toNat = if b[j.toNat] != 10 then nl b (j.toNat + 1) else j.toNat := by
        rw [nl, dif_pos hj']
      rw [hnl]
      have hu : b.uget j (Nat.lt_of_lt_of_le hlt (usize_le' b)) = b[j.toNat] := rfl
      rw [hu]
      split
      · have hj1 : (j + 1).toNat = j.toNat + 1 := by
          rw [USize.toNat_add, USize.toNat_one, Nat.mod_eq_of_lt (by omega)]
        have := findNewlineU_eq b hs (n - 1) (j + 1) (by rw [hj1]; omega) (by rw [hj1]; omega)
        rw [this, hj1]
      · rfl
    · have : ¬ j.toNat < b.size := by
        intro h; apply hlt; rw [USize.lt_iff_toNat_lt, hus]; exact h
      rw [dif_neg hlt, nl, dif_neg this]
termination_by n => n
decreasing_by all_goals omega

-- ## `nl` cuts `takeLine`
def D (b : ByteArray) (i : Nat) : List UInt8 := b.data.toList.drop i

theorem D_cons (b : ByteArray) (i : Nat) (h : i < b.size) : D b i = b.data.toList[i]'(by simpa using h) :: D b (i + 1) := by
  unfold D
  exact List.drop_eq_getElem_cons _

theorem takeLine_nl (b : ByteArray) : ∀ n i, b.size - i = n → i ≤ b.size →
    (nl b i < b.size → takeLine (D b i) = ((D b i).take (nl b i - i), some (D b (nl b i + 1)))) ∧
    (¬ nl b i < b.size → takeLine (D b i) = (D b i, none))
  | n, i, hn, hi => by
    have hnl : nl b i = if h : i < b.size then (if b[i] != 10 then nl b (i + 1) else i) else i := by rw [nl]
    by_cases h : i < b.size
    · rw [dif_pos h] at hnl
      rw [D_cons b i h]
      have hx : b.data.toList[i]'(by simpa using h) = b[i] := by simp [ByteArray.getElem_eq_getElem_data]
      by_cases h10 : b[i] != 10
      · rw [if_pos h10] at hnl
        have ih := takeLine_nl b (n - 1) (i + 1) (by omega) (by omega)
        have hge := nl_ge b (n - 1) (i + 1) (by omega)
        have hne : (b.data.toList[i]'(by simpa using h) == 10) = false := by
          rw [hx]; simpa using h10
        rw [hnl]
        refine ⟨fun hlt => ?_, fun hlt => ?_⟩
        · have := ih.1 hlt
          unfold takeLine; rw [hne]; simp only [Bool.false_eq_true, if_false]
          rw [this]
          have : nl b (i + 1) - i = (nl b (i + 1) - (i + 1)) + 1 := by omega
          rw [this, List.take_succ_cons]
        · have := ih.2 hlt
          unfold takeLine; rw [hne]; simp only [Bool.false_eq_true, if_false]
          rw [this]
      · rw [if_neg h10] at hnl
        have : b[i] = 10 := by simpa using h10
        rw [hnl]
        refine ⟨fun _ => ?_, fun hlt => absurd h hlt⟩
        have : (b.data.toList[i]'(by simpa using h) == 10) = true := by rw [hx]; simpa using this
        unfold takeLine; rw [this]; simp
    · have hge : D b i = [] := List.drop_eq_nil_of_le (by simpa using (by omega : b.size ≤ i))
      rw [dif_neg h] at hnl
      rw [hge]
      refine ⟨fun hlt => by omega, fun _ => ?_⟩
      rfl
termination_by n => n
decreasing_by all_goals omega

-- ## The serial boundary scan: position after the k-th newline, by recursion on k (the prototype's `scanLines`, made total)
def scanK (b : ByteArray) : Nat → Nat → Option Nat
  | 0, i => some i
  | k + 1, i => if nl b i < b.size then scanK b k (nl b i + 1) else none

theorem scanK_range (b : ByteArray) : ∀ k i p, i ≤ b.size → scanK b k i = some p → i ≤ p ∧ p ≤ b.size
  | 0, i, p, hi, h => by simp [scanK] at h; omega
  | k + 1, i, p, hi, h => by
    unfold scanK at h
    split at h
    · rename_i hlt
      have hge := nl_ge b _ i rfl
      have := scanK_range b k (nl b i + 1) p (by omega) h
      omega
    · cases h

theorem take_cut (c R : List UInt8) (m : Nat) : (c ++ 10 :: R).take (c.length + 1 + m) = c ++ 10 :: R.take m := by
  rw [List.take_append, List.take_of_length_le (by omega)]
  rw [show c.length + 1 + m - c.length = m + 1 by omega, List.take_succ_cons]

-- THE refinement: cutting the list after k lines (`cutLinesL`, whose spec and `Boundary` result are proved above) is exactly what the
-- byte scan computes on the buffer from position i: the prefix is the bytes `[i, p)`, the rest starts at `p`
theorem cutLinesL_scanK (b : ByteArray) : ∀ k i, i ≤ b.size →
    cutLinesL k (D b i) = (scanK b k i).map fun p => ((D b i).take (p - i), D b p)
  | 0, i, hi => by simp [cutLinesL, scanK]
  | k + 1, i, hi => by
    have hT := takeLine_nl b _ i rfl hi
    have hle := nl_le b _ i rfl hi
    have hge := nl_ge b _ i rfl
    unfold cutLinesL scanK
    by_cases hlt : nl b i < b.size
    · rw [if_pos hlt, hT.1 hlt]
      simp only
      rw [cutLinesL_scanK b k (nl b i + 1) (by omega)]
      obtain ⟨hsp, hc10⟩ := takeLine_spec (D b i) _ _ (hT.1 hlt)
      cases hs : scanK b k (nl b i + 1) with
      | none => rfl
      | some p =>
        have hp := scanK_range b k (nl b i + 1) p (by omega) hs
        simp only [Option.map_some]
        congr 1
        have hlen : ((D b i).take (nl b i - i)).length = nl b i - i := by
          simp [D]; omega
        generalize hcdef : (D b i).take (nl b i - i) = c at hsp hc10 hlen ⊢
        generalize hRdef : D b (nl b i + 1) = R at hsp ⊢
        have hq : (D b i).take (p - i) = c ++ 10 :: R.take (p - (nl b i + 1)) := by
          have key := take_cut c R (p - (nl b i + 1))
          rw [hlen, show nl b i - i + 1 + (p - (nl b i + 1)) = p - i by omega, ← hsp] at key
          exact key
        rw [hq]
    · rw [if_neg hlt, (hT.2 hlt)]
      rfl

theorem extract_mk (b : ByteArray) (s e : Nat) : b.extract s e = ByteArray.mk ((D b s).take (e - s)).toArray := by
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  apply Array.ext'
  simp [Array.toList_extract, D]

-- the serial scan cuts at a record boundary: `scanK` finds the position after 4n lines, and the bytes `[i, p)` are a `Boundary`
theorem scanK_boundary (b : ByteArray) (n i p : Nat) (hi : i ≤ b.size) (h : scanK b (4 * n) i = some p) :
    Boundary (b.extract i p) := by
  have := cutLinesL_scanK b (4 * n) i hi
  rw [h] at this
  rw [extract_mk]
  exact cutLinesL_boundary n (D b i) _ _ this

-- ## Reading lines by position (what the prototype's `parseOne` does on the shared buffer)

theorem lines_term (c : List UInt8) (h : ∀ x ∈ c, x != 10) :
    lines (ByteArray.mk (c ++ [10]).toArray) = [stripCR c] := by
  rw [lines_eq, toList_mk, show c ++ [10] = c ++ 10 :: [] from rfl, List.splitOn_append_cons_self,
    List.splitOn_eq_singleton (fun h10 => by simpa using h 10 h10), List.splitOn_nil]
  have he : (stripCR []).size = 0 := by unfold stripCR; simp [ByteArray.size]
  simp [he]

-- the lines of `[s, e)` read by position: each line is `[s, nl)` (a "\r" before the "\n" dropped), the next starts after it
def linesFrom (b : ByteArray) (s e : Nat) : List ByteArray :=
  if s < e then stripCR ((D b s).take (nl b s - s)) :: linesFrom b (nl b s + 1) e else []
termination_by e - s
decreasing_by have := nl_ge b _ s rfl; omega

theorem nl_le_of (b : ByteArray) (s k : Nat) (hsk : s ≤ k) (hk : b.data.toList[k]? = some 10) : nl b s ≤ k := by
  rcases Nat.lt_or_ge k (nl b s) with hlt | hge
  · exact absurd hk ((nl_spec b _ s rfl).2 k hsk hlt)
  · exact hge

theorem mk_append (x y : List UInt8) :
    ByteArray.mk (x ++ y).toArray = ByteArray.mk x.toArray ++ ByteArray.mk y.toArray := by
  apply ByteArray.ext; simp

-- reading by position equals `lines` of the slice, for a slice that ends with "\n" (every slice of the parallel parser does)
theorem linesFrom_eq (b : ByteArray) (e : Nat) (he : e ≤ b.size) (hT : b.data.toList[e - 1]? = some 10) :
    ∀ n s, e - s = n → linesFrom b s e = lines (b.extract s e)
  | n, s, hn => by
    by_cases hs : s < e
    · have hk : e - 1 < b.data.toList.length := by simpa using (List.getElem?_eq_some_iff.1 hT).1
      have hj : nl b s ≤ e - 1 := nl_le_of b s (e - 1) (by omega) hT
      have hjs : nl b s < b.size := by omega
      have hge := nl_ge b _ s rfl
      have hT' := (takeLine_nl b _ s rfl (by omega)).1 hjs
      obtain ⟨hsp, hc10⟩ := takeLine_spec (D b s) _ _ hT'
      have hlen : ((D b s).take (nl b s - s)).length = nl b s - s := by
        simp [D]; omega
      rw [linesFrom, if_pos hs]
      generalize hcdef : (D b s).take (nl b s - s) = c at hsp hc10 hlen ⊢
      have hl2 : (D b s).take (e - s) = c ++ [10] ++ (D b (nl b s + 1)).take (e - (nl b s + 1)) := by
        have key := take_cut c (D b (nl b s + 1)) (e - (nl b s + 1))
        rw [hlen, show nl b s - s + 1 + (e - (nl b s + 1)) = e - s by omega, ← hsp] at key
        rw [key]; simp
      have ih := linesFrom_eq b e he hT (e - (nl b s + 1)) (nl b s + 1) rfl
      rw [extract_mk, hl2, mk_append, lines_append_of_end, lines_term c hc10, ← extract_mk, ← ih]
      rfl
    · rw [linesFrom, if_neg hs]
      have : b.extract s e = ByteArray.empty := ByteArray.extract_eq_empty_iff.2 (by omega)
      rw [this, lines_empty]
termination_by n => n
decreasing_by all_goals omega


#print axioms parseFastq_append
#print axioms parseSlices_eq
#print axioms cutLinesL_spec
-- parsing one slice straight from the shared buffer (lines by position) = `parseFastq` of that slice
theorem parseFastq_slice (b : ByteArray) (s e : Nat) (he : e ≤ b.size) (hT : b.data.toList[e - 1]? = some 10) :
    parseFastq (b.extract s e) = parseLines (linesFrom b s e) := by
  rw [linesFrom_eq b e he hT _ s rfl]; rfl

#print axioms cutLinesL_boundary
#print axioms findNewlineU_eq
#print axioms cutLinesL_scanK
#print axioms scanK_boundary
#print axioms linesFrom_eq
#print axioms parseFastq_slice

end Spec.Draft
