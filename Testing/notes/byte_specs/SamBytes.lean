import Proofs.Sam
/-! DRAFT for Rowan (not built by lake, not part of Spec/). The SAM output file as bytes, stated with the
readable String functions already in Spec/Sam.lean. A fast byte writer (`samChunkB`, research/io2,
Testing/notes/sam_bytes.patch, proved equal to `samChunk` there) is then equal to `samFile` chunk by chunk.
PROOF STATUS (no `sorry`): `linesBytes_append`, `samFile_chunks`, `samChunk_eq` (the chunk the shim writes is
`linesBytes` of all its pairs' lines). Composition with `samChunkB_eq`: see LEMMAS.md. -/
namespace Spec.Draft

def linesBytes (lines : List String) : ByteArray := (String.join (lines.map (· ++ "\n"))).toUTF8

def samFile (chromosomes : ChromosomeList) (pairs : List ((FastqRecord × FastqRecord) × PairResult)) : ByteArray :=
  linesBytes (samHeader chromosomes) ++
    linesBytes (pairs.flatMap fun ((record1, record2), result) => samLines chromosomes record1 record2 result)

theorem linesBytes_append (l1 l2 : List String) : linesBytes (l1 ++ l2) = linesBytes l1 ++ linesBytes l2 := by
  unfold linesBytes
  induction l1 with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, List.map_cons, String.join_cons, String.toUTF8_eq_toByteArray, String.toByteArray_append] at ih ⊢
    rw [ih]
    simp only [ByteArray.append_assoc]

theorem samFile_chunks (chromosomes : ChromosomeList) (chunks : List (List ((FastqRecord × FastqRecord) × PairResult))) :
    samFile chromosomes chunks.flatten =
      linesBytes (samHeader chromosomes) ++
        (chunks.map fun c => linesBytes (c.flatMap fun ((r1, r2), res) => samLines chromosomes r1 r2 res)).foldl (· ++ ·) ByteArray.empty := by
  unfold samFile
  congr 1
  have hfold : ∀ (bs : List ByteArray) (acc : ByteArray), bs.foldl (· ++ ·) acc = acc ++ bs.foldl (· ++ ·) ByteArray.empty := by
    intro bs
    induction bs with
    | nil => intro acc; simp [ByteArray.append_empty]
    | cons x xs ih =>
      intro acc
      simp only [List.foldl_cons]
      rw [ih (acc ++ x), ih (ByteArray.empty ++ x), ByteArray.empty_append, ByteArray.append_assoc]
  induction chunks with
  | nil => simp [linesBytes]
  | cons c cs ih =>
    simp only [List.flatten_cons, List.flatMap_append, linesBytes_append, List.map_cons, List.foldl_cons, ih]
    rw [hfold _ (ByteArray.empty ++ _), ByteArray.empty_append]


-- the slices `samChunk` uses cover the whole array in order
theorem range_slices (l : List α) (s : Nat) : ∀ m : Nat,
    (List.range m).flatMap (fun k => (l.drop (k * s)).take s) = l.take (m * s)
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.flatMap_append, range_slices l s m, List.flatMap_singleton,
      show (m + 1) * s = m * s + s by rw [Nat.succ_mul], List.take_add]

-- text folding as in `samChunk`
theorem foldl_lines (lines : List String) : ∀ text : String,
    lines.foldl (fun text line => text ++ line ++ "\n") text = text ++ String.join (lines.map (· ++ "\n")) := by
  induction lines with
  | nil => intro text; simp
  | cons x xs ih =>
    intro text
    rw [List.foldl_cons, ih, List.map_cons, String.join_cons]
    simp only [String.append_assoc]

theorem foldl_pairs (f : α → List String) (l : List α) : ∀ text : String,
    l.foldl (fun text x => (f x).foldl (fun text line => text ++ line ++ "\n") text) text =
      text ++ String.join (((l.flatMap f)).map (· ++ "\n")) := by
  induction l with
  | nil => intro text; simp
  | cons x xs ih =>
    intro text
    rw [List.foldl_cons, foldl_lines, ih, List.flatMap_cons, List.map_append, String.join_append, String.append_assoc]


theorem linesBytes_nil : linesBytes [] = ByteArray.empty := by simp [linesBytes]

theorem foldl_linesBytes (L : List β) (S : β → List String) : ∀ acc : ByteArray,
    L.foldl (fun b x => b ++ linesBytes (S x)) acc = acc ++ linesBytes (L.flatMap S) := by
  induction L with
  | nil => intro acc; simp [linesBytes_nil, ByteArray.append_empty]
  | cons x xs ih =>
    intro acc
    rw [List.foldl_cons, ih, List.flatMap_cons, linesBytes_append, ByteArray.append_assoc]

theorem foldl_tasks (T : Nat → ByteArray) (L : List Nat) : ∀ acc : ByteArray,
    (L.map fun part => Task.spawn fun _ => T part).foldl (fun bytes task => bytes ++ task.get) acc =
      L.foldl (fun bytes part => bytes ++ T part) acc := by
  induction L with
  | nil => intro acc; rfl
  | cons x xs ih => intro acc; exact ih _

-- one task's text, as bytes
theorem slice_bytes (chromosomes : ChromosomeList) (pairs : Array ((FastqRecord × FastqRecord) × PairResult))
    (size part : Nat) :
    ((pairs.extract (part * size) ((part + 1) * size)).foldl (init := "")
      fun text ((record1, record2), result) =>
        (samLines chromosomes record1 record2 result).foldl (fun text line => text ++ line ++ "\n") text).toUTF8 =
    linesBytes (((pairs.toList.drop (part * size)).take size).flatMap fun ((r1, r2), res) => samLines chromosomes r1 r2 res) := by
  have hlen : (part + 1) * size - part * size = size := by rw [Nat.succ_mul]; omega
  rw [← Array.foldl_toList, Array.toList_extract, List.extract_eq_drop_take, hlen]
  have key := foldl_pairs (fun x : (FastqRecord × FastqRecord) × PairResult =>
    match x with | ((r1, r2), res) => samLines chromosomes r1 r2 res) ((pairs.toList.drop (part * size)).take size) ""
  refine (congrArg String.toUTF8 key).trans ?_
  simp [linesBytes]

-- `samChunk`: the chunk's pairs cut into `parts` slices, formatted on tasks, joined in order = one `linesBytes` of all lines
theorem samChunk_eq (chromosomes : ChromosomeList) (chunk : Array (FastqRecord × FastqRecord))
    (results : List PairResult) (parts : Nat) (hp : 0 < parts) :
    samChunk chromosomes chunk results parts =
      linesBytes ((chunk.zip results.toArray).toList.flatMap fun ((r1, r2), res) => samLines chromosomes r1 r2 res) := by
  unfold samChunk
  dsimp only
  generalize chunk.zip results.toArray = pairs
  have hcover : pairs.size ≤ parts * ((pairs.size + parts - 1) / parts) := by
    have h1 := Nat.div_add_mod (pairs.size + parts - 1) parts
    have h2 := Nat.mod_lt (pairs.size + parts - 1) hp
    generalize parts * ((pairs.size + parts - 1) / parts) = P at h1 ⊢
    omega
  generalize (pairs.size + parts - 1) / parts = size at hcover ⊢
  rw [foldl_tasks]
  simp only [slice_bytes]
  rw [foldl_linesBytes, ByteArray.empty_append, ← List.flatMap_assoc, range_slices pairs.toList size parts,
    List.take_of_length_le (by simpa using hcover)]

-- the digit writer a byte SAM writer needs: decimal digits pushed straight into the buffer
def pushNat (out : ByteArray) (n : Nat) : ByteArray := out ++ (toString n).toUTF8   -- spec; fast version proved equal
-- (the digit-by-digit version is proved equal in research/io2: Proofs/SamBytes.lean `pushNat_eq`, `pushInt_eq`)

#print axioms samFile_chunks
#print axioms samChunk_eq

end Spec.Draft
