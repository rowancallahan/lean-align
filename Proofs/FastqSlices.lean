import Proofs.Fastq
/-! The shim cuts each FASTQ file at every `4 · jobPairs`-th newline, parses the slices separately and joins the results.
This file proves, on lists, that this equals `parse` of the whole file (`slices_parse`), using `parse_cons`, `parse_of_records`
and `parse_some` of Proofs/Fastq.lean. Check: `lake env lean Testing/notes/byte_specs/FastqSlices.lean`.
Model: `cutLines n l` = the bytes up to and including the n-th newline, and the rest (the reader's `cutAfter`);
`sliceAt n l` = `l` cut that way again and again; the last slice has fewer than `n` newlines (it may lack the final one). -/
namespace Spec.FQ

-- the first line (without its newline) and what follows; none if there is no newline
def splitNl : List UInt8 → Option (List UInt8 × List UInt8)
  | [] => none
  | x :: xs => if x = newline then some ([], xs) else (splitNl xs).map fun (c, r) => (x :: c, r)

theorem splitNl_append : ∀ (c r : List UInt8), newline ∉ c → splitNl (c ++ newline :: r) = some (c, r)
  | [], r, _ => by simp [splitNl]
  | x :: xs, r, h => by
    have hx : x ≠ newline := fun e => h (by simp [e])
    have ih := splitNl_append xs r (fun e => h (List.mem_cons_of_mem _ e))
    simp [splitNl, hx, ih]

theorem splitNl_spec : ∀ (l c r : List UInt8), splitNl l = some (c, r) → l = c ++ newline :: r
  | [], c, r, h => by simp [splitNl] at h
  | x :: xs, c, r, h => by
    unfold splitNl at h
    split at h
    · rename_i hx
      obtain ⟨rfl, rfl⟩ := by simpa using h
      simp [hx]
    · cases hr : splitNl xs with
      | none => simp [hr] at h
      | some p =>
        obtain ⟨c', r'⟩ := p
        simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [splitNl_spec xs c' r' hr]; rfl

def cutLines : Nat → List UInt8 → Option (List UInt8 × List UInt8)
  | 0, l => some ([], l)
  | n + 1, l => (splitNl l).bind fun (c, rest) => (cutLines n rest).map fun (pre, post) => (c ++ newline :: pre, post)

theorem cutLines_spec : ∀ (n : Nat) (l pre post : List UInt8), cutLines n l = some (pre, post) → l = pre ++ post
  | 0, l, pre, post, h => by simp [cutLines] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | n + 1, l, pre, post, h => by
    unfold cutLines at h
    cases hs : splitNl l with
    | none => simp [hs] at h
    | some p =>
      obtain ⟨c, rest⟩ := p
      cases hc : cutLines n rest with
      | none => simp [hs, hc] at h
      | some q =>
        obtain ⟨p1, p2⟩ := q
        simp only [hs, hc, Option.bind_some, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [splitNl_spec l c rest hs, cutLines_spec n rest p1 p2 hc]; simp

-- a valid record is exactly four lines
theorem cutLines_record (r : Record) (hr : r.valid) (m : Nat) (x : List UInt8) :
    cutLines (m + 4) (toBytes r ++ x) = (cutLines m x).map fun (p, q) => (toBytes r ++ p, q) := by
  obtain ⟨h1, h2, h3, h4⟩ := valid_no_newline r hr
  have e : toBytes r ++ x = r.name ++ newline :: (r.sequence ++ newline :: (r.plus ++ newline :: (r.quality ++ newline :: x))) := by
    simp [toBytes]
  rw [e]
  simp only [show m + 4 = m + 1 + 1 + 1 + 1 from rfl, cutLines, splitNl_append _ _ h1, splitNl_append _ _ h2,
    splitNl_append _ _ h3, splitNl_append _ _ h4, Option.bind_some]
  cases cutLines m x <;> simp [toBytes]

-- cutting a valid file after 4k lines cuts between records
theorem cutLines_valid : ∀ (k : Nat) (rs : List Record), (∀ r ∈ rs, r.valid) → ∀ pre post,
    cutLines (4 * k) (rs.flatMap toBytes) = some (pre, post) →
    ∃ rs1 rs2, rs = rs1 ++ rs2 ∧ pre = rs1.flatMap toBytes ∧ post = rs2.flatMap toBytes
  | 0, rs, _, pre, post, h => by
    simp [cutLines] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rs, rfl, rfl, rfl⟩
  | k + 1, [], _, pre, post, h => by
    simp [show 4 * (k + 1) = 4 * k + 3 + 1 from by omega, cutLines, splitNl] at h
  | k + 1, r :: rs, hv, pre, post, h => by
    have hr := hv r (by simp)
    rw [List.flatMap_cons, show 4 * (k + 1) = 4 * k + 4 from by omega, cutLines_record r hr] at h
    cases hc : cutLines (4 * k) (rs.flatMap toBytes) with
    | none => simp [hc] at h
    | some q =>
      obtain ⟨p1, p2⟩ := q
      simp only [hc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rs1, rs2, e, e1, e2⟩ := cutLines_valid k rs (fun x m => hv x (List.mem_cons_of_mem _ m)) p1 p2 hc
      exact ⟨r :: rs1, rs2, by simp [e], by simp [e1], e2⟩

-- the slices
def sliceAt (n : Nat) (l : List UInt8) : List (List UInt8) :=
  if l = [] then [] else
  match hc : cutLines n l with
  | some (pre, post) => if hp : pre = [] then [l] else pre :: sliceAt n post
  | none => [l]
termination_by l.length
decreasing_by
  have h1 := cutLines_spec n l pre post hc
  have h2 : 0 < pre.length := List.length_pos_iff.2 hp
  rw [h1, List.length_append]; omega

-- a parsed prefix: parse the rest and put the reads behind
theorem parse_append (a b : List UInt8) (ra : List Read) (ha : parse a = some ra) :
    parse (a ++ b) = (parse b).map (ra ++ ·) := by
  obtain ⟨rs, hv, rfl, rfl⟩ := parse_some a ra ha
  induction rs with
  | nil => simp
  | cons r rs ih =>
    rw [List.flatMap_cons, List.append_assoc, parse_cons r (hv r (by simp)), ih (fun x m => hv x (List.mem_cons_of_mem _ m))]
    · cases parse b <;> simp
    · exact parse_of_records rs (fun x m => hv x (List.mem_cons_of_mem _ m))

-- THE theorem: slice, parse each slice, join = parse the whole file
theorem slices_parse (n : Nat) (hn : ∃ k, n = 4 * k) : ∀ (len : Nat) (bytes : List UInt8), bytes.length = len →
    ((sliceAt n bytes).mapM parse).map List.flatten = parse bytes := by
  obtain ⟨k, rfl⟩ := hn
  intro len
  induction len using Nat.strongRecOn with
  | _ len ih =>
    intro bytes hl
    rw [sliceAt]
    by_cases hb : bytes = []
    · subst hb
      have := parse_of_records [] (by simp)
      simp at this
      simp [this]
    · rw [if_neg hb]
      split
      · rename_i pre post hc
        split
        · rename_i hp
          rw [List.mapM_cons, List.mapM_nil]
          cases parse bytes <;> simp
        · rename_i hp
          have hsp := cutLines_spec _ bytes pre post hc
          have hlt : post.length < len := by
            have : 0 < pre.length := List.length_pos_iff.2 hp
            rw [← hl, hsp, List.length_append]; omega
          have ih' := ih post.length hlt post rfl
          rw [List.mapM_cons]
          cases hpa : parse pre with
          | none =>
            -- the whole file cannot parse: a parsing file would be cut at a record boundary, so `pre` would parse
            symm
            apply parse_none
            rintro ⟨rs, hv, hrs⟩
            subst hsp
            obtain ⟨rs1, rs2, e, e1, e2⟩ := cutLines_valid k rs hv pre post (by rw [hrs]; exact hc)
            have := parse_of_records rs1 (fun x m => hv x (by rw [e]; exact List.mem_append_left _ m))
            rw [← e1, hpa] at this
            cases this
          | some ra =>
            rw [hsp, parse_append pre post ra hpa, ← ih']
            cases (sliceAt (4 * k) post).mapM parse <;> simp
      · rw [List.mapM_cons, List.mapM_nil]
        cases parse bytes <;> simp

#print axioms slices_parse

end Spec.FQ
