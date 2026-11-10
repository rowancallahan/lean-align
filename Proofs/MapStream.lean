import Proofs.FastqSlices
/-! # The streaming fold equals the whole-file function (`mapFilesFast_correct`), abstractly.

Everything about the two FASTQ files is about lists of bytes (`FQ.parse`); what is done to a pair of reads, and how pairs are
written, is a `Cfg` (the trimmer `tr`, the QNAME `key` and its check `okName`, and `render`, the SAM bytes of a list of pairs,
which only has to be additive: `render (a ++ b) = render a ++ render b`; `SamSpec.body` of `alignPairs` is, because `alignPairs`
is a map and `body` is a zip-map-flatten). -/
namespace Spec.FQ
namespace MapStream

/-! ## Facts about cutting at newlines -/

theorem splitNl_nl_free : ∀ (l c r : List UInt8), splitNl l = some (c, r) → newline ∉ c
  | [], c, r, h => by simp [splitNl] at h
  | x :: xs, c, r, h => by
    unfold splitNl at h
    split at h
    · obtain ⟨rfl, rfl⟩ := by simpa using h
      simp
    · rename_i hx
      cases hr : splitNl xs with
      | none => simp [hr] at h
      | some p =>
        obtain ⟨c', r'⟩ := p
        simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have := splitNl_nl_free xs c' r' hr
        simp only [List.mem_cons, not_or]
        exact ⟨fun e => hx e.symm, this⟩

theorem splitNl_of_mem : ∀ l : List UInt8, newline ∈ l → ∃ c r, splitNl l = some (c, r)
  | [], h => by simp at h
  | x :: xs, h => by
    unfold splitNl
    by_cases hx : x = newline
    · exact ⟨[], xs, by simp [hx]⟩
    · have : newline ∈ xs := by
        rcases List.mem_cons.1 h with e | e
        · exact absurd e.symm hx
        · exact e
      obtain ⟨c, r, hr⟩ := splitNl_of_mem xs this
      exact ⟨x :: c, r, by simp [hx, hr]⟩

theorem cutLines_extend : ∀ (n : Nat) (l pre post R : List UInt8), cutLines n l = some (pre, post) →
    cutLines n (l ++ R) = some (pre, post ++ R)
  | 0, l, pre, post, R, h => by
    simp [cutLines] at h; obtain ⟨rfl, rfl⟩ := h; simp [cutLines]
  | n + 1, l, pre, post, R, h => by
    unfold cutLines at h ⊢
    cases hs : splitNl l with
    | none => simp [hs] at h
    | some p =>
      obtain ⟨c, rest⟩ := p
      have e := splitNl_spec l c rest hs
      have hc := splitNl_nl_free l c rest hs
      cases hr : cutLines n rest with
      | none => simp [hs, hr] at h
      | some q =>
        obtain ⟨p1, p2⟩ := q
        simp only [hs, hr, Option.bind_some, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hsn : splitNl (l ++ R) = some (c, rest ++ R) := by
          rw [e, List.append_assoc, List.cons_append]; exact splitNl_append c _ hc
        simp [hsn, cutLines_extend n rest p1 p2 R hr]

-- the cut holds exactly n newlines
theorem cutLines_count : ∀ (n : Nat) (l pre post : List UInt8), cutLines n l = some (pre, post) →
    pre.count newline = n
  | 0, l, pre, post, h => by simp [cutLines] at h; obtain ⟨rfl, rfl⟩ := h; simp
  | n + 1, l, pre, post, h => by
    unfold cutLines at h
    cases hs : splitNl l with
    | none => simp [hs] at h
    | some p =>
      obtain ⟨c, rest⟩ := p
      have hc := splitNl_nl_free l c rest hs
      have hcc : c.count newline = 0 := List.count_eq_zero.2 hc
      cases hr : cutLines n rest with
      | none => simp [hs, hr] at h
      | some q =>
        obtain ⟨p1, p2⟩ := q
        simp only [hs, hr, Option.bind_some, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have := cutLines_count n rest p1 p2 hr
        rw [List.count_append, List.count_cons_self, hcc, this]; omega

theorem cutLines_some_of_count : ∀ (n : Nat) (l : List UInt8), n ≤ l.count newline → ∃ pre post, cutLines n l = some (pre, post)
  | 0, l, _ => ⟨[], l, by simp [cutLines]⟩
  | n + 1, l, h => by
    have hm : newline ∈ l := List.count_pos_iff.1 (by omega)
    obtain ⟨c, rest, hs⟩ := splitNl_of_mem l hm
    have e := splitNl_spec l c rest hs
    have hcc : c.count newline = 0 := List.count_eq_zero.2 (splitNl_nl_free l c rest hs)
    have hcnt : rest.count newline + 1 = l.count newline := by
      rw [e, List.count_append, List.count_cons_self, hcc]; omega
    obtain ⟨pre, post, hc⟩ := cutLines_some_of_count n rest (by omega)
    exact ⟨c ++ newline :: pre, post, by unfold cutLines; simp [hs, hc]⟩

-- all complete records of a buffer, and what is left (fewer than 4 newlines)
def cutRecords (l : List UInt8) : List UInt8 × List UInt8 :=
  match cutLines (4 * (l.count newline / 4)) l with
  | some (pre, post) => (pre, post)
  | none => ([], l)

theorem cutRecords_spec (l : List UInt8) :
    cutLines (4 * (l.count newline / 4)) l = some (cutRecords l) ∧ (cutRecords l).2.count newline < 4 := by
  obtain ⟨pre, post, h⟩ := cutLines_some_of_count (4 * (l.count newline / 4)) l (by omega)
  have e := cutLines_spec _ l pre post h
  have c := cutLines_count _ l pre post h
  have hc : l.count newline = pre.count newline + post.count newline := by rw [e, List.count_append]
  have : cutRecords l = (pre, post) := by simp [cutRecords, h]
  rw [this]
  exact ⟨h, by show post.count newline < 4; omega⟩

/-! ## Facts about `parse` -/

theorem count_toBytes (r : Record) (hr : r.valid) : (toBytes r).count newline = 4 := by
  obtain ⟨h1, h2, h3, h4⟩ := valid_no_newline r hr
  have z : ∀ l : List UInt8, newline ∉ l → l.count newline = 0 := fun l h => List.count_eq_zero.2 h
  simp only [toBytes, List.count_append, z _ h1, z _ h2, z _ h3, z _ h4]
  simp [newline]

-- a nonempty valid file has at least 4 newlines
theorem parse_few (c : List UInt8) (hne : c ≠ []) (h : c.count newline < 4) : parse c = none := by
  apply parse_none
  rintro ⟨rs, hv, hb⟩
  cases rs with
  | nil => simp at hb; exact hne hb
  | cons r rs =>
    rw [← hb, List.flatMap_cons, List.count_append, count_toBytes r (hv r (by simp))] at h
    omega

-- split a parsing file after a parsing prefix
theorem parse_split (x y : List UInt8) (dx R : List Read) (hx : parse x = some dx) (h : parse (x ++ y) = some R) :
    ∃ M, parse y = some M ∧ R = dx ++ M := by
  rw [parse_append x y dx hx] at h
  cases hy : parse y with
  | none => simp [hy] at h
  | some M => simp [hy] at h; exact ⟨M, rfl, h.symm⟩

theorem parse_nil : parse [] = some [] := by
  have := parse_of_records [] (by simp)
  simpa using this

/-! ## The whole-file function and the streaming step, on lists -/

structure Cfg where
  key : Read → List UInt8
  okName : List UInt8 → Bool
  tr : Read → Read
  render : List (Read × Read) → List UInt8
  header : List UInt8
  render_append : ∀ a b, render (a ++ b) = render a ++ render b

-- `Total.mapFiles` (Spec/Draft/MapFiles.lean) with `key` = `qname ∘ name`, `tr` = `trim ∘ cut`,
-- `render pairs` = `body chrs pairs (alignPairs ... (pairs.map mateLetters))`
def Cfg.mapFiles (c : Cfg) (f1 f2 : List UInt8) : Option (List UInt8) :=
  match parse f1, parse f2 with
  | some r1, some r2 =>
    if r1.map c.key = r2.map c.key ∧ (r1.map c.key).all c.okName = true then
      some (c.header ++ c.render (List.zip (r1.map c.tr) (r2.map c.tr)))
    else none
  | _, _ => none

-- the streaming state: bytes of an incomplete trailing record group per file, and reads waiting for their mate
structure St where
  c1 : List UInt8
  c2 : List UInt8
  p1 : List Read
  p2 : List Read

def Cfg.step (c : Cfg) (s : St) (a b : List UInt8) : Option (St × List UInt8) :=
  match parse (cutRecords (s.c1 ++ a)).1, parse (cutRecords (s.c2 ++ b)).1 with
  | some n1, some n2 =>
    if ((s.p1 ++ n1).take (min (s.p1 ++ n1).length (s.p2 ++ n2).length)).map c.key =
          ((s.p2 ++ n2).take (min (s.p1 ++ n1).length (s.p2 ++ n2).length)).map c.key ∧
        (((s.p1 ++ n1).take (min (s.p1 ++ n1).length (s.p2 ++ n2).length)).map c.key).all c.okName = true then
      some (⟨(cutRecords (s.c1 ++ a)).2, (cutRecords (s.c2 ++ b)).2,
              (s.p1 ++ n1).drop (min (s.p1 ++ n1).length (s.p2 ++ n2).length),
              (s.p2 ++ n2).drop (min (s.p1 ++ n1).length (s.p2 ++ n2).length)⟩,
            c.render (List.zip (((s.p1 ++ n1).take (min (s.p1 ++ n1).length (s.p2 ++ n2).length)).map c.tr)
                               (((s.p2 ++ n2).take (min (s.p1 ++ n1).length (s.p2 ++ n2).length)).map c.tr)))
    else none
  | _, _ => none

def finish (s : St) : Option (List UInt8) :=
  if s.c1 = [] ∧ s.c2 = [] ∧ s.p1 = [] ∧ s.p2 = [] then some [] else none

/-! ## The invariant: what the state says about the bytes read so far -/

def Inv (c : Cfg) (s : St) (out F1 F2 : List UInt8) : Prop :=
  ∃ X1 X2 E1 E2, F1 = X1 ++ s.c1 ∧ F2 = X2 ++ s.c2 ∧
    parse X1 = some (E1 ++ s.p1) ∧ parse X2 = some (E2 ++ s.p2) ∧
    s.c1.count newline < 4 ∧ s.c2.count newline < 4 ∧
    E1.length = E2.length ∧ E1.map c.key = E2.map c.key ∧ (E1.map c.key).all c.okName = true ∧
    (s.p1 = [] ∨ s.p2 = []) ∧
    out = c.header ++ c.render (List.zip (E1.map c.tr) (E2.map c.tr))

-- whatever follows the bytes read so far, cutting the buffer at record boundaries cuts the valid file at record boundaries
theorem decomp (X D : List Read) (XB cc a T : List UInt8) (R : List Read) (hX : parse XB = some D)
    (hF : parse (XB ++ (cc ++ a ++ T)) = some R) :
    ∃ n M, parse (cutRecords (cc ++ a)).1 = some n ∧ parse ((cutRecords (cc ++ a)).2 ++ T) = some M ∧
      R = D ++ (n ++ M) := by
  obtain ⟨M', hM', hR⟩ := parse_split XB (cc ++ a ++ T) D R hX hF
  obtain ⟨rs, hv, hb, hm⟩ := parse_some _ M' hM'
  obtain ⟨hc, -⟩ := cutRecords_spec (cc ++ a)
  have hext := cutLines_extend _ _ _ _ T hc
  rw [← hb] at hext
  obtain ⟨rs1, rs2, e, e1, e2⟩ := cutLines_valid _ rs hv _ _ hext
  have p1 := parse_of_records rs1 (fun x m => hv x (by rw [e]; exact List.mem_append_left _ m))
  have p2 := parse_of_records rs2 (fun x m => hv x (by rw [e]; exact List.mem_append_right _ m))
  rw [← e1] at p1
  rw [← e2] at p2
  refine ⟨rs1.map toRead, rs2.map toRead, p1, p2, ?_⟩
  rw [hR, ← hm, e]; simp

-- a successful step keeps the invariant
theorem step_inv (c : Cfg) (s s' : St) (a b piece out F1 F2 : List UInt8) (hI : Inv c s out F1 F2)
    (h : c.step s a b = some (s', piece)) : Inv c s' (out ++ piece) (F1 ++ a) (F2 ++ b) := by
  obtain ⟨X1, X2, E1, E2, hF1, hF2, hp1, hp2, hc1, hc2, hl, hk, hok, hone, hout⟩ := hI
  obtain ⟨hcut1, hcnt1⟩ := cutRecords_spec (s.c1 ++ a)
  obtain ⟨hcut2, hcnt2⟩ := cutRecords_spec (s.c2 ++ b)
  have hsp1 : s.c1 ++ a = (cutRecords (s.c1 ++ a)).1 ++ (cutRecords (s.c1 ++ a)).2 := cutLines_spec _ _ _ _ hcut1
  have hsp2 : s.c2 ++ b = (cutRecords (s.c2 ++ b)).1 ++ (cutRecords (s.c2 ++ b)).2 := cutLines_spec _ _ _ _ hcut2
  unfold Cfg.step at h
  generalize cutRecords (s.c1 ++ a) = cr1 at *
  generalize cutRecords (s.c2 ++ b) = cr2 at *
  cases hn1 : parse cr1.1 with
  | none => simp [hn1] at h
  | some n1 =>
  cases hn2 : parse cr2.1 with
  | none => simp [hn1, hn2] at h
  | some n2 =>
  simp only [hn1, hn2] at h
  generalize hr1 : s.p1 ++ n1 = r1 at h
  generalize hr2 : s.p2 ++ n2 = r2 at h
  generalize hkk : min r1.length r2.length = k at h
  split at h
  · rename_i hcond
    obtain ⟨rfl, rfl⟩ := by simpa using h
    have hk1 : k ≤ r1.length := by omega
    have hk2 : k ≤ r2.length := by omega
    have hl1 : (r1.take k).length = k := by simp; omega
    have hl2 : (r2.take k).length = k := by simp; omega
    refine ⟨X1 ++ cr1.1, X2 ++ cr2.1, E1 ++ r1.take k, E2 ++ r2.take k,
      ?_, ?_, ?_, ?_, hcnt1, hcnt2, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hF1, List.append_assoc, hsp1, List.append_assoc]
    · rw [hF2, List.append_assoc, hsp2, List.append_assoc]
    · rw [parse_append X1 _ _ hp1, hn1]
      simp only [Option.map_some, Option.some.injEq]
      rw [← hr1]
      simp [List.append_assoc]
    · rw [parse_append X2 _ _ hp2, hn2]
      simp only [Option.map_some, Option.some.injEq]
      rw [← hr2]
      simp [List.append_assoc]
    · simp [hl, hl1, hl2]
    · rw [List.map_append, List.map_append, hk, hcond.1]
    · rw [List.map_append, List.all_append, hok, hcond.2]; rfl
    · rcases Nat.le_total r1.length r2.length with h12 | h12
      · left; apply List.drop_eq_nil_of_le; omega
      · right; apply List.drop_eq_nil_of_le; omega
    · rw [hout, List.map_append, List.map_append, List.zip_append (by simp [hl]), c.render_append, List.append_assoc]
      simp [List.map_take]
  · simp at h

-- a failing step means the whole files (whatever follows) are not valid, matching FASTQ
theorem step_none (c : Cfg) (s : St) (a b out F1 F2 : List UInt8) (hI : Inv c s out F1 F2)
    (h : c.step s a b = none) (T1 T2 : List UInt8) : c.mapFiles (F1 ++ (a ++ T1)) (F2 ++ (b ++ T2)) = none := by
  obtain ⟨X1, X2, E1, E2, hF1, hF2, hp1, hp2, hc1, hc2, hl, hk, hok, hone, hout⟩ := hI
  cases hmf : c.mapFiles (F1 ++ (a ++ T1)) (F2 ++ (b ++ T2)) with
  | none => rfl
  | some o =>
    exfalso
    unfold Cfg.mapFiles at hmf
    cases hq1 : parse (F1 ++ (a ++ T1)) with
    | none => simp [hq1] at hmf
    | some R1 =>
    cases hq2 : parse (F2 ++ (b ++ T2)) with
    | none => simp [hq1, hq2] at hmf
    | some R2 =>
    simp only [hq1, hq2] at hmf
    split at hmf
    · rename_i hcond
      rw [hF1, show X1 ++ s.c1 ++ (a ++ T1) = X1 ++ (s.c1 ++ a ++ T1) by simp [List.append_assoc]] at hq1
      rw [hF2, show X2 ++ s.c2 ++ (b ++ T2) = X2 ++ (s.c2 ++ b ++ T2) by simp [List.append_assoc]] at hq2
      obtain ⟨n1, M1, hn1, -, hR1⟩ := decomp [] (E1 ++ s.p1) X1 s.c1 a T1 R1 hp1 hq1
      obtain ⟨n2, M2, hn2, -, hR2⟩ := decomp [] (E2 ++ s.p2) X2 s.c2 b T2 R2 hp2 hq2
      unfold Cfg.step at h
      rw [hn1, hn2] at h
      simp only [] at h
      generalize hr1 : s.p1 ++ n1 = r1 at h
      generalize hr2 : s.p2 ++ n2 = r2 at h
      generalize hkk : min r1.length r2.length = k at h
      split at h
      · cases h
      · rename_i hnc
        apply hnc
        have hk1 : k ≤ r1.length := by omega
        have hk2 : k ≤ r2.length := by omega
        have e1 : R1 = E1 ++ (r1 ++ M1) := by rw [hR1, ← hr1]; simp [List.append_assoc]
        have e2 : R2 = E2 ++ (r2 ++ M2) := by rw [hR2, ← hr2]; simp [List.append_assoc]
        rw [e1, e2] at hcond
        obtain ⟨hceq, hcall⟩ := hcond
        simp only [List.map_append] at hceq hcall
        rw [hk] at hceq
        have hceq' := List.append_cancel_left hceq
        have ht := congrArg (List.take k) hceq'
        rw [List.take_append_of_le_length (by simp; omega), List.take_append_of_le_length (by simp; omega)] at ht
        refine ⟨by rw [List.map_take, List.map_take]; exact ht, ?_⟩
        rw [List.all_append, List.all_append] at hcall
        have hb : ((r1.map c.key)).all c.okName = true := by simp at hcall ⊢; exact hcall.2.1
        rw [List.map_take]
        simp only [List.all_eq_true] at hb ⊢
        intro x hx
        exact hb x (List.mem_of_mem_take hx)
    · simp at hmf

-- at the end: leftover bytes or an unmatched read mean the files are not valid, matching FASTQ
theorem finish_eq (c : Cfg) (s : St) (out F1 F2 : List UInt8) (hI : Inv c s out F1 F2) :
    (finish s).map (out ++ ·) = c.mapFiles F1 F2 := by
  obtain ⟨X1, X2, E1, E2, hF1, hF2, hp1, hp2, hc1, hc2, hl, hk, hok, hone, hout⟩ := hI
  unfold finish
  by_cases hfin : s.c1 = [] ∧ s.c2 = [] ∧ s.p1 = [] ∧ s.p2 = []
  · obtain ⟨h1, h2, h3, h4⟩ := hfin
    rw [if_pos ⟨h1, h2, h3, h4⟩]
    unfold Cfg.mapFiles
    rw [hF1, hF2, h1, h2, List.append_nil, List.append_nil, hp1, hp2, h3, h4, List.append_nil, List.append_nil, hout]
    have hok2 : (E2.map c.key).all c.okName = true := by rw [← hk]; exact hok
    simp [hk, hok2]
  · rw [if_neg hfin]
    simp only [Option.map_none]
    unfold Cfg.mapFiles
    by_cases h1 : s.c1 = []
    · by_cases h2 : s.c2 = []
      · rw [hF1, hF2, h1, h2, List.append_nil, List.append_nil, hp1, hp2]
        simp only []
        rw [if_neg]
        intro hc
        have hlen := congrArg List.length hc.1
        simp only [List.length_map, List.length_append] at hlen
        have e1 : s.p1.length = 0 ∨ s.p2.length = 0 := by rcases hone with h | h <;> simp [h]
        have hp1' : s.p1 = [] := List.length_eq_zero_iff.1 (by omega)
        have hp2' : s.p2 = [] := List.length_eq_zero_iff.1 (by omega)
        exact hfin ⟨h1, h2, hp1', hp2'⟩
      · rw [hF2, parse_append X2 s.c2 _ hp2, parse_few _ h2 hc2]
        cases parse F1 <;> simp
    · rw [hF1, parse_append X1 s.c1 _ hp1, parse_few _ h1 hc1]
      simp

-- the streaming fold from any invariant state
theorem run_gen (c : Cfg) : ∀ (blocks : List (List UInt8 × List UInt8)) (s : St) (out F1 F2 : List UInt8),
    Inv c s out F1 F2 →
    (blocks.foldlM (fun (sofar : St × List UInt8) (bp : List UInt8 × List UInt8) =>
        (c.step sofar.1 bp.1 bp.2).map fun (n, piece) => (n, sofar.2 ++ piece)) (s, out)).bind
      (fun sofar => (finish sofar.1).map fun last => sofar.2 ++ last) =
    c.mapFiles (F1 ++ blocks.flatMap (·.1)) (F2 ++ blocks.flatMap (·.2))
  | [], s, out, F1, F2, hI => by
    simp only [List.foldlM_nil, List.flatMap_nil, List.append_nil]
    exact finish_eq c s out F1 F2 hI
  | (a, b) :: rest, s, out, F1, F2, hI => by
    simp only [List.foldlM_cons, List.flatMap_cons]
    cases hst : c.step s a b with
    | none =>
      simp only [Option.map_none, Option.bind_none]
      exact (step_none c s a b out F1 F2 hI hst (rest.flatMap (·.1)) (rest.flatMap (·.2))).symm
    | some p =>
      obtain ⟨s', piece⟩ := p
      simp only [Option.map_some, Option.bind_some]
      have := run_gen c rest s' (out ++ piece) (F1 ++ a) (F2 ++ b) (step_inv c s s' a b piece out F1 F2 hI hst)
      simp only [List.append_assoc] at this
      exact this

-- THE theorem (list level): start, one step per pair of blocks, end = the whole-file function
theorem render_nil (c : Cfg) : c.render [] = [] := by
  have := c.render_append [] []
  simpa using this

theorem fast_correct (c : Cfg) (blocks : List (List UInt8 × List UInt8)) :
    (blocks.foldlM (fun (sofar : St × List UInt8) (bp : List UInt8 × List UInt8) =>
        (c.step sofar.1 bp.1 bp.2).map fun (n, piece) => (n, sofar.2 ++ piece)) (⟨[], [], [], []⟩, c.header)).bind
      (fun sofar => (finish sofar.1).map fun last => sofar.2 ++ last) =
    c.mapFiles (blocks.flatMap (·.1)) (blocks.flatMap (·.2)) := by
  have := run_gen c blocks ⟨[], [], [], []⟩ c.header [] [] ⟨[], [], [], [], rfl, rfl, by simp [parse_nil], by simp [parse_nil],
    by simp, by simp, rfl, rfl, rfl, Or.inl rfl, by simp [render_nil]⟩
  simpa using this

#print axioms fast_correct

end MapStream
end Spec.FQ
