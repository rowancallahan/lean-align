/-! # Unique genomes: every k-mer once on both strands ⇒ every two 150-letter windows are far apart

Proved here (no `sorry`, standard axioms only, nothing from `Spec/`):
* `windows_far_edits`: if every k-mer of the strands occurs once and `(d + 1) * k ≤ L`, two windows of
  length `L` within edit distance `d` lie on the same strand and start at most `d` apart.
  (Shifts `≤ d` cannot be excluded: the windows at `i` and `i + 1` are always 2 edits apart.)
* `windows_far_hamming`: under the same hypotheses, two different windows differ in more than `d` letters.
* `checkUnique_sound`: the executable checker (sort the k-mer codes, check strictly increasing) is sound.

Pigeonhole: cut the first window into `d + 1` blocks of `k`; `d` edits touch at most `d` blocks, so one block
appears exactly in the other window, as the same k-mer of the genome; uniqueness puts both at one place. -/

namespace UniqueGenome

/-! ## Edit distance -/

/-- `Edits u v n`: `u` becomes `v` with `n` substitutions, deletions and insertions (Levenshtein). -/
inductive Edits {α : Type} : List α → List α → Nat → Prop
  | nil : Edits [] [] 0
  | keep (a : α) {u v n} : Edits u v n → Edits (a :: u) (a :: v) n
  | sub (a b : α) {u v n} : Edits u v n → Edits (a :: u) (b :: v) (n + 1)
  | del (a : α) {u v n} : Edits u v n → Edits (a :: u) v (n + 1)
  | ins (b : α) {u v n} : Edits u v n → Edits u (b :: v) (n + 1)

/-- edit distance at most `d` -/
def EditDistanceLE {α : Type} (u v : List α) (d : Nat) : Prop := ∃ n ≤ d, Edits u v n

variable {α : Type}

theorem Edits.length {u v : List α} {n : Nat} (h : Edits u v n) :
    u.length ≤ v.length + n ∧ v.length ≤ u.length + n := by
  induction h with
  | nil => simp
  | keep _ _ ih => simp; omega
  | sub _ _ _ ih => simp; omega
  | del _ _ ih => simp; omega
  | ins _ _ ih => simp; omega

theorem Edits.eq_of_zero {u v : List α} {n : Nat} (h : Edits u v n) (h0 : n = 0) : u = v := by
  induction h with
  | nil => rfl
  | keep a _ ih => rw [ih h0]
  | sub => omega
  | del => omega
  | ins => omega

/-- an edit script for `a ++ b` splits into one for `a` and one for `b` -/
theorem Edits.split {u v : List α} {n : Nat} (h : Edits u v n) :
    ∀ a b, u = a ++ b → ∃ c e n₁ n₂, v = c ++ e ∧ Edits a c n₁ ∧ Edits b e n₂ ∧ n₁ + n₂ = n := by
  induction h with
  | nil =>
    intro a b hab
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hab.symm
    exact ⟨[], [], 0, 0, rfl, .nil, .nil, rfl⟩
  | @keep x u v n h ih =>
    intro a b hab
    cases a with
    | nil => simp at hab; subst hab; exact ⟨[], _, 0, n, rfl, .nil, .keep x h, by omega⟩
    | cons y a =>
      simp at hab; obtain ⟨rfl, hu⟩ := hab
      obtain ⟨c, e, n₁, n₂, hv, h₁, h₂, hn⟩ := ih a b hu
      exact ⟨x :: c, e, n₁, n₂, by simp [hv], .keep x h₁, h₂, hn⟩
  | @sub x y u v n h ih =>
    intro a b hab
    cases a with
    | nil => simp at hab; subst hab; exact ⟨[], _, 0, n + 1, rfl, .nil, .sub x y h, by omega⟩
    | cons z a =>
      simp at hab; obtain ⟨rfl, hu⟩ := hab
      obtain ⟨c, e, n₁, n₂, hv, h₁, h₂, hn⟩ := ih a b hu
      exact ⟨y :: c, e, n₁ + 1, n₂, by simp [hv], .sub x y h₁, h₂, by omega⟩
  | @del x u v n h ih =>
    intro a b hab
    cases a with
    | nil => simp at hab; subst hab; exact ⟨[], _, 0, n + 1, rfl, .nil, .del x h, by omega⟩
    | cons z a =>
      simp at hab; obtain ⟨rfl, hu⟩ := hab
      obtain ⟨c, e, n₁, n₂, hv, h₁, h₂, hn⟩ := ih a b hu
      exact ⟨c, e, n₁ + 1, n₂, hv, .del x h₁, h₂, by omega⟩
  | @ins y u v n h ih =>
    intro a b hab
    obtain ⟨c, e, n₁, n₂, hv, h₁, h₂, hn⟩ := ih a b hab
    exact ⟨y :: c, e, n₁ + 1, n₂, by simp [hv], .ins y h₁, h₂, by omega⟩

/-- fewer than `m` edits on `m` blocks of `k`: some block of `u` appears exactly in `v`, shifted by at most `n` -/
theorem Edits.shared_block (k : Nat) : ∀ (m : Nat) (u v : List α) (n : Nat), Edits u v n → n < m →
    m * k ≤ u.length → ∃ p q, p + k ≤ u.length ∧ q + k ≤ v.length ∧
      (u.drop p).take k = (v.drop q).take k ∧ p ≤ q + n ∧ q ≤ p + n := by
  intro m
  induction m with
  | zero => intro u v n _ hn; omega
  | succ m ih =>
    intro u v n h hn hlen
    rw [Nat.succ_mul] at hlen
    obtain ⟨c, e, n₁, n₂, hv, h₁, h₂, hn₁₂⟩ := h.split (u.take k) (u.drop k) (List.take_append_drop k u).symm
    have hc := h₁.length
    have htk : (u.take k).length = k := by simp; omega
    rw [htk] at hc
    by_cases h0 : n₁ = 0
    · have hce := h₁.eq_of_zero h0
      have hcl : c.length = k := by rw [← hce, htk]
      refine ⟨0, 0, by omega, by rw [hv]; simp; omega, ?_, by omega, by omega⟩
      rw [hv, ← hce]; simp [htk]
    · obtain ⟨p, q, hp, hq, heq, h₃, h₄⟩ := ih (u.drop k) e n₂ h₂ (by omega) (by simp; omega)
      simp at hp
      refine ⟨k + p, c.length + q, by omega, by rw [hv]; simp; omega, ?_, by omega, by omega⟩
      have e₁ : u.drop (k + p) = (u.drop k).drop p := by rw [List.drop_drop]
      have e₂ : (c ++ e).drop (c.length + q) = e.drop q := by simp
      rw [hv, e₁, e₂]; exact heq

/-! ## Hamming distance -/

/-- letters that differ, position by position (up to the shorter list) -/
def hamming [DecidableEq α] : List α → List α → Nat
  | a :: u, b :: v => (if a = b then 0 else 1) + hamming u v
  | _, _ => 0

theorem hamming_nil_right [DecidableEq α] (u : List α) : hamming u [] = 0 := by cases u <;> rfl

theorem hamming_split [DecidableEq α] : ∀ (k : Nat) (u v : List α),
    hamming u v = hamming (u.take k) (v.take k) + hamming (u.drop k) (v.drop k)
  | 0, u, v => by simp [hamming]
  | _ + 1, [], v => by simp [hamming]
  | _ + 1, _ :: _, [] => by simp [hamming, hamming_nil_right]
  | k + 1, a :: u, b :: v => by simp [hamming, hamming_split k u v]; omega

theorem eq_of_hamming_zero [DecidableEq α] : ∀ (u v : List α), u.length = v.length → hamming u v = 0 → u = v
  | [], [], _, _ => rfl
  | a :: u, b :: v, hl, h => by
    simp [hamming] at hl h
    obtain ⟨h₁, h₂⟩ := h
    rw [h₁, eq_of_hamming_zero u v hl h₂]

theorem hamming_shared_block [DecidableEq α] (k : Nat) : ∀ (m : Nat) (u v : List α), u.length = v.length →
    hamming u v < m → m * k ≤ u.length → ∃ p, p + k ≤ u.length ∧ (u.drop p).take k = (v.drop p).take k := by
  intro m
  induction m with
  | zero => intro u v _ hn; omega
  | succ m ih =>
    intro u v hl hn hlen
    rw [Nat.succ_mul] at hlen
    rw [hamming_split k] at hn
    by_cases h0 : hamming (u.take k) (v.take k) = 0
    · refine ⟨0, by omega, ?_⟩
      simpa using eq_of_hamming_zero _ _ (by simp; omega) h0
    · obtain ⟨p, hp, heq⟩ := ih (u.drop k) (v.drop k) (by simp; omega) (by omega) (by simp; omega)
      simp at hp
      exact ⟨k + p, by omega, by simpa [List.drop_drop] using heq⟩

/-! ## Strands, k-mers, windows -/

/-- the `k` letters of `s` from position `i` (a window, for `k = L`) -/
def kmerAt (s : List α) (i k : Nat) : List α := (s.drop i).take k

/-- every k-mer of every strand occurs at exactly one (strand, position) -/
def KmersUnique (k : Nat) (S : Array (Array α)) : Prop :=
  ∀ (t t' i j : Nat) (ht : t < S.size) (ht' : t' < S.size), i + k ≤ S[t].size → j + k ≤ S[t'].size →
    kmerAt S[t].toList i k = kmerAt S[t'].toList j k → t = t' ∧ i = j

theorem kmerAt_kmerAt (s : List α) (i L p k : Nat) (h : p + k ≤ L) :
    kmerAt (kmerAt s i L) p k = kmerAt s (i + p) k := by
  simp only [kmerAt, List.drop_take, List.take_take, List.drop_drop]
  rw [Nat.min_eq_left (by omega)]

theorem length_kmerAt (s : List α) (i k : Nat) (h : i + k ≤ s.length) : (kmerAt s i k).length = k := by
  simp [kmerAt]; omega

/-- two windows of length `L` within edit distance `d`: same strand, starts at most `d` apart -/
theorem windows_far_edits {k d L : Nat} {S : Array (Array α)} (hU : KmersUnique k S) (hk : (d + 1) * k ≤ L)
    {t t' i j : Nat} (ht : t < S.size) (ht' : t' < S.size) (hi : i + L ≤ S[t].size) (hj : j + L ≤ S[t'].size)
    (hE : EditDistanceLE (kmerAt S[t].toList i L) (kmerAt S[t'].toList j L) d) :
    t = t' ∧ i ≤ j + d ∧ j ≤ i + d := by
  obtain ⟨n, hn, h⟩ := hE
  have l₁ := length_kmerAt S[t].toList i L (by simpa using hi)
  have l₂ := length_kmerAt S[t'].toList j L (by simpa using hj)
  obtain ⟨p, q, hp, hq, heq, h₃, h₄⟩ := h.shared_block k (d + 1) _ _ n (by omega) (by rw [l₁]; exact hk)
  rw [l₁] at hp; rw [l₂] at hq
  have := hU t t' (i + p) (j + q) ht ht' (by omega) (by omega)
    (by rw [← kmerAt_kmerAt _ _ L _ _ hp, ← kmerAt_kmerAt _ _ L _ _ hq]; exact heq)
  omega

/-- two windows of length `L` differing in at most `d` letters are the same window -/
theorem windows_far_hamming [DecidableEq α] {k d L : Nat} {S : Array (Array α)} (hU : KmersUnique k S)
    (hk : (d + 1) * k ≤ L) {t t' i j : Nat} (ht : t < S.size) (ht' : t' < S.size) (hi : i + L ≤ S[t].size)
    (hj : j + L ≤ S[t'].size) (hH : hamming (kmerAt S[t].toList i L) (kmerAt S[t'].toList j L) ≤ d) :
    t = t' ∧ i = j := by
  have l₁ := length_kmerAt S[t].toList i L (by simpa using hi)
  have l₂ := length_kmerAt S[t'].toList j L (by simpa using hj)
  obtain ⟨p, hp, heq⟩ := hamming_shared_block k (d + 1) (kmerAt S[t].toList i L) (kmerAt S[t'].toList j L)
    (l₁.trans l₂.symm) (by omega) (by rw [l₁]; exact hk)
  rw [l₁] at hp
  have := hU t t' (i + p) (j + p) ht ht' (by omega) (by omega)
    (by rw [← kmerAt_kmerAt _ _ L _ _ hp, ← kmerAt_kmerAt _ _ L _ _ hp]; exact heq)
  omega

/-! ## The strands of a genome -/

/-- A ↔ T, C ↔ G, other bytes unchanged (as `Spec.complementByte`) -/
def complement (b : UInt8) : UInt8 :=
  if b = 65 then 84 else if b = 84 then 65 else if b = 67 then 71 else if b = 71 then 67 else b

def reverseComplement (s : Array UInt8) : Array UInt8 := (s.map complement).reverse

/-- strand `2c` is chromosome `c`, strand `2c + 1` its reverse complement -/
def strands (chromosomes : Array ByteArray) : Array (Array UInt8) :=
  Array.ofFn (n := 2 * chromosomes.size) fun t =>
    let c := chromosomes[t.val / 2]'(by omega)
    if t.val % 2 = 0 then c.data else reverseComplement c.data

theorem strands_size (g : Array ByteArray) : (strands g).size = 2 * g.size := by simp [strands]

theorem strands_forward (g : Array ByteArray) (c : Nat) (hc : c < g.size) :
    (strands g)[2 * c]'(by rw [strands_size]; omega) = g[c].data := by
  simp [strands]

theorem strands_reverse (g : Array ByteArray) (c : Nat) (hc : c < g.size) :
    (strands g)[2 * c + 1]'(by rw [strands_size]; omega) = reverseComplement g[c].data := by
  have h : (2 * c + 1) / 2 = c := by omega
  simp [strands, h]

/-! ## The checker: sort the k-mer codes, check they strictly increase -/

/-- base-4 code of a k-mer (A C G T = 0 1 2 3, anything else 4). Soundness needs no injectivity:
equal k-mers get equal codes, so distinct codes mean distinct k-mers. -/
def letterCode (b : UInt8) : Nat :=
  if b = 65 then 0 else if b = 67 then 1 else if b = 71 then 2 else if b = 84 then 3 else 4

def code : List UInt8 → Nat
  | [] => 0
  | b :: l => letterCode b + 4 * code l

/-- every (strand, start) with a whole k-mer -/
def occurrences (k : Nat) (S : Array (Array UInt8)) : List (Nat × Nat) :=
  (List.range S.size).flatMap fun t => (List.range (S[t]!.size + 1 - k)).map fun i => (t, i)

def kmerCode (k : Nat) (S : Array (Array UInt8)) (o : Nat × Nat) : Nat :=
  code (S[o.1]!.extract o.2 (o.2 + k)).toList

def strictlyIncreasing : List Nat → Bool
  | a :: b :: l => a < b && strictlyIncreasing (b :: l)
  | _ => true

def checkUnique (k : Nat) (S : Array (Array UInt8)) : Bool :=
  strictlyIncreasing (((occurrences k S).map (kmerCode k S)).mergeSort)

theorem strictlyIncreasing_lt : ∀ (a : Nat) (l : List Nat), strictlyIncreasing (a :: l) = true → ∀ x ∈ l, a < x
  | a, b :: l, h, x, hx => by
    simp [strictlyIncreasing] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact Nat.lt_trans h.1 (strictlyIncreasing_lt b l h.2 x hx)

theorem strictlyIncreasing_nodup : ∀ l : List Nat, strictlyIncreasing l = true → l.Nodup
  | [], _ => List.nodup_nil
  | [_], _ => by simp
  | a :: b :: l, h => by
    have hlt := strictlyIncreasing_lt a (b :: l) h
    simp [strictlyIncreasing] at h
    exact List.nodup_cons.mpr ⟨fun hm => Nat.lt_irrefl a (hlt a hm), strictlyIncreasing_nodup (b :: l) h.2⟩

theorem mem_occurrences {k : Nat} {S : Array (Array UInt8)} {t i : Nat} (ht : t < S.size)
    (hi : i + k ≤ S[t].size) : (t, i) ∈ occurrences k S := by
  simp only [occurrences, List.mem_flatMap, List.mem_range, List.mem_map]
  exact ⟨t, ht, i, by rw [getElem!_pos S t ht]; omega, rfl⟩

theorem kmerCode_eq {k : Nat} {S : Array (Array UInt8)} {t i : Nat} (ht : t < S.size) :
    kmerCode k S (t, i) = code (kmerAt S[t].toList i k) := by
  simp [kmerCode, kmerAt, getElem!_pos S t ht, Array.toList_extract, List.extract_eq_take_drop]

theorem eq_of_nodup_map {β γ : Type} {f : β → γ} : ∀ {l : List β}, (l.map f).Nodup →
    ∀ {a b}, a ∈ l → b ∈ l → f a = f b → a = b
  | x :: l, h, a, b, ha, hb, hab => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h
    rcases List.mem_cons.mp ha with h₁ | ha' <;> rcases List.mem_cons.mp hb with h₂ | hb'
    · rw [h₁, h₂]
    · exact absurd ⟨b, hb', h₁ ▸ hab.symm⟩ h.1
    · exact absurd ⟨a, ha', h₂ ▸ hab⟩ h.1
    · exact eq_of_nodup_map h.2 ha' hb' hab

theorem checkUnique_sound (k : Nat) (S : Array (Array UInt8)) (h : checkUnique k S = true) : KmersUnique k S := by
  have hnd : ((occurrences k S).map (kmerCode k S)).Nodup :=
    (List.mergeSort_perm _ _).nodup_iff.mp (strictlyIncreasing_nodup _ h)
  intro t t' i j ht ht' hi hj heq
  have := eq_of_nodup_map hnd (mem_occurrences ht hi) (mem_occurrences ht' hj)
    (by rw [kmerCode_eq ht, kmerCode_eq ht', heq])
  simp at this
  exact this

/-- what the executable establishes when the checker says yes, for windows of 150 -/
theorem genome_windows_far {k d : Nat} (chromosomes : Array ByteArray) (hc : checkUnique k (strands chromosomes) = true)
    (hk : (d + 1) * k ≤ 150) :
    let S := strands chromosomes
    ∀ (t t' i j : Nat) (ht : t < S.size) (ht' : t' < S.size), i + 150 ≤ S[t].size → j + 150 ≤ S[t'].size →
      (hamming (kmerAt S[t].toList i 150) (kmerAt S[t'].toList j 150) ≤ d → t = t' ∧ i = j) ∧
      (EditDistanceLE (kmerAt S[t].toList i 150) (kmerAt S[t'].toList j 150) d → t = t' ∧ i ≤ j + d ∧ j ≤ i + d) :=
  fun _ _ _ _ ht ht' hi hj =>
    ⟨windows_far_hamming (checkUnique_sound k _ hc) hk ht ht' hi hj,
     windows_far_edits (checkUnique_sound k _ hc) hk ht ht' hi hj⟩

end UniqueGenome

#print axioms UniqueGenome.windows_far_edits
#print axioms UniqueGenome.windows_far_hamming
#print axioms UniqueGenome.checkUnique_sound
#print axioms UniqueGenome.genome_windows_far
