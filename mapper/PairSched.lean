import PairInterleave

/-!
# Codec `pairFastS`: one lookup scheduler over all chromosomes and both strands

`pairFastI` folds the chromosomes one after another, so a read from chromosome 2
has no best while chromosome 1 is searched and looks up all 4 seeds there,
huge repeat buckets included.  Here every (chromosome, strand) is a slot
(slot `i < n`: chromosome `i` forward; `n ≤ i < 2n`: chromosome `i - n` reverse;
the slot is the window tag) with its own lazy-lookup state (`LzS`), and one
shared `Best`.  Each step looks up the next seed of the live slot with the
smallest `key slot k size` (`k` = lookups done in the slot, `size` = its next
bucket).  A slot is live while seeds remain and `4k ≤ best`.  Any `key` is exact:
the proof only uses that a step advances a live slot (`adv_ok`) and that a dead
slot has covered its tag (`dead_cover`).  After the loop (fuel `8n`), `drain`
finishes any slot still live (never in practice).

    … → mapFastS lk key gbs idxs R = mapSpecBoth sc0 (-12) g read             (mapFastS_eq_mapSpecBoth)
    … → pairFastS lk key lo hi gbs idxs R1 R2 = pairSpec sc0 (-12) lo hi g m1 m2 (pairFastS_eq_pairSpec)
    … → pairFastX lk key1 key2 lo hi gbs idxs R1 R2 = pairSpec …               (pairFastX_eq_pairSpec)

`pairFastX` adds two exact early exits (`amb0_final`, `target_final`, see `pairFastX`).
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-! ## Algorithm -/

deriving instance Inhabited for LzS

/-- Chromosome of slot `i`. -/
@[inline] def sChr (n i : Nat) : Nat := if i < n then i else i - n

/-- Read of slot `i`. -/
@[inline] def sRead (n : Nat) (R Rr : ByteArray) (i : Nat) : ByteArray := if i < n then R else Rr

/-- The live slot of `l` with the smallest key (first on ties), or `acc`. -/
@[specialize] def pickLive (live : Nat → Bool) (key : Nat → Nat) : List Nat → Option Nat → Option Nat
  | [], acc => acc
  | i :: l, acc =>
    pickLive live key l (if live i then
      match acc with
      | none => some i
      | some a => if key i < key a then some i else acc
      else acc)

/-- Global loop: one lookup per step in the chosen live slot. -/
@[specialize] def schedLoop {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P)
    (key : Nat → Nat → Nat → Nat) (gbs : Array ByteArray) (idxs : Array L) (R Rr : ByteArray)
    (pss : Array (Array P)) : Nat → Array LzS → Best → Array LzS × Best
  | 0, ss, b => (ss, b)
  | f + 1, ss, b =>
    let n := gbs.size
    match pickLive (fun i => ss[i]!.live b)
        (fun i => key i ss[i]!.k (ss[i]!.next lk idxs[sChr n i]! pss[i]!)) (List.range ss.size) none with
    | none => (ss, b)
    | some i =>
      let r := ss[i]!.adv (sRead n R Rr i) gbs[sChr n i]! i lk idxs[sChr n i]! pss[i]! b
      schedLoop lk key gbs idxs R Rr pss f (ss.set! i r.1) r.2

/-- Finish one slot. -/
@[specialize] def drain {L P : Type} [Inhabited P] (lk : Look L P) (R G : ByteArray) (c : Nat) (ix : L)
    (ps : Array P) : Nat → LzS → Best → Best
  | 0, _, b => b
  | f + 1, s, b =>
    if s.live b then
      let r := s.adv R G c lk ix ps b
      drain lk R G c ix ps f r.1 r.2
    else b

@[specialize] def mapChromsS {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P)
    (key : Nat → Nat → Nat → Nat) (R : ByteArray) (gbs : Array ByteArray) (idxs : Array L) : Best :=
  let n := gbs.size
  let Rr := revCompB R
  let pss := (Array.range (2 * n)).map fun i =>
    prepAll lk idxs[sChr n i]! (seedHashes (sRead n R Rr i))
  let ss0 := (Array.range (2 * n)).map fun i => LzS.init lk idxs[sChr n i]! pss[i]!
  let r := schedLoop lk key gbs idxs R Rr pss (8 * n) ss0 {}
  (List.range (2 * n)).foldl (fun b i =>
    drain lk (sRead n R Rr i) gbs[sChr n i]! i idxs[sChr n i]! pss[i]! 4 r.1[i]! b) r.2

def mapFastS {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P) (key : Nat → Nat → Nat → Nat)
    (gbs : Array ByteArray) (idxs : Array L) (R : ByteArray) : Option (Placement × Int) :=
  decodeJ gbs.size (mapChromsS lk key R gbs idxs)

/-- Mate 2 gets its own key, chosen from mate 1's placement (e.g. its strand). -/
def pairFastS {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P)
    (key1 : Nat → Nat → Nat → Nat) (key2 : Placement → Nat → Nat → Nat → Nat) (lo hi : Nat)
    (gbs : Array ByteArray) (idxs : Array L) (R1 R2 : ByteArray) :
    Option ((Placement × Int) × (Placement × Int)) :=
  match mapFastS lk key1 gbs idxs R1 with
  | none => none
  | some a =>
    match mapFastS lk (key2 a.1) gbs idxs R2 with
    | some b => if properPair lo hi a.1 b.1 then some (a, b) else none
    | none => none

/-! ## Early exit

`stop ss b` ends the search early; the caller decides what a stopped search means.
Two exact uses (`pairFastX`): a best of penalty 0 that is ambiguous stays so
(the read is unmapped), and for mate 2, once the slot of mate 1's chromosome on
the other strand is finished, the pair is kept only if the current best is
already a proper partner (a better or tying window elsewhere would only make it
not proper or ambiguous). -/

@[specialize] def schedLoopX {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P)
    (key : Nat → Nat → Nat → Nat) (stop : Array LzS → Best → Bool) (gbs : Array ByteArray) (idxs : Array L)
    (R Rr : ByteArray) (pss : Array (Array P)) : Nat → Array LzS → Best → Array LzS × Best × Bool
  | 0, ss, b => (ss, b, false)
  | f + 1, ss, b =>
    if stop ss b then (ss, b, true) else
    let n := gbs.size
    match pickLive (fun i => ss[i]!.live b)
        (fun i => key i ss[i]!.k (ss[i]!.next lk idxs[sChr n i]! pss[i]!)) (List.range ss.size) none with
    | none => (ss, b, false)
    | some i =>
      let r := ss[i]!.adv (sRead n R Rr i) gbs[sChr n i]! i lk idxs[sChr n i]! pss[i]! b
      schedLoopX lk key stop gbs idxs R Rr pss f (ss.set! i r.1) r.2

/-- The best, and whether `stop` ended the search. -/
@[specialize] def mapChromsX {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P)
    (key : Nat → Nat → Nat → Nat) (stop : Array LzS → Best → Bool) (R : ByteArray) (gbs : Array ByteArray)
    (idxs : Array L) : Best × Bool :=
  let n := gbs.size
  let Rr := revCompB R
  let pss := (Array.range (2 * n)).map fun i =>
    prepAll lk idxs[sChr n i]! (seedHashes (sRead n R Rr i))
  let ss0 := (Array.range (2 * n)).map fun i => LzS.init lk idxs[sChr n i]! pss[i]!
  let r := schedLoopX lk key stop gbs idxs R Rr pss (8 * n) ss0 {}
  if r.2.2 then (r.2.1, true) else
  ((List.range (2 * n)).foldl (fun b i =>
    drain lk (sRead n R Rr i) gbs[sChr n i]! i idxs[sChr n i]! pss[i]! 4 r.1[i]! b) r.2.1, false)

/-- Ambiguous at penalty 0. -/
@[inline] def amb0 (b : Best) : Bool := b.pen == 0 && b.amb

/-- Slot of mate 2 that can hold a proper partner of mate 1 at `a`. -/
@[inline] def partnerSlot (n : Nat) (a : Placement) : Nat := if a.2 == Strand.fwd then n + a.1.chr else a.1.chr

def pairFastX {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P)
    (key1 : Nat → Nat → Nat → Nat) (key2 : Placement → Nat → Nat → Nat → Nat) (lo hi : Nat)
    (gbs : Array ByteArray) (idxs : Array L) (R1 R2 : ByteArray) :
    Option ((Placement × Int) × (Placement × Int)) :=
  let n := gbs.size
  let r1 := mapChromsX lk key1 (fun _ b => amb0 b) R1 gbs idxs
  if r1.2 then none else
  match decodeJ n r1.1 with
  | none => none
  | some a =>
    let t := partnerSlot n a.1
    let ok (b : Best) : Bool := match decodeJ n b with
      | some x => properPair lo hi a.1 x.1
      | none => false
    let r2 := mapChromsX lk (key2 a.1) (fun ss b => amb0 b || (!ss[t]!.live b && !ok b)) R2 gbs idxs
    if r2.2 then none else
    match decodeJ n r2.1 with
    | some x => if properPair lo hi a.1 x.1 then some (a, x) else none
    | none => none

/-! ## Proofs -/

theorem set!_self {α : Type} [Inhabited α] (a : Array α) (i : Nat) (x : α) (h : i < a.size) :
    (a.set! i x)[i]! = x := by
  simp [Array.set!_eq_setIfInBounds, h]

theorem set!_ne {α : Type} [Inhabited α] (a : Array α) (i j : Nat) (x : α) (h : j ≠ i) :
    (a.set! i x)[j]! = a[j]! := by
  simp [Array.set!_eq_setIfInBounds, getElem!_def, Array.getElem?_setIfInBounds_ne (Ne.symm h)]

theorem pickLive_some (live : Nat → Bool) (key : Nat → Nat) :
    ∀ (l : List Nat) acc i, pickLive live key l acc = some i → acc = some i ∨ (i ∈ l ∧ live i = true) := by
  intro l
  induction l with
  | nil => intro acc i h; exact Or.inl h
  | cons x l ih =>
    intro acc i h
    rcases ih _ i h with h' | ⟨hm, hl⟩
    · by_cases hx : live x = true
      · rw [if_pos hx] at h'
        split at h'
        · cases h'; exact Or.inr ⟨List.mem_cons_self, hx⟩
        · split at h'
          · cases h'; exact Or.inr ⟨List.mem_cons_self, hx⟩
          · exact Or.inl h'
      · rw [if_neg hx] at h'; exact Or.inl h'
    · exact Or.inr ⟨List.mem_cons_of_mem _ hm, hl⟩

theorem pickLive_none (live : Nat → Bool) (key : Nat → Nat) :
    ∀ (l : List Nat) acc, pickLive live key l acc = none → acc = none ∧ ∀ i ∈ l, live i = false := by
  intro l
  induction l with
  | nil => intro acc h; exact ⟨h, fun i hi => by simp at hi⟩
  | cons x l ih =>
    intro acc h
    obtain ⟨h1, h2⟩ := ih _ h
    by_cases hx : live x = true
    · rw [if_pos hx] at h1; split at h1
      · cases h1
      · split at h1 <;> cases h1
    · rw [if_neg hx] at h1
      refine ⟨h1, fun i hi => ?_⟩
      rcases List.mem_cons.mp hi with rfl | hi
      · simpa using hx
      · exact h2 i hi

section sched

variable {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P) (R : ByteArray)
  (gbs : Array ByteArray) (idxs : Array L) (hn : 100 ≤ R.size) (hlk : LookAll lk gbs idxs)

/-- Penalty of slot `i`'s windows. -/
theorem cwJ_slot (i : Nat) (hi : i < 2 * gbs.size) (st len : Nat) :
    cwJ R gbs ⟨i, st, len⟩ = penB (sRead gbs.size R (revCompB R) i) gbs[sChr gbs.size i]! st len := by
  unfold cwJ cwG sRead sChr
  by_cases h : i < gbs.size
  · simp [h]
  · simp [h, hi, show i - gbs.size < gbs.size by omega]

include hn in
theorem sRead_size (i : Nat) : 100 ≤ (sRead gbs.size R (revCompB R) i).size := by
  unfold sRead; split
  · exact hn
  · rw [revCompB_size]; exact hn

omit [Inhabited P] in
include hlk in
theorem slot_lk (i : Nat) (hi : i < 2 * gbs.size) : ∀ j, j < 4 →
    LookOk gbs[sChr gbs.size i]! (sRead gbs.size R (revCompB R) i) j
      (lk.look idxs[sChr gbs.size i]! gbs[sChr gbs.size i]! (sRead gbs.size R (revCompB R) i) j
        (lk.prep idxs[sChr gbs.size i]! (seedHash (sRead gbs.size R (revCompB R) i) j))) :=
  hlk _ (by unfold sChr; split <;> omega) _

/-- Prepared seeds of every slot. -/
def PssOk (pss : Array (Array P)) : Prop :=
  ∀ i, i < 2 * gbs.size → pss[i]! = prepAll lk idxs[sChr gbs.size i]! (seedHashes (sRead gbs.size R (revCompB R) i))

/-- Every slot's state is right for best `b` and looked-at windows `S`. -/
def AllOk (ss : Array LzS) (b : Best) (S : Window → Prop) : Prop :=
  Inv (cwJ R gbs) S b ∧ ss.size = 2 * gbs.size ∧ ∀ i, i < 2 * gbs.size →
    SOk (cwJ R gbs) (sRead gbs.size R (revCompB R) i) gbs[sChr gbs.size i]! i ss[i]! b S

include hn hlk in
theorem schedLoop_inv (key : Nat → Nat → Nat → Nat) (pss : Array (Array P)) (hp : PssOk lk R gbs idxs pss) :
    ∀ f ss b S, AllOk R gbs ss b S →
      ∃ S', AllOk R gbs (schedLoop lk key gbs idxs R (revCompB R) pss f ss b).1
        (schedLoop lk key gbs idxs R (revCompB R) pss f ss b).2 S' ∧ (∀ w, S w → S' w) ∧
        (schedLoop lk key gbs idxs R (revCompB R) pss f ss b).2.pen ≤ b.pen := by
  intro f
  induction f with
  | zero => intro ss b S h; simp only [schedLoop]; exact ⟨S, h, fun w hw => hw, Nat.le_refl _⟩
  | succ f ih =>
    intro ss b S h
    unfold schedLoop
    simp only []
    split
    · exact ⟨S, h, fun w hw => hw, Nat.le_refl _⟩
    · next i hpk =>
      rcases pickLive_some _ _ _ _ _ hpk with h0 | ⟨hm, hl⟩
      · cases h0
      have hi : i < 2 * gbs.size := by rw [← h.2.1]; exact List.mem_range.mp hm
      rw [hp i hi]
      obtain ⟨S2, k2, hS, hpen, -⟩ := adv_ok (cwJ R gbs) (cwJ_le R gbs) _ _ i (cwJ_slot R gbs i hi)
        (sRead_size R gbs hn i) lk idxs[sChr gbs.size i]! (slot_lk lk R gbs idxs hlk i hi) ss[i]! b S
        (h.2.2 i hi) (fun e => by simp [LzS.live, e] at hl)
      have h2 : AllOk R gbs (ss.set! i (ss[i]!.adv (sRead gbs.size R (revCompB R) i) gbs[sChr gbs.size i]! i lk
          idxs[sChr gbs.size i]! (prepAll lk idxs[sChr gbs.size i]!
            (seedHashes (sRead gbs.size R (revCompB R) i))) b).1)
          (ss[i]!.adv (sRead gbs.size R (revCompB R) i) gbs[sChr gbs.size i]! i lk
            idxs[sChr gbs.size i]! (prepAll lk idxs[sChr gbs.size i]!
              (seedHashes (sRead gbs.size R (revCompB R) i))) b).2 S2 := by
        refine ⟨k2.inv, by simp [h.2.1], fun i' hi' => ?_⟩
        have hsz : i < ss.size := by rw [h.2.1]; exact hi
        by_cases e : i' = i
        · subst e; rw [set!_self _ _ _ hsz]; exact k2
        · rw [set!_ne _ _ _ _ e]
          exact (h.2.2 i' hi').mono k2.inv hS hpen
      obtain ⟨S', h', s', p'⟩ := ih _ _ S2 h2
      exact ⟨S', h', fun w hw => s' w (hS w hw), Nat.le_trans p' hpen⟩

include hn hlk in
theorem drain_inv (i : Nat) (hi : i < 2 * gbs.size) :
    ∀ f s b S, SOk (cwJ R gbs) (sRead gbs.size R (revCompB R) i) gbs[sChr gbs.size i]! i s b S →
      s.ord.length ≤ f →
      ∃ S', Inv (cwJ R gbs) S' (drain lk (sRead gbs.size R (revCompB R) i) gbs[sChr gbs.size i]! i
          idxs[sChr gbs.size i]! (prepAll lk idxs[sChr gbs.size i]!
            (seedHashes (sRead gbs.size R (revCompB R) i))) f s b) ∧ (∀ w, S w → S' w) ∧
        (drain lk (sRead gbs.size R (revCompB R) i) gbs[sChr gbs.size i]! i
          idxs[sChr gbs.size i]! (prepAll lk idxs[sChr gbs.size i]!
            (seedHashes (sRead gbs.size R (revCompB R) i))) f s b).pen ≤ b.pen ∧
        ∀ st len, cwJ R gbs ⟨i, st, len⟩ ≤ 12 → S' ⟨i, st, len⟩ := by
  intro f
  induction f with
  | zero =>
    intro s b S h hf
    obtain ⟨S', i', s', cv⟩ := dead_cover (cwJ R gbs) (cwJ_le R gbs) _ _ i (cwJ_slot R gbs i hi)
      (sRead_size R gbs hn i) s b S h (by simp [LzS.live, List.length_eq_zero_iff.mp (by omega : s.ord.length = 0)])
    exact ⟨S', i', s', Nat.le_refl _, cv⟩
  | succ f ih =>
    intro s b S h hf
    unfold drain
    split
    · next hl =>
      obtain ⟨S2, k2, hS, hpen, hlen⟩ := adv_ok (cwJ R gbs) (cwJ_le R gbs) _ _ i (cwJ_slot R gbs i hi)
        (sRead_size R gbs hn i) lk idxs[sChr gbs.size i]! (slot_lk lk R gbs idxs hlk i hi) s b S h
        (fun e => by simp [LzS.live, e] at hl)
      obtain ⟨S', i', s', p', cv⟩ := ih _ _ S2 k2 (by omega)
      exact ⟨S', i', fun w hw => s' w (hS w hw), Nat.le_trans p' hpen, cv⟩
    · next hl =>
      obtain ⟨S', i', s', cv⟩ := dead_cover (cwJ R gbs) (cwJ_le R gbs) _ _ i (cwJ_slot R gbs i hi)
        (sRead_size R gbs hn i) s b S h (by simpa using hl)
      exact ⟨S', i', s', Nat.le_refl _, cv⟩

omit [Inhabited P] hn hlk in
theorem pss_ok : PssOk lk R gbs idxs ((Array.range (2 * gbs.size)).map fun i =>
    prepAll lk idxs[sChr gbs.size i]! (seedHashes (sRead gbs.size R (revCompB R) i))) := fun i hi => by
  simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, hi]

omit hn hlk in
theorem ss0_ok : AllOk R gbs ((Array.range (2 * gbs.size)).map fun i => LzS.init lk idxs[sChr gbs.size i]!
    ((Array.range (2 * gbs.size)).map fun i =>
      prepAll lk idxs[sChr gbs.size i]! (seedHashes (sRead gbs.size R (revCompB R) i)))[i]!) {} (fun _ => False) := by
  refine ⟨inv_init _ (cwJ_le R gbs), by simp, fun i hi => ?_⟩
  have e : ((Array.range (2 * gbs.size)).map fun i => LzS.init lk idxs[sChr gbs.size i]!
      ((Array.range (2 * gbs.size)).map fun i =>
        prepAll lk idxs[sChr gbs.size i]! (seedHashes (sRead gbs.size R (revCompB R) i)))[i]!)[i]! =
      LzS.init lk idxs[sChr gbs.size i]!
        (prepAll lk idxs[sChr gbs.size i]! (seedHashes (sRead gbs.size R (revCompB R) i))) := by
    rw [← pss_ok lk R gbs idxs i hi]; simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, hi]
  rw [e]
  exact init_ok _ _ _ i lk _ {} _ (inv_init _ (cwJ_le R gbs))

include hn hlk in
/-- Draining every slot from any good state covers every window. -/
theorem drainAll_inv (pss : Array (Array P)) (hp : PssOk lk R gbs idxs pss) (ss : Array LzS) (bL : Best)
    (S1 : Window → Prop) (h1 : AllOk R gbs ss bL S1) :
    ∃ S', Inv (cwJ R gbs) S' ((List.range (2 * gbs.size)).foldl (fun b i =>
        drain lk (sRead gbs.size R (revCompB R) i) gbs[sChr gbs.size i]! i idxs[sChr gbs.size i]!
          pss[i]! 4 ss[i]! b) bL) ∧ (∀ w, S1 w → S' w) ∧
      ((List.range (2 * gbs.size)).foldl (fun b i =>
        drain lk (sRead gbs.size R (revCompB R) i) gbs[sChr gbs.size i]! i idxs[sChr gbs.size i]!
          pss[i]! 4 ss[i]! b) bL).pen ≤ bL.pen ∧ ∀ w, cwJ R gbs w ≤ 12 → S' w := by
  have step : ∀ (l : List Nat) S b, (∀ i ∈ l, i < 2 * gbs.size) → Inv (cwJ R gbs) S b →
      (∀ w, S1 w → S w) → b.pen ≤ bL.pen →
      ∃ S', Inv (cwJ R gbs) S' (l.foldl (fun b i =>
          drain lk (sRead gbs.size R (revCompB R) i) gbs[sChr gbs.size i]! i idxs[sChr gbs.size i]!
            pss[i]! 4 ss[i]! b) b) ∧ (∀ w, S w → S' w) ∧
        (l.foldl (fun b i => drain lk (sRead gbs.size R (revCompB R) i) gbs[sChr gbs.size i]! i
            idxs[sChr gbs.size i]! pss[i]! 4 ss[i]! b) b).pen ≤ b.pen ∧
        ∀ i ∈ l, ∀ st len, cwJ R gbs ⟨i, st, len⟩ ≤ 12 → S' ⟨i, st, len⟩ := by
    intro l
    induction l with
    | nil => intro S b _ h _ _; exact ⟨S, h, fun w hw => hw, Nat.le_refl _, fun i hi => by simp at hi⟩
    | cons i l ih =>
      intro S b hl h hS1 hb
      have hi := hl i List.mem_cons_self
      have hs := (h1.2.2 i hi).mono h hS1 hb
      obtain ⟨J, -, -, -, -, -, hlen⟩ := id hs
      simp only [List.foldl_cons]
      rw [hp i hi]
      obtain ⟨S2, i2, s2, p2, cv2⟩ := drain_inv lk R gbs idxs hn hlk i hi 4 _ b S hs (by omega)
      obtain ⟨S', i', s', p', cv⟩ := ih S2 _ (fun i' h' => hl i' (List.mem_cons_of_mem _ h')) i2
        (fun w hw => s2 w (hS1 w hw)) (Nat.le_trans p2 hb)
      refine ⟨S', i', fun w hw => s' w (s2 w hw), Nat.le_trans p' p2, fun i' hi' st len hw => ?_⟩
      rcases List.mem_cons.mp hi' with rfl | hi'
      · exact s' _ (cv2 st len hw)
      · exact cv i' hi' st len hw
  obtain ⟨S', h', hsub, hpen, cov⟩ := step (List.range (2 * gbs.size)) S1 bL (fun i hi => List.mem_range.mp hi)
    h1.1 (fun w hw => hw) (Nat.le_refl _)
  refine ⟨S', h', hsub, hpen, fun w hw => ?_⟩
  · rcases w with ⟨c, st, len⟩
    by_cases hc : c < 2 * gbs.size
    · exact cov c (List.mem_range.mpr hc) st len hw
    · unfold cwJ at hw; simp [show ¬ c < gbs.size by omega, hc] at hw

include hn hlk in
theorem mapChromsS_inv (key : Nat → Nat → Nat → Nat) :
    ∃ S, Inv (cwJ R gbs) S (mapChromsS lk key R gbs idxs) ∧ ∀ w, cwJ R gbs w ≤ 12 → S w := by
  obtain ⟨S1, h1, -, -⟩ := schedLoop_inv lk R gbs idxs hn hlk key _ (pss_ok lk R gbs idxs) (8 * gbs.size) _ {} _
    (ss0_ok lk R gbs idxs)
  obtain ⟨S', h', -, -, cov⟩ := drainAll_inv lk R gbs idxs hn hlk _ (pss_ok lk R gbs idxs) _ _ _ h1
  exact ⟨S', h', cov⟩

include hn hlk in
theorem schedLoopX_inv (key : Nat → Nat → Nat → Nat) (stop : Array LzS → Best → Bool) (pss : Array (Array P))
    (hp : PssOk lk R gbs idxs pss) :
    ∀ f ss b S, AllOk R gbs ss b S →
      ∃ S', AllOk R gbs (schedLoopX lk key stop gbs idxs R (revCompB R) pss f ss b).1
        (schedLoopX lk key stop gbs idxs R (revCompB R) pss f ss b).2.1 S' ∧ (∀ w, S w → S' w) ∧
        ((schedLoopX lk key stop gbs idxs R (revCompB R) pss f ss b).2.2 = true →
          stop (schedLoopX lk key stop gbs idxs R (revCompB R) pss f ss b).1
            (schedLoopX lk key stop gbs idxs R (revCompB R) pss f ss b).2.1 = true) := by
  intro f
  induction f with
  | zero => intro ss b S h; simp only [schedLoopX]; exact ⟨S, h, fun w hw => hw, fun h => nomatch h⟩
  | succ f ih =>
    intro ss b S h
    unfold schedLoopX
    simp only []
    split
    · next hs => exact ⟨S, h, fun w hw => hw, fun _ => hs⟩
    · split
      · exact ⟨S, h, fun w hw => hw, fun h => nomatch h⟩
      · next i hpk =>
        rcases pickLive_some _ _ _ _ _ hpk with h0 | ⟨hm, hl⟩
        · cases h0
        have hi : i < 2 * gbs.size := by rw [← h.2.1]; exact List.mem_range.mp hm
        rw [hp i hi]
        obtain ⟨S2, k2, hS, hpen, -⟩ := adv_ok (cwJ R gbs) (cwJ_le R gbs) _ _ i (cwJ_slot R gbs i hi)
          (sRead_size R gbs hn i) lk idxs[sChr gbs.size i]! (slot_lk lk R gbs idxs hlk i hi) ss[i]! b S
          (h.2.2 i hi) (fun e => by simp [LzS.live, e] at hl)
        have hsz : i < ss.size := by rw [h.2.1]; exact hi
        have h2 : AllOk R gbs (ss.set! i (ss[i]!.adv (sRead gbs.size R (revCompB R) i) gbs[sChr gbs.size i]! i lk
            idxs[sChr gbs.size i]! (prepAll lk idxs[sChr gbs.size i]!
              (seedHashes (sRead gbs.size R (revCompB R) i))) b).1)
            (ss[i]!.adv (sRead gbs.size R (revCompB R) i) gbs[sChr gbs.size i]! i lk
              idxs[sChr gbs.size i]! (prepAll lk idxs[sChr gbs.size i]!
                (seedHashes (sRead gbs.size R (revCompB R) i))) b).2 S2 := by
          refine ⟨k2.inv, by simp [h.2.1], fun i' hi' => ?_⟩
          by_cases e : i' = i
          · subst e; rw [set!_self _ _ _ hsz]; exact k2
          · rw [set!_ne _ _ _ _ e]; exact (h.2.2 i' hi').mono k2.inv hS hpen
        obtain ⟨S', h', s', st'⟩ := ih _ _ S2 h2
        exact ⟨S', h', fun w hw => s' w (hS w hw), st'⟩

include hn hlk in
/-- The early-exit search: either it ran to the end (`bF`), or it stopped in a
good state `(ss, bL)` with `stop ss bL`; `bF` is what the full search gives from there. -/
theorem mapChromsX_inv (key : Nat → Nat → Nat → Nat) (stop : Array LzS → Best → Bool) :
    ∃ ss bL S bF SF, AllOk R gbs ss bL S ∧ Inv (cwJ R gbs) SF bF ∧ bF.pen ≤ bL.pen ∧
      (∀ w, cwJ R gbs w ≤ 12 → SF w) ∧
      ((mapChromsX lk key stop R gbs idxs).2 = false → (mapChromsX lk key stop R gbs idxs).1 = bF) ∧
      ((mapChromsX lk key stop R gbs idxs).2 = true →
        (mapChromsX lk key stop R gbs idxs).1 = bL ∧ stop ss bL = true) := by
  obtain ⟨S1, h1, -, hst⟩ := schedLoopX_inv lk R gbs idxs hn hlk key stop _ (pss_ok lk R gbs idxs)
    (8 * gbs.size) _ {} _ (ss0_ok lk R gbs idxs)
  generalize hr : schedLoopX lk key stop gbs idxs R (revCompB R) _ (8 * gbs.size) _ {} = r at h1 hst
  obtain ⟨SF, hF, -, hpen, cov⟩ := drainAll_inv lk R gbs idxs hn hlk _ (pss_ok lk R gbs idxs) _ _ _ h1
  refine ⟨r.1, r.2.1, S1, _, SF, h1, hF, hpen, cov, fun h => ?_, fun h => ?_⟩
  · dsimp only [mapChromsX] at h ⊢; rw [hr] at h ⊢
    by_cases hs : r.2.2 = true
    · simp only [if_pos hs] at h; cases h
    · simp only [if_neg hs]
  · dsimp only [mapChromsX] at h ⊢; rw [hr] at h ⊢
    by_cases hs : r.2.2 = true
    · simp only [if_pos hs]; exact ⟨trivial, hst hs⟩
    · simp only [if_neg hs] at h; cases h

end sched

theorem mapFastS_eq_mapSpecBoth {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P)
    (key : Nat → Nat → Nat → Nat) (g : Genome) (read : List Char) (gbs : Array ByteArray) (idxs : Array L)
    (R : ByteArray) (hg : GenomeBytes gbs g) (hr : Encodes R read) (hlk : LookAll lk gbs idxs)
    (hok : fastOk R = true) : mapFastS lk key gbs idxs R = mapSpecBoth sc0 (-12) g read :=
  decodeJ_eq_mapSpecBoth g read gbs R _ hg hr
    (mapChromsS_inv lk R gbs idxs (by unfold fastOk q at hok; simp at hok; omega) hlk key)

theorem pairFastS_eq_pairSpec {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P)
    (key1 : Nat → Nat → Nat → Nat) (key2 : Placement → Nat → Nat → Nat → Nat) (lo hi : Nat)
    (g : Genome) (m1 m2 : List Char) (gbs : Array ByteArray) (idxs : Array L) (R1 R2 : ByteArray)
    (hg : GenomeBytes gbs g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hlk : LookAll lk gbs idxs)
    (hok1 : fastOk R1 = true) (hok2 : fastOk R2 = true) :
    pairFastS lk key1 key2 lo hi gbs idxs R1 R2 = pairSpec sc0 (-12) lo hi g m1 m2 := by
  unfold pairFastS pairSpec
  rw [mapFastS_eq_mapSpecBoth lk key1 g m1 gbs idxs R1 hg h1 hlk hok1]
  cases mapSpecBoth sc0 (-12) g m1 with
  | none => rfl
  | some a =>
    simp only
    rw [mapFastS_eq_mapSpecBoth lk _ g m2 gbs idxs R2 hg h2 hlk hok2]
    cases mapSpecBoth sc0 (-12) g m2 <;> rfl

/-! ### Early exits are exact -/

/-- Ambiguous at penalty 0 stays ambiguous. -/
theorem amb0_final (cw : Window → Nat) (S SF : Window → Prop) (b bF : Best) (hb : Inv cw S b)
    (hF : Inv cw SF bF) (hp : bF.pen ≤ b.pen) (cov : ∀ w, cw w ≤ 12 → SF w) (h : amb0 b = true) :
    result bF = none := by
  unfold amb0 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h0, ha⟩ := h
  obtain ⟨w', hw', hne, hcw⟩ := (hb.amb (by omega)).mp ha
  have hF0 : bF.pen = 0 := by omega
  have hbw : cw b.win = 0 := by rw [hb.hit (by omega), h0]
  have : bF.amb = true := by
    rw [hF.amb (by omega)]
    by_cases e : b.win = bF.win
    · exact ⟨w', cov w' (by omega), by rw [← e]; exact hne, by omega⟩
    · exact ⟨b.win, cov _ (by omega), e, by omega⟩
  unfold result; simp [this]

/-- Once every window of tag `t` was looked at, a final answer on tag `t` is already the current one. -/
theorem target_final (cw : Window → Nat) (t : Nat) (S SF : Window → Prop) (b bF : Best) (hb : Inv cw S b)
    (ht : ∀ st len, cw ⟨t, st, len⟩ ≤ 12 → S ⟨t, st, len⟩) (hF : Inv cw SF bF) (hp : bF.pen ≤ b.pen)
    (cov : ∀ w, cw w ≤ 12 → SF w) (st len p : Nat) (hr : result bF = some (t, st, len, p)) :
    result b = result bF := by
  have hr' := hr
  unfold result at hr'
  split at hr'
  · next hc =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hr'
    obtain ⟨e1, -, -, -⟩ := hr'
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
    obtain ⟨hc12, hna⟩ := hc
    unfold cap at hc12
    have hwF : cw bF.win = bF.pen := hF.hit hc12
    have hS : S bF.win := by
      have := ht bF.st bF.len; unfold Best.win at hwF ⊢; rw [e1] at hwF ⊢; exact this (by omega)
    have hbp : b.pen = bF.pen := Nat.le_antisymm (by have := hb.min _ hS; omega) hp
    have hbw : cw b.win = b.pen := hb.hit (by omega)
    have hwin : b.win = bF.win := by
      by_cases e : b.win = bF.win
      · exact e
      have : bF.amb = true := (hF.amb hc12).mpr ⟨b.win, cov _ (by omega), e, by omega⟩
      rw [hna] at this; cases this
    have hba : b.amb = false := by
      cases e : b.amb
      · rfl
      · obtain ⟨w', hw', hne, hcw⟩ := (hb.amb (by omega)).mp e
        have : bF.amb = true := (hF.amb hc12).mpr ⟨w', cov _ (by omega), by rw [← hwin]; exact hne, by omega⟩
        rw [hna] at this; cases this
    unfold Best.win at hwin
    simp only [Window.mk.injEq] at hwin
    obtain ⟨w1, w2, w3⟩ := hwin
    have hb12 : b.pen ≤ 12 := by omega
    unfold result
    simp only [hba, hna, cap, w1, w2, w3, hbp, Bool.not_false, Bool.and_true, decide_eq_true_eq]
    simp [hc12]
  · cases hr'

/-- A decoded proper partner of `a` lies in `partnerSlot n a`. -/
theorem decode_partner (lo hi n : Nat) (b : Best) (a : Placement) (x : Placement × Int)
    (hd : decodeJ n b = some x) (hpp : properPair lo hi a x.1 = true) :
    ∃ st len p, result b = some (partnerSlot n a, st, len, p) := by
  unfold decodeJ at hd
  split at hd
  · next c st len pen hres =>
    refine ⟨st, len, pen, ?_⟩
    rw [hres]
    simp only [Option.some.injEq] at hd
    subst hd
    obtain ⟨⟨ac, ast, alen⟩, astr⟩ := a
    unfold properPair at hpp
    unfold partnerSlot
    by_cases hc : c < n <;> cases astr <;> simp [hc] at hpp ⊢ <;> omega
  · cases hd

/-- **Early exits.** -/
theorem pairFastX_eq_pairSpec {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P)
    (key1 : Nat → Nat → Nat → Nat) (key2 : Placement → Nat → Nat → Nat → Nat) (lo hi : Nat)
    (g : Genome) (m1 m2 : List Char) (gbs : Array ByteArray) (idxs : Array L) (R1 R2 : ByteArray)
    (hg : GenomeBytes gbs g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hlk : LookAll lk gbs idxs)
    (hok1 : fastOk R1 = true) (hok2 : fastOk R2 = true) :
    pairFastX lk key1 key2 lo hi gbs idxs R1 R2 = pairSpec sc0 (-12) lo hi g m1 m2 := by
  have hn1 : 100 ≤ R1.size := by unfold fastOk q at hok1; simp at hok1; omega
  have hn2 : 100 ≤ R2.size := by unfold fastOk q at hok2; simp at hok2; omega
  have dnone : ∀ b : Best, result b = none → decodeJ gbs.size b = none := fun b h => by
    unfold decodeJ; rw [h]
  unfold pairFastX pairSpec
  dsimp only
  obtain ⟨ss1, bL1, S1, bF1, SF1, hA1, hF1, hp1, cov1, hno1, hyes1⟩ :=
    mapChromsX_inv lk R1 gbs idxs hn1 hlk key1 (fun _ b => amb0 b)
  have e1 := decodeJ_eq_mapSpecBoth g m1 gbs R1 bF1 hg h1 ⟨SF1, hF1, cov1⟩
  generalize mapChromsX lk key1 (fun _ b => amb0 b) R1 gbs idxs = r1 at hno1 hyes1
  obtain ⟨rb1, rs1⟩ := r1
  cases rs1 with
  | true =>
    obtain ⟨-, hs⟩ := hyes1 (by simp)
    rw [← e1, dnone _ (amb0_final _ _ _ _ _ hA1.1 hF1 hp1 cov1 hs)]
    rfl
  | false =>
    simp only at hno1 ⊢
    rw [if_neg (by simp), hno1 (by simp), e1]
    cases mapSpecBoth sc0 (-12) g m1 with
    | none => rfl
    | some a =>
      simp only
      obtain ⟨ss2, bL2, S2, bF2, SF2, hA2, hF2, hp2, cov2, hno2, hyes2⟩ :=
        mapChromsX_inv lk R2 gbs idxs hn2 hlk (key2 a.1) (fun ss b => amb0 b ||
          (!ss[partnerSlot gbs.size a.1]!.live b && !(match decodeJ gbs.size b with
            | some x => properPair lo hi a.1 x.1
            | none => false)))
      have e2 := decodeJ_eq_mapSpecBoth g m2 gbs R2 bF2 hg h2 ⟨SF2, hF2, cov2⟩
      generalize mapChromsX lk (key2 a.1) _ R2 gbs idxs = r2 at hno2 hyes2
      obtain ⟨rb2, rs2⟩ := r2
      cases rs2 with
      | false =>
        simp only at hno2 ⊢
        rw [if_neg (by simp), hno2 (by simp), e2]
        cases mapSpecBoth sc0 (-12) g m2 <;> rfl
      | true =>
        obtain ⟨-, hs⟩ := hyes2 (by simp)
        simp only [if_true]
        rw [← e2]
        simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hs
        rcases hs with hs | ⟨hd, hok⟩
        · rw [dnone _ (amb0_final _ _ _ _ _ hA2.1 hF2 hp2 cov2 hs)]
        · -- every window of the partner slot was looked at
          have cov_t : ∃ S', Inv (cwJ R2 gbs) S' bL2 ∧ ∀ st len,
              cwJ R2 gbs ⟨partnerSlot gbs.size a.1, st, len⟩ ≤ 12 → S' ⟨partnerSlot gbs.size a.1, st, len⟩ := by
            by_cases ht : partnerSlot gbs.size a.1 < 2 * gbs.size
            · obtain ⟨S', i', -, cv⟩ := dead_cover (cwJ R2 gbs) (cwJ_le R2 gbs) _ _ _
                (cwJ_slot R2 gbs _ ht) (sRead_size R2 gbs hn2 _) _ bL2 S2 (hA2.2.2 _ ht) hd
              exact ⟨S', i', cv⟩
            · refine ⟨S2, hA2.1, fun st len hw => ?_⟩
              unfold cwJ at hw; simp [show ¬ partnerSlot gbs.size a.1 < gbs.size by omega, ht] at hw
          obtain ⟨S', hS', hcv⟩ := cov_t
          cases hdF : decodeJ gbs.size bF2 with
          | none => rfl
          | some x =>
            simp only
            cases hpp : properPair lo hi a.1 x.1 with
            | false => rfl
            | true =>
              exfalso
              obtain ⟨st, len, p, hres⟩ := decode_partner lo hi gbs.size bF2 a.1 x hdF hpp
              have := target_final _ _ _ _ _ _ hS' hcv hF2 (Nat.le_trans hp2 (Nat.le_refl _)) cov2 st len p hres
              have hdL : decodeJ gbs.size bL2 = some x := by
                rw [← hdF]; unfold decodeJ; rw [this]
              rw [hdL] at hok
              simp [hpp] at hok

/-- The same through minimizer indexes that pass the checker. -/
theorem pairFastS_mz_eq_pairSpec (key1 : Nat → Nat → Nat → Nat) (key2 : Placement → Nat → Nat → Nat → Nat)
    (lo hi : Nat) (g : Genome) (m1 m2 : List Char) (gbs : Array ByteArray)
    (idxs : Array Mz.MzIdx) (R1 R2 : ByteArray) (hg : GenomeBytes gbs g) (h1 : Encodes R1 m1)
    (h2 : Encodes R2 m2) (hchk : checkAllMz idxs gbs = true)
    (hok1 : fastOk R1 = true) (hok2 : fastOk R2 = true) :
    pairFastS mzL key1 key2 lo hi gbs idxs R1 R2 = pairSpec sc0 (-12) lo hi g m1 m2 := by
  apply pairFastS_eq_pairSpec mzL key1 key2 lo hi g m1 m2 gbs idxs R1 R2 hg h1 h2 _ hok1 hok2
  intro c hc R' j hj
  unfold checkAllMz at hchk
  simp only [List.all_eq_true, List.mem_range] at hchk
  exact mzLook_ok _ _ _ _ hj (by rw [← Mz.check2_eq]; exact hchk c hc)

theorem pairFastX_mz_eq_pairSpec (key1 : Nat → Nat → Nat → Nat) (key2 : Placement → Nat → Nat → Nat → Nat)
    (lo hi : Nat) (g : Genome) (m1 m2 : List Char) (gbs : Array ByteArray)
    (idxs : Array Mz.MzIdx) (R1 R2 : ByteArray) (hg : GenomeBytes gbs g) (h1 : Encodes R1 m1)
    (h2 : Encodes R2 m2) (hchk : checkAllMz idxs gbs = true)
    (hok1 : fastOk R1 = true) (hok2 : fastOk R2 = true) :
    pairFastX mzL key1 key2 lo hi gbs idxs R1 R2 = pairSpec sc0 (-12) lo hi g m1 m2 := by
  apply pairFastX_eq_pairSpec mzL key1 key2 lo hi g m1 m2 gbs idxs R1 R2 hg h1 h2 _ hok1 hok2
  intro c hc R' j hj
  unfold checkAllMz at hchk
  simp only [List.all_eq_true, List.mem_range] at hchk
  exact mzLook_ok _ _ _ _ hj (by rw [← Mz.check2_eq]; exact hchk c hc)

end MapSpec.Fast

#print axioms MapSpec.Fast.mapFastS_eq_mapSpecBoth
#print axioms MapSpec.Fast.pairFastS_eq_pairSpec
#print axioms MapSpec.Fast.pairFastS_mz_eq_pairSpec
#print axioms MapSpec.Fast.pairFastX_eq_pairSpec
#print axioms MapSpec.Fast.pairFastX_mz_eq_pairSpec
