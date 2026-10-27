import MapperFastLazy

/-!
# Interleaved lazy lookups of two reads (the prototype's `mapStreams`)

`ilLoop` runs two `lazyLoop`s on one chromosome (in practice the read and its
reverse complement, tags `c` and `n + c`) sharing one `Best`, one lookup at a
time: the next lookup goes to the live strand with fewer lookups, then the
smaller next bucket.  A strand is live while seeds remain and the shared best is
`≥ 4k` (`k` = its lookups).  Each step is one `lzStep`, so the per-strand loop
state (`LoopState`) is kept (`lzStep_inv`); the other strand's state survives
because the best only goes down (`lzStep_le`) and the window set only grows.
-/

namespace MapSpec.Fast

open MapSpec

/-! ## Algorithm -/

/-- One strand: seeds still to look up, lookups done, anchors, looked-up mask. -/
structure LzS where
  ord : List Nat
  k : Nat
  as : Array Nat
  looked : Nat

@[inline] def LzS.init {L P : Type} [Inhabited P] (lk : Look L P) (ix : L) (ps : Array P) : LzS :=
  ⟨seedOrder lk ix ps, 0, #[], 0⟩

/-- Seeds remain and the best is not below `4k`. -/
@[inline] def LzS.live (s : LzS) (b : Best) : Bool := !s.ord.isEmpty && decide (4 * s.k ≤ b.pen)

/-- Bucket size of the next seed. -/
@[inline] def LzS.next {L P : Type} [Inhabited P] (lk : Look L P) (ix : L) (ps : Array P) (s : LzS) : Nat :=
  match s.ord with
  | j :: _ => lk.size ix ps[j]!
  | [] => 0

/-- Look up the next seed. -/
@[inline] def LzS.adv {L P : Type} [Inhabited P] (R G : ByteArray) (c : Nat) (lk : Look L P) (ix : L)
    (ps : Array P) (s : LzS) (b : Best) : LzS × Best :=
  match s.ord with
  | [] => (s, b)
  | j :: rest =>
    let r := lzStep R G c lk ix ps j s.k s.as s.looked b
    (⟨rest, s.k + 1, r.1, s.looked + pow2 j⟩, r.2)

/-- Two strands, one lookup at a time (fewer lookups first, then the smaller
bucket, ties to strand 1); `f` bounds the lookups left. -/
@[specialize] def ilLoop {L P : Type} [Inhabited P] (lk : Look L P) (G : ByteArray) (ix : L)
    (R1 R2 : ByteArray) (c1 c2 : Nat) (ps1 ps2 : Array P) : Nat → LzS → LzS → Best → Best
  | 0, _, _, b => b
  | f + 1, s1, s2, b =>
    let l2 := s2.live b
    if s1.live b && (!l2 || s1.k < s2.k || (s1.k == s2.k && s1.next lk ix ps1 ≤ s2.next lk ix ps2)) then
      let r := s1.adv R1 G c1 lk ix ps1 b
      ilLoop lk G ix R1 R2 c1 c2 ps1 ps2 f r.1 s2 r.2
    else if l2 then
      let r := s2.adv R2 G c2 lk ix ps2 b
      ilLoop lk G ix R1 R2 c1 c2 ps1 ps2 f s1 r.1 r.2
    else b

/-- One chromosome, two reads (`hs1 = seedHashes R1`, tag `c1`; same for 2). -/
@[inline] def mapChromI {L P : Type} [Inhabited P] (lk : Look L P) (G : ByteArray) (ix : L)
    (R1 R2 : ByteArray) (c1 c2 : Nat) (hs1 hs2 : Array (Option UInt64)) (b : Best) : Best :=
  let ps1 := prepAll lk ix hs1
  let ps2 := prepAll lk ix hs2
  ilLoop lk G ix R1 R2 c1 c2 ps1 ps2 8 (LzS.init lk ix ps1) (LzS.init lk ix ps2) b

/-! ## The best only goes down -/

theorem add_pen_le (b : Best) (c st len p : Nat) : (b.add c st len p).pen ≤ b.pen := by
  unfold Best.add; split
  · simp only; omega
  · split <;> exact Nat.le_refl _

theorem sameStep2_le (R G : ByteArray) (c : Nat) (b : Best) (e : Nat) : (sameStep2 R G c b e).pen ≤ b.pen := by
  unfold sameStep2; simp only []
  split
  · split
    · exact add_pen_le _ _ _ _ _
    · exact Nat.le_refl _
  · exact Nat.le_refl _

theorem gapW_le (R G : ByteArray) (c st len s : Nat) (ok : Bool) (b : Best) :
    (gapW R G c st len s ok b).pen ≤ b.pen := by
  unfold gapW addGap; split
  · exact add_pen_le _ _ _ _ _
  · exact Nat.le_refl _

theorem gapL2_le (R G : ByteArray) (c : Nat) (as : Array Nat) (looked i A cs L : Nat) (b : Best) :
    (gapL2 R G c as looked i A cs L b).pen ≤ b.pen := by
  unfold gapL2; simp only []
  exact Nat.le_trans (gapW_le _ _ _ _ _ _ _ _) (Nat.le_trans (gapW_le _ _ _ _ _ _ _ _)
    (Nat.le_trans (gapW_le _ _ _ _ _ _ _ _) (gapW_le _ _ _ _ _ _ _ _)))

theorem gapAll2_le (R G : ByteArray) (c : Nat) (as : Array Nat) (looked : Nat) :
    ∀ k i b, (gapAll2 R G c as looked k i b).pen ≤ b.pen := by
  intro k
  induction k with
  | zero => intro i b; exact Nat.le_refl _
  | succ k ih =>
    intro i b
    unfold gapAll2
    exact Nat.le_trans (ih _ _) (Nat.le_trans (gapL2_le _ _ _ _ _ _ _ _ _ _)
      (Nat.le_trans (gapL2_le _ _ _ _ _ _ _ _ _ _) (gapL2_le _ _ _ _ _ _ _ _ _ _)))

theorem lzStepA_le (R G : ByteArray) (c : Nat) (a : Array Nat) (k : Nat) (as : Array Nat) (looked : Nat)
    (b : Best) : (lzStepA R G c a k as looked b).2.pen ≤ b.pen := by
  have hf : ∀ (l : List Nat) b, (l.foldl (sameStep2 R G c) b).pen ≤ b.pen := by
    intro l; induction l with
    | nil => intro b; exact Nat.le_refl _
    | cons e l ih => intro b; exact Nat.le_trans (ih _) (sameStep2_le R G c b e)
  unfold lzStepA; simp only []
  rw [← Array.foldl_toList]
  split
  · exact Nat.le_trans (gapAll2_le _ _ _ _ _ _ _ _) (hf _ _)
  · exact hf _ _

theorem lzStep_le {L P : Type} [Inhabited P] (R G : ByteArray) (c : Nat) (lk : Look L P) (ix : L)
    (ps : Array P) (j k : Nat) (as : Array Nat) (looked : Nat) (b : Best) :
    (lzStep R G c lk ix ps j k as looked b).2.pen ≤ b.pen := by
  rw [lzStep_eq_A]; exact lzStepA_le _ _ _ _ _ _ _ _

/-! ## Per-strand state -/

theorem LoopState.mono {cw : Window → Nat} {R G : ByteArray} {c J K : Nat} {as : Array Nat} {b b' : Best}
    {S S' : Window → Prop} (h : LoopState cw R G c J K as b S) (hi : Inv cw S' b') (hS : ∀ w, S w → S' w)
    (hb : b'.pen ≤ b.pen) : LoopState cw R G c J K as b' S' :=
  ⟨hi, h.anchors, h.hJ, h.card, fun st hm => hS _ (h.same st hm), fun h3 => by
    rcases h.gap h3 with hp | hc
    · exact Or.inl (by omega)
    · exact Or.inr fun st len a b c => hS _ (hc st len a b c)⟩

/-- Strand state `s` of read `R` (tag `c`) with best `b` and looked-at windows `S`. -/
def SOk (cw : Window → Nat) (R G : ByteArray) (c : Nat) (s : LzS) (b : Best) (S : Window → Prop) : Prop :=
  ∃ J, LoopState cw R G c J (pop4 J) s.as b S ∧ s.k = pop4 J ∧ s.looked = J ∧ s.ord.Nodup ∧
    (∀ j ∈ s.ord, j < 4 ∧ bit J j = 0) ∧ pop4 J + s.ord.length = 4

theorem SOk.mono {cw : Window → Nat} {R G : ByteArray} {c : Nat} {s : LzS} {b b' : Best}
    {S S' : Window → Prop} (h : SOk cw R G c s b S) (hi : Inv cw S' b') (hS : ∀ w, S w → S' w)
    (hb : b'.pen ≤ b.pen) : SOk cw R G c s b' S' := by
  obtain ⟨J, h1, h2⟩ := h
  exact ⟨J, h1.mono hi hS hb, h2⟩

theorem SOk.inv {cw : Window → Nat} {R G : ByteArray} {c : Nat} {s : LzS} {b : Best} {S : Window → Prop}
    (h : SOk cw R G c s b S) : Inv cw S b := by
  obtain ⟨J, h1, -⟩ := h; exact h1.inv

section strand

variable (cw : Window → Nat) (hc13 : ∀ w, cw w ≤ 13) (R G : ByteArray) (c : Nat)
  (hcw : ∀ st len, cw ⟨c, st, len⟩ = penB R G st len) (hn : 100 ≤ R.size)
  {L P : Type} [Inhabited P] (lk : Look L P) (ix : L)
  (hlk : ∀ j, j < 4 → LookOk G R j (lk.look ix G R j (lk.prep ix (seedHash R j))))

include hc13 hcw hn hlk

/-- A lookup keeps the strand state. -/
theorem adv_ok (s : LzS) (b : Best) (S : Window → Prop) (h : SOk cw R G c s b S) (hl : s.ord ≠ []) :
    ∃ S2, SOk cw R G c (s.adv R G c lk ix (prepAll lk ix (seedHashes R)) b).1
        (s.adv R G c lk ix (prepAll lk ix (seedHashes R)) b).2 S2 ∧ (∀ w, S w → S2 w) ∧
      (s.adv R G c lk ix (prepAll lk ix (seedHashes R)) b).2.pen ≤ b.pen ∧
      (s.adv R G c lk ix (prepAll lk ix (seedHashes R)) b).1.ord.length + 1 = s.ord.length := by
  obtain ⟨J, hs, hk, hlo, hnd, hord, hlen⟩ := h
  rcases s with ⟨_ | ⟨j, rest⟩, k, as, looked⟩
  · exact absurd rfl hl
  simp only at hk hlo hnd hord hlen hs
  subst k looked
  obtain ⟨hj4, hj0⟩ := hord j List.mem_cons_self
  obtain ⟨hpop, hJ'⟩ := pop4_add J hs.hJ j hj4 hj0
  obtain ⟨S2, hst, hS12⟩ := lzStep_inv cw hc13 R G c hcw hn lk ix hlk j J as b S hs hj4 hj0
  have hnd' := List.nodup_cons.mp hnd
  simp only [LzS.adv]
  refine ⟨S2, ⟨J + 2 ^ j, by rw [hpop]; exact hst, hpop.symm, by rw [pow2_eq j hj4], hnd'.2, fun j' hj' => ?_,
    by simp at hlen ⊢; omega⟩, hS12, lzStep_le _ _ _ _ _ _ _ _ _ _ _, rfl⟩
  obtain ⟨a1, a2⟩ := hord j' (List.mem_cons_of_mem _ hj')
  refine ⟨a1, ?_⟩
  rw [bit_add J j j' hj4 a1 hs.hJ hj0, if_neg (fun e : j' = j => hnd'.1 (e ▸ hj'))]; exact a2

omit [Inhabited P] hlk in
/-- A strand that is not live has looked at every hit of its tag. -/
theorem dead_cover (s : LzS) (b : Best) (S : Window → Prop) (h : SOk cw R G c s b S) (hd : s.live b = false) :
    ∃ S', Inv cw S' b ∧ (∀ w, S w → S' w) ∧ ∀ st len, cw ⟨c, st, len⟩ ≤ 12 → S' ⟨c, st, len⟩ := by
  obtain ⟨J, hs, hk, -, -, -, hlen⟩ := h
  apply finish cw hc13 R G c hcw hn J _ s.as b S hs
  unfold LzS.live at hd
  cases ho : s.ord with
  | nil => rw [ho] at hlen; exact Or.inr (pop4_full J hs.hJ (by simpa using hlen))
  | cons j rest => rw [ho] at hd; simp at hd; omega

omit hc13 hcw hn hlk in
theorem init_ok (b : Best) (S : Window → Prop) (h : Inv cw S b) :
    SOk cw R G c (LzS.init lk ix (prepAll lk ix (seedHashes R))) b S := by
  obtain ⟨hnd, hlt, hl⟩ := seedOrder_spec lk ix (prepAll lk ix (seedHashes R))
  exact ⟨0, ⟨h, anchorsM_init G R, by omega, rfl, fun st hm => by simp [maskJ] at hm,
    fun h3 => by simp [pop4] at h3⟩, rfl, rfl, hnd, fun j hj => ⟨hlt j hj, by simp [bit]⟩, by
    simp [LzS.init, hl, pop4]⟩

end strand

/-! ## The interleaved loop -/

section two

variable (cw : Window → Nat) (hc13 : ∀ w, cw w ≤ 13) (G : ByteArray) {L P : Type} [Inhabited P]
  (lk : Look L P) (ix : L) (R1 R2 : ByteArray) (c1 c2 : Nat)
  (hcw1 : ∀ st len, cw ⟨c1, st, len⟩ = penB R1 G st len) (hn1 : 100 ≤ R1.size)
  (hlk1 : ∀ j, j < 4 → LookOk G R1 j (lk.look ix G R1 j (lk.prep ix (seedHash R1 j))))
  (hcw2 : ∀ st len, cw ⟨c2, st, len⟩ = penB R2 G st len) (hn2 : 100 ≤ R2.size)
  (hlk2 : ∀ j, j < 4 → LookOk G R2 j (lk.look ix G R2 j (lk.prep ix (seedHash R2 j))))

include hc13 hcw1 hn1 hlk1 hcw2 hn2 hlk2

omit [Inhabited P] hlk1 hlk2 in
/-- Both strands dead: every hit of both tags was looked at. -/
theorem both_dead (s1 s2 : LzS) (b : Best) (S : Window → Prop) (h1 : SOk cw R1 G c1 s1 b S)
    (h2 : SOk cw R2 G c2 s2 b S) (d1 : s1.live b = false) (d2 : s2.live b = false) :
    ∃ S', Inv cw S' b ∧ (∀ w, S w → S' w) ∧ (∀ st len, cw ⟨c1, st, len⟩ ≤ 12 → S' ⟨c1, st, len⟩) ∧
      (∀ st len, cw ⟨c2, st, len⟩ ≤ 12 → S' ⟨c2, st, len⟩) := by
  obtain ⟨S1, i1, s1', cv1⟩ := dead_cover cw hc13 R1 G c1 hcw1 hn1 s1 b S h1 d1
  obtain ⟨S2, i2, s2', cv2⟩ := dead_cover cw hc13 R2 G c2 hcw2 hn2 s2 b S1
    (h2.mono i1 s1' (Nat.le_refl _)) d2
  exact ⟨S2, i2, fun w hw => s2' _ (s1' _ hw), fun st len hw => s2' _ (cv1 st len hw), cv2⟩

theorem ilLoop_inv : ∀ (f : Nat) (s1 s2 : LzS) (b : Best) (S : Window → Prop),
    SOk cw R1 G c1 s1 b S → SOk cw R2 G c2 s2 b S → s1.ord.length + s2.ord.length ≤ f →
    ∃ S', Inv cw S' (ilLoop lk G ix R1 R2 c1 c2 (prepAll lk ix (seedHashes R1)) (prepAll lk ix (seedHashes R2))
        f s1 s2 b) ∧ (∀ w, S w → S' w) ∧ (∀ st len, cw ⟨c1, st, len⟩ ≤ 12 → S' ⟨c1, st, len⟩) ∧
      (∀ st len, cw ⟨c2, st, len⟩ ≤ 12 → S' ⟨c2, st, len⟩) := by
  have dead : ∀ (s : LzS) b, s.ord.length = 0 → s.live b = false := fun s b h => by
    simp [LzS.live, List.length_eq_zero_iff.mp h]
  have ne : ∀ (s : LzS) b, s.live b = true → s.ord ≠ [] := fun s b h e => by simp [LzS.live, e] at h
  intro f
  induction f with
  | zero =>
    intro s1 s2 b S h1 h2 hf
    exact both_dead cw hc13 G R1 R2 c1 c2 hcw1 hn1 hcw2 hn2 s1 s2 b S h1 h2
      (dead s1 b (by omega)) (dead s2 b (by omega))
  | succ f ih =>
    intro s1 s2 b S h1 h2 hf
    unfold ilLoop
    simp only []
    split
    · next hc =>
      have hl1 : s1.live b = true := by simp only [Bool.and_eq_true] at hc; exact hc.1
      obtain ⟨S2, k1, hS, hp, hlen⟩ := adv_ok cw hc13 R1 G c1 hcw1 hn1 lk ix hlk1 s1 b S h1 (ne s1 b hl1)
      obtain ⟨S', i', s', cv⟩ := ih _ s2 _ S2 k1 (h2.mono k1.inv hS hp) (by omega)
      exact ⟨S', i', fun w hw => s' _ (hS _ hw), cv⟩
    · next hc =>
      split
      · next hl2 =>
        obtain ⟨S2, k2, hS, hp, hlen⟩ := adv_ok cw hc13 R2 G c2 hcw2 hn2 lk ix hlk2 s2 b S h2 (ne s2 b hl2)
        obtain ⟨S', i', s', cv⟩ := ih s1 _ _ S2 (h1.mono k2.inv hS hp) k2 (by omega)
        exact ⟨S', i', fun w hw => s' _ (hS _ hw), cv⟩
      · next hl2 =>
        have hl2' : s2.live b = false := by simpa using hl2
        have hl1 : s1.live b = false := by
          cases e : s1.live b
          · rfl
          · exact absurd (by simp [e, hl2']) hc
        exact both_dead cw hc13 G R1 R2 c1 c2 hcw1 hn1 hcw2 hn2 s1 s2 b S h1 h2 hl1 hl2'

/-- **One chromosome, two reads.** -/
theorem mapChromI_inv (S : Window → Prop) (b : Best) (h : Inv cw S b) :
    ∃ S', Inv cw S' (mapChromI lk G ix R1 R2 c1 c2 (seedHashes R1) (seedHashes R2) b) ∧ (∀ w, S w → S' w) ∧
      (∀ st len, cw ⟨c1, st, len⟩ ≤ 12 → S' ⟨c1, st, len⟩) ∧
      (∀ st len, cw ⟨c2, st, len⟩ ≤ 12 → S' ⟨c2, st, len⟩) := by
  have l1 := (seedOrder_spec lk ix (prepAll lk ix (seedHashes R1))).2.2
  have l2 := (seedOrder_spec lk ix (prepAll lk ix (seedHashes R2))).2.2
  exact ilLoop_inv cw hc13 G lk ix R1 R2 c1 c2 hcw1 hn1 hlk1 hcw2 hn2 hlk2 8 _ _ b S
    (init_ok cw R1 G c1 lk ix b S h) (init_ok cw R2 G c2 lk ix b S h)
    (by simp [LzS.init, l1, l2])

end two

end MapSpec.Fast
