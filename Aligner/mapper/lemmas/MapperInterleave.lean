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

/-! ## The best only goes down -/

theorem add_pen_le (b : Best) (c st len p : Nat) : (b.add c st len p).pen ≤ b.pen := by
  unfold Best.add; split
  · simp only; omega
  · split <;> exact Nat.le_refl _

/-! ## Per-strand state -/

/-- Strand state `s` of read `R` (tag `c`) with best `b` and looked-at windows `S`. -/
def SOk (cw : Window → Nat) (R G : ByteArray) (c : Nat) (s : LzS) (b : Best) (S : Window → Prop) : Prop :=
  ∃ J, LoopState cw R G c J (pop4 J) s.as b S ∧ s.k = pop4 J ∧ s.looked = J ∧ s.ord.Nodup ∧
    (∀ j ∈ s.ord, j < 4 ∧ bit J j = 0) ∧ pop4 J + s.ord.length = 4

theorem SOk.inv {cw : Window → Nat} {R G : ByteArray} {c : Nat} {s : LzS} {b : Best} {S : Window → Prop}
    (h : SOk cw R G c s b S) : Inv cw S b := by
  obtain ⟨J, h1, -⟩ := h; exact h1.inv

section strand

variable (cw : Window → Nat) (hc13 : ∀ w, cw w ≤ 13) (R G : ByteArray) (c : Nat)
  (hcw : ∀ st len, cw ⟨c, st, len⟩ = penB R G st len) (hn : 100 ≤ R.size)
  {L P : Type} [Inhabited P] (lk : Look L P) (ix : L)
  (hlk : ∀ j, j < 4 → LookOk G R j (lk.look ix G R j (lk.prep ix (seedHash R j))))

include hc13 hcw hn hlk

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

end two

end MapSpec.Fast
