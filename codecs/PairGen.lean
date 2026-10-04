import FastGenMz
import PairJoint

/-!
# Codec `pairFastGJ`: proper pairs at any read length, `T = −P`, joint strand search

The general fast path (`chromG`, codecs/FastGenAlgo.lean) run over `2n` virtual
chromosomes sharing ONE `Best`, as `pairFastJ` (codecs/PairJoint.lean) does for
the 100 bp path: chromosome `c` with the read, `n + c` with its reverse
complement (genome array doubled, `gbs ++ gbs`: same byte arrays, no copy).
The search is exact in any order (`rf`: reverse strand first).  Mate 1 searches
its forward strand first; mate 2 the strand opposite to mate 1's hit, so the
second strand stops early once the first has a good hit.  Coverage per step is
`chromG_coverW` (codecs/FastGenProof.lean): windows of penalty ≤ min(best, P)
are added, the rest cannot change the result.

    GenomeBytes gbs g → Encodes R read → LookAllG gbs idxs → fastT P R →
      mapBothGJ P gbs idxs R rf = mapSpecBoth sc0 (-P) g read            (mapBothGJ_eq_mapSpecBoth)
    … → pairFastGJ P lo hi gbs idxs R1 R2 = pairSpec sc0 (-P) lo hi g m1 m2   (pairFastGJ_eq_pairSpec)
    hashed (`checkAll`) and minimizer (`checkAllMz`) indexes             (pairFastGJ_hashed/mz_eq_pairSpec)

`fastT P R`: at least `sbound P + 1` 25-letter seeds (T = −12: ≥ 100 letters;
T = −16: ≥ 150).  Shorter mates are left to the caller (the proved slow path
scans the whole genome per read).
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-! ## Algorithm -/

/-- One chromosome `c` of one strand: virtual chromosome `base + c`. -/
@[inline] def stepGJ {L Pp : Type} [LookG L Pp] [Inhabited L] [Inhabited Pp] (P : Nat) (R : ByteArray)
    (gb2 : Array ByteArray) (idxs : Array L) (base Ls m : Nat) (hs : Array (Option UInt64)) (b : Best) (c : Nat) :
    Best :=
  let ix := idxs[c]!
  let ps := hs.map (LookG.prep ix)
  chromG ix R gb2 (base + c) P Ls ps (ordG (ps.map (LookG.size ix)) m) b

/-- One strand (read `R`, tags `base + c`) over chromosomes `0 … n-1`. -/
@[inline] def foldGJ {L Pp : Type} [LookG L Pp] [Inhabited L] [Inhabited Pp] (P : Nat) (R : ByteArray)
    (gb2 : Array ByteArray) (idxs : Array L) (n base : Nat) (b : Best) : Best :=
  let m := R.size / 25
  (List.range n).foldl (stepGJ P R gb2 idxs base (R.size / m) m
    ((Array.range m).map fun j => seedHashAt R (j * (R.size / m)))) b

/-- Both strands through one shared `Best`; `rf`: reverse strand first. -/
@[specialize] def mapChromsGJ {L Pp : Type} [LookG L Pp] [Inhabited L] [Inhabited Pp] (P : Nat) (R : ByteArray)
    (gbs : Array ByteArray) (idxs : Array L) (rf : Bool) : Best :=
  let n := gbs.size
  let gb2 := gbs ++ gbs
  if rf then foldGJ P R gb2 idxs n 0 (foldGJ P (revCompB R) gb2 idxs n n (initP P))
  else foldGJ P (revCompB R) gb2 idxs n n (foldGJ P R gb2 idxs n 0 (initP P))

/-- Virtual window → placement, with the score. -/
def decodeGJ (P n : Nat) (b : Best) : Option (Placement × Int) :=
  match resultP P b with
  | some (c, st, len, pen) => some (decJ n ⟨c, st, len⟩, -(pen : Int))
  | none => none

def mapBothGJ {L Pp : Type} [LookG L Pp] [Inhabited L] [Inhabited Pp] (P : Nat) (gbs : Array ByteArray)
    (idxs : Array L) (R : ByteArray) (rf : Bool) : Option (Placement × Int) :=
  decodeGJ P gbs.size (mapChromsGJ P R gbs idxs rf)

/-- Proper-pair mapping; mate 2 searches the strand opposite to mate 1's hit first. -/
def pairFastGJ {L Pp : Type} [LookG L Pp] [Inhabited L] [Inhabited Pp] (P lo hi : Nat)
    (gbs : Array ByteArray) (idxs : Array L) (R1 R2 : ByteArray) :
    Option ((Placement × Int) × (Placement × Int)) :=
  match mapBothGJ P gbs idxs R1 false with
  | none => none
  | some a =>
    match mapBothGJ P gbs idxs R2 (a.1.2 == Strand.fwd) with
    | some b => if properPair lo hi a.1 b.1 then some (a, b) else none
    | none => none

/-! ## Penalties of virtual windows -/

/-- Penalty of a virtual window over the doubled genome. -/
def cwGJ (P : Nat) (read : List Char) (g : Genome) (w : Window) : Nat :=
  if w.chr < g.length then cwT P read (g ++ g) w else cwT P (revComp read) (g ++ g) w

/-- Penalty of a placement. -/
def cwPG (P : Nat) (read : List Char) (g : Genome) : Strand → Window → Nat
  | .fwd => cwT P read g
  | .rev => cwT P (revComp read) g

section
variable (P : Nat) (x : List Char) (g : Genome)

theorem cwT_out (w : Window) (h : g.length ≤ w.chr) : cwT P x g w = P + 1 := by
  unfold cwT windowScore windowSeq; rw [List.getElem?_eq_none h]

theorem cwT_appL (c st len : Nat) (h : c < g.length) : cwT P x (g ++ g) ⟨c, st, len⟩ = cwT P x g ⟨c, st, len⟩ := by
  unfold cwT windowScore windowSeq; simp only []; rw [List.getElem?_append_left h]

theorem cwT_appR (c st len : Nat) : cwT P x (g ++ g) ⟨g.length + c, st, len⟩ = cwT P x g ⟨c, st, len⟩ := by
  unfold cwT windowScore windowSeq; simp only []
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

theorem cwGJ_le (read : List Char) (w : Window) : cwGJ P read g w ≤ P + 1 := by
  unfold cwGJ; split <;> exact cwT_le _ _ _ _

theorem cwPG_chr_lt (read : List Char) (p : Placement) (h : cwPG P read g p.2 p.1 ≤ P) : p.1.chr < g.length := by
  rcases p with ⟨w, st⟩
  show w.chr < g.length
  apply Classical.byContradiction; intro hc
  cases st <;> simp only [cwPG] at h <;> rw [cwT_out _ _ _ _ (by omega)] at h <;> omega

theorem cwGJ_encJ (read : List Char) (p : Placement) (h : cwPG P read g p.2 p.1 ≤ P) :
    cwGJ P read g (encJ g.length p) = cwPG P read g p.2 p.1 := by
  have hc := cwPG_chr_lt P g read p h
  rcases p with ⟨⟨c, st, len⟩, s⟩
  simp only at hc
  cases s
  · simp [encJ, cwGJ, cwPG, hc, cwT_appL]
  · have : ¬ g.length + c < g.length := by omega
    simp [encJ, cwGJ, cwPG, this, cwT_appR]

theorem cwGJ_chr_lt (read : List Char) (w : Window) (h : cwGJ P read g w ≤ P) : w.chr < 2 * g.length := by
  apply Classical.byContradiction; intro hc
  unfold cwGJ at h
  split at h <;> rw [cwT_out _ _ _ _ (by simp; omega)] at h <;> omega

theorem cwPG_decJ (read : List Char) (w : Window) :
    cwPG P read g (decJ g.length w).2 (decJ g.length w).1 = cwGJ P read g w := by
  rcases w with ⟨c, st, len⟩
  unfold decJ cwGJ
  by_cases hc : c < g.length
  · simp [hc, cwPG, cwT_appL]
  · simp only [hc, if_false, cwPG]
    have := cwT_appR P (revComp read) g (c - g.length) st len
    rw [show g.length + (c - g.length) = c by omega] at this
    rw [this]

end

theorem genomeBytes_dbl (gbs : Array ByteArray) (g : Genome) (hg : GenomeBytes gbs g) :
    GenomeBytes (gbs ++ gbs) (g ++ g) := by
  obtain ⟨hs, he⟩ := hg
  refine ⟨by simp [hs], fun c h1 h2 => ?_⟩
  simp only [Array.size_append] at h1
  by_cases hc : c < gbs.size
  · rw [Array.getElem_append_left hc, List.getElem_append_left (by omega)]; exact he c hc (by omega)
  · rw [Array.getElem_append_right (by omega), List.getElem_append_right (by omega)]
    have e : c - gbs.size = c - g.length := by omega
    have := he (c - gbs.size) (by omega) (by omega)
    simp only [e] at this ⊢
    exact this

theorem dbl_get (gbs : Array ByteArray) (base c : Nat) (hb : base = 0 ∨ base = gbs.size) (hc : c < gbs.size) :
    (gbs ++ gbs)[base + c]! = gbs[c]! := by
  rw [getElem!_pos gbs c hc, getElem!_pos _ _ (by simp; omega), Array.getElem_append]
  rcases hb with rfl | rfl
  · simp [hc]
  · simp [show ¬ gbs.size + c < gbs.size by omega]

/-! ## One strand -/

theorem foldGJ_inv {L Pp : Type} [LookG L Pp] [Inhabited L] [Inhabited Pp] (P : Nat) (read read' : List Char)
    (g : Genome) (gbs : Array ByteArray) (idxs : Array L) (R' : ByteArray) (base : Nat)
    (hg : GenomeBytes gbs g) (hr : Encodes R' read') (hlk : LookAllG gbs idxs)
    (hb : base = 0 ∨ base = gbs.size)
    (hcw : ∀ c, c < gbs.size → ∀ st len,
      cwGJ P read g ⟨base + c, st, len⟩ = cwT P read' (g ++ g) ⟨base + c, st, len⟩)
    (hm : 0 < R'.size / 25) (hsb : sbound P < R'.size / 25) (S : Window → Prop) (b : Best)
    (h : InvP P (cwGJ P read g) S b) :
    ∃ S', InvP P (cwGJ P read g) S' (foldGJ P R' (gbs ++ gbs) idxs gbs.size base b) ∧ (∀ w, S w → S' w) ∧
      ∀ c, c < gbs.size → ∀ st len, cwGJ P read g ⟨base + c, st, len⟩ ≤ P → S' ⟨base + c, st, len⟩ := by
  have hg2 := genomeBytes_dbl gbs g hg
  unfold foldGJ
  simp only []
  generalize hhs : (Array.range (R'.size / 25)).map (fun j => seedHashAt R' (j * (R'.size / (R'.size / 25)))) = hs
  have hhs' : ∀ j, j < R'.size / 25 → hs[j]! = seedHashAt R' (j * (R'.size / (R'.size / 25))) := by
    intro j hj
    rw [← hhs, getElem!_pos _ j (by simpa using hj)]
    simp
  have hsz : hs.size = R'.size / 25 := by rw [← hhs]; simp
  have step : ∀ (l : List Nat) S b, (∀ c ∈ l, c < gbs.size) → InvP P (cwGJ P read g) S b →
      ∃ S', InvP P (cwGJ P read g) S' (l.foldl (stepGJ P R' (gbs ++ gbs) idxs base
          (R'.size / (R'.size / 25)) (R'.size / 25) hs) b) ∧
        (∀ w, S w → S' w) ∧ ∀ c ∈ l, ∀ st len, cwGJ P read g ⟨base + c, st, len⟩ ≤ P → S' ⟨base + c, st, len⟩ := by
    intro l
    induction l with
    | nil => intro S b _ h; exact ⟨S, h, fun w hw => hw, fun c hc => by simp at hc⟩
    | cons c l ih =>
      intro S b hl h
      have hc : c < gbs.size := hl c List.mem_cons_self
      obtain ⟨hnd, hlt, hlen⟩ := ordG_spec ((hs.map (LookG.prep idxs[c]!)).map (LookG.size idxs[c]!)) (R'.size / 25)
      obtain ⟨S1, h1, s1, c1⟩ := chromG_coverW (cwGJ P read g) P read' (g ++ g) (gbs ++ gbs) R' hg2 hr
        (cwGJ_le P g read) idxs[c]! (base + c) (hs.map (LookG.prep idxs[c]!)) _
        (by simp; omega) (fun st len => hcw c hc st len) hm hsb (fun j hj => by
          rw [getElem!_pos _ j (by simp [hsz]; omega)]
          simp only [Array.getElem_map]
          rw [← hhs' j hj, getElem!_pos _ j (by omega)])
        (fun s base' hs' => by rw [dbl_get gbs base c hb hc]; exact hlk c hc R' s base' hs') hnd hlt hlen S b h
      simp only [List.foldl_cons]
      unfold stepGJ
      simp only []
      generalize chromG idxs[c]! R' (gbs ++ gbs) (base + c) P (R'.size / (R'.size / 25)) (hs.map (LookG.prep idxs[c]!))
        (ordG ((hs.map (LookG.prep idxs[c]!)).map (LookG.size idxs[c]!)) (R'.size / 25)) b = b1 at h1 c1
      -- the windows of this chromosome not added cannot beat or tie the best
      have h1' := inv_skipP P (cwGJ P read g) (cwGJ_le P g read) S1
        (fun w => w.chr = base + c ∧ cwGJ P read g w ≤ P ∧ ¬ S1 w) b1 h1 (by
          rintro w ⟨hwc, hwP, hnot⟩
          left
          apply Classical.byContradiction; intro hle
          exact hnot (c1 w hwc (by omega)))
      obtain ⟨S2, h2, s2, c2⟩ := ih _ _ (fun c' h' => hl c' (List.mem_cons_of_mem _ h')) h1'
      refine ⟨S2, h2, fun w hw => s2 w (Or.inl (s1 w hw)), fun c' hc' st len hwP => ?_⟩
      rcases List.mem_cons.mp hc' with rfl | hc'
      · apply s2
        by_cases hs1 : S1 ⟨base + c', st, len⟩
        · exact Or.inl hs1
        · exact Or.inr ⟨rfl, hwP, hs1⟩
      · exact c2 c' hc' st len hwP
  obtain ⟨S', h', s', c'⟩ := step (List.range gbs.size) S b (fun c hc => List.mem_range.mp hc) h
  exact ⟨S', h', s', fun c hc => c' c (List.mem_range.mpr hc)⟩

/-- **Both strands, shared best**: the invariant over virtual windows, covering
every virtual window of penalty ≤ `P`. -/
theorem mapChromsGJ_inv {L Pp : Type} [LookG L Pp] [Inhabited L] [Inhabited Pp] (P : Nat) (read : List Char)
    (g : Genome) (gbs : Array ByteArray) (idxs : Array L) (R : ByteArray) (rf : Bool)
    (hg : GenomeBytes gbs g) (hr : Encodes R read) (hlk : LookAllG gbs idxs)
    (hm : 0 < R.size / 25) (hsb : sbound P < R.size / 25) :
    ∃ S, InvP P (cwGJ P read g) S (mapChromsGJ P R gbs idxs rf) ∧ ∀ w, cwGJ P read g w ≤ P → S w := by
  have hn := hg.1
  have hrr := revCompB_encodes R read hr
  have hsz := revCompB_size R
  have F := foldGJ_inv P read read g gbs idxs R 0 hg hr hlk (Or.inl rfl)
    (fun c hc st len => by unfold cwGJ; simp [show c < g.length by omega]) hm hsb
  have V := foldGJ_inv P read (revComp read) g gbs idxs (revCompB R) gbs.size hg hrr hlk (Or.inr rfl)
    (fun c hc st len => by unfold cwGJ; simp only [show ¬ (gbs.size + c < g.length) by omega, if_false]) (by rw [hsz]; exact hm) (by rw [hsz]; exact hsb)
  have cover : ∀ (S : Window → Prop),
      (∀ c, c < gbs.size → ∀ st len, cwGJ P read g ⟨0 + c, st, len⟩ ≤ P → S ⟨0 + c, st, len⟩) →
      (∀ c, c < gbs.size → ∀ st len, cwGJ P read g ⟨gbs.size + c, st, len⟩ ≤ P → S ⟨gbs.size + c, st, len⟩) →
      ∀ w, cwGJ P read g w ≤ P → S w := by
    intro S cf cr ⟨c, st, len⟩ hw
    have h2 := cwGJ_chr_lt P g read _ hw
    simp only at h2
    by_cases hc : c < gbs.size
    · have := cf c hc st len (by simpa using hw); simpa using this
    · have := cr (c - gbs.size) (by omega) st len
        (by rw [show gbs.size + (c - gbs.size) = c by omega]; exact hw)
      rwa [show gbs.size + (c - gbs.size) = c by omega] at this
  unfold mapChromsGJ
  cases rf with
  | false =>
    obtain ⟨S1, h1, -, cov1⟩ := F (fun _ => False) (initP P) (inv_initP P _)
    obtain ⟨S2, h2, s2, cov2⟩ := V S1 _ h1
    exact ⟨S2, h2, cover S2 (fun c hc st len hw => s2 _ (cov1 c hc st len hw)) cov2⟩
  | true =>
    obtain ⟨S1, h1, -, cov1⟩ := V (fun _ => False) (initP P) (inv_initP P _)
    obtain ⟨S2, h2, s2, cov2⟩ := F S1 _ h1
    exact ⟨S2, h2, cover S2 cov2 (fun c hc st len hw => s2 _ (cov1 c hc st len hw))⟩

/-! ## Decoding -/

theorem decodeGJ_spec (P : Nat) (read : List Char) (g : Genome) (S : Window → Prop) (b : Best)
    (h : InvP P (cwGJ P read g) S b) (hall : ∀ w, cwGJ P read g w ≤ P → S w) (p : Placement) (s : Int) :
    decodeGJ P g.length b = some (p, s) ↔
      (cwPG P read g p.2 p.1 ≤ P ∧ s = -(cwPG P read g p.2 p.1 : Int)) ∧
      ∀ p', cwPG P read g p'.2 p'.1 ≤ P → p' ≠ p → cwPG P read g p.2 p.1 < cwPG P read g p'.2 p'.1 := by
  have key := resultP_spec P (cwGJ P read g) S b h hall
  constructor
  · intro hd
    unfold decodeGJ at hd
    split at hd
    · next c st len pen hr =>
      obtain ⟨e1, e2, e3⟩ := (key ⟨c, st, len⟩ pen).mp hr
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨hp, hs⟩ := hd
      have hcp : cwPG P read g p.2 p.1 = pen := by rw [← hp, cwPG_decJ, e1]
      refine ⟨⟨by omega, by rw [← hs, hcp]⟩, fun p' h1 h2 => ?_⟩
      rw [hcp, ← cwGJ_encJ P g read p' h1]
      apply e3 _ (by rw [cwGJ_encJ P g read p' h1]; exact h1)
      intro he
      apply h2
      rw [← hp, ← he, decJ_encJ _ _ (cwPG_chr_lt P g read p' h1)]
    · exact absurd hd (by simp)
  · rintro ⟨⟨h1, rfl⟩, h3⟩
    have hr : resultP P b = some ((encJ g.length p).chr, (encJ g.length p).start,
        (encJ g.length p).len, cwPG P read g p.2 p.1) := by
      refine (key _ _).mpr ⟨cwGJ_encJ P g read p h1, h1, fun w' h4 h5 => ?_⟩
      have := h3 (decJ g.length w') (by rw [cwPG_decJ]; exact h4) (by
        intro he; apply h5; rw [← he, encJ_decJ _ _ (cwGJ_chr_lt P g read w' h4)])
      rwa [cwPG_decJ] at this
    unfold decodeGJ
    rw [hr]
    simp only [Option.some.injEq, Prod.mk.injEq, and_true]
    exact decJ_encJ g.length p (cwPG_chr_lt P g read p h1)

/-! ## `mapSpecBoth` at any threshold -/

theorem mem_hitsBothT (T : Int) (g : Genome) (read : List Char) (p : Placement) (s : Int) :
    (p, s) ∈ hitsBoth sc0 T g read ↔
      p.1 ∈ allWindows g ∧ strandScore g read p.2 p.1 = some s ∧ T ≤ s := by
  obtain ⟨w, st⟩ := p
  unfold hitsBoth
  rw [List.mem_append, List.mem_map, List.mem_map]
  cases st with
  | fwd =>
    show _ ↔ w ∈ allWindows g ∧ windowScore sc0 read g w = some s ∧ T ≤ s
    rw [← mem_hitsOf]
    constructor
    · rintro (⟨⟨w', s'⟩, h, he⟩ | ⟨⟨w', s'⟩, h, he⟩)
      · simp only [Prod.mk.injEq] at he
        obtain ⟨⟨rfl, -⟩, rfl⟩ := he
        exact h
      · simp at he
    · intro h; exact Or.inl ⟨(w, s), h, rfl⟩
  | rev =>
    show _ ↔ w ∈ allWindows g ∧ windowScore sc0 (revComp read) g w = some s ∧ T ≤ s
    rw [← mem_hitsOf]
    constructor
    · rintro (⟨⟨w', s'⟩, h, he⟩ | ⟨⟨w', s'⟩, h, he⟩)
      · simp at he
      · simp only [Prod.mk.injEq] at he
        obtain ⟨⟨rfl, -⟩, rfl⟩ := he
        exact h
    · intro h; exact Or.inr ⟨(w, s), h, rfl⟩

theorem mapSpecBoth_iffT (T : Int) (g : Genome) (read : List Char) (p : Placement) (s : Int) :
    mapSpecBoth sc0 T g read = some (p, s) ↔
      (strandScore g read p.2 p.1 = some s ∧ T ≤ s) ∧
      ∀ p' s', strandScore g read p'.2 p'.1 = some s' → T ≤ s' → s' < s ∨ p' = p := by
  unfold mapSpecBoth
  rw [selectUniqueBy_eq_some_iff _ (by
    rintro ⟨a, sa⟩ ha ⟨b, sb⟩ hb (rfl : a = b)
    rw [mem_hitsBothT] at ha hb
    have := ha.2.1.symm.trans hb.2.1
    simpa using this)]
  constructor
  · rintro ⟨hm, h3⟩
    rw [mem_hitsBothT] at hm
    exact ⟨⟨hm.2.1, hm.2.2⟩, fun p' s' h4 h5 =>
      h3 (p', s') ((mem_hitsBothT _ _ _ _ _).2
        ⟨strandScore_allWindows g read p'.2 p'.1 s' h4, h4, h5⟩)⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨(mem_hitsBothT _ _ _ _ _).2
      ⟨strandScore_allWindows g read p.2 p.1 s h1, h1, h2⟩, fun ⟨p', s'⟩ hb => ?_⟩
    rw [mem_hitsBothT] at hb
    exact h3 p' s' hb.2.1 hb.2.2

/-! ## Top theorems -/

/-- **Both strands through one shared best, any length the general fast path takes, `T = −P`.** -/
theorem mapBothGJ_eq_mapSpecBoth {L Pp : Type} [LookG L Pp] [Inhabited L] [Inhabited Pp] (P : Nat)
    (g : Genome) (read : List Char) (gbs : Array ByteArray) (idxs : Array L) (R : ByteArray) (rf : Bool)
    (hg : GenomeBytes gbs g) (hr : Encodes R read) (hlk : LookAllG gbs idxs) (hok : fastT P R = true) :
    mapBothGJ P gbs idxs R rf = mapSpecBoth sc0 (-(P : Int)) g read := by
  unfold fastT at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨S, hinv, hall⟩ := mapChromsGJ_inv P read g gbs idxs R rf hg hr hlk hok.1 hok.2
  have key : ∀ (st : Strand) w' s', (strandScore g read st w' = some s' ∧ -(P : Int) ≤ s') ↔
      (cwPG P read g st w' ≤ P ∧ s' = -(cwPG P read g st w' : Int)) := by
    intro st w' s'
    cases st with
    | fwd => exact cwT_iff P read g w' s'
    | rev => exact cwT_iff P (revComp read) g w' s'
  apply Option.ext
  rintro ⟨p, s⟩
  unfold mapBothGJ
  rw [hg.1, mapSpecBoth_iffT, decodeGJ_spec P read g S _ hinv hall]
  constructor
  · rintro ⟨⟨h1, rfl⟩, h3⟩
    refine ⟨(key p.2 p.1 _).mpr ⟨h1, rfl⟩, fun p' s' h4 h5 => ?_⟩
    obtain ⟨h6, rfl⟩ := (key p'.2 p'.1 s').mp ⟨h4, h5⟩
    by_cases hp : p' = p
    · right; exact hp
    · left; have := h3 p' h6 hp; omega
  · rintro ⟨h1, h3⟩
    obtain ⟨h1a, rfl⟩ := (key p.2 p.1 s).mp h1
    refine ⟨⟨h1a, rfl⟩, fun p' h4 h5 => ?_⟩
    rcases h3 p' _ ((key p'.2 p'.1 _).mpr ⟨h4, rfl⟩).1 ((key p'.2 p'.1 _).mpr ⟨h4, rfl⟩).2 with h6 | h6
    · omega
    · exact absurd h6 h5

/-- **Proper pairs, any mate lengths the general fast path takes, `T = −P`.** -/
theorem pairFastGJ_eq_pairSpec {L Pp : Type} [LookG L Pp] [Inhabited L] [Inhabited Pp] (P lo hi : Nat)
    (g : Genome) (m1 m2 : List Char) (gbs : Array ByteArray) (idxs : Array L) (R1 R2 : ByteArray)
    (hg : GenomeBytes gbs g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hlk : LookAllG gbs idxs)
    (hok1 : fastT P R1 = true) (hok2 : fastT P R2 = true) :
    pairFastGJ P lo hi gbs idxs R1 R2 = pairSpec sc0 (-(P : Int)) lo hi g m1 m2 := by
  unfold pairFastGJ pairSpec
  rw [mapBothGJ_eq_mapSpecBoth P g m1 gbs idxs R1 false hg h1 hlk hok1]
  cases mapSpecBoth sc0 (-(P : Int)) g m1 with
  | none => rfl
  | some a =>
    simp only
    rw [mapBothGJ_eq_mapSpecBoth P g m2 gbs idxs R2 _ hg h2 hlk hok2]
    cases mapSpecBoth sc0 (-(P : Int)) g m2 <;> rfl

/-- Hashed per-chromosome indexes, checked at run time. -/
theorem pairFastGJ_hashed_eq_pairSpec (P lo hi : Nat) (g : Genome) (m1 m2 : List Char) (gbs : Array ByteArray)
    (idxs : Array HIdx) (R1 R2 : ByteArray) (hg : GenomeBytes gbs g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2)
    (hchk : checkAll idxs gbs = true) (hok1 : fastT P R1 = true) (hok2 : fastT P R2 = true) :
    pairFastGJ P lo hi gbs idxs R1 R2 = pairSpec sc0 (-(P : Int)) lo hi g m1 m2 :=
  pairFastGJ_eq_pairSpec P lo hi g m1 m2 gbs idxs R1 R2 hg h1 h2 (lookAllG_hashed gbs idxs hchk) hok1 hok2

/-- Minimizer per-chromosome indexes, checked at run time. -/
theorem pairFastGJ_mz_eq_pairSpec (P lo hi : Nat) (g : Genome) (m1 m2 : List Char) (gbs : Array ByteArray)
    (idxs : Array Mz.MzIdx) (R1 R2 : ByteArray) (hg : GenomeBytes gbs g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2)
    (hchk : checkAllMz idxs gbs = true) (hok1 : fastT P R1 = true) (hok2 : fastT P R2 = true) :
    pairFastGJ P lo hi gbs idxs R1 R2 = pairSpec sc0 (-(P : Int)) lo hi g m1 m2 :=
  pairFastGJ_eq_pairSpec P lo hi g m1 m2 gbs idxs R1 R2 hg h1 h2 (lookAllG_mz gbs idxs hchk) hok1 hok2

end MapSpec.Fast

#print axioms MapSpec.Fast.mapBothGJ_eq_mapSpecBoth
#print axioms MapSpec.Fast.pairFastGJ_eq_pairSpec
#print axioms MapSpec.Fast.pairFastGJ_hashed_eq_pairSpec
#print axioms MapSpec.Fast.pairFastGJ_mz_eq_pairSpec
