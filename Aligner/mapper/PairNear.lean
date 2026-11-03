import PairHybrid

/-!
# The ladder with the second mate searched near the first only

At each rung the ladder uses the second-searched mate's hits only through the proper
pairs they make with the first mate's hits.  So the second mate's list may be any list
of its hits that holds every hit with a proper partner in the first mate's list
(`NearOk`); the answers do not change (`ladderUB_eq`: `ladderUB` = `ladderUR`).
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-- `x` has a proper partner in `l` (either mate order). -/
def Partner (sl lo hi : Nat) (l : List (Placement × Int)) (x : Placement × Int) : Prop :=
  ∃ y ∈ l, properPairU sl lo hi y.1 x.1 = true ∨ properPairU sl lo hi x.1 y.1 = true

/-- `l` holds every hit of `H` with a partner in `A`, and only hits of `H`. -/
def NearOk (sl lo hi : Nat) (A H l : List (Placement × Int)) : Prop :=
  (∀ x ∈ l, x ∈ H) ∧ ∀ x ∈ H, Partner sl lo hi A x → x ∈ l

theorem pp_near_right {sl lo hi : Nat} {A H l : List (Placement × Int)} (hn : NearOk sl lo hi A H l) (p : PairHit) :
    p ∈ properPairs sl lo hi A l ↔ p ∈ properPairs sl lo hi A H := by
  rw [mem_properPairs, mem_properPairs]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, hn.1 _ h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, hn.2 _ h2 ⟨p.1, h1, Or.inl h3⟩, h3⟩

theorem pp_near_left {sl lo hi : Nat} {A H l : List (Placement × Int)} (hn : NearOk sl lo hi A H l) (p : PairHit) :
    p ∈ properPairs sl lo hi l A ↔ p ∈ properPairs sl lo hi H A := by
  rw [mem_properPairs, mem_properPairs]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨hn.1 _ h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨hn.2 _ h1 ⟨p.2, h2, Or.inr h3⟩, h2, h3⟩

theorem topW_none_iff (dc : Nat → Nat) (l : List PairHit) : topW dc l = none ↔ l = [] := by
  cases l <;> simp [topW]

section near
variable (dc : Nat → Nat) (sl lo hi P1 P2 : Nat) (hf : Bool → Nat → List (Placement × Int))
  (hn : Bool → Nat → List (Placement × Int) → List (Placement × Int))
  (hSF : ∀ b c, c ≤ (if b then P1 else P2) → ScoreFun (hf b c))
  (hN : ∀ b c lA, c ≤ (if b then P1 else P2) → NearOk sl lo hi lA (hf b c) (hn b c lA))

end near

/-! ## Hits near the first mate's hits -/

/-- `hitsCK` on the diagonals `sel` keeps. -/
def hitsCKN (K : RP) (R : ByteArray) (pgs2 : Array PGen) (c lim : Nat) (acc : List (Array Nat))
    (us : List Nat) (Ls : Nat) (sel : Nat → Bool) : List (Window × Nat) :=
  (diags acc).flatMap fun D =>
    if sel D && kfiltV K R pgs2[c]! acc us Ls lim (initP lim) D then
      (shapesAt lim).filterMap fun sh =>
        if 0 ≤ dst R.size D sh ∧ 0 ≤ wlen R.size sh then
          let k := kerHKG R K pgs2 pgs2 c (dst R.size D sh).toNat (wlen R.size sh).toNat lim
          if k ≤ lim then some (⟨c, (dst R.size D sh).toNat, (wlen R.size sh).toNat⟩, k) else none
        else none
    else []

/-- `hitsCKN` with the shapes taken once from the table (`hitsCKN_eqT`). -/
def hitsCKNT (K : RP) (R : ByteArray) (pgs2 : Array PGen) (c lim : Nat) (acc : List (Array Nat))
    (us : List Nat) (Ls : Nat) (sel : Nat → Bool) : List (Window × Nat) :=
  if acc.all fun a => a.isEmpty then [] else
  let shs := shapesT lim
  (diags acc).flatMap fun D =>
    if sel D && kfiltV K R pgs2[c]! acc us Ls lim (initP lim) D then
      shs.filterMap fun sh =>
        if 0 ≤ dst R.size D sh ∧ 0 ≤ wlen R.size sh then
          let k := kerHKG R K pgs2 pgs2 c (dst R.size D sh).toNat (wlen R.size sh).toNat lim
          if k ≤ lim then some (⟨c, (dst R.size D sh).toNat, (wlen R.size sh).toNat⟩, k) else none
        else none
    else []

/-- Compiled code runs `hitsCKNT`. -/
@[csimp] theorem hitsCKN_eqT : @hitsCKN = @hitsCKNT := by
  funext K R pgs2 c lim acc us Ls sel
  unfold hitsCKN hitsCKNT
  split
  · rename_i h; rw [diags_empty acc h]; rfl
  · simp only [shapesT_eq]

theorem hitsCKN_sub (K : RP) (R : ByteArray) (pgs2 : Array PGen) (c lim : Nat) (acc : List (Array Nat))
    (us : List Nat) (Ls : Nat) (sel : Nat → Bool) (x : Window × Nat)
    (h : x ∈ hitsCKN K R pgs2 c lim acc us Ls sel) : x ∈ hitsCK K R pgs2 c lim acc us Ls := by
  unfold hitsCKN at h
  unfold hitsCK
  rw [List.mem_flatMap] at h ⊢
  obtain ⟨D, hD, hx⟩ := h
  refine ⟨D, hD, ?_⟩
  split at hx
  · next hk =>
    rw [Bool.and_eq_true] at hk
    rw [if_pos hk.2]; exact hx
  · cases hx

theorem hitsCKN_of (K : RP) (R : ByteArray) (pgs2 : Array PGen) (c lim : Nat) (acc : List (Array Nat))
    (us : List Nat) (Ls : Nat) (sel : Nat → Bool) (x : Window × Nat)
    (h : x ∈ hitsCK K R pgs2 c lim acc us Ls)
    (hs : ∀ D sh, sh ∈ shapesAt lim → 0 ≤ dst R.size D sh →
      x.1 = ⟨c, (dst R.size D sh).toNat, (wlen R.size sh).toNat⟩ → sel D = true) :
    x ∈ hitsCKN K R pgs2 c lim acc us Ls sel := by
  unfold hitsCK at h
  unfold hitsCKN
  rw [List.mem_flatMap] at h ⊢
  obtain ⟨D, hD, hx⟩ := h
  refine ⟨D, hD, ?_⟩
  split at hx
  · next hk =>
    have hx' := hx
    rw [List.mem_filterMap] at hx'
    obtain ⟨sh, hsh, he⟩ := hx'
    split at he
    · next hc =>
      simp only [] at he
      split at he
      · simp only [Option.some.injEq] at he
        have hsel := hs D sh hsh hc.1 (by rw [← he])
        rw [if_pos (by rw [Bool.and_eq_true]; exact ⟨hsel, hk⟩)]
        exact hx
      · cases he
    · cases he
  · cases hx

/-- `hitsSK` with each chromosome's diagonals chosen by `keep` (virtual chromosome, read length). -/
def hitsSKN {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G : ByteArray) (offs : Array Nat)
    (pgs2 : Array PGen) (n t lim : Nat) (Rs : ByteArray) (keep : Nat → Nat → Nat → Bool) : List (Window × Nat) :=
  let m := Rs.size / 25
  let Ls := Rs.size / m
  let K := packRP Rs
  let ps := prepG ix Rs m Ls
  let J := (ordG (ps.map (LookG.size ix)) m).take (sbound lim + 1)
  let lk := J.map fun j => (j, LookG.look ix G Rs (j * Ls) (Rs.size - j * Ls) ps[j]!)
  let us := unseen m J
  (List.range n).flatMap fun c =>
    hitsCKN K Rs pgs2 (t + c) lim (slicesAt lk Rs.size Ls offs[c]! (GRead.size pgs2[t + c]!)) us Ls
      (keep (t + c) Rs.size)

/-- `hitsAtKP` on the diagonals `keep` chooses. -/
def hitsAtKPN {L Pp : Type} [LookG L Pp] [Inhabited Pp] (lim : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (pgs : Array PGen) (R : ByteArray) (keep : Nat → Nat → Nat → Bool) :
    Option (List (Placement × Int)) :=
  if fastT lim R then
    let n := pgs.size
    let pgs2 := pgs ++ pgs
    some ((hitsSKN ix G offs pgs2 n 0 lim R keep ++ hitsSKN ix G offs pgs2 n n lim (revCompK R) keep).map
      fun x => (decB n x.1, -(x.2 : Int)))
  else none

theorem hitsSKN_sub {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G : ByteArray) (offs : Array Nat)
    (pgs2 : Array PGen) (n t lim : Nat) (Rs : ByteArray) (keep : Nat → Nat → Nat → Bool) (x : Window × Nat)
    (h : x ∈ hitsSKN ix G offs pgs2 n t lim Rs keep) : x ∈ hitsSK ix G offs pgs2 n t lim Rs := by
  unfold hitsSKN at h
  unfold hitsSK
  simp only [List.mem_flatMap] at h ⊢
  obtain ⟨c, hc, hx⟩ := h
  exact ⟨c, hc, hitsCKN_sub _ _ _ _ _ _ _ _ _ x hx⟩

theorem hitsSKN_of {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G : ByteArray) (offs : Array Nat)
    (pgs2 : Array PGen) (n t lim : Nat) (Rs : ByteArray) (keep : Nat → Nat → Nat → Bool) (x : Window × Nat)
    (h : x ∈ hitsSK ix G offs pgs2 n t lim Rs)
    (hs : ∀ vc D sh, sh ∈ shapesAt lim → 0 ≤ dst Rs.size D sh →
      x.1 = ⟨vc, (dst Rs.size D sh).toNat, (wlen Rs.size sh).toNat⟩ → keep vc Rs.size D = true) :
    x ∈ hitsSKN ix G offs pgs2 n t lim Rs keep := by
  unfold hitsSK at h
  unfold hitsSKN
  simp only [List.mem_flatMap] at h ⊢
  obtain ⟨c, hc, hx⟩ := h
  exact ⟨c, hc, hitsCKN_of _ _ _ _ _ _ _ _ _ x hx (fun D sh h1 h2 h3 => hs _ D sh h1 h2 h3)⟩

/-- The near hits are hits; a hit whose every possible diagonal is kept is a near hit. -/
theorem hitsAtKPN_mem {L Pp : Type} [LookG L Pp] [Inhabited Pp] (lim : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (pgs : Array PGen) (R : ByteArray) (keep : Nat → Nat → Nat → Bool)
    (l l' : List (Placement × Int)) (hl : hitsAtKP lim ix G offs pgs R = some l)
    (hl' : hitsAtKPN lim ix G offs pgs R keep = some l') (x : Placement × Int) :
    (x ∈ l' → x ∈ l) ∧
    (x ∈ l → (∀ vc nR D sh, sh ∈ shapesAt lim → 0 ≤ dst nR D sh →
      x.1 = decB pgs.size ⟨vc, (dst nR D sh).toNat, (wlen nR sh).toNat⟩ → keep vc nR D = true) → x ∈ l') := by
  unfold hitsAtKP at hl
  unfold hitsAtKPN at hl'
  split at hl
  · next hf =>
    rw [if_pos hf] at hl'
    simp only [Option.some.injEq] at hl hl'
    subst hl hl'
    constructor
    · intro hx
      simp only [List.mem_map, List.mem_append] at hx ⊢
      obtain ⟨y, hy, rfl⟩ := hx
      refine ⟨y, ?_, rfl⟩
      rcases hy with hy | hy
      · exact Or.inl (hitsSKN_sub _ _ _ _ _ _ _ _ _ y hy)
      · exact Or.inr (hitsSKN_sub _ _ _ _ _ _ _ _ _ y hy)
    · intro hx hk
      simp only [List.mem_map, List.mem_append] at hx ⊢
      obtain ⟨y, hy, rfl⟩ := hx
      refine ⟨y, ?_, rfl⟩
      have hs : ∀ (Rs : ByteArray), ∀ vc D sh, sh ∈ shapesAt lim → 0 ≤ dst Rs.size D sh →
          y.1 = ⟨vc, (dst Rs.size D sh).toNat, (wlen Rs.size sh).toNat⟩ → keep vc Rs.size D = true := by
        intro Rs vc D sh h1 h2 h3
        exact hk vc Rs.size D sh h1 h2 (by rw [h3])
      rcases hy with hy | hy
      · exact Or.inl (hitsSKN_of _ _ _ _ _ _ _ _ _ y hy (hs _))
      · exact Or.inr (hitsSKN_of _ _ _ _ _ _ _ _ _ y hy (hs _))
  · cases hl

/-! ## The diagonal choice from the first mate's hits -/

/-- Diagonal `D` of virtual chromosome `vc` (read length `nR`, shift bound `gb`) may hold a
window with a proper partner among the hits `ys`. -/
def keepN (sl hi n gb : Nat) (ys : List (Placement × Int)) (vc nR D : Nat) : Bool :=
  ys.any fun y => y.1.1.chr == (if vc < n then vc else vc - n) &&
    decide (D ≤ y.1.1.start + y.1.1.len + hi + sl + nR + gb) && decide (y.1.1.start + nR ≤ D + hi + sl + gb)

theorem properPairU_near (sl lo hi : Nat) (a b : Placement) (h : properPairU sl lo hi a b = true) :
    a.1.chr = b.1.chr ∧ b.1.start ≤ a.1.start + a.1.len + hi + sl ∧ a.1.start ≤ b.1.start + hi + sl ∧
      a.1.start ≤ b.1.start + b.1.len + hi + sl ∧ b.1.start ≤ a.1.start + hi + sl := by
  rcases a with ⟨⟨ca, sa, la⟩, ta⟩
  rcases b with ⟨⟨cb, sb, lb⟩, tb⟩
  cases ta <;> cases tb <;> simp [properPairU, properPair, fwdRev] at h ⊢ <;> omega

theorem shapesAt_fst (lim : Nat) (sh : Int × Int) (h : sh ∈ shapesAt lim) :
    sh.1.natAbs ≤ gapBound sc0 (-(lim : Int)) := by
  unfold shapesAt at h
  rw [List.mem_mergeSort] at h
  have := (shapes_ok _ _ sh h).1
  omega

/-- The near list of a read at cap `c` given the first mate's hits `ys`. -/
def hitsKPFN {L Pp : Type} [LookG L Pp] [Inhabited Pp] (sl hi : Nat) (ix : L) (G : ByteArray) (offs : Array Nat)
    (pgs : Array PGen) (R : ByteArray) (c : Nat) (ys : List (Placement × Int)) : List (Placement × Int) :=
  match hitsAtKPN c ix G offs pgs R (keepN sl hi pgs.size (gapBound sc0 (-(c : Int))) ys) with
  | some l => l
  | none => hitsKPF ix G offs pgs R c

theorem hitsKPFN_near {L Pp : Type} [LookG L Pp] [Inhabited Pp] (sl lo hi : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (pgs : Array PGen) (R : ByteArray) (c : Nat) (ys : List (Placement × Int)) :
    NearOk sl lo hi ys (hitsKPF ix G offs pgs R c) (hitsKPFN sl hi ix G offs pgs R c ys) := by
  unfold hitsKPFN hitsKPF
  cases hl : hitsAtKP c ix G offs pgs R with
  | none =>
    have hn : hitsAtKPN c ix G offs pgs R (keepN sl hi pgs.size (gapBound sc0 (-(c : Int))) ys) = none := by
      unfold hitsAtKP at hl; unfold hitsAtKPN
      split at hl
      · cases hl
      · next hf => rw [if_neg hf]
    simp only [hn]
    exact ⟨fun x hx => hx, fun x hx _ => hx⟩
  | some l =>
    have hs : ∃ l', hitsAtKPN c ix G offs pgs R (keepN sl hi pgs.size (gapBound sc0 (-(c : Int))) ys) = some l' := by
      unfold hitsAtKP at hl; unfold hitsAtKPN
      split at hl
      · next hf => rw [if_pos hf]; exact ⟨_, rfl⟩
      · cases hl
    obtain ⟨l', hl'⟩ := hs
    simp only [hl']
    refine ⟨fun x hx => (hitsAtKPN_mem c ix G offs pgs R _ l l' hl hl' x).1 hx, fun x hx hp => ?_⟩
    apply (hitsAtKPN_mem c ix G offs pgs R _ l l' hl hl' x).2 hx
    intro vc nR D sh hsh hd hxe
    obtain ⟨y, hy, hpy⟩ := hp
    have hb := shapesAt_fst c sh hsh
    have hxs : x.1.1.start = (dst nR D sh).toNat := by rw [hxe]; unfold decB; split <;> rfl
    have hxc : x.1.1.chr = (if vc < pgs.size then vc else vc - pgs.size) := by
      rw [hxe]; unfold decB; split <;> simp [*]
    have hdd : dst nR D sh = (D : Int) - nR - sh.1 := rfl
    unfold keepN
    rw [List.any_eq_true]
    refine ⟨y, hy, ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    rcases hpy with h | h
    · obtain ⟨e1, e2, e3, e4, e5⟩ := properPairU_near sl lo hi y.1 x.1 h
      refine ⟨⟨e1.trans hxc, ?_⟩, ?_⟩ <;> omega
    · obtain ⟨e1, e2, e3, e4, e5⟩ := properPairU_near sl lo hi x.1 y.1 h
      refine ⟨⟨e1.symm.trans hxc, ?_⟩, ?_⟩ <;> omega

/-! ## Mode HN: mode H with the second mate searched near the first -/

/-! ### Compiled `hitsKPFN`: chromosomes without a hit of the other mate are skipped (`hitsKPFN_eqG`) -/

/-- `hitsSKN`, a chromosome searched only when `gate` holds on it. -/
def hitsSKNG {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G : ByteArray) (offs : Array Nat)
    (pgs2 : Array PGen) (n t lim : Nat) (Rs : ByteArray) (keep : Nat → Nat → Nat → Bool) (gate : Nat → Bool) :
    List (Window × Nat) :=
  if !(List.range n).any gate then [] else
  let m := Rs.size / 25
  let Ls := Rs.size / m
  let K := packRP Rs
  let ps := prepG ix Rs m Ls
  let J := (ordG (ps.map (LookG.size ix)) m).take (sbound lim + 1)
  let lk := J.map fun j => (j, LookG.look ix G Rs (j * Ls) (Rs.size - j * Ls) ps[j]!)
  let us := unseen m J
  (List.range n).flatMap fun c =>
    if gate c then
      hitsCKN K Rs pgs2 (t + c) lim (slicesAt lk Rs.size Ls offs[c]! (GRead.size pgs2[t + c]!)) us Ls
        (keep (t + c) Rs.size)
    else []

theorem hitsCKN_none (K : RP) (R : ByteArray) (pgs2 : Array PGen) (c lim : Nat) (acc : List (Array Nat))
    (us : List Nat) (Ls : Nat) (sel : Nat → Bool) (h : ∀ D, sel D = false) :
    hitsCKN K R pgs2 c lim acc us Ls sel = [] := by
  unfold hitsCKN
  simp [h]

theorem hitsSKNG_eq {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G : ByteArray) (offs : Array Nat)
    (pgs2 : Array PGen) (n t lim : Nat) (Rs : ByteArray) (keep : Nat → Nat → Nat → Bool) (gate : Nat → Bool)
    (h : ∀ c D, c < n → gate c = false → keep (t + c) Rs.size D = false) :
    hitsSKNG ix G offs pgs2 n t lim Rs keep gate = hitsSKN ix G offs pgs2 n t lim Rs keep := by
  unfold hitsSKNG hitsSKN
  split
  · rename_i hn
    simp only [Bool.not_eq_true', List.any_eq_false, List.mem_range] at hn
    simp only []
    symm
    rw [List.flatMap_eq_nil_iff]
    intro c hc
    rw [List.mem_range] at hc
    exact hitsCKN_none _ _ _ _ _ _ _ _ _ (fun D => h c D hc (by simpa using hn c hc))
  simp only []
  rw [List.flatMap_def, List.flatMap_def]
  congr 1
  apply List.map_congr_left
  intro c hc
  rw [List.mem_range] at hc
  cases hg : gate c
  · rw [hitsCKN_none _ _ _ _ _ _ _ _ _ (fun D => h c D hc hg)]; rfl
  · rfl

def hitsAtKPNG {L Pp : Type} [LookG L Pp] [Inhabited Pp] (lim : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (pgs : Array PGen) (R : ByteArray) (keep : Nat → Nat → Nat → Bool) (gate : Nat → Bool) :
    Option (List (Placement × Int)) :=
  if fastT lim R then
    let n := pgs.size
    let pgs2 := pgs ++ pgs
    some ((hitsSKNG ix G offs pgs2 n 0 lim R keep gate ++
      hitsSKNG ix G offs pgs2 n n lim (revCompK R) keep gate).map fun x => (decB n x.1, -(x.2 : Int)))
  else none

/-- Compiled `hitsKPFN`: a chromosome is searched only when the other mate has a hit on it. -/
def hitsKPFNG {L Pp : Type} [LookG L Pp] [Inhabited Pp] (sl hi : Nat) (ix : L) (G : ByteArray) (offs : Array Nat)
    (pgs : Array PGen) (R : ByteArray) (c : Nat) (ys : List (Placement × Int)) : List (Placement × Int) :=
  match hitsAtKPNG c ix G offs pgs R (keepN sl hi pgs.size (gapBound sc0 (-(c : Int))) ys)
      (fun k => ys.any fun y => y.1.1.chr == k) with
  | some l => l
  | none => hitsKPF ix G offs pgs R c

theorem keepN_gate (sl hi n gb : Nat) (ys : List (Placement × Int)) (t c nR D : Nat) (ht : t = 0 ∨ t = n)
    (hc : c < n) (hg : (ys.any fun y => y.1.1.chr == c) = false) : keepN sl hi n gb ys (t + c) nR D = false := by
  have hv : (if t + c < n then t + c else t + c - n) = c := by
    rcases ht with h0 | hn
    · rw [h0, if_pos (by omega)]; omega
    · rw [hn, if_neg (by omega)]; omega
  unfold keepN
  rw [hv]
  rw [List.any_eq_false] at hg ⊢
  intro y hy h'
  simp only [Bool.and_eq_true] at h'
  exact hg y hy h'.1.1

@[csimp] theorem hitsKPFN_eqG : @hitsKPFN = @hitsKPFNG := by
  funext L Pp i1 i2 sl hi ix G offs pgs R c ys
  have e0 := hitsSKNG_eq ix G offs (pgs ++ pgs) pgs.size 0 c R (keepN sl hi pgs.size (gapBound sc0 (-(c : Int))) ys)
    (fun k => ys.any fun y => y.1.1.chr == k)
    (fun c' D hc hg => keepN_gate sl hi _ _ ys 0 c' _ D (Or.inl rfl) hc hg)
  have e1 := hitsSKNG_eq ix G offs (pgs ++ pgs) pgs.size pgs.size c (revCompK R)
    (keepN sl hi pgs.size (gapBound sc0 (-(c : Int))) ys) (fun k => ys.any fun y => y.1.1.chr == k)
    (fun c' D hc hg => keepN_gate sl hi _ _ ys _ c' _ D (Or.inr rfl) hc hg)
  unfold hitsKPFN hitsKPFNG hitsAtKPNG hitsAtKPN
  simp only [e0, e1]

section topN
variable (dc : Nat → Nat) (sl lo hi : Nat) (caps : List Nat) (a1 : Bool) (g : Genome)
  (m1 m2 : List Char) (ix : Mz.MzIdx) (G : PGen) (offs ns : Array Nat) (R1 R2 : ByteArray)
  (hcut : cutOk G offs ns = true) (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) g)
  (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hchk : Mz.check2P ix G = true)

end topN

end MapSpec.Fast

#print axioms MapSpec.Fast.hitsKPFN_near
#print axioms MapSpec.Fast.hitsKPFN_eqG
