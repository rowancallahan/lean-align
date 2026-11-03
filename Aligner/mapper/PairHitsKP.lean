import PairHits
import WgPacked
import FastGenSupp

/-!
# `hitsAtKP`: every hit of a read within a cap, packed genome, word filter, word kernels

`hitsAtB` (codecs/PairHits.lean) with the chromosomes held 2-bit (`PGen`), the word
filter `kfiltV` before the kernels and the word kernels `kerHKG`:

    hitsAtKP lim ix G offs pgs R = hitsAtB lim ix G offs (pgs.map Mz.unpack) R   (hitsAtKP_eq)

and, over the packed whole-genome index (`PkMz`),

    hitsAtKP … = some l → (x ∈ l ↔ x ∈ hitsBoth sc0 (−lim) g read)            (mem_hitsAtKP_mz)
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-- `hitsC` on packed chromosomes: the word filter, then the word kernels. -/
def hitsCK (K : RP) (R : ByteArray) (pgs2 : Array PGen) (c lim : Nat) (acc : List (Array Nat))
    (us : List Nat) (Ls : Nat) : List (Window × Nat) :=
  (diags acc).flatMap fun D =>
    if kfiltV K R pgs2[c]! acc us Ls lim (initP lim) D then
      (shapesAt lim).filterMap fun sh =>
        if 0 ≤ dst R.size D sh ∧ 0 ≤ wlen R.size sh then
          let k := kerHKG R K pgs2 pgs2 c (dst R.size D sh).toNat (wlen R.size sh).toNat lim
          if k ≤ lim then some (⟨c, (dst R.size D sh).toNat, (wlen R.size sh).toNat⟩, k) else none
        else none
    else []

theorem diags_empty (acc : List (Array Nat)) (h : (acc.all fun a => a.isEmpty) = true) : diags acc = [] := by
  unfold diags
  have : (acc.flatMap fun arr => arr.toList.map (· / 16)) = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro a ha
    rw [List.all_eq_true] at h
    have := h a ha
    simp only [Array.isEmpty_iff] at this
    simp [this]
  rw [this, List.mergeSort_nil, dedupAdj]

/-- A `flatMap` over `ds` reading a per-position value from `cnt` equals the one computing it (`s`). -/
theorem zipIdx_flatMap {β : Type} (G : Nat → Nat → List β) (s : Nat → Nat) (cnt : Array Nat) :
    ∀ (ds : List Nat) n, (∀ t, t < ds.length → cnt.getD (n + t) 0 = s (ds.getD t 0)) →
      (ds.zipIdx n).flatMap (fun p => G p.1 (cnt.getD p.2 0)) = ds.flatMap (fun D => G D (s D)) := by
  intro ds
  induction ds with
  | nil => intro n _; rfl
  | cons D ds ih =>
    intro n h
    rw [List.zipIdx_cons, List.flatMap_cons, List.flatMap_cons]
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.getD_cons_zero] at h0
    rw [h0, ih (n + 1) (fun t ht => by
      have := h (t + 1) (by simp; omega)
      rw [show n + (t + 1) = n + 1 + t by omega, List.getD_cons_succ] at this
      exact this)]

/-- `hitsCK` with the shapes taken once from the table, nothing done when every slice is empty, the
supports of all diagonals by one sweep (`suppCntC`) and the packed genome looked up once (`hitsCK_eqT`). -/
def hitsCKT (K : RP) (R : ByteArray) (pgs2 : Array PGen) (c lim : Nat) (acc : List (Array Nat))
    (us : List Nat) (Ls : Nat) : List (Window × Nat) :=
  if acc.all fun a => a.isEmpty then [] else
  let shs := shapesT lim
  let ds := diags acc
  let cnt := suppCntC acc (2 * gapBound sc0 (-((min lim (initP lim).pen : Nat) : Int))) ds
  let pk := pkU pgs2[c]! Ls R.size us
  ds.zipIdx.flatMap fun p =>
    let D := p.1
    if kfiltVF pk K R pgs2[c]! acc us Ls lim (initP lim) D (cnt.getD p.2 0) then
      shs.filterMap fun sh =>
        if 0 ≤ dst R.size D sh ∧ 0 ≤ wlen R.size sh then
          let k := kerHKG R K pgs2 pgs2 c (dst R.size D sh).toNat (wlen R.size sh).toNat lim
          if k ≤ lim then some (⟨c, (dst R.size D sh).toNat, (wlen R.size sh).toNat⟩, k) else none
        else none
    else []

/-- Compiled code runs `hitsCKT`. -/
@[csimp] theorem hitsCK_eqT : @hitsCK = @hitsCKT := by
  funext K R pgs2 c lim acc us Ls
  unfold hitsCK hitsCKT
  split
  · rename_i h; rw [diags_empty acc h]; rfl
  · simp only [shapesT_eq]
    exact (zipIdx_flatMap (β := Window × Nat) (fun D x => if kfiltVF (pkU pgs2[c]! Ls R.size us) K R pgs2[c]! acc us Ls lim (initP lim) D x then
        (shapesAt lim).filterMap fun sh =>
          if 0 ≤ dst R.size D sh ∧ 0 ≤ wlen R.size sh then
            let k := kerHKG R K pgs2 pgs2 c (dst R.size D sh).toNat (wlen R.size sh).toNat lim
            if k ≤ lim then some ((⟨c, (dst R.size D sh).toNat, (wlen R.size sh).toNat⟩ : Window), k) else none
          else none
        else [])
      (fun D => suppA acc D (2 * gapBound sc0 (-((min lim (initP lim).pen : Nat) : Int))))
      _ (diags acc) 0 (fun t ht => by rw [Nat.zero_add]; exact suppCntC_get acc _ _ t ht)).symm

/-- `hitsS` on packed chromosomes (the read packed once per strand). -/
def hitsSK {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G : ByteArray) (offs : Array Nat)
    (pgs2 : Array PGen) (n t lim : Nat) (Rs : ByteArray) : List (Window × Nat) :=
  let m := Rs.size / 25
  let Ls := Rs.size / m
  let K := packRP Rs
  let ps := prepG ix Rs m Ls
  let J := (ordG (ps.map (LookG.size ix)) m).take (sbound lim + 1)
  let lk := J.map fun j => (j, LookG.look ix G Rs (j * Ls) (Rs.size - j * Ls) ps[j]!)
  let us := unseen m J
  (List.range n).flatMap fun c =>
    hitsCK K Rs pgs2 (t + c) lim (slicesAt lk Rs.size Ls offs[c]! (GRead.size pgs2[t + c]!)) us Ls

/-! ## `hitsSK` visiting only the chromosomes that hold an anchor (`hitsSK_eqV`)

When every looked-up anchor array is strictly increasing and the chromosome table is laid out in order
(`layoutOk`), an anchor can only fall in the slice of the chromosome found by one binary search over `offs`
(`chromOfA`). Chromosomes that no anchor marks have only empty slices, so `hitsCK` gives `[]` there; they are
skipped instead of sliced. Otherwise the original loop runs. -/

-- strictly increasing, checked
def incB (a : Array Nat) : Bool := (List.range (a.size - 1)).all fun i => a[i]! < a[i + 1]!

theorem incA_of_incB {a : Array Nat} (h : incB a = true) : IncA a := by
  unfold incB at h
  rw [List.all_eq_true] at h
  have step : ∀ i, i + 1 < a.size → a[i]! < a[i + 1]! := fun i hi => by
    have := h i (List.mem_range.mpr (by omega)); simpa using this
  have key : ∀ d i, i + d + 1 < a.size → a[i]! < a[i + d + 1]! := by
    intro d
    induction d with
    | zero => intro i hi; exact step i hi
    | succ d ih =>
      intro i hi
      have h1 := ih i (by omega)
      have h2 := step (i + d + 1) (by omega)
      rw [show i + (d + 1) + 1 = i + d + 1 + 1 by omega]; omega
  intro i k hik hk
  have := key (k - i - 1) i (by omega)
  rwa [show i + (k - i - 1) + 1 = k by omega] at this

-- the chromosome table is in order, without overlaps beyond a seed
def layoutOk (offs : Array Nat) (pgs2 : Array PGen) (n t : Nat) : Bool :=
  offs.size == n && incB offs &&
    (List.range (n - 1)).all fun c => decide (offs[c]! + GRead.size pgs2[t + c]! + 1 ≤ offs[c + 1]! + q)

-- the only chromosome whose slice (base `b`) can hold anchor `e`
@[inline] def chromOfA (offs : Array Nat) (b e : Nat) : Nat := lbA offs (e / 16 - b + 1) 0 offs.size - 1

def markA (offs : Array Nat) (b : Nat) (v : Array Bool) (a : Array Nat) : Array Bool :=
  a.foldl (fun v e => if b ≤ e / 16 then v.set! (chromOfA offs b e) true else v) v

def visOf (offs : Array Nat) (n Ls N : Nat) (lk : List (Nat × Array Nat)) : Array Bool :=
  lk.foldl (fun v x => markA offs (N - x.1 * Ls) v x.2) (Array.replicate n false)

theorem set!_get_self (v : Array Bool) (i : Nat) (h : i < v.size) : (v.set! i true)[i]! = true := by
  rw [getElem!_pos _ i (by simpa using h)]
  simp [Array.set!]

theorem set!_get_keep (v : Array Bool) (i j : Nat) (h : v[j]! = true) : (v.set! i true)[j]! = true := by
  by_cases hj : j < v.size
  · by_cases e : i = j
    · subst e; exact set!_get_self v i hj
    · rw [getElem!_pos _ j (by simpa using hj)]
      rw [getElem!_pos _ j hj] at h
      simp only [Array.set!]
      rw [Array.getElem_setIfInBounds_ne (by simpa using hj) e]
      exact h
  · rw [getElem!_neg _ j (by simpa using hj)] at h; cases h

-- the marking pass on a list of anchors
def markL (offs : Array Nat) (b : Nat) (v : Array Bool) (l : List Nat) : Array Bool :=
  l.foldl (fun v e => if b ≤ e / 16 then v.set! (chromOfA offs b e) true else v) v

theorem markA_eqL (offs : Array Nat) (b : Nat) (v : Array Bool) (a : Array Nat) :
    markA offs b v a = markL offs b v a.toList := by
  unfold markA markL; rw [Array.foldl_toList]

theorem markL_size (offs : Array Nat) (b : Nat) : ∀ (v : Array Bool) (l : List Nat),
    (markL offs b v l).size = v.size
  | _, [] => rfl
  | v, e :: l => by
    unfold markL; simp only [List.foldl_cons]
    rw [← markL, markL_size]; split <;> simp

theorem markA_size (offs : Array Nat) (b : Nat) (v : Array Bool) (a : Array Nat) :
    (markA offs b v a).size = v.size := by rw [markA_eqL, markL_size]

theorem markL_keep (offs : Array Nat) (b : Nat) : ∀ (l : List Nat) (v : Array Bool) (j : Nat), v[j]! = true →
    (markL offs b v l)[j]! = true
  | [], _, _, h => h
  | e :: l, v, j, h => by
    unfold markL; simp only [List.foldl_cons]; rw [← markL]
    apply markL_keep offs b l
    split
    · exact set!_get_keep v _ j h
    · exact h

theorem markA_keep (offs : Array Nat) (b : Nat) (a : Array Nat) (v : Array Bool) (j : Nat) (h : v[j]! = true) :
    (markA offs b v a)[j]! = true := by rw [markA_eqL]; exact markL_keep offs b _ v j h

theorem markL_mark (offs : Array Nat) (b e : Nat) (hb : b ≤ e / 16) : ∀ (l : List Nat), e ∈ l →
    ∀ (v : Array Bool), chromOfA offs b e < v.size → (markL offs b v l)[chromOfA offs b e]! = true
  | [], he, _, _ => by cases he
  | x :: l, he, v, hv => by
    unfold markL; simp only [List.foldl_cons]; rw [← markL]
    rcases List.mem_cons.mp he with rfl | hl
    · exact markL_keep offs b l _ _ (by simp only [hb, ↓reduceIte]; exact set!_get_self v _ hv)
    · apply markL_mark offs b e hb l hl
      split <;> simp [hv]

theorem markA_mark (offs : Array Nat) (b : Nat) (a : Array Nat) (e : Nat) (he : e ∈ a.toList) (hb : b ≤ e / 16)
    (v : Array Bool) (hv : chromOfA offs b e < v.size) : (markA offs b v a)[chromOfA offs b e]! = true := by
  rw [markA_eqL]; exact markL_mark offs b e hb _ he v hv

theorem visOf_mark (offs : Array Nat) (n Ls N : Nat) (lk : List (Nat × Array Nat)) (x : Nat × Array Nat)
    (hx : x ∈ lk) (e : Nat) (he : e ∈ x.2.toList) (hb : N - x.1 * Ls ≤ e / 16)
    (hc : chromOfA offs (N - x.1 * Ls) e < n) : (visOf offs n Ls N lk)[chromOfA offs (N - x.1 * Ls) e]! = true := by
  unfold visOf
  suffices ∀ (v : Array Bool), v.size = n →
      (lk.foldl (fun v x => markA offs (N - x.1 * Ls) v x.2) v)[chromOfA offs (N - x.1 * Ls) e]! = true by
    exact this _ (by simp)
  have keep : ∀ (l : List (Nat × Array Nat)) (v : Array Bool) (j : Nat), v[j]! = true →
      (l.foldl (fun v x => markA offs (N - x.1 * Ls) v x.2) v)[j]! = true := by
    intro l
    induction l with
    | nil => intro v j h; exact h
    | cons y l ih => intro v j h; simp only [List.foldl_cons]; exact ih _ j (markA_keep _ _ _ v j h)
  have szs : ∀ (l : List (Nat × Array Nat)) (v : Array Bool),
      (l.foldl (fun v x => markA offs (N - x.1 * Ls) v x.2) v).size = v.size := by
    intro l
    induction l with
    | nil => intro v; rfl
    | cons y l ih => intro v; simp only [List.foldl_cons]; rw [ih, markA_size]
  induction lk with
  | nil => cases hx
  | cons y l ih =>
    intro v hv
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hl
    · exact keep l _ _ (markA_mark offs _ x.2 e he hb v (by omega))
    · exact ih hl _ (by rw [markA_size]; exact hv)

/-- The binary search finds the chromosome whose slice holds the anchor. -/
theorem chromOfA_eq {offs : Array Nat} {pgs2 : Array PGen} {n t : Nat} (hl : layoutOk offs pgs2 n t = true)
    (c b e : Nat) (hc : c < n) (h1 : 16 * (offs[c]! + b) ≤ e)
    (h2 : e < 16 * (offs[c]! + GRead.size pgs2[t + c]! + 1 + b - q)) :
    chromOfA offs b e = c ∧ b ≤ e / 16 := by
  unfold layoutOk at hl
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hl
  obtain ⟨⟨hsz, hinc⟩, hgap⟩ := hl
  have ha := incA_of_incB hinc
  have hx : offs[c]! + b ≤ e / 16 := by omega
  have L := lbA_spec offs (e / 16 - b + 1) ha 0 offs.size (Nat.le_refl _) (Nat.zero_le _) (fun k hk => by omega)
    (fun k _ hk => by omega)
  obtain ⟨Lb, Lh, -, Lle⟩ := L
  -- every chromosome up to `c` starts at or before `e / 16 - b`
  have hge : c + 1 ≤ lbA offs (e / 16 - b + 1) 0 offs.size := by
    rcases Nat.lt_or_ge (lbA offs (e / 16 - b + 1) 0 offs.size) (c + 1) with hlt | hge
    · have := Lh c (by omega) (by omega)
      omega
    · exact hge
  have hle : lbA offs (e / 16 - b + 1) 0 offs.size ≤ c + 1 := by
    by_cases hn : c + 1 < n
    · have hg := hgap c (by omega)
      rcases Nat.lt_or_ge (c + 1) (lbA offs (e / 16 - b + 1) 0 offs.size) with hlt | hle
      · have := Lb (c + 1) hlt
        omega
      · exact hle
    · omega
  unfold chromOfA
  omega

/-- An unmarked chromosome has only empty slices. -/
theorem slices_empty {offs : Array Nat} {pgs2 : Array PGen} {n t Ls N : Nat} {lk : List (Nat × Array Nat)}
    (hl : layoutOk offs pgs2 n t = true) (hinc : (lk.all fun x => incB x.2) = true) (c : Nat) (hc : c < n)
    (hv : (visOf offs n Ls N lk)[c]! = false) :
    ((slicesAt lk N Ls offs[c]! (GRead.size pgs2[t + c]!)).all fun a => a.isEmpty) = true := by
  unfold slicesAt
  rw [List.all_eq_true]
  intro a ha
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
  have hia := incA_of_incB (List.all_eq_true.mp hinc x hx)
  rw [sliceG_eqE]
  unfold sliceGE
  simp only []
  split
  · rfl
  · rename_i hne
    exfalso
    -- the first entry of the slice is an anchor in the chromosome's range
    generalize hi : lbA x.2 (16 * (offs[c]! + (N - x.1 * Ls))) 0 x.2.size = i at hne
    generalize hj : lbA x.2 (16 * (offs[c]! + GRead.size pgs2[t + c]! + 1 + (N - x.1 * Ls) - q)) 0 x.2.size = j at hne
    have hjs : j ≤ x.2.size := by
      rw [← hj]
      exact (lbA_spec x.2 _ hia 0 x.2.size (Nat.le_refl _) (Nat.zero_le _) (fun k hk => by omega)
        (fun k _ hk => by omega)).2.2.2
    have hmem := (mem_lb_extract x.2 hia (16 * (offs[c]! + (N - x.1 * Ls)))
      (16 * (offs[c]! + GRead.size pgs2[t + c]! + 1 + (N - x.1 * Ls) - q)) x.2[i]!).mp (by
        rw [hi, hj]
        simp only [Array.mem_toList_iff, Array.mem_iff_getElem, Array.size_extract, Array.getElem_extract]
        exact ⟨0, by omega, by rw [getElem!_pos x.2 i (by omega)]; simp⟩)
    obtain ⟨he, h1, h2⟩ := hmem
    obtain ⟨hco, hb⟩ := chromOfA_eq hl c _ _ hc h1 (by omega)
    have := visOf_mark offs n Ls N lk x hx _ he hb (by rw [hco]; exact hc)
    rw [hco, hv] at this
    cases this

theorem flatMap_congr' {α β : Type} {f g : α → List β} : ∀ (l : List α), (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.flatMap_cons]
    rw [h x List.mem_cons_self, flatMap_congr' l fun y hy => h y (List.mem_cons_of_mem _ hy)]

def hitsSKV {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G : ByteArray) (offs : Array Nat)
    (pgs2 : Array PGen) (n t lim : Nat) (Rs : ByteArray) : List (Window × Nat) :=
  let m := Rs.size / 25
  let Ls := Rs.size / m
  let K := packRP Rs
  let ps := prepG ix Rs m Ls
  let J := (ordG (ps.map (LookG.size ix)) m).take (sbound lim + 1)
  let lk := J.map fun j => (j, LookG.look ix G Rs (j * Ls) (Rs.size - j * Ls) ps[j]!)
  let us := unseen m J
  if layoutOk offs pgs2 n t && lk.all (fun x => incB x.2) then
    let vis := visOf offs n Ls Rs.size lk
    (List.range n).flatMap fun c =>
      if vis[c]! then hitsCK K Rs pgs2 (t + c) lim (slicesAt lk Rs.size Ls offs[c]! (GRead.size pgs2[t + c]!)) us Ls
      else []
  else
    (List.range n).flatMap fun c =>
      hitsCK K Rs pgs2 (t + c) lim (slicesAt lk Rs.size Ls offs[c]! (GRead.size pgs2[t + c]!)) us Ls

/-- Compiled code runs `hitsSKV`. -/
@[csimp] theorem hitsSK_eqV : @hitsSK = @hitsSKV := by
  funext L Pp _ _ ix G offs pgs2 n t lim Rs
  unfold hitsSK hitsSKV
  simp only []
  split
  · rename_i hok
    simp only [Bool.and_eq_true] at hok
    apply flatMap_congr'
    intro c hc
    rw [List.mem_range] at hc
    split
    · rfl
    · rename_i hv
      rw [hitsCK_eqT]
      unfold hitsCKT
      rw [if_pos (slices_empty hok.1 hok.2 c hc (by simpa using hv))]
  · rfl

/-- Every placement of a read within penalty `lim ≤ 16`, packed genome. -/
def hitsAtKP {L Pp : Type} [LookG L Pp] [Inhabited Pp] (lim : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (pgs : Array PGen) (R : ByteArray) : Option (List (Placement × Int)) :=
  if fastT lim R then
    let n := pgs.size
    let pgs2 := pgs ++ pgs
    some ((hitsSK ix G offs pgs2 n 0 lim R ++ hitsSK ix G offs pgs2 n n lim (revCompK R)).map
      fun x => (decB n x.1, -(x.2 : Int)))
  else none

theorem hitsCK_eq (pgs : Array PGen) (R : ByteArray) (c lim : Nat) (acc : List (Array Nat)) (us : List Nat)
    (Ls : Nat) :
    hitsCK (packRP R) R (pgs ++ pgs) c lim acc us Ls =
      hitsC R (pgs.map Mz.unpack ++ pgs.map Mz.unpack) c lim acc us Ls := by
  have hs := sameA_append (sameA_unpack pgs) sameG_default
  have hk : ∀ st len, kerHKG R (packRP R) (pgs ++ pgs) (pgs ++ pgs) c st len lim =
      kerH R (pgs.map Mz.unpack ++ pgs.map Mz.unpack) c st len lim := by
    intro st len
    rw [kerHKG_same hs, kerHKG_bytes, kerHK_eq R _ _ (repAllK_unpack pgs)]
  have hf : ∀ D, kfiltV (packRP R) R (pgs ++ pgs)[c]! acc us Ls lim (initP lim) D =
      kfilt R (pgs.map Mz.unpack ++ pgs.map Mz.unpack)[c]! acc us Ls lim (initP lim) D := by
    intro D; rw [kfiltV_eq, kfilt_same (hs.2 c)]
  unfold hitsCK hitsC
  simp only [hk, hf]

theorem hitsSK_eq {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G : ByteArray) (offs : Array Nat)
    (pgs : Array PGen) (n t lim : Nat) (Rs : ByteArray) :
    hitsSK ix G offs (pgs ++ pgs) n t lim Rs = hitsS ix G offs (pgs.map Mz.unpack ++ pgs.map Mz.unpack) n t lim Rs := by
  have hs := sameA_append (sameA_unpack pgs) sameG_default
  have hz : ∀ c, GRead.size (pgs ++ pgs)[c]! = ByteArray.size ((pgs.map Mz.unpack ++ pgs.map Mz.unpack)[c]!) :=
    fun c => (hs.2 c).1
  unfold hitsSK hitsS
  simp only [hitsCK_eq, hz]

theorem hitsAtKP_eq {L Pp : Type} [LookG L Pp] [Inhabited Pp] (lim : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (pgs : Array PGen) (R : ByteArray) :
    hitsAtKP lim ix G offs pgs R = hitsAtB lim ix G offs (pgs.map Mz.unpack) R := by
  unfold hitsAtKP hitsAtB
  simp only [hitsSK_eq, revCompK_eq, revCompB2_eq, Array.size_map]

theorem hitsAtB_congrG {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G G' : ByteArray)
    (hG : ∀ R s base p, LookG.look ix G R s base p = LookG.look ix G' R s base p) (lim : Nat)
    (offs : Array Nat) (gbs : Array ByteArray) (R : ByteArray) :
    hitsAtB lim ix G offs gbs R = hitsAtB lim ix G' offs gbs R := by
  simp only [hitsAtB, hitsS, hG]

/-- **Every hit, packed whole genome.** -/
theorem mem_hitsAtKP_mz (lim : Nat) (hl16 : lim ≤ 16) (g : Genome) (read : List Char) (ix : Mz.MzIdx)
    (G : PGen) (offs ns : Array Nat) (R : ByteArray) (hcut : cutOk G offs ns = true)
    (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) g) (hr : Encodes R read)
    (hchk : Mz.check2P ix G = true) (l : List (Placement × Int))
    (hl : hitsAtKP lim ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) R = some l)
    (x : Placement × Int) : x ∈ l ↔ x ∈ hitsBoth sc0 (-(lim : Int)) g read := by
  rw [hitsAtKP_eq, hitsAtB_congrG ((ix, G) : PkMz) ByteArray.empty (Mz.unpack G) (fun _ _ _ _ => rfl)] at hl
  exact mem_hitsAtB lim hl16 read g _ R hg hr _ _ offs (catOk_cut G offs ns hcut) (lookOk_pk ix G hchk) l hl x

end MapSpec.Fast

#print axioms MapSpec.Fast.hitsSK_eqV
#print axioms MapSpec.Fast.hitsAtKP_eq
#print axioms MapSpec.Fast.mem_hitsAtKP_mz
