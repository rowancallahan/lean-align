import FastGenPair

/-!
# Short reads on the general path

Reads too short for the 25-mer index (`fastT` false: fewer than
`sbound P + 1` seeds of 25 letters) are cut into `m = sbound P + 1` seeds of
`Ls = n / m` letters; each seed's exact places are found by scanning the
chromosome bytes (`scanL`, complete and sorted: `scanL_ok`).  Every anchor's
same-length window goes through the kernel, then stages K and B (`chromKB`) run
on the anchors (`chromKB_coverL`).  Both strands share one `Best` as in
`mapChromsGB`.
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-! ## Scanning a chromosome for a seed -/

@[specialize] def scanAux {Gt : Type} [GRead Gt] (G : Gt) (R : ByteArray) (s l base stop : Nat) (p : Nat) (acc : Array Nat) : Array Nat :=
  if p < stop then scanAux G R s l base stop (p + 1) (if eqRun G R p s l then acc.push ((p + base) * 16) else acc)
  else acc
termination_by stop - p

/-- Anchors `(p + base)·16` of every place `p` of `G` where `R[s, s+l)` occurs. -/
def scanL {Gt : Type} [GRead Gt] (G : Gt) (R : ByteArray) (s l base : Nat) : Array Nat := scanAux G R s l base (GRead.size G + 1 - l) 0 #[]

theorem scanAux_spec (G R : ByteArray) (s l base stop : Nat) :
    ∀ d p (acc : Array Nat), stop - p = d → (∀ e ∈ acc.toList, e < (p + base) * 16) → acc.toList.Pairwise (· < ·) →
      (scanAux G R s l base stop p acc).toList.Pairwise (· < ·) ∧
      ∀ p', p ≤ p' → p' < stop → eqRun G R p' s l = true → (p' + base) * 16 ∈ (scanAux G R s l base stop p acc).toList := by
  intro d
  induction d with
  | zero =>
    intro p acc hd _ hpw
    unfold scanAux; rw [if_neg (by omega)]
    exact ⟨hpw, fun p' h1 h2 => by omega⟩
  | succ d ih =>
    intro p acc hd hlt hpw
    unfold scanAux; rw [if_pos (by omega)]
    by_cases hm : eqRun G R p s l = true
    · rw [if_pos hm]
      have hlt' : ∀ e ∈ (acc.push ((p + base) * 16)).toList, e < (p + 1 + base) * 16 := by
        intro e he
        rw [Array.toList_push, List.mem_append] at he
        rcases he with he | he
        · have := hlt e he; omega
        · simp at he; omega
      have hpw' : (acc.push ((p + base) * 16)).toList.Pairwise (· < ·) := by
        rw [Array.toList_push, List.pairwise_append]
        exact ⟨hpw, by simp, fun a ha b hb => by simp at hb; subst hb; exact hlt a ha⟩
      obtain ⟨r1, r2⟩ := ih (p + 1) _ (by omega) hlt' hpw'
      refine ⟨r1, fun p' h1 h2 h3 => ?_⟩
      by_cases e : p' = p
      · subst e
        -- the pushed anchor stays: it is below every later push
        have keep : ∀ d' q (acc' : Array Nat), stop - q = d' → (p' + base) * 16 ∈ acc'.toList →
            (p' + base) * 16 ∈ (scanAux G R s l base stop q acc').toList := by
          intro d'
          induction d' with
          | zero => intro q acc' hq ha; unfold scanAux; rw [if_neg (by omega)]; exact ha
          | succ d' ih' =>
            intro q acc' hq ha
            unfold scanAux; rw [if_pos (by omega)]
            apply ih' _ _ (by omega)
            split
            · rw [Array.toList_push]; exact List.mem_append_left _ ha
            · exact ha
        exact keep _ (p' + 1) _ rfl (by rw [Array.toList_push]; simp)
      · exact r2 p' (by omega) h2 h3
    · rw [if_neg hm]
      obtain ⟨r1, r2⟩ := ih (p + 1) acc (by omega) (fun e he => by have := hlt e he; omega) hpw
      refine ⟨r1, fun p' h1 h2 h3 => ?_⟩
      by_cases e : p' = p
      · subst e; exact absurd h3 hm
      · exact r2 p' (by omega) h2 h3

/-- **The scan is a complete sorted lookup.** -/
theorem scanL_ok (G R : ByteArray) (s l base : Nat) :
    (scanL G R s l base).toList.Pairwise (· < ·) ∧
      ∀ p, MatchAtL G p R s l → (p + base) * 16 + 0 ∈ (scanL G R s l base).toList := by
  obtain ⟨h1, h2⟩ := scanAux_spec G R s l base (G.size + 1 - l) _ 0 #[] rfl (by simp) (by simp)
  refine ⟨h1, fun p hp => ?_⟩
  rw [Nat.add_zero]
  exact h2 p (Nat.zero_le _) (by have := hp.1; omega) ((eqRun_spec G R l p s).2 hp.2)

/-! ## Driver -/

/-- Chromosome `c` of a strand (read `R`, tag `t + c`): `m` seeds of `Ls` letters. -/
@[specialize] def shortChrom {Gt : Type} [GRead Gt] [Inhabited Gt] (R : ByteArray) (gbs2 : Array Gt) (t c P m Ls : Nat) (b : Best) : Best :=
  let arrs := (List.range m).map fun j => scanL gbs2[t + c]! R (j * Ls) Ls (R.size - j * Ls)
  let b1 := arrs.foldl (fun b a =>
    a.foldl (fun b e => addK R gbs2 (t + c) (min P 16) ((e / 16 : Nat) - (R.size : Int)) R.size b) b) b
  chromKB R gbs2 (t + c) P arrs.reverse b1

/-- Both strands of a short read. -/
@[specialize] def mapChromsShort {Gt : Type} [GRead Gt] [Inhabited Gt] (P : Nat) (gbs : Array Gt) (R : ByteArray) : Best :=
  let n := gbs.size
  let gbs2 := gbs ++ gbs
  let m := sbound P + 1
  let Ls := R.size / m
  let b := (List.range n).foldl (fun b c => shortChrom R gbs2 0 c P m Ls b) (initP P)
  (List.range n).foldl (fun b c => shortChrom (revCompB R) gbs2 n c P m Ls b) b

/-! ## Proof -/

section short
variable (P : Nat) (read : List Char) (g : Genome) (gbs : Array ByteArray) (hg : GenomeBytes gbs g)
  (Rs : ByteArray) (reads : List Char) (hrs : Encodes Rs reads) (t : Nat) (ht : t = 0 ∨ t = gbs.size)
  (hcwc : ∀ c, c < gbs.size → ∀ st len, cwB P read g ⟨t + c, st, len⟩ = cwT P reads (g ++ g) ⟨t + c, st, len⟩)
  (hn : 2 * (sbound P + 1) ≤ Rs.size)

include hg hrs ht hcwc hn

set_option maxHeartbeats 1000000 in
theorem shortChrom_cover (c : Nat) (hc : c < gbs.size) (S : Window → Prop) (b : Best)
    (hi : InvP P (cwB P read g) S b) :
    ∃ S', InvP P (cwB P read g) S' (shortChrom Rs (gbs ++ gbs) t c P (sbound P + 1) (Rs.size / (sbound P + 1)) b) ∧
      (∀ w, S w → S' w) ∧ ∀ w, w.chr = t + c → cwB P read g w ≤ P → S' w := by
  have hg2 := genomeBytes_app gbs g hg
  have hc2 : t + c < (gbs ++ gbs).size := by simp; omega
  have hLs : 0 < Rs.size / (sbound P + 1) := Nat.div_pos (by omega) (by omega)
  have hL2 : 2 ≤ Rs.size / (sbound P + 1) := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  generalize hm : sbound P + 1 = m at *
  generalize hL : Rs.size / m = Ls at *
  unfold shortChrom
  simp only []
  generalize harr : (fun j => scanL (gbs ++ gbs)[t + c]! Rs (j * Ls) Ls (Rs.size - j * Ls)) = arr
  have hf := foldl_invP P (cwB P read g)
    (fun b (a : Array Nat) =>
      a.foldl (fun b e => addK Rs (gbs ++ gbs) (t + c) (min P 16) ((e / 16 : Nat) - (Rs.size : Int)) Rs.size b) b)
    (fun a w => ∃ e ∈ a.toList, GX P reads (g ++ g) Rs (t + c) (min P 16) e w)
    (fun a S b h => by
      have := foldl_invP P (cwB P read g)
        (fun b e => addK Rs (gbs ++ gbs) (t + c) (min P 16) ((e / 16 : Nat) - (Rs.size : Int)) Rs.size b)
        (fun e w => GX P reads (g ++ g) Rs (t + c) (min P 16) e w)
        (fun e S b h => addK_inv P reads (g ++ g) (gbs ++ gbs) Rs hg2 hrs (cwB P read g) (cwB_le P read g)
          (t + c) (min P 16) hc2 (hcwc c hc) (Nat.min_le_left _ _) (Nat.min_le_right _ _) _ _ S b h)
        a.toList S b h
      rw [Array.foldl_toList] at this
      exact this)
    ((List.range m).map arr) S b hi
  obtain ⟨S1, i1, s1, c1⟩ := chromKB_coverL P reads (g ++ g) (gbs ++ gbs) Rs hg2 hrs (t + c) hc2
    (cwB P read g) (cwB_le P read g) (hcwc c hc) m Ls Ls (by omega) (by omega) hL hL2 hLs (Nat.le_refl _) arr
    (fun j _ => by rw [← harr]; exact scanL_ok _ _ _ _ _)
    (List.range m) List.nodup_range (fun j hj => List.mem_range.mp hj) _ _ hf
    (fun j hj e he w hw => Or.inr ⟨arr j, List.mem_map_of_mem hj, e, he, hw⟩)
    (Or.inr (List.length_range))
  generalize chromKB Rs (gbs ++ gbs) (t + c) P ((List.range m).map arr).reverse _ = b2 at i1 c1
  have i1' := inv_skipP P (cwB P read g) (cwB_le P read g) S1
    (fun w => w.chr = t + c ∧ cwB P read g w ≤ P ∧ ¬ S1 w) b2 i1 (by
      rintro w ⟨hwc, hwP, hnot⟩
      left
      apply Classical.byContradiction; intro hle
      apply hnot (c1 w hwc _)
      obtain ⟨wc, wst, wlen⟩ := w
      simp only at hwc; subst hwc
      rw [← hcwc c hc]; omega)
  refine ⟨_, i1', fun w hw => Or.inl (s1 w (Or.inl hw)), fun w hwc hwP => ?_⟩
  by_cases h : S1 w
  · exact Or.inl h
  · exact Or.inr ⟨hwc, hwP, h⟩

theorem shortFold : ∀ (l : List Nat) (S : Window → Prop) (b : Best), (∀ c ∈ l, c < gbs.size) →
    InvP P (cwB P read g) S b →
    ∃ S', InvP P (cwB P read g) S'
        (l.foldl (fun b c => shortChrom Rs (gbs ++ gbs) t c P (sbound P + 1) (Rs.size / (sbound P + 1)) b) b) ∧
      (∀ w, S w → S' w) ∧ ∀ c ∈ l, ∀ w, w.chr = t + c → cwB P read g w ≤ P → S' w := by
  intro l
  induction l with
  | nil => intro S b _ hi; exact ⟨S, hi, fun w hw => hw, fun c hc => by simp at hc⟩
  | cons c l ih =>
    intro S b hl hi
    obtain ⟨S1, i1, s1, c1⟩ := shortChrom_cover P read g gbs hg Rs reads hrs t ht hcwc hn c
      (hl c List.mem_cons_self) S b hi
    obtain ⟨S2, i2, s2, c2⟩ := ih S1 _ (fun c' h' => hl c' (List.mem_cons_of_mem _ h')) i1
    refine ⟨S2, i2, fun w hw => s2 w (s1 w hw), fun c' hc' w hwc hwP => ?_⟩
    rcases List.mem_cons.mp hc' with rfl | hc'
    · exact s2 w (c1 w hwc hwP)
    · exact c2 c' hc' w hwc hwP

end short

theorem mapChromsShort_inv (P : Nat) (read : List Char) (g : Genome) (gbs : Array ByteArray) (R : ByteArray)
    (hg : GenomeBytes gbs g) (hr : Encodes R read) (hn : 2 * (sbound P + 1) ≤ R.size) :
    ∃ S, InvP P (cwB P read g) S (mapChromsShort P gbs R) ∧ ∀ w, cwB P read g w ≤ P → S w := by
  have hsz : gbs.size = g.length := hg.1
  have hrr := revCompB_encodes R read hr
  have hcw1 : ∀ c, c < gbs.size → ∀ st len,
      cwB P read g ⟨0 + c, st, len⟩ = cwT P read (g ++ g) ⟨0 + c, st, len⟩ := by
    intro c hc st len
    rw [Nat.zero_add, cwT_app_left P read g _ (by simp only; omega)]
    unfold cwB; rw [if_pos (by simp only; omega)]
  have hcw2 : ∀ c, c < gbs.size → ∀ st len,
      cwB P read g ⟨gbs.size + c, st, len⟩ = cwT P (revComp read) (g ++ g) ⟨gbs.size + c, st, len⟩ := by
    intro c hc st len
    rw [hsz, cwT_app_right]
    unfold cwB; rw [if_neg (by simp only; omega)]
    simp
  unfold mapChromsShort
  simp only []
  obtain ⟨S1, i1, -, c1⟩ := shortFold P read g gbs hg R read hr 0 (Or.inl rfl) hcw1 hn (List.range gbs.size)
    (fun _ => False) (initP P) (fun c hc => List.mem_range.mp hc) (inv_initP P (cwB P read g))
  simp only [Nat.zero_add] at i1 c1
  have hrn : 2 * (sbound P + 1) ≤ (revCompB R).size := by rw [revCompB_size]; exact hn
  obtain ⟨S2, i2, s2, c2⟩ := shortFold P read g gbs hg (revCompB R) (revComp read) hrr gbs.size (Or.inr rfl) hcw2
    hrn (List.range gbs.size) S1 _ (fun c hc => List.mem_range.mp hc) i1
  rw [revCompB_size] at i2
  refine ⟨S2, i2, fun w hw => ?_⟩
  have hw2 := cwB_chr_lt P read g w hw
  by_cases hwc : w.chr < gbs.size
  · exact s2 w (c1 w.chr (List.mem_range.mpr hwc) w rfl hw)
  · exact c2 (w.chr - gbs.size) (List.mem_range.mpr (by omega)) w (by omega) hw

/-! ## The mapper with the short-read path -/

/-- Both strands at `T = −P`: the indexed path, the short-read scan, and the
specification itself only for reads of at most `sbound P` letters. -/
def mapFastGS {L Pp : Type} [LookG L Pp] [Inhabited Pp] (P : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (gbs : Array ByteArray) (R : ByteArray) : Option (Placement × Int) :=
  if fastT P R then decodeP gbs.size P (mapChromsGB P ix G offs gbs R)
  else if 2 * (sbound P + 1) ≤ R.size then decodeP gbs.size P (mapChromsShort P gbs R)
  else mapSpecBoth sc0 (-(P : Int)) (decodeGenomeB gbs) (decodeBytes R)

def pairFastGS {L Pp : Type} [LookG L Pp] [Inhabited Pp] (P lo hi : Nat) (ix : L) (G : ByteArray)
    (offs : Array Nat) (gbs : Array ByteArray) (R1 R2 : ByteArray) :
    Option ((Placement × Int) × (Placement × Int)) :=
  match mapFastGS P ix G offs gbs R1, mapFastGS P ix G offs gbs R2 with
  | some a, some b => if properPair lo hi a.1 b.1 then some (a, b) else none
  | _, _ => none

theorem mapFastGS_eq_mapSpecBoth {L Pp : Type} [LookG L Pp] [Inhabited Pp] (P : Nat) (g : Genome)
    (read : List Char) (gbs : Array ByteArray) (R : ByteArray) (ix : L) (G : ByteArray) (offs : Array Nat)
    (hg : GenomeBytes gbs g) (hr : Encodes R read) (hcat : catOk G offs gbs = true)
    (hlk : ∀ (R' : ByteArray) s base, s + q ≤ R'.size →
      LookOkS G R' s base 0 (LookG.look ix G R' s base (LookG.prep ix (seedHashAt R' s)))) :
    mapFastGS P ix G offs gbs R = mapSpecBoth sc0 (-(P : Int)) g read := by
  have hgb := mapFastGB_eq_mapSpecBoth P g read gbs R ix G offs hg hr hcat hlk
  unfold mapFastGB at hgb
  unfold mapFastGS
  split
  · next h => rw [if_pos h] at hgb; exact hgb
  · next h =>
    rw [if_neg h] at hgb
    split
    · next hn =>
      obtain ⟨S, hi, hall⟩ := mapChromsShort_inv P read g gbs R hg hr hn
      rw [hg.1]
      exact decodeP_eq P g read S _ hi hall
    · exact hgb

theorem pairFastGS_eq_pairSpec {L Pp : Type} [LookG L Pp] [Inhabited Pp] (P lo hi : Nat) (g : Genome)
    (m1 m2 : List Char) (gbs : Array ByteArray) (R1 R2 : ByteArray) (ix : L) (G : ByteArray) (offs : Array Nat)
    (hg : GenomeBytes gbs g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hcat : catOk G offs gbs = true)
    (hlk : ∀ (R' : ByteArray) s base, s + q ≤ R'.size →
      LookOkS G R' s base 0 (LookG.look ix G R' s base (LookG.prep ix (seedHashAt R' s)))) :
    pairFastGS P lo hi ix G offs gbs R1 R2 = pairSpec sc0 (-(P : Int)) lo hi g m1 m2 := by
  unfold pairFastGS pairSpec
  rw [mapFastGS_eq_mapSpecBoth P g m1 gbs R1 ix G offs hg h1 hcat hlk,
    mapFastGS_eq_mapSpecBoth P g m2 gbs R2 ix G offs hg h2 hcat hlk]
  cases mapSpecBoth sc0 (-(P : Int)) g m1 <;> cases mapSpecBoth sc0 (-(P : Int)) g m2 <;> rfl

theorem pairFastGS_hashed_eq_pairSpec (P lo hi : Nat) (g : Genome) (m1 m2 : List Char) (gbs : Array ByteArray)
    (R1 R2 : ByteArray) (ix : HIdx) (G : ByteArray) (offs : Array Nat)
    (hg : GenomeBytes gbs g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hcat : catOk G offs gbs = true)
    (hchk : checkAll #[ix] #[G] = true) :
    pairFastGS P lo hi ix G offs gbs R1 R2 = pairSpec sc0 (-(P : Int)) lo hi g m1 m2 :=
  pairFastGS_eq_pairSpec P lo hi g m1 m2 gbs R1 R2 ix G offs hg h1 h2 hcat (lookG_hashed G ix hchk)

theorem pairFastGS_mz_eq_pairSpec (P lo hi : Nat) (g : Genome) (m1 m2 : List Char) (gbs : Array ByteArray)
    (R1 R2 : ByteArray) (ix : Mz.MzIdx) (G : ByteArray) (offs : Array Nat)
    (hg : GenomeBytes gbs g) (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hcat : catOk G offs gbs = true)
    (hchk : checkAllMz #[ix] #[G] = true) :
    pairFastGS P lo hi ix G offs gbs R1 R2 = pairSpec sc0 (-(P : Int)) lo hi g m1 m2 :=
  pairFastGS_eq_pairSpec P lo hi g m1 m2 gbs R1 R2 ix G offs hg h1 h2 hcat (lookG_mz G ix hchk)

end MapSpec.Fast

#print axioms MapSpec.Fast.scanL_ok
#print axioms MapSpec.Fast.mapFastGS_eq_mapSpecBoth
#print axioms MapSpec.Fast.pairFastGS_hashed_eq_pairSpec
#print axioms MapSpec.Fast.pairFastGS_mz_eq_pairSpec
