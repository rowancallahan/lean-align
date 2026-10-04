import FastGenProof

/-!
# Codec `mapFastTG`: the general fast mapper, any read length and threshold

For a penalty bound `P` (threshold `T = −P`, scoring (0, −4, −6, −2)), a byte
genome `gbs` with `GenomeBytes gbs g`, a read `R` with `Encodes R read`, and
per-chromosome indexes whose seed lookups are right (`LookAllG`, e.g. a hashed
index passing `checkIdx`):

    mapFastTG P gbs idxs R = mapSpec sc0 (-P) g read               (mapFastTG_eq_mapSpec)

Reads with `sbound P < ⌊n/25⌋` seeds take the fast path (`fastT`); the others
the slow proved path.
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-- What the general mapper needs of the lookups: right on every chromosome. -/
def LookAllG {L Pp : Type} [LookG L Pp] [Inhabited L] (gbs : Array ByteArray) (idxs : Array L) : Prop :=
  ∀ c, c < gbs.size → ∀ (R : ByteArray) (s base : Nat), s + q ≤ R.size →
    LookOkS gbs[c]! R s base 0 (LookG.look idxs[c]! gbs[c]! R s base (LookG.prep idxs[c]! (seedHashAt R s)))

theorem insKey_fold_perm (ks : Array Nat) :
    ∀ (xs l : List Nat), (xs.foldl (fun l j => insKey ks j l) l).Perm (xs.reverse ++ l) := by
  intro xs
  induction xs with
  | nil => intro l; simp
  | cons x xs ih =>
    intro l
    simp only [List.foldl_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
    exact (ih _).trans (List.Perm.append_left _ (insKey_perm ks x l))

theorem ordG_spec (ks : Array Nat) (m : Nat) :
    (ordG ks m).Nodup ∧ (∀ j ∈ ordG ks m, j < m) ∧ (ordG ks m).length = m := by
  have hp : (ordG ks m).Perm (List.range m) := by
    unfold ordG
    have := insKey_fold_perm ks (List.range m) []
    rw [List.append_nil] at this
    exact this.trans (List.reverse_perm _)
  refine ⟨hp.nodup_iff.2 List.nodup_range, fun j hj => List.mem_range.1 (hp.mem_iff.1 hj), by
    rw [hp.length_eq, List.length_range]⟩

section
variable (P : Nat) (read : List Char) (g : Genome) (gbs : Array ByteArray) (R : ByteArray)
  (hg : GenomeBytes gbs g) (hr : Encodes R read)
  {L Pp : Type} [LookG L Pp] [Inhabited L] [Inhabited Pp] (idxs : Array L)
  (hlk : LookAllG gbs idxs) (hm : 0 < R.size / 25) (hsb : sbound P < R.size / 25)

include hg hr hlk hm hsb

/-- **All chromosomes.**  `mapChromsG` ends with the invariant over a set containing every hit. -/
theorem mapChromsG_inv :
    ∃ S, InvP P (cwT P read g) S (mapChromsG P R gbs idxs) ∧ ∀ w, cwT P read g w ≤ P → S w := by
  unfold mapChromsG
  simp only []
  generalize hhs : (Array.range (R.size / 25)).map (fun j => seedHashAt R (j * (R.size / (R.size / 25)))) = hs
  have hhs' : ∀ j, j < R.size / 25 → hs[j]! = seedHashAt R (j * (R.size / (R.size / 25))) := by
    intro j hj
    rw [← hhs, getElem!_pos _ j (by simpa using hj)]
    simp
  have hsz : hs.size = R.size / 25 := by rw [← hhs]; simp
  have step : ∀ (l : List Nat) S b, (∀ c ∈ l, c < gbs.size) → InvP P (cwT P read g) S b →
      ∃ S', InvP P (cwT P read g) S' (l.foldl (fun b c =>
          chromG idxs[c]! R gbs c P (R.size / (R.size / 25)) (hs.map (LookG.prep idxs[c]!))
            (ordG ((hs.map (LookG.prep idxs[c]!)).map (LookG.size idxs[c]!)) (R.size / 25)) b) b) ∧
        (∀ w, S w → S' w) ∧ ∀ c ∈ l, ∀ w, w.chr = c → cwT P read g w ≤ P → S' w := by
    intro l
    induction l with
    | nil => intro S b _ h; exact ⟨S, h, fun w hw => hw, fun c hc => by simp at hc⟩
    | cons c l ih =>
      intro S b hl h
      have hc : c < gbs.size := hl c List.mem_cons_self
      obtain ⟨hnd, hlt, hlen⟩ := ordG_spec ((hs.map (LookG.prep idxs[c]!)).map (LookG.size idxs[c]!)) (R.size / 25)
      obtain ⟨S1, h1, s1, c1⟩ := chromG_cover P read g gbs R hg hr idxs[c]! c (hs.map (LookG.prep idxs[c]!)) _
        hc hm hsb (cwT P read g) (cwT_le P read g) (fun _ _ => rfl) (fun j hj => by
          rw [getElem!_pos _ j (by simp [hsz]; omega)]
          simp only [Array.getElem_map]
          rw [← hhs' j hj, getElem!_pos _ j (by omega)])
        (fun s base hs => hlk c hc R s base hs) hnd hlt hlen S b h
      simp only [List.foldl_cons]
      generalize chromG idxs[c]! R gbs c P (R.size / (R.size / 25)) (hs.map (LookG.prep idxs[c]!))
        (ordG ((hs.map (LookG.prep idxs[c]!)).map (LookG.size idxs[c]!)) (R.size / 25)) b = b1 at h1 c1
      -- the windows of chromosome `c` not added cannot beat or tie the best
      have h1' := inv_skipP P (cwT P read g) (cwT_le P read g) S1
        (fun w => w.chr = c ∧ cwT P read g w ≤ P ∧ ¬ S1 w) b1 h1 (by
          rintro w ⟨hwc, hwP, hnot⟩
          left
          apply Classical.byContradiction; intro hle
          exact hnot (c1 w hwc (by omega)))
      obtain ⟨S2, h2, s2, c2⟩ := ih _ _ (fun c' h' => hl c' (List.mem_cons_of_mem _ h')) h1'
      refine ⟨S2, h2, fun w hw => s2 w (Or.inl (s1 w hw)), fun c' hc' w hwc hwP => ?_⟩
      rcases List.mem_cons.mp hc' with rfl | hc'
      · apply s2
        by_cases hs1 : S1 w
        · exact Or.inl hs1
        · exact Or.inr ⟨hwc, hwP, hs1⟩
      · exact c2 c' hc' w hwc hwP
  obtain ⟨S, h, -, hcov⟩ := step (List.range gbs.size) (fun _ => False) (initP P)
    (fun c hc => List.mem_range.mp hc) (inv_initP P (cwT P read g))
  refine ⟨S, h, fun w hw => ?_⟩
  by_cases hwc : w.chr < gbs.size
  · exact hcov w.chr (List.mem_range.mpr hwc) w rfl hw
  · exfalso
    have hnone : windowScore sc0 read g w = none := by
      unfold windowScore windowSeq
      rw [List.getElem?_eq_none (by have := hg.1; omega)]
    have : cwT P read g w = P + 1 := by unfold cwT; rw [hnone]
    omega

end

theorem slowMapT_eq (T : Int) (gbs : Array ByteArray) (R : ByteArray) :
    slowMapT T gbs R = mapSpec sc0 T (decodeGenomeB gbs) (decodeBytes R) :=
  mapWith_eq_mapSpec _ _ _ sc0 valid_sc0 T _ _ (scanLookup_complete _ _) (kernelScore_eq sc0 _ _)

/-- `mapSpec` is the unique best hit (any threshold). -/
theorem mapSpec_iffT (T : Int) (g : Genome) (read : List Char) (w : Window) (s : Int) :
    mapSpec sc0 T g read = some (w, s) ↔
      (windowScore sc0 read g w = some s ∧ T ≤ s) ∧
      ∀ w' s', windowScore sc0 read g w' = some s' → T ≤ s' → s' < s ∨ w' = w := by
  unfold mapSpec
  rw [selectUnique_eq_some_iff _ (by
    rintro ⟨a, sa⟩ ha ⟨b, sb⟩ hb (rfl : a = b)
    rw [mem_hitsOf] at ha hb
    have := ha.2.1.symm.trans hb.2.1
    simpa using this)]
  have allw : ∀ w' s', windowScore sc0 read g w' = some s' → w' ∈ allWindows g := by
    intro w' s' h4
    apply (mem_allWindows g w').2
    unfold windowScore at h4; cases hw : windowSeq g w' <;> simp_all
  constructor
  · rintro ⟨hm, h3⟩
    rw [mem_hitsOf] at hm
    exact ⟨⟨hm.2.1, hm.2.2⟩, fun w' s' h4 h5 =>
      h3 (w', s') ((mem_hitsOf _ _ _ _ _).2 ⟨allw w' s' h4, h4, h5⟩)⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨(mem_hitsOf _ _ _ _ _).2 ⟨allw w s h1, h1, h2⟩, fun ⟨w', s'⟩ hb => ?_⟩
    rw [mem_hitsOf] at hb
    exact h3 w' s' hb.2.1 hb.2.2

/-- **The general fast mapper is the specification**, at threshold `−P`. -/
theorem mapFastTG_eq_mapSpec {L Pp : Type} [LookG L Pp] [Inhabited L] [Inhabited Pp] (P : Nat)
    (g : Genome) (read : List Char) (gbs : Array ByteArray) (idxs : Array L) (R : ByteArray)
    (hg : GenomeBytes gbs g) (hr : Encodes R read) (hlk : LookAllG gbs idxs) :
    mapFastTG P gbs idxs R = mapSpec sc0 (-(P : Int)) g read := by
  unfold mapFastTG
  split
  · next hok =>
    unfold fastT at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨S, hinv, hall⟩ := mapChromsG_inv P read g gbs R hg hr idxs hlk hok.1 hok.2
    apply Option.ext
    rintro ⟨w, s⟩
    rw [mapSpec_iffT]
    have key : ∀ w' s', (windowScore sc0 read g w' = some s' ∧ -(P : Int) ≤ s') ↔
        (cwT P read g w' ≤ P ∧ s' = -(cwT P read g w' : Int)) := fun w' s' => cwT_iff P read g w' s'
    rw [key]
    have hres := resultP_spec P (cwT P read g) S _ hinv hall w
    constructor
    · intro hm
      split at hm
      · next c st len pen hp =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        obtain ⟨h1, h2, h3⟩ := (hres pen).mp hp
        refine ⟨⟨by omega, by rw [h1]⟩, fun w' s' h4 h5 => ?_⟩
        obtain ⟨h6, rfl⟩ := (key w' s').mp ⟨h4, h5⟩
        by_cases hw : w' = ⟨c, st, len⟩
        · right; exact hw
        · left; have := h3 w' h6 hw; omega
      · cases hm
    · rintro ⟨⟨h1, rfl⟩, h3⟩
      have hp : resultP P (mapChromsG P R gbs idxs) = some (w.chr, w.start, w.len, cwT P read g w) := by
        rw [hres]
        refine ⟨rfl, h1, fun w' h4 h5 => ?_⟩
        rcases h3 w' _ ((key w' _).mpr ⟨h4, rfl⟩).1 ((key w' _).mpr ⟨h4, rfl⟩).2 with h6 | h6
        · omega
        · exact absurd h6 h5
      rw [hp]
  · rw [slowMapT_eq, decodeBytes_of_encodes R read hr]
    apply mapSpec_seqs
    obtain ⟨hsz, henc⟩ := hg
    unfold decodeGenomeB
    apply List.ext_getElem
    · simp [hsz]
    · intro i h1 h2
      simp only [List.getElem_map, Array.getElem_toList]
      exact decodeBytes_of_encodes _ _ (henc i (by simpa using h1) (by simpa using h2))

/-! ## The hashed index -/

def checkAllH (idxs : Array HIdx) (gbs : Array ByteArray) : Bool := checkAll idxs gbs

theorem lookAllG_hashed (gbs : Array ByteArray) (idxs : Array HIdx) (hchk : checkAll idxs gbs = true) :
    LookAllG gbs idxs := by
  intro c hc R s base _
  unfold checkAll at hchk
  simp only [List.all_eq_true, List.mem_range] at hchk
  exact lookupHG_spec idxs[c]! gbs[c]! R s base 0 (hchk c hc)

/-- Map one read at threshold `−P` through hashed indexes. -/
def mapFastT (P : Nat) (gbs : Array ByteArray) (idxs : Array HIdx) (R : ByteArray) : Option (Window × Int) :=
  mapFastTG P gbs idxs R

/-- **Hashed indexes.** -/
theorem mapFastT_eq_mapSpec (P : Nat) (g : Genome) (read : List Char) (gbs : Array ByteArray)
    (idxs : Array HIdx) (R : ByteArray) (hg : GenomeBytes gbs g) (hr : Encodes R read)
    (hchk : checkAll idxs gbs = true) :
    mapFastT P gbs idxs R = mapSpec sc0 (-(P : Int)) g read :=
  mapFastTG_eq_mapSpec P g read gbs idxs R hg hr (lookAllG_hashed gbs idxs hchk)

end MapSpec.Fast

#print axioms MapSpec.Fast.mapFastTG_eq_mapSpec
#print axioms MapSpec.Fast.mapFastT_eq_mapSpec
