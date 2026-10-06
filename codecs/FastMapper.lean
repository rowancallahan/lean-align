import MapSpec                    -- the mapping specification (spec/, draft)
import SeedMapper                 -- mapWith, kernelScore, LookupComplete (slow fallback)
import BandScore                  -- Encodes, GenomeBytes
import MapperBytes                -- decodeBytes
import MapperFastAlgo             -- the fast code
import MapperFastLazy             -- its invariant: every hit looked at

/-!
# Codec `mapFast`: the fast proved read mapper

Scoring (0, −4, −6, −2) (`sc0`) and threshold `T = −12` only.  Genome and read
are byte strings (`GenomeBytes`, `Encodes`: one byte per letter).

* Reads of 100–103 letters (`fastOk`) take the fast path of
  `pool/mapper/MapperFastAlgo.lean` (the code of `bench/Proto.lean`, branch
  `speed/proto-tune`, `mapCore`): hashed 25-mer index per chromosome, 4 seeds
  looked up lazily (smallest bucket first, stop once the best is below
  `4·lookups`), packed anchors with clean-seed masks, same-length windows
  (`4·mismatches`), one-gap windows (`6 + 2L + 4·mismatches`) only after 3
  lookups and while the best costs ≥ 8, with support pruning.  Letters other
  than ACGT in a seed are looked up through the index's per-letter place lists.
* Other reads take a slow proved path (`mapWith` of `SeedMapper.lean` with a
  scanning lookup and the proved codec `wfaAlignU3`).

The index is not trusted: `checkAll idxs gbs` checks it at run time.

Measured (`lake exe fast_bench`, chr21 = 46.7 Mb, 100k simulated 100-letter
reads, one thread): 220k–290k reads/s; the prototype (`speed/proto-tune`
dc0b687) 230k–270k reads/s on the same machine; identical answers on all
100k reads.  Index build 31 s (untrusted), `checkAll` 9–13 s.

## The theorems

    GenomeBytes gbs g → Encodes R read → checkAll idxs gbs = true →
      mapFast gbs idxs R = mapSpec sc0 (-12) g read                         (mapFast_eq_mapSpec)
    … mapFastReads gbs idxs Rs = reads.map (mapSpec sc0 (-12) g)            (mapFastReads_eq_mapSpec)
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-! ## The algorithm -/

/-- The runtime index checker, every chromosome. -/
def checkAll (idxs : Array HIdx) (gbs : Array ByteArray) : Bool :=
  (List.range gbs.size).all fun c => checkIdx idxs[c]! gbs[c]!

/-- Every place of the genome where `word` occurs (slow fallback only). -/
def scanLookup (g : Genome) (l0 : Nat) (word : List Char) : List (Nat × Nat) :=
  (List.range g.length).flatMap fun c =>
    match g[c]? with
    | some ch => ((List.range (ch.seq.length + 1)).filter fun p => (ch.seq.drop p).take l0 == word).map (c, ·)
    | none => []

def decodeGenomeB (gbs : Array ByteArray) : Genome :=
  gbs.toList.map fun B => { name := "", seq := decodeBytes B }

/-- Slow proved path for reads the fast path does not take. -/
def slowMap (gbs : Array ByteArray) (R : ByteArray) : Option (Window × Int) :=
  let g := decodeGenomeB gbs
  let read := decodeBytes R
  let l0 := read.length / (errBound sc0 (-12) + 1)
  mapWith (scanLookup g l0) (kernelScore sc0 read g) l0 (-12) (errBound sc0 (-12)) g read

/-- Map one read through any seed lookup `lk` (index `idxs[c]` for chromosome `c`). -/
@[specialize] def mapFastG {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P) (gbs : Array ByteArray) (idxs : Array L)
    (R : ByteArray) : Option (Window × Int) :=
  if fastOk R then
    match result (mapChroms lk R gbs idxs) with
    | some (c, st, len, pen) => some (⟨c, st, len⟩, -(pen : Int))
    | none => none
  else slowMap gbs R

/-- Map one read (hashed index). -/
def mapFast (gbs : Array ByteArray) (idxs : Array HIdx) (R : ByteArray) : Option (Window × Int) :=
  mapFastG hLook gbs idxs R

/-- What the generic mapper needs of a lookup: every chromosome's lookup is right. -/
def LookAll {L P : Type} [Inhabited L] (lk : Look L P) (gbs : Array ByteArray) (idxs : Array L) : Prop :=
  ∀ c, c < gbs.size → ∀ R j, j < 4 →
    LookOk gbs[c]! R j (lk.look idxs[c]! gbs[c]! R j (lk.prep idxs[c]! (seedHash R j)))

def mapFastReads (gbs : Array ByteArray) (idxs : Array HIdx) (Rs : List ByteArray) :
    List (Option (Window × Int)) :=
  Rs.map (mapFast gbs idxs)

/-! ## Proof -/

theorem decodeBytes_of_encodes (B : ByteArray) (cs : List Char) (h : Encodes B cs) : decodeBytes B = cs := by
  apply List.ext_getElem
  · rw [length_decodeBytes]; exact h.1
  · intro i h1 h2
    rw [getElem_decodeBytes]
    apply Char.toNat_inj.mp
    rw [← h.2 i h2]
    exact toChar_val_toNat _

theorem scanLookup_complete (g : Genome) (l0 : Nat) : LookupComplete g l0 (scanLookup g l0) := by
  intro c ch p hc hp
  unfold scanLookup
  rw [List.mem_flatMap]
  refine ⟨c, List.mem_range.mpr (List.getElem?_eq_some_iff.mp hc).1, ?_⟩
  rw [hc, List.mem_map]
  exact ⟨p, List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), by simp⟩, rfl⟩

theorem slowMap_eq (gbs : Array ByteArray) (R : ByteArray) :
    slowMap gbs R = mapSpec sc0 (-12) (decodeGenomeB gbs) (decodeBytes R) :=
  mapWith_eq_mapSpec _ _ _ sc0 valid_sc0 (-12) _ _ (scanLookup_complete _ _) (kernelScore_eq sc0 _ _)

/-- `mapSpec` only looks at the letters of the chromosomes. -/
theorem mapSpec_seqs (sc : Scoring) (T : Int) (g g' : Genome) (read : List Char)
    (h : g.map (·.seq) = g'.map (·.seq)) : mapSpec sc T g read = mapSpec sc T g' read := by
  have hl : g.length = g'.length := by simpa using congrArg List.length h
  have hc : ∀ c : Nat, (g[c]?).map (fun x : Chromosome => x.seq) = (g'[c]?).map (fun x : Chromosome => x.seq) := by
    intro c; rw [← List.getElem?_map, ← List.getElem?_map, h]
  have hws : windowSeq g = windowSeq g' := by
    funext w
    unfold windowSeq
    have := hc w.chr
    cases h1 : g[w.chr]? <;> cases h2 : g'[w.chr]? <;> simp_all
  have haw : allWindows g = allWindows g' := by
    unfold allWindows
    rw [hl]
    congr 1
    funext c
    have := hc c
    cases h1 : g[c]? <;> cases h2 : g'[c]? <;> simp_all
  unfold mapSpec windowScore
  rw [hws, haw]

theorem windowScore_nonpos (read : List Char) (g : Genome) (w : Window) (s : Int)
    (h : windowScore sc0 read g w = some s) : s ≤ 0 := by
  unfold windowScore at h
  split at h
  · next ys _ =>
    split at h
    · next best hb =>
      obtain ⟨path, bs⟩ := best
      cases h
      obtain ⟨-, hs⟩ := getBestAlignment_returns_a_valid_walk sc0 read ys path bs hb
      rw [← hs]; exact scoreWalk_nonpos sc0 valid_sc0 _ _ _ _
    · cases h
  · cases h

/-- The fast path's window penalty is the specification's. -/
theorem cwG_eq (g : Genome) (read : List Char) (gbs : Array ByteArray) (R : ByteArray) (hg : GenomeBytes gbs g)
    (hr : Encodes R read) (w : Window) : cwG R gbs w = penOf (windowScore sc0 read g w) := by
  obtain ⟨hsz, henc⟩ := hg
  unfold cwG windowScore windowSeq
  by_cases hc : w.chr < gbs.size
  · rw [if_pos hc, List.getElem?_eq_getElem (by omega)]
    have he := henc w.chr hc (by omega)
    rw [getElem!_pos gbs w.chr hc]
    simp only []
    by_cases hfit : w.start + w.len ≤ g[w.chr].seq.length
    · rw [if_pos hfit]
      simp only []
      have := penB_eq_penL R gbs[w.chr] read g[w.chr].seq hr he w.start w.len hfit
      rw [← this]
      unfold penL
      cases getBestAlignment sc0 read ((g[w.chr].seq.drop w.start).take w.len) <;> rfl
    · rw [if_neg hfit]
      unfold penB; rw [if_neg (by rw [he.1]; exact hfit)]; rfl
  · rw [if_neg hc, List.getElem?_eq_none (by omega)]; rfl

theorem penOf_some (o : Option Int) (s : Int) (hs : ∀ t, o = some t → t ≤ 0) :
    (o = some s ∧ -12 ≤ s) ↔ (penOf o ≤ 12 ∧ s = -(penOf o : Int)) := by
  cases o with
  | none => simp [penOf]
  | some s' =>
    simp only [penOf, Option.some.injEq]
    constructor
    · rintro ⟨rfl, h⟩; rw [if_pos h]; have := hs s' rfl; omega
    · intro ⟨h1, h2⟩
      have := hs s' rfl
      split at h1
      · next h => split at h2 <;> omega
      · omega

/-- `mapSpec` is the unique best hit. -/
theorem mapSpec_iff (g : Genome) (read : List Char) (w : Window) (s : Int) :
    mapSpec sc0 (-12) g read = some (w, s) ↔
      (windowScore sc0 read g w = some s ∧ -12 ≤ s) ∧
      ∀ w' s', windowScore sc0 read g w' = some s' → -12 ≤ s' → s' < s ∨ w' = w := by
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

/-- **Generic.**  Through any lookup satisfying `LookAll`, `mapFastG` is the specification's answer. -/
theorem mapFastG_eq_mapSpec {L P : Type} [Inhabited L] [Inhabited P] (lk : Look L P) (g : Genome) (read : List Char)
    (gbs : Array ByteArray) (idxs : Array L) (R : ByteArray) (hg : GenomeBytes gbs g) (hr : Encodes R read)
    (hlk : LookAll lk gbs idxs) :
    mapFastG lk gbs idxs R = mapSpec sc0 (-12) g read := by
  unfold mapFastG
  split
  · next hok =>
    have hn : 100 ≤ R.size := by unfold fastOk q at hok; simp at hok; omega
    obtain ⟨S, hinv, hall⟩ := mapChroms_inv lk R gbs idxs hn (fun c hc j hj => hlk c hc R j hj)
    have hcw := cwG_eq g read gbs R hg hr
    apply Option.ext
    rintro ⟨w, s⟩
    rw [mapSpec_iff]
    have key : ∀ w' s', (windowScore sc0 read g w' = some s' ∧ -12 ≤ s') ↔
        (cwG R gbs w' ≤ 12 ∧ s' = -(cwG R gbs w' : Int)) := by
      intro w' s'
      rw [hcw]; exact penOf_some _ s' (windowScore_nonpos read g w')
    rw [key]
    have hres := result_spec (cwG R gbs) S _ hinv hall w
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
      have hp : result (mapChroms lk R gbs idxs) = some (w.chr, w.start, w.len, cwG R gbs w) := by
        rw [hres]
        refine ⟨rfl, h1, fun w' h4 h5 => ?_⟩
        rcases h3 w' _ ((key w' _).mpr ⟨h4, rfl⟩).1 ((key w' _).mpr ⟨h4, rfl⟩).2 with h6 | h6
        · omega
        · exact absurd h6 h5
      rw [hp]
  · rw [slowMap_eq, decodeBytes_of_encodes R read hr]
    apply mapSpec_seqs
    obtain ⟨hsz, henc⟩ := hg
    unfold decodeGenomeB
    apply List.ext_getElem
    · simp [hsz]
    · intro i h1 h2
      simp only [List.getElem_map, Array.getElem_toList]
      exact decodeBytes_of_encodes _ _ (henc i (by simpa using h1) (by simpa using h2))

theorem lookAll_hLook (gbs : Array ByteArray) (idxs : Array HIdx) (hchk : checkAll idxs gbs = true) :
    LookAll hLook gbs idxs := by
  intro c hc R j hj
  unfold checkAll at hchk
  simp only [List.all_eq_true, List.mem_range] at hchk
  exact hLook_ok _ _ _ _ hj (hchk c hc)

/-- **Fast path.**  Under the hypotheses, `mapFast` is the specification's answer. -/
theorem mapFast_eq_mapSpec (g : Genome) (read : List Char) (gbs : Array ByteArray) (idxs : Array HIdx)
    (R : ByteArray) (hg : GenomeBytes gbs g) (hr : Encodes R read) (hchk : checkAll idxs gbs = true) :
    mapFast gbs idxs R = mapSpec sc0 (-12) g read :=
  mapFastG_eq_mapSpec hLook g read gbs idxs R hg hr (lookAll_hLook gbs idxs hchk)

/-- **Many reads.** -/
theorem mapFastReads_eq_mapSpec (g : Genome) (gbs : Array ByteArray) (idxs : Array HIdx)
    (hg : GenomeBytes gbs g) (hchk : checkAll idxs gbs = true) :
    ∀ (Rs : List ByteArray) (reads : List (List Char)), Rs.length = reads.length →
      (∀ p ∈ Rs.zip reads, Encodes p.1 p.2) →
      mapFastReads gbs idxs Rs = reads.map (mapSpec sc0 (-12) g) := by
  intro Rs
  induction Rs with
  | nil => intro reads hl _; cases reads <;> simp_all [mapFastReads]
  | cons R Rs ih =>
    intro reads hl hr
    cases reads with
    | nil => simp at hl
    | cons r reads =>
      simp only [mapFastReads, List.map_cons] at *
      rw [mapFast_eq_mapSpec g r gbs idxs R hg (hr (R, r) (by simp)) hchk,
        ih reads (by simpa using hl) (fun p hp => hr p (by simp [hp]))]

end MapSpec.Fast

#print axioms MapSpec.Fast.mapFastG_eq_mapSpec
#print axioms MapSpec.Fast.mapFast_eq_mapSpec
#print axioms MapSpec.Fast.mapFastReads_eq_mapSpec
#print axioms MapSpec.Fast.lookupSeed_spec
#print axioms MapSpec.Fast.mapChroms_inv
#print axioms MapSpec.penL_same
#print axioms MapSpec.penL_ins
#print axioms MapSpec.penL_del
#print axioms MapSpec.Fast.gap_support
#print axioms MapSpec.Fast.hamSeeds_spec
#print axioms MapSpec.Fast.gappedPen2_spec
