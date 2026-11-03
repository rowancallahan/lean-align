import Proofs.LastResort

/-! # Giving up on repeats (prototype for the proposed `.gaveUp` answer)

Spec (proposal): `.gaveUp` claims `found = none` and a mate has a seed (a window of `seedLength = 25` letters)
that occurs at least `gaveUpRepeats = 500` times (`Genome.RepeatWitness`, counted over both strands).

The check (`repeatMate`): look up seeds of the mate at `0, 25, 50, …` in the index. The lookup returns exactly
the places of the seed in the whole packed genome (`Mz.lookupSeed_mem`, strictly increasing:
`Mz.lookupSeed_sorted`). A place counts when it lies inside one chromosome (`inChrom`; the chromosome is
guessed by a binary search over `offs` and then checked, so the guess needs no proof). Counted places are
distinct `(chromosome, start)` windows equal to the seed, so the count is a LOWER bound on
`Genome.occurrences` (`count_le_occurrences`); reverse-complement windows are not counted (only a smaller
count). Nothing about the index beyond the existing lookup theorem is needed.
-/

namespace Spec.GaveUp

/-! ## Counting: a list of distinct windows that occur is no longer than `occurrences` -/

-- the starts in `chromosome` where `word` (or its reverse complement) occurs, as `Genome.occurrences` counts them
def occOf (word : Read) (chromosome : Chromosome) : List Nat :=
  (List.range (chromosome.seq.length + 1 - word.length)).filter fun start =>
    let window := (chromosome.seq.drop start).take word.length
    window == word || window == reverseComplement word

-- `(chromosome index, start)` of every occurrence, chromosomes numbered from `c`
def occList (word : Read) : Nat → Genome → List (Nat × Nat)
  | _, [] => []
  | c, chr :: rest => (occOf word chr).map (c, ·) ++ occList word (c + 1) rest

theorem occList_length (word : Read) : ∀ c (g : Genome),
    (occList word c g).length = (g.map fun chr => (occOf word chr).length).sum
  | _, [] => rfl
  | c, chr :: rest => by simp [occList, occList_length word (c + 1) rest]

theorem occurrences_eq (genome : Genome) (word : Read) :
    genome.occurrences word = (occList word 0 genome).length := by
  rw [occList_length]; rfl

theorem mem_occList (word : Read) : ∀ c (g : Genome) (x : Nat × Nat) (chr : Chromosome),
    c ≤ x.1 → g[x.1 - c]? = some chr → x.2 ∈ occOf word chr → x ∈ occList word c g
  | _, [], _, _, _, h, _ => by simp at h
  | c, chr :: rest, x, chr', hc, hg, hs => by
    unfold occList
    rw [List.mem_append]
    by_cases h0 : x.1 = c
    · left
      rw [show x.1 - c = 0 by omega] at hg
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hg
      subst hg
      exact List.mem_map.mpr ⟨x.2, hs, by rw [← h0]⟩
    · right
      apply mem_occList word (c + 1) rest x chr' (by omega)
      rw [show x.1 - c = (x.1 - (c + 1)) + 1 by omega, List.getElem?_cons_succ] at hg
      exact hg
      exact hs

-- a list without repeats inside another is no longer
theorem length_le_of_nodup_sub {α : Type} [DecidableEq α] : ∀ (l1 l2 : List α), l1.Nodup →
    (∀ x ∈ l1, x ∈ l2) → l1.length ≤ l2.length
  | [], _, _, _ => Nat.zero_le _
  | a :: t, l2, hn, hs => by
    rw [List.nodup_cons] at hn
    have ha := hs a List.mem_cons_self
    have ht : ∀ x ∈ t, x ∈ l2.erase a := fun x hx => by
      have hne : x ≠ a := fun e => hn.1 (by rw [← e]; exact hx)
      exact (List.mem_erase_of_ne hne).mpr (hs x (List.mem_cons_of_mem _ hx))
    have := length_le_of_nodup_sub t (l2.erase a) hn.2 ht
    rw [List.length_erase_of_mem ha] at this
    have : 0 < l2.length := List.length_pos_of_mem ha
    simp only [List.length_cons]; omega

/-- Distinct occurring windows are at most `occurrences`. -/
theorem count_le_occurrences (genome : Genome) (word : Read) (L : List (Nat × Nat)) (hn : L.Nodup)
    (hL : ∀ x ∈ L, ∃ chr, genome[x.1]? = some chr ∧ x.2 ∈ occOf word chr) :
    L.length ≤ genome.occurrences word := by
  rw [occurrences_eq]
  refine length_le_of_nodup_sub L _ hn fun x hx => ?_
  obtain ⟨chr, hg, hs⟩ := hL x hx
  exact mem_occList word 0 genome x chr (Nat.zero_le _) (by rw [Nat.sub_zero]; exact hg) hs

/-! ## The check -/

open MapSpec.Fast in
-- the last chromosome starting at or before `p` (binary search over `offs`; `inChrom` checks the answer)
def chromGo (offs : Array Nat) (p : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo + 1 < hi then
      let mid := (lo + hi) / 2
      if offs[mid]! ≤ p then chromGo offs p f mid hi else chromGo offs p f lo mid
    else lo

def chromAt (offs : Array Nat) (p : Nat) : Nat := chromGo offs p 64 0 offs.size

-- whole-genome place `p` starts a seed-long window inside chromosome `chromAt offs p`
def inChrom (offs ns : Array Nat) (p : Nat) : Bool :=
  chromAt offs p < ns.size && offs[chromAt offs p]! ≤ p && p + seedLength ≤ offs[chromAt offs p]! + ns[chromAt offs p]!

-- the places of the seed `R[s, s+25)` in the whole packed genome, as `16 · place` (the router's lookup)
def seedPlaces (pk : MapSpec.Fast.PkMz) (R : ByteArray) (s : Nat) : Array Nat :=
  MapSpec.Fast.mzLookSP pk.1 pk.2 R s 0 (MapSpec.Fast.mzPrep pk.1 (MapSpec.Fast.seedHashAt R s))

-- how many of them lie inside a chromosome
def seedCount (pk : MapSpec.Fast.PkMz) (offs ns : Array Nat) (R : ByteArray) (s : Nat) : Nat :=
  (seedPlaces pk R s).toList.countP fun e => inChrom offs ns (e / 16)

-- the grid seeds of the mate (starts `0, 25, 50, …`) that lie inside chromosomes at least `gaveUpRepeats` times
def repeatSeeds (pk : MapSpec.Fast.PkMz) (offs ns : Array Nat) (R : ByteArray) : List Nat :=
  ((List.range (R.size / seedLength)).filter fun j => gaveUpRepeats ≤ seedCount pk offs ns R (seedLength * j)).map
    (seedLength * ·)

-- the mate has at least `gaveUpSeeds` repeat grid seeds
def repeatMate (pk : MapSpec.Fast.PkMz) (offs ns : Array Nat) (R : ByteArray) : Bool :=
  gaveUpSeeds ≤ (repeatSeeds pk offs ns R).length

/-! ## Soundness -/

theorem decodeRead_getElem? (B : ByteArray) (k : Nat) (hk : k < B.size) :
    (decodeRead B)[k]? = some (Char.ofNat (B.get! k).toNat) := by
  have h : B.get! k = B[k] := by simp [ByteArray.get!, hk]; rfl
  simp only [decodeRead, Bridge.byteArray_toList, List.getElem?_map, Array.getElem?_toList, h]
  rw [Array.getElem?_eq_getElem hk]; rfl

theorem decodeRead_length (B : ByteArray) : (decodeRead B).length = B.size := by
  simp [decodeRead, Bridge.byteArray_toList]

-- the place of `p` as `(chromosome, start)`
def placeOf (offs : Array Nat) (p : Nat) : Nat × Nat := (chromAt offs p, p - offs[chromAt offs p]!)

theorem placeOf_nodup (offs ns : Array Nat) : ∀ F : List Nat, F.Pairwise (· < ·) →
    (∀ p ∈ F, inChrom offs ns p = true) → (F.map (placeOf offs)).Nodup
  | [], _, _ => List.nodup_nil
  | a :: t, hs, hin => by
    rw [List.pairwise_cons] at hs
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, placeOf_nodup offs ns t hs.2 fun p hp => hin p (List.mem_cons_of_mem _ hp)⟩
    obtain ⟨p, hp, he⟩ := List.mem_map.mp hm
    have ha := hin a List.mem_cons_self
    have hpi := hin p (List.mem_cons_of_mem _ hp)
    have hlt := hs.1 p hp
    simp only [inChrom, Bool.and_eq_true, decide_eq_true_eq] at ha hpi
    simp only [placeOf, Prod.mk.injEq] at he
    rw [he.1] at he
    omega

/-- One seed: `gaveUpRepeats` counted places make it occur at least `gaveUpRepeats` times. -/
theorem seed_sound {ix : MapSpec.Mz.MzIdx} {G : MapSpec.Fast.PGen} {offs ns : Array Nat} {genome : Genome}
    (hchk : MapSpec.Mz.check2P ix G = true)
    (hslice : ∀ (c : Nat) (chr : Chromosome), genome[c]? = some chr →
      offs[c]! + chr.seq.length ≤ (decodeRead (MapSpec.Mz.unpack G)).length ∧
      chr.seq = ((decodeRead (MapSpec.Mz.unpack G)).drop offs[c]!).take chr.seq.length)
    (hchr : ∀ c, c < ns.size → ∃ chr : Chromosome, genome[c]? = some chr ∧ chr.seq.length = ns[c]!)
    (R : ByteArray) (s : Nat) (hsR : s + 25 ≤ R.size)
    (hcnt : gaveUpRepeats ≤ seedCount (ix, G) offs ns R s) :
    gaveUpRepeats ≤ genome.occurrences (((decodeRead R).drop s).take seedLength) := by
  have hc : MapSpec.Mz.check ix (MapSpec.Mz.unpack G) = true := by
    rw [← MapSpec.Mz.check2_eq, ← MapSpec.Mz.check2P_eq (MapSpec.Mz.rep_unpack G) ix]; exact hchk
  -- the counted places
  let H := (MapSpec.Mz.lookupSeed ix (MapSpec.Mz.unpack G) R s).toList
  let F := H.filter (inChrom offs ns)
  have hcount : seedCount (ix, G) offs ns R s = F.length := by
    unfold seedCount seedPlaces
    simp only
    rw [MapSpec.Fast.mzLookSP_eq (MapSpec.Mz.rep_unpack G), MapSpec.Fast.mzLookS_eq, Array.toList_map,
      List.countP_map, List.countP_eq_length_filter]
    congr 2
    funext p
    simp [MapSpec.Fast.anc]
  rw [hcount] at hcnt
  have hsorted : F.Pairwise (· < ·) := (MapSpec.Mz.lookupSeed_sorted hc R s).filter _
  have hinF : ∀ p ∈ F, inChrom offs ns p = true := fun p hp => (List.mem_filter.mp hp).2
  have hnd := placeOf_nodup offs ns F hsorted hinF
  -- each counted place is an occurrence
  let word := ((decodeRead R).drop s).take seedLength
  have hw : word.length = 25 := by
    show (((decodeRead R).drop s).take 25).length = 25
    simp [decodeRead_length]; omega
  have hocc : ∀ x ∈ F.map (placeOf offs), ∃ chr, genome[x.1]? = some chr ∧ x.2 ∈ occOf word chr := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    have hpH := (List.mem_filter.mp hp).1
    have hin := hinF p hp
    obtain ⟨hpU, heq⟩ := (MapSpec.Mz.lookupSeed_mem hc R s p).mp hpH
    simp only [inChrom, Bool.and_eq_true, decide_eq_true_eq] at hin
    obtain ⟨⟨hcn, hop⟩, hend⟩ := hin
    show ∃ chr, genome[chromAt offs p]? = some chr ∧ p - offs[chromAt offs p]! ∈ occOf word chr
    generalize chromAt offs p = c at hcn hop hend ⊢
    obtain ⟨chr, hg, hlen⟩ := hchr c hcn
    obtain ⟨hfit, hseq⟩ := hslice c chr hg
    refine ⟨chr, hg, ?_⟩
    unfold occOf
    rw [List.mem_filter, List.mem_range, hw]
    have hq : MapSpec.Mz.q = 25 := rfl
    have hsl : seedLength = 25 := rfl
    rw [hsl] at hend
    refine ⟨by omega, ?_⟩
    have hwin : (chr.seq.drop (p - offs[c]!)).take 25 = word := by
      have hU := decodeRead_length (MapSpec.Mz.unpack G)
      apply List.ext_getElem?
      intro i
      show _ = (((decodeRead R).drop s).take 25)[i]?
      rw [List.getElem?_take, List.getElem?_take, List.getElem?_drop, List.getElem?_drop]
      split
      · rename_i hi
        rw [hseq, List.getElem?_take]
        simp only [show p - offs[c]! + i < chr.seq.length from by omega, ↓reduceIte]
        rw [List.getElem?_drop,
          show offs[c]! + (p - offs[c]! + i) = p + i by omega,
          decodeRead_getElem? _ _ (by omega), decodeRead_getElem? _ _ (by omega), heq i (by rw [hq]; omega)]
      · rfl
    simp [hwin]
  have hle := count_le_occurrences genome word (F.map (placeOf offs)) hnd hocc
  rw [List.length_map] at hle
  exact Nat.le_trans hcnt hle

/-- **The check is sound**: a mate that `repeatMate` flags has `gaveUpSeeds` non-overlapping seeds, each
occurring at least `gaveUpRepeats` times. -/
theorem repeatMate_sound {ix : MapSpec.Mz.MzIdx} {G : MapSpec.Fast.PGen} {offs ns : Array Nat} {genome : Genome}
    (hchk : MapSpec.Mz.check2P ix G = true)
    (hslice : ∀ (c : Nat) (chr : Chromosome), genome[c]? = some chr →
      offs[c]! + chr.seq.length ≤ (decodeRead (MapSpec.Mz.unpack G)).length ∧
      chr.seq = ((decodeRead (MapSpec.Mz.unpack G)).drop offs[c]!).take chr.seq.length)
    (hchr : ∀ c, c < ns.size → ∃ chr : Chromosome, genome[c]? = some chr ∧ chr.seq.length = ns[c]!)
    (R : ByteArray) (h : repeatMate (ix, G) offs ns R = true) : genome.RepeatWitness (decodeRead R) := by
  unfold repeatMate at h
  simp only [decide_eq_true_eq] at h
  have hsl : seedLength = 25 := rfl
  refine ⟨(repeatSeeds (ix, G) offs ns R).take gaveUpSeeds, by simp; omega, ?_, ?_⟩
  · refine List.Pairwise.sublist (List.take_sublist _ _) ?_
    unfold repeatSeeds
    rw [List.pairwise_map]
    exact (List.pairwise_lt_range.filter _).imp fun {a b} hab => by rw [hsl]; omega
  · intro start hm
    have hm' := List.mem_of_mem_take hm
    unfold repeatSeeds at hm'
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hm'
    obtain ⟨hjr, hjc⟩ := List.mem_filter.mp hj
    rw [List.mem_range] at hjr
    simp only [decide_eq_true_eq] at hjc
    have hsR : seedLength * j + 25 ≤ R.size := by
      rw [hsl] at hjr ⊢
      have := Nat.lt_div_iff_mul_lt (by decide : 0 < 25) |>.mp hjr
      omega
    exact ⟨by rw [decodeRead_length, hsl]; rw [hsl] at hsR; exact hsR,
      seed_sound hchk hslice hchr R _ hsR hjc⟩

/-! ## Many places: a mate's checked hits at `gaveUpPlaces` distinct placements (PROTOTYPE) -/

-- the distinct elements of `l` after `acc` (newest first), stopping once `k` are collected
def distinctGo {α : Type} [DecidableEq α] (k : Nat) : List α → List α → List α
  | acc, [] => acc
  | acc, x :: xs => if k ≤ acc.length then acc else if x ∈ acc then distinctGo k acc xs else distinctGo k (x :: acc) xs

theorem distinctGo_spec {α : Type} [DecidableEq α] (k : Nat) : ∀ (l acc : List α), acc.Nodup →
    (distinctGo k acc l).Nodup ∧ ∀ y ∈ distinctGo k acc l, y ∈ acc ∨ y ∈ l
  | [], acc, h => ⟨h, fun y hy => .inl hy⟩
  | x :: xs, acc, h => by
    unfold distinctGo
    split
    · exact ⟨h, fun y hy => .inl hy⟩
    · split
      · obtain ⟨h1, h2⟩ := distinctGo_spec k xs acc h
        exact ⟨h1, fun y hy => (h2 y hy).imp id (List.mem_cons_of_mem _)⟩
      · rename_i hx
        obtain ⟨h1, h2⟩ := distinctGo_spec k xs (x :: acc) (List.nodup_cons.mpr ⟨hx, h⟩)
        refine ⟨h1, fun y hy => ?_⟩
        rcases h2 y hy with h | h
        · rcases List.mem_cons.mp h with rfl | h
          · exact .inr List.mem_cons_self
          · exact .inl h
        · exact .inr (List.mem_cons_of_mem _ h)

-- the placements of the hits scoring at least `bound` (up to `gaveUpPlaces` distinct ones)
def placesOf (bound : Int) (l : List (MapSpec.Placement × Int)) : List Placement :=
  distinctGo gaveUpPlaces [] ((l.filter fun x => decide (bound ≤ x.2)).map fun x => Bridge.newPlacement x.1)

-- at least `gaveUpPlaces` distinct placements score at least `bound`
def manyHits (bound : Int) (l : List (MapSpec.Placement × Int)) : Bool :=
  gaveUpPlaces ≤ (placesOf bound l).length

/-- **Many places**: hits that are alignments give `ManyPlaces` when `manyHits` holds. -/
theorem manyHits_sound {genome : Genome} {m : Read} {bound : Int} {l : List (MapSpec.Placement × Int)}
    (hl : ∀ x ∈ l, ∃ a : GenomicAlignment genome m, a.placement = Bridge.newPlacement x.1 ∧ a.score = x.2)
    (h : manyHits bound l = true) : genome.ManyPlaces m bound := by
  unfold manyHits at h
  simp only [decide_eq_true_eq] at h
  obtain ⟨hn, hm⟩ := distinctGo_spec gaveUpPlaces
    ((l.filter fun x => decide (bound ≤ x.2)).map fun x => Bridge.newPlacement x.1) [] List.nodup_nil
  refine ⟨placesOf bound l, hn, h, fun p hp => ?_⟩
  rcases hm p hp with h0 | h0
  · simp at h0
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h0
    obtain ⟨hxl, hxb⟩ := List.mem_filter.mp hx
    simp only [decide_eq_true_eq] at hxb
    obtain ⟨a, ha, hs⟩ := hl x hxl
    exact ⟨a, ha, by rw [hs]; exact hxb⟩

open MapSpec MapSpec.Fast AlignmentSpec in
/-- A checked hit is an alignment at its placement, with its score. -/
theorem hit_alignment {genome : Genome} {m : Read} {T : Int} {pgs : Array PGen}
    (hg : GenomeBytes (pgs.map Mz.unpack) (Bridge.oldGenome genome)) {R : ByteArray}
    (hr : Encodes R m) {x : MapSpec.Placement × Int}
    (hx : x ∈ hitsBoth sc0 T (Bridge.oldGenome genome) m) :
    ∃ a : GenomicAlignment genome m, a.placement = Bridge.newPlacement x.1 ∧ a.score = x.2 := by
  obtain ⟨a, ha⟩ := Report.alignment_of_cigar (LastResort.runsIx_ok hg hr hx)
  exact ⟨a, congrArg MateReport.placement ha, congrArg MateReport.score ha⟩

#print axioms repeatMate_sound
#print axioms manyHits_sound
#print axioms hit_alignment

/-! ## Compiled form: stop a seed's lookup after `gaveUpRepeats` places -/

-- one seed of `repeatMate`: with a word prep, look up only the first `gaveUpRepeats` places (`lookupPWk`); a shorter
-- result is the whole result (`lookupPWk_small`), and `gaveUpRepeats` counted places among the first ones suffice
def seedRepF (pk : MapSpec.Fast.PkMz) (offs ns : Array Nat) (R : ByteArray) (s : Nat) : Bool :=
  let p := MapSpec.Fast.mzPrep pk.1 (MapSpec.Fast.seedHashAt R s)
  if p.ok then
    let a := MapSpec.Fast.lookupPWk pk.1 pk.2 R s p 0 0 gaveUpRepeats
    if a.size < gaveUpRepeats then false
    else if gaveUpRepeats ≤ (a.extract 0 gaveUpRepeats).toList.countP (fun e => inChrom offs ns (e / 16)) then true
    else decide (gaveUpRepeats ≤ seedCount pk offs ns R s)
  else decide (gaveUpRepeats ≤ seedCount pk offs ns R s)

theorem seedRepF_eq (pk : MapSpec.Fast.PkMz) (offs ns : Array Nat) (R : ByteArray) (s : Nat) :
    seedRepF pk offs ns R s = decide (gaveUpRepeats ≤ seedCount pk offs ns R s) := by
  unfold seedRepF
  simp only []
  split
  · rename_i hok
    have hsp : seedPlaces pk R s = MapSpec.Fast.lookupPW pk.1 pk.2 R s
        (MapSpec.Fast.mzPrep pk.1 (MapSpec.Fast.seedHashAt R s)) 0 0 := by
      unfold seedPlaces MapSpec.Fast.mzLookSP; rw [if_pos hok]
    split
    · rename_i hs
      have hfull := MapSpec.Fast.lookupPWk_small _ _ _ _ _ _ _ _ hs
      have hle : seedCount pk offs ns R s < gaveUpRepeats := by
        unfold seedCount
        rw [hsp, ← hfull]
        exact Nat.lt_of_le_of_lt (List.countP_le_length) (by simpa using hs)
      simp; omega
    · split
      · rename_i hc
        have hpre := MapSpec.Fast.lookupPWk_extract pk.1 pk.2 R s
          (MapSpec.Fast.mzPrep pk.1 (MapSpec.Fast.seedHashAt R s)) 0 0 gaveUpRepeats
        rw [hpre] at hc
        have hsub : ((MapSpec.Fast.lookupPW pk.1 pk.2 R s
            (MapSpec.Fast.mzPrep pk.1 (MapSpec.Fast.seedHashAt R s)) 0 0).extract 0 gaveUpRepeats).toList.Sublist
            (seedPlaces pk R s).toList := by
          rw [hsp, Array.toList_extract]
          simpa [List.extract] using List.take_sublist gaveUpRepeats _
        have := hsub.countP_le (p := fun e => inChrom offs ns (e / 16))
        unfold seedCount
        simp only [decide_eq_true_eq, Bool.true_eq, decide_eq_true_iff]; omega
      · rfl
  · rfl

def repeatMateF (pk : MapSpec.Fast.PkMz) (offs ns : Array Nat) (R : ByteArray) : Bool :=
  gaveUpSeeds ≤ (List.range (R.size / seedLength)).countP fun j => seedRepF pk offs ns R (seedLength * j)

@[csimp] theorem repeatMate_eqF : @repeatMate = @repeatMateF := by
  funext pk offs ns R
  unfold repeatMate repeatMateF repeatSeeds
  simp only [seedRepF_eq, List.length_map, List.countP_eq_length_filter]

#print axioms repeatMate_eqF

end Spec.GaveUp

namespace Spec.GaveUp

/-! ## Compiled `decodeRead`: one pass over the bytes from the end, no intermediate `List UInt8` -/

def decodeReadF (B : ByteArray) : Read := B.data.foldr (fun b acc => Char.ofNat b.toNat :: acc) []

@[csimp] theorem decodeRead_eqF : @decodeRead = @decodeReadF := by
  funext B
  unfold decodeRead decodeReadF
  rw [Bridge.byteArray_toList, ← Array.foldr_toList]
  generalize B.data.toList = l
  induction l with
  | nil => rfl
  | cons x xs ih => rw [List.foldr_cons, List.map_cons, ih]

#print axioms decodeRead_eqF

end Spec.GaveUp

/-! ## Compiled second look: mate 1's hits enumerated until `gaveUpPlaces` distinct placements are seen -/

namespace Spec.GaveUp

theorem distinctGo_stop {α : Type} [DecidableEq α] (k : Nat) (acc l : List α) (h : k ≤ acc.length) :
    distinctGo k acc l = acc := by
  cases l <;> simp [distinctGo, h]

theorem distinctGo_append {α : Type} [DecidableEq α] (k : Nat) : ∀ (p s acc : List α),
    distinctGo k acc (p ++ s) = distinctGo k (distinctGo k acc p) s
  | [], _, _ => rfl
  | x :: p, s, acc => by
    simp only [List.cons_append, distinctGo]
    split
    · rename_i h; rw [distinctGo_stop k acc s h]
    · split <;> exact distinctGo_append k p s _

/-- The inner walk: hits `h d` of each `d`, stopping (`none`) once `k` distinct `g`-values are seen. -/
def walkIn {δ β P : Type} [DecidableEq P] (k : Nat) (g : β → Option P) (h : δ → List β) :
    List δ → List P → Array β → Option (List P × Array β)
  | [], acc, out => some (acc, out)
  | d :: ds, acc, out =>
    let ys := h d
    let acc' := distinctGo k acc (ys.filterMap g)
    if k ≤ acc'.length then none else walkIn k g h ds acc' (out ++ ys.toArray)

theorem walkIn_eq {δ β P : Type} [DecidableEq P] (k : Nat) (g : β → Option P) (h : δ → List β) :
    ∀ (ds : List δ) (acc : List P) (out : Array β), acc.length < k →
    walkIn k g h ds acc out =
      if k ≤ (distinctGo k acc ((ds.flatMap h).filterMap g)).length then none
      else some (distinctGo k acc ((ds.flatMap h).filterMap g), out ++ (ds.flatMap h).toArray)
  | [], acc, out, hacc => by simp [walkIn, distinctGo, show ¬ k ≤ acc.length by omega]
  | d :: ds, acc, out, hacc => by
    simp only [walkIn, List.flatMap_cons, List.filterMap_append, distinctGo_append]
    split
    · rename_i hk; rw [distinctGo_stop k _ _ hk, if_pos hk]
    · rename_i hk
      rw [walkIn_eq k g h ds _ _ (by omega)]
      simp [Array.append_assoc]

/-- The outer walk: each `a` prepared once (`prep`), then its inner list walked. -/
def walkOut {α σ δ β P : Type} [DecidableEq P] (k : Nat) (g : β → Option P) (prep : α → σ) (inn : σ → List δ)
    (h : σ → δ → List β) : List α → List P → Array β → Option (List P × Array β)
  | [], acc, out => some (acc, out)
  | a :: as, acc, out =>
    let s := prep a
    match walkIn k g (h s) (inn s) acc out with
    | none => none
    | some (acc', out') => walkOut k g prep inn h as acc' out'

theorem walkOut_eq {α σ δ β P : Type} [DecidableEq P] (k : Nat) (g : β → Option P) (prep : α → σ)
    (inn : σ → List δ) (h : σ → δ → List β) :
    ∀ (as : List α) (acc : List P) (out : Array β), acc.length < k →
    walkOut k g prep inn h as acc out =
      let L := as.flatMap fun a => (inn (prep a)).flatMap (h (prep a))
      if k ≤ (distinctGo k acc (L.filterMap g)).length then none
      else some (distinctGo k acc (L.filterMap g), out ++ L.toArray)
  | [], acc, out, hacc => by simp [walkOut, distinctGo, show ¬ k ≤ acc.length by omega]
  | a :: as, acc, out, hacc => by
    simp only [walkOut, List.flatMap_cons, List.filterMap_append, distinctGo_append]
    rw [walkIn_eq k g _ _ acc out hacc]
    by_cases hk : k ≤ (distinctGo k acc (((inn (prep a)).flatMap (h (prep a))).filterMap g)).length
    · simp only [if_pos hk]; rw [distinctGo_stop k _ _ hk, if_pos hk]
    · simp only [if_neg hk]
      rw [walkOut_eq k g prep inn h as _ _ (by omega)]
      simp [Array.append_assoc]

end Spec.GaveUp

namespace Spec.GaveUp
open MapSpec MapSpec.Fast

/-- One diagonal of `hitsCK` (shapes given). -/
@[inline] def skBody (K : RP) (R : ByteArray) (pgs2 : Array PGen) (c lim : Nat) (acc : List (Array Nat))
    (us : List Nat) (Ls : Nat) (shs : List (Int × Int)) (D : Nat) : List (Window × Nat) :=
  if kfiltV K R pgs2[c]! acc us Ls lim (initP lim) D then
    shs.filterMap fun sh =>
      if 0 ≤ dst R.size D sh ∧ 0 ≤ wlen R.size sh then
        let k := kerHKG R K pgs2 pgs2 c (dst R.size D sh).toNat (wlen R.size sh).toNat lim
        if k ≤ lim then some (⟨c, (dst R.size D sh).toNat, (wlen R.size sh).toNat⟩, k) else none
      else none
  else []

/-- `hitsSK` by `walkOut`: chromosome by chromosome, diagonal by diagonal, stopping at `k` distinct `g`-values. -/
def walkSK {P : Type} [DecidableEq P] (k : Nat) (g : Window × Nat → Option P) (ix : PkMz) (G : ByteArray)
    (offs : Array Nat) (pgs2 : Array PGen) (n t lim : Nat) (Rs : ByteArray) (acc0 : List P)
    (out0 : Array (Window × Nat)) : Option (List P × Array (Window × Nat)) :=
  let m := Rs.size / 25
  let Ls := Rs.size / m
  let K := packRP Rs
  let ps := prepG ix Rs m Ls
  let J := (ordG (ps.map (LookG.size ix)) m).take (sbound lim + 1)
  let lk := J.map fun j => (j, LookG.look ix G Rs (j * Ls) (Rs.size - j * Ls) ps[j]!)
  let us := unseen m J
  let shs := shapesT lim
  walkOut k g (fun c => (c, slicesAt lk Rs.size Ls offs[c]! (GRead.size pgs2[t + c]!)))
    (fun s => if s.2.all fun a => a.isEmpty then [] else diags s.2)
    (fun s D => skBody K Rs pgs2 (t + s.1) lim s.2 us Ls shs D) (List.range n) acc0 out0

theorem walkSK_eq {P : Type} [DecidableEq P] (k : Nat) (g : Window × Nat → Option P) (ix : PkMz) (G : ByteArray)
    (offs : Array Nat) (pgs2 : Array PGen) (n t lim : Nat) (Rs : ByteArray) (acc0 : List P)
    (out0 : Array (Window × Nat)) (hacc : acc0.length < k) :
    walkSK k g ix G offs pgs2 n t lim Rs acc0 out0 =
      if k ≤ (distinctGo k acc0 ((hitsSK ix G offs pgs2 n t lim Rs).filterMap g)).length then none
      else some (distinctGo k acc0 ((hitsSK ix G offs pgs2 n t lim Rs).filterMap g),
        out0 ++ (hitsSK ix G offs pgs2 n t lim Rs).toArray) := by
  unfold walkSK
  rw [walkOut_eq _ _ _ _ _ _ _ _ hacc]
  have e : ∀ L1 L2 : List (Window × Nat), L1 = L2 →
      (if k ≤ (distinctGo k acc0 (L1.filterMap g)).length then none
        else some (distinctGo k acc0 (L1.filterMap g), out0 ++ L1.toArray)) =
      (if k ≤ (distinctGo k acc0 (L2.filterMap g)).length then none
        else some (distinctGo k acc0 (L2.filterMap g), out0 ++ L2.toArray)) := by
    intro L1 L2 h; rw [h]
  apply e
  unfold hitsSK hitsCK
  simp only [shapesT_eq]
  congr 1
  funext c
  split
  · rename_i h; rw [diags_empty _ h]; rfl
  · rfl

theorem filterMap_of_map_filter {α β γ : Type} (f : α → β) (q : β → Bool) (r : β → γ) :
    ∀ l : List α, ((l.map f).filter q).map r = l.filterMap fun x => if q (f x) then some (r (f x)) else none
  | [] => rfl
  | x :: l => by
    simp only [List.map_cons, List.filter_cons, List.filterMap_cons]
    split <;> simp_all [filterMap_of_map_filter f q r l]

/-- `hitsX`, or `none` once its hits scoring `≥ req` reach `gaveUpPlaces` distinct placements (`hitsXS_none`,
`hitsXS_some`). -/
def hitsXS (req : Int) (c : Nat) (pk : PkMz) (offs : Array Nat) (pgs : Array PGen) (R : ByteArray) :
    Option (List (MapSpec.Placement × Int)) :=
  if fastT c R then
    let n := pgs.size
    let pgs2 := pgs ++ pgs
    let g := fun x : Window × Nat =>
      if decide (req ≤ -(x.2 : Int)) then some (Bridge.newPlacement (decB n x.1)) else none
    match walkSK gaveUpPlaces g pk ByteArray.empty offs pgs2 n 0 c R [] #[] with
    | none => none
    | some (acc, out) =>
      match walkSK gaveUpPlaces g pk ByteArray.empty offs pgs2 n n c (revCompK R) acc out with
      | none => none
      | some (_, out') => some (out'.toList.map fun x => (decB n x.1, -(x.2 : Int)))
  else some (LastResort.hitsX c pk offs pgs R)

theorem hitsXS_spec (req : Int) (c : Nat) (pk : PkMz) (offs : Array Nat) (pgs : Array PGen) (R : ByteArray) :
    (hitsXS req c pk offs pgs R = none → manyHits req (LastResort.hitsX c pk offs pgs R) = true) ∧
      (∀ l, hitsXS req c pk offs pgs R = some l → l = LastResort.hitsX c pk offs pgs R) := by
  unfold hitsXS
  split
  · rename_i hf
    have hX : LastResort.hitsX c pk offs pgs R =
        (hitsSK pk ByteArray.empty offs (pgs ++ pgs) pgs.size 0 c R ++
          hitsSK pk ByteArray.empty offs (pgs ++ pgs) pgs.size pgs.size c (revCompK R)).map
          fun x => (decB pgs.size x.1, -(x.2 : Int)) := by
      unfold LastResort.hitsX hitsKPF hitsAtKP; rw [if_pos hf]
    have hp : (0 : Nat) < gaveUpPlaces := by decide
    simp only []
    rw [walkSK_eq _ _ _ _ _ _ _ _ _ _ [] #[] hp]
    unfold manyHits placesOf
    rw [hX, filterMap_of_map_filter, List.filterMap_append, distinctGo_append]
    simp only [decide_eq_true_eq]
    generalize hA : hitsSK pk ByteArray.empty offs (pgs ++ pgs) pgs.size 0 c R = A
    generalize hB : hitsSK pk ByteArray.empty offs (pgs ++ pgs) pgs.size pgs.size c (revCompK R) = B
    generalize (fun x : Window × Nat =>
      if req ≤ -(x.2 : Int) then some (Bridge.newPlacement (decB pgs.size x.1)) else none) = g
    by_cases hk : gaveUpPlaces ≤ (distinctGo gaveUpPlaces [] (A.filterMap g)).length
    · rw [if_pos hk, distinctGo_stop _ _ _ hk]
      exact ⟨fun _ => (by simpa using hk), fun l hl => (by cases hl)⟩
    · rw [if_neg hk]
      simp only []
      rw [walkSK_eq _ _ _ _ _ _ _ _ _ _ _ _ (by omega), hB]
      by_cases hk2 : gaveUpPlaces ≤ (distinctGo gaveUpPlaces (distinctGo gaveUpPlaces [] (A.filterMap g))
          (B.filterMap g)).length
      · rw [if_pos hk2]
        exact ⟨fun _ => (by simpa using hk2), fun l hl => (by cases hl)⟩
      · rw [if_neg hk2]
        exact ⟨fun h => (by cases h), fun l hl => (by cases hl; simp)⟩
  · exact ⟨fun h => (by cases h), fun l hl => (by cases hl; rfl)⟩

#print axioms hitsXS_spec

end Spec.GaveUp
