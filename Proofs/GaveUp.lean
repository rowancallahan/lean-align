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

#print axioms repeatMate_sound

end Spec.GaveUp
