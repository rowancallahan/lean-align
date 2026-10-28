import Proofs.Bridge

/-! # The whole genome as one chromosome

The router runs on the packed genome as ONE sequence (`alignOne`: offsets `#[0]`, lengths `#[G.n]`),
so its seed loop does not pay per chromosome. Its answers are proved for `whole`, the genome
with one chromosome holding every letter; this file moves them back to the real genome.
Each real chromosome is a slice of `whole`'s one chromosome, so every alignment on the real genome
is an alignment on `whole`, shifted by where its chromosome starts: same letters, same path, same
score, and a proper pair stays proper. A bound over `whole` is therefore a bound over the genome. -/

namespace Spec.Whole

open Bridge

section slice
variable {genome : Genome} {name : String} {W : Read} {off : Nat → Nat}

-- shifted placement: chromosome 0 of `whole`, the same strand
def shift (off : Nat → Nat) (p : Placement) : Placement :=
  { p with chromosome := 0, start := off p.chromosome + p.start, stop := off p.chromosome + p.stop }

theorem reference_whole (q : Placement) (h0 : q.chromosome = 0) (hs : q.start ≤ q.stop)
    (he : q.stop ≤ W.length) :
    q.reference [⟨name, W⟩] = some ((W.drop q.start).take (q.stop - q.start)) := by
  unfold Placement.reference
  rw [h0]
  simp [hs, he]

theorem reference_shift
    (hslice : ∀ c chr, genome[c]? = some chr →
      off c + chr.seq.length ≤ W.length ∧ chr.seq = (W.drop (off c)).take chr.seq.length)
    {p : Placement} {ref : Read} (h : p.reference genome = some ref) :
    (shift off p).reference [⟨name, W⟩] = some ref := by
  unfold Placement.reference at h
  cases hc : genome[p.chromosome]? with
  | none => rw [hc] at h; cases h
  | some chr =>
    rw [hc] at h
    obtain ⟨hle, hseq⟩ := hslice _ _ hc
    dsimp only at h
    split at h
    · rename_i hp
      cases h
      rw [reference_whole _ rfl (by dsimp only [shift]; omega) (by dsimp only [shift]; omega)]
      dsimp only [shift]
      congr 1
      rw [hseq, List.drop_take, List.drop_drop, List.take_take]
      congr 1
      omega
    · cases h

-- every alignment on the genome is one on `whole`, shifted, with the same score
theorem alignment_shift
    (hslice : ∀ c chr, genome[c]? = some chr →
      off c + chr.seq.length ≤ W.length ∧ chr.seq = (W.drop (off c)).take chr.seq.length)
    {read : Read} (a : GenomicAlignment genome read) :
    ∃ b : GenomicAlignment [⟨name, W⟩] read, b.placement = shift off a.placement ∧ b.score = a.score :=
  ⟨⟨shift off a.placement, a.reference, reference_shift hslice a.fits, a.path⟩, rfl, rfl⟩

theorem isProper_shift {range : Nat × Nat} {slack : Nat} {m1 m2 : Read}
    (pair : PairAlignment genome m1 m2) (pair' : PairAlignment [⟨name, W⟩] m1 m2)
    (h1 : pair'.first.placement = shift off pair.first.placement)
    (h2 : pair'.second.placement = shift off pair.second.placement)
    (hp : pair.IsProper range slack) : pair'.IsProper range slack := by
  obtain ⟨lo, hi⟩ := range
  unfold PairAlignment.IsProper at hp ⊢
  rw [h1, h2]
  generalize pair.first.placement = p at *
  generalize pair.second.placement = q at *
  obtain ⟨c1, s1, e1, t1⟩ := p
  obtain ⟨c2, s2, e2, t2⟩ := q
  simp only [shift] at hp ⊢
  obtain ⟨rfl, hp⟩ := hp
  cases t1 <;> cases t2 <;> simp_all <;> omega

/-- **Answers about `whole` hold for the genome** (bounds-only answers: nothing found, uniqueness
unknown, which is all `answerOf` reports). -/
theorem correct_of_whole (insertSettings : InsertSettings) (m1 m2 : Read)
    (hslice : ∀ c chr, genome[c]? = some chr →
      off c + chr.seq.length ≤ W.length ∧ chr.seq = (W.drop (off c)).take chr.seq.length)
    (answer : PairAnswer) (hfound : answer.found = none) (huniq : answer.uniqueness = .unknown)
    (h : answer.Correct insertSettings [⟨name, W⟩] m1 m2) :
    answer.Correct insertSettings genome m1 m2 := by
  unfold PairAnswer.Correct at h ⊢
  refine ⟨fun _ hr => (by rw [hfound] at hr; cases hr), fun pair hp => ?_, (by rw [huniq]; trivial)⟩
  obtain ⟨a, ha, hsa⟩ := alignment_shift (name := name) hslice pair.first
  obtain ⟨b, hb, hsb⟩ := alignment_shift (name := name) hslice pair.second
  have := h.2.1 ⟨a, b⟩ (isProper_shift pair ⟨a, b⟩ ha hb hp)
  unfold PairAlignment.score at this ⊢
  simp only at this
  omega

end slice

/-! ## The packed genome: one view of all of it, and each chromosome a slice of it -/

section packed
open MapSpec MapSpec.Fast

-- `whole`: one chromosome, every letter of the packed genome
def wholeOf (G : PGen) : Spec.Genome := [⟨"", decodeRead (Mz.unpack G)⟩]

theorem cutOk_whole {G : PGen} (h0 : G.o = 0) : cutOk G #[0] #[G.n] = true := by
  simp [cutOk, h0]

theorem genomeBytes_whole (G : PGen) :
    GenomeBytes ((cutAll G #[0] #[G.n]).map Mz.unpack) (oldGenome (wholeOf G)) := by
  refine ⟨by simp [cutAll, oldGenome, wholeOf], fun c h1 h2 => ?_⟩
  have hc : c = 0 := by simp [cutAll] at h1; omega
  subst hc
  have hv : view G 0 G.n = G := rfl
  simp [cutAll, oldGenome, wholeOf, hv]
  exact encodes_decodeRead _

-- every chromosome checked against the per-chromosome views is a slice of `wholeOf G`
theorem slice_of_cut {G : PGen} {offs ns : Array Nat} {genome : Spec.Genome}
    (hcut : cutOk G offs ns = true)
    (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) (oldGenome genome)) :
    ∀ (c : Nat) (chr : Spec.Chromosome), genome[c]? = some chr →
      offs[c]! + chr.seq.length ≤ (decodeRead (Mz.unpack G)).length ∧
      chr.seq = ((decodeRead (Mz.unpack G)).drop offs[c]!).take chr.seq.length := by
  intro c chr hchr
  obtain ⟨hcg, rfl⟩ : ∃ h : c < genome.length, genome[c] = chr := List.getElem?_eq_some_iff.mp hchr
  have hsz := hg.1
  simp only [Array.size_map, oldGenome, List.length_map] at hsz
  have hc : c < ((cutAll G offs ns).map Mz.unpack).size := by simp only [Array.size_map]; omega
  have henc := hg.2 c hc (by simp [oldGenome]; omega)
  simp only [oldGenome, List.getElem_map] at henc
  have hcat := catOk_cut G offs ns hcut
  unfold catOk at hcat
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hcat
  obtain ⟨hle, hrun⟩ := hcat c hc
  rw [eqRun_spec] at hrun
  rw [getElem!_pos ((cutAll G offs ns).map Mz.unpack) c hc] at hle hrun
  have E := encodes_decodeRead (Mz.unpack G)
  have hlen := henc.1
  refine ⟨by rw [← E.1, ← hlen]; exact hle, ?_⟩
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop]; rw [← E.1]; omega
  · intro i h1 h2
    rw [List.getElem_take, List.getElem_drop, ← Char.toNat_inj, ← henc.2 i h1,
      ← E.2 _ (by rw [← E.1]; omega), hrun i (by omega), Nat.zero_add]

end packed

end Spec.Whole

#print axioms Spec.Whole.correct_of_whole
#print axioms Spec.Whole.slice_of_cut
