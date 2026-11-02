import Proofs.Build
import Proofs.IndexBuild

/-! # The index builder is right: `buildIndex g ≠ ByteArray.empty` when the genome fits

`Fits g`: the letters `N` of all chromosomes with the block bytes ahead of the slots fit the
`UInt32` bucket offsets (`N + ⌈wBytes N / 5⌉ < 2^32`, about 4.07e9 letters), and there are fewer than
`2^64` chromosomes. Then the saved index loads back (`loadIndex_saveIndex`), the genome checks
pass on what it loads to (`genomeChecks`), and the loaded minimizer index passes the checker when
the built one does (`check2_sh`). -/

namespace Spec.IndexFinal

open MapSpec MapSpec.Mz Spec.Pack Spec.SaveLoad Spec.Shift Spec.Build
open MapSpec.Fast (PGen)

/-- Letters in all chromosomes. -/
def letters (g : GenomeFile) : Nat := (g.toList.map (·.2.size)).sum

/-- The genome fits the index format. -/
def Fits (g : GenomeFile) : Prop := letters g + (wBytes (letters g) + 4) / 5 < 2 ^ 32 ∧ g.size < 2 ^ 64

theorem letters_eq (g : GenomeFile) : (catG g).length = letters g := by
  unfold catG letters; rw [catL_length]; simp; rfl

theorem rd4_eq (B : ByteArray) (j : Nat) (h : j + 3 < B.size) :
    rd4 B j = (B.get! j).toUInt64 ||| ((B.get! (j + 1)).toUInt64 <<< 8) |||
      ((B.get! (j + 2)).toUInt64 <<< 16) ||| ((B.get! (j + 3)).toUInt64 <<< 24) := by
  unfold rd4; rw [dif_pos h]
  simp only [bget, ByteArray.getElem_eq_getElem_data]
  rw [getElem!_pos B.data j (by show j < B.size; omega), getElem!_pos B.data (j + 1) (by show j + 1 < B.size; omega),
    getElem!_pos B.data (j + 2) (by show j + 2 < B.size; omega), getElem!_pos B.data (j + 3) (by show j + 3 < B.size; omega)]

theorem unpack_congr (P P' : PGen) (hn : P'.n = P.n) (h : ∀ i, P'.get i = P.get i) : unpack P' = unpack P := by
  unfold unpack; rw [hn]; congr 1; exact Array.map_congr_left (fun i _ => h i)


theorem offL_le : ∀ (L : List ByteArray) (m x : Nat), x ∈ offL m L → x ≤ m + (catL L).length
  | [], _, _, h => by simp [offL] at h
  | b :: r, m, x, h => by
    simp only [offL, List.mem_cons] at h
    rcases h with rfl | h
    · omega
    · have := offL_le r _ x h; simp only [catL, List.length_append, dl_len]; omega

theorem size_le_catL : ∀ (L : List ByteArray) (b : ByteArray), b ∈ L → b.size ≤ (catL L).length
  | [], _, h => by simp at h
  | c :: r, b, h => by
    simp only [List.mem_cons] at h
    simp only [catL, List.length_append, dl_len]
    rcases h with rfl | h
    · omega
    · have := size_le_catL r b h; omega

/-- **Built, saved, loaded: the index passes the checks** (given the minimizer check on the built
index, `check3P`, which is the other half). -/
theorem indexOk_loaded (g : GenomeFile) (hf : Fits g)
    (h3 : check3P (buildLoaded g).1 (buildLoaded g).2.1 4 = true) :
    ∃ L', loadIndex (saveIndex (buildLoaded g)) = some L' ∧ indexOk g L' = true := by
  obtain ⟨hfit, hgs⟩ := hf
  have hNl := letters_eq g
  generalize hN : letters g = N at hfit hNl
  have hN32 : (catG g).length < 2 ^ 32 := by omega
  obtain ⟨Pn, Po, Praw, Pw, Pex⟩ := packAll_spec g hN32
  have BO := buildMz_ok g hN32
  generalize hG : Index.packAll (g.map (·.2)) = G at Pn Po Praw Pw Pex BO
  generalize hix : Index.buildMz (g.map (·.2)) G = ix at BO
  have hL : buildLoaded g = (ix, G, Index.offsOf (g.map (·.2)), (g.map (·.2)).map (·.size)) := by
    rw [← hix, ← hG]; rfl
  rw [hL] at h3 ⊢
  simp only at h3
  have GC := genomeChecks g
  generalize ho : Index.offsOf (g.map (·.2)) = offs at GC
  generalize hns : (g.map (·.2)).map (·.size) = ns at GC
  rw [hNl] at Pn Pw Pex BO
  have hsw := BO.sw
  have hB := BO.B26
  -- sizes
  generalize hT : getU32 ix.offs (2 ^ ix.B) = T at BO
  have hTN : T ≤ N := by rw [← hT]; exact BO.tot
  have hp1 := pad_size G.w ix.sw
  have hp1m := pad_mod G.w ix.sw (by omega)
  have hm5 : ix.sw * mOf ix G = (Index.pad G.w ix.sw).size := by
    unfold mOf; have := Nat.div_add_mod (Index.pad G.w ix.sw).size ix.sw; omega
  generalize hm : mOf ix G = m at hm5
  rw [hsw] at hp1 hp1m hm5
  have hmw : m ≤ (wBytes N + 4) / 5 := by
    have : (5 - G.w.size % 5) % 5 ≤ 4 := by omega
    omega
  have hfitT : T + m < 2 ^ 32 := by omega
  have hsl : ix.sl.size = 5 * T := by rw [← hT]; exact BO.sl
  have hp2 := pad_size (Index.pad G.w ix.sw ++ ix.sl) 4
  have hp2m := pad_mod (Index.pad G.w ix.sw ++ ix.sl) 4 (by omega)
  have hob : 4 * obOf ix G = (Index.pad (Index.pad G.w ix.sw ++ ix.sl) 4).size := by unfold obOf; omega
  generalize hobd : obOf ix G = ob at hob
  simp only [ByteArray.size_append] at hp2 hp2m
  rw [hsw] at hp2 hp2m hob
  have hbig : (bigOf ix G).size = 4 * ob + 4 * (2 ^ ix.B + 1) := by
    unfold bigOf; rw [putOffs_eq, (putOffs_spec _ _ _ _).1, BO.sz, hsw]; omega
  have hbig64 : (bigOf ix G).size < 2 ^ 64 := by
    rw [hbig, hB]; rw [hp1, hsl] at hp2
    have : (4 - (G.w.size + (5 - G.w.size % 5) % 5 + 5 * T) % 4) % 4 ≤ 3 := by omega
    have : (5 - G.w.size % 5) % 5 ≤ 4 := by omega
    unfold wBytes at Pw; split at Pw <;> omega
  have hob64 : ob < 2 ^ 64 := by omega
  -- the chromosome table
  have hoffsz : offs.size = g.size := by rw [← ho, offsOf_eq]; simp [offL_length]
  have hnssz : ns.size = g.size := by rw [← hns]; simp
  have hoffle : ∀ x ∈ offs, x < 2 ^ 64 := by
    intro x hx
    rw [← ho, offsOf_eq, Array.mem_toArray] at hx
    have := offL_le _ 0 x hx
    have : (catL (g.map (·.2)).toList).length = N := hNl
    omega
  have hnsle : ∀ x ∈ ns, x < 2 ^ 64 := by
    intro x hx
    rw [← hns, Array.mem_map] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    have := size_le_catL (g.map (·.2)).toList b (by simpa using hb)
    have : (catL (g.map (·.2)).toList).length = N := hNl
    omega
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16⟩ := BO.small
  have hfits : MzFits ix (obOf ix G) := ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16,
    by rw [hobd]; exact hob64, by omega, by have := BO.runsSz; omega, fun x hx => by have := BO.runsLe x hx; omega⟩
  have LS := loadIndex_saveIndex ix G offs ns hfits (by omega) (by omega) (by omega) (by omega) hoffle (by omega)
    hnsle hbig64
  refine ⟨_, LS, ?_⟩
  have PW := save_w ix G offs ns
  have SL := save_sl ix G offs ns (by omega)
  have SO := save_offs ix G offs ns
  have PBg := pre_big_save ix G offs ns
  have PP : Pre (Index.pad G.w ix.sw ++ ix.sl) (saveIndex (ix, G, offs, ns)) :=
    (pre_pad _ 4).trans ((pre_pad2_big ix G).trans PBg)
  rw [hm] at SL SO
  rw [hobd] at SO ⊢
  generalize saveIndex (ix, G, offs, ns) = S at PW SL SO PBg PP ⊢
  -- the packed genome read from `S`
  have hraw : ∀ i, i < G.n → ({ G with w := S } : PGen).raw i = G.raw i := fun i hi =>
    raw_congr G _ i rfl (PW.2 _ (Praw i hi).2.1) (PW.2 _ (Praw i hi).2.2)
  have hget : ∀ i, ({ G with w := S } : PGen).get i = G.get i := by
    intro i; unfold PGen.get
    split
    · rename_i h; rw [hraw _ (by simp only [Po, Nat.zero_add] at h ⊢; exact h)]
    · rfl
  obtain ⟨hcut, hchr⟩ := GC { G with w := S } (Pn.trans hNl.symm) Po (fun i hi => (hraw i hi).trans (Praw i hi).1)
  -- the minimizer index read from `S`
  have hsz5 : (Index.pad G.w ix.sw ++ ix.sl).size = 5 * m + 5 * T := by
    simp only [ByteArray.size_append]; rw [hsw, ← hm5, hsl]
  have H : Shifted ix S ob m T := by
    refine ⟨BO.sz, BO.ob0, fun b hb => ?_, fun b hb => ?_, hfitT, fun t ht => ?_, ?_⟩
    · rw [SO b (by rw [BO.sz]; omega), Nat.mod_eq_of_lt]
      have := BO.le b hb; rw [hT] at this; omega
    · have := BO.le b hb; rw [hT] at this; exact this
    · have e : ∀ k, k < 5 → S.get! (5 * (t + m) + k) = ix.sl.get! (5 * t + k) := by
        intro k hk
        have := SL (5 * t + k) (by omega)
        rw [hsw, show 5 * m + (5 * t + k) = 5 * (t + m) + k by omega] at this
        exact this
      have hS1 : 5 * (t + m) + 3 < S.size := by have := PP.1; omega
      unfold rdSlot
      rw [hsw]
      simp only [show ¬ (5 : Nat) = 4 by decide, ite_false, ite_true]
      rw [rd4_eq _ _ hS1, rd4_eq _ _ (by omega)]
      unfold byteAt
      have e0 := e 0 (by omega); have e1 := e 1 (by omega); have e2 := e 2 (by omega)
      have e3 := e 3 (by omega); have e4 := e 4 (by omega)
      simp only [Nat.add_zero] at e0
      rw [e0, e1, e2, e3, e4]
    · have := PBg.1; rw [hbig] at this; omega
  unfold indexOk
  simp only [Bool.and_eq_true]
  refine ⟨⟨hcut, ?_⟩, hchr⟩
  rw [check3P_eq, check2P_eq (rep_unpack _), unpack_congr G { G with w := S } rfl hget]
  rw [check3P_eq, check2P_eq (rep_unpack _)] at h3
  exact check2_sh H _ h3


theorem saveIndex_size (L : LoadedIndex) : 16 ≤ (saveIndex L).size := by
  obtain ⟨ix, G, offs, ns⟩ := L
  rw [saveIndex_eq, putU64_size, putNat_size]; omega

/-- **The index builder writes a non-empty index whenever the genome fits.** The minimizer check
on the built index is `Spec.check3P_buildLoaded` (`Proofs/IndexBuild.lean`). -/
theorem buildIndex_ne_empty (g : GenomeFile) (hf : Fits g) : buildIndex g ≠ ByteArray.empty := by
  have hN : (catG g).length < 2 ^ 32 := by rw [letters_eq]; have := hf.1; omega
  obtain ⟨L', hl, hok⟩ := indexOk_loaded g hf (Spec.check3P_buildLoaded g hN)
  have e : buildIndex g = saveIndex (buildLoaded g) := by
    unfold buildIndex; simp only [hl, hok, ite_true]
  rw [e]
  intro h
  have := saveIndex_size (buildLoaded g)
  rw [h] at this
  simp at this

end Spec.IndexFinal

#print axioms Spec.IndexFinal.indexOk_loaded
#print axioms Spec.IndexFinal.buildIndex_ne_empty
