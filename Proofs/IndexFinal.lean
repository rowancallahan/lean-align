import Proofs.Build
import Proofs.IndexBuild

/-! # The index builder is right: `buildIndex g = saveIndex (buildLoaded g)` when the genome fits

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

/-! ## A built index is never read as a lengths record

`LastResort.decLens` succeeds only on byte lists whose every length ends with a `0` byte, so a decodable
list after the tag is empty or ends with `0`; every saved index ends with the last byte of `Index.magic`
(`0x32`, "2"). So `readLens` never mistakes a saved index for the lengths record, whatever the genome. -/

theorem decNat_split : ∀ (bs : List UInt8) (n : Nat) (r : List UInt8), LastResort.decNat bs = some (n, r) →
    ∃ pre, bs = pre ++ 0 :: r
  | [], _, _, h => by simp [LastResort.decNat] at h
  | b :: rest, n, r, h => by
    unfold LastResort.decNat at h
    by_cases hb : b = 0
    · rw [if_pos hb] at h; cases h; exact ⟨[], by simp [hb]⟩
    · rw [if_neg hb] at h
      cases hd : LastResort.decNat rest with
      | none => rw [hd] at h; cases h
      | some p =>
        rw [hd] at h; obtain ⟨n', r'⟩ := p; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨pre, hp⟩ := decNat_split rest n' r' hd
        rw [← h.2]; exact ⟨b :: pre, by simp [hp]⟩

theorem decLensGo_last : ∀ (f : Nat) (bs : List UInt8) (ls : List Nat), LastResort.decLensGo f bs = some ls →
    bs = [] ∨ bs.getLast? = some 0
  | _, [], _, _ => .inl rfl
  | 0, _ :: _, _, h => by simp [LastResort.decLensGo] at h
  | f + 1, b :: rest, ls, h => by
    unfold LastResort.decLensGo at h
    cases hd : LastResort.decNat (b :: rest) with
    | none => rw [hd] at h; cases h
    | some p =>
      rw [hd] at h; obtain ⟨n, r⟩ := p
      obtain ⟨pre, hp⟩ := decNat_split _ n r hd
      cases hg : LastResort.decLensGo f r with
      | none => simp [hg] at h
      | some ls' =>
        right; rw [hp]
        rcases decLensGo_last f r ls' hg with hr | hr
        · subst hr; simp
        · rw [List.getLast?_append, List.getLast?_cons]; simp [hr]

theorem putU64_last (b : ByteArray) (x : UInt64) :
    (Index.putU64 b x).data.toList.getLast? = some (x >>> 56).toUInt8 := by
  have e : (Index.putU64 b x).data.toList = b.data.toList ++
      [x.toUInt8, (x >>> 8).toUInt8, (x >>> 16).toUInt8, (x >>> 24).toUInt8, (x >>> 32).toUInt8,
        (x >>> 40).toUInt8, (x >>> 48).toUInt8, (x >>> 56).toUInt8] := by
    simp only [Index.putU64, List.range, List.range.loop, List.foldl, ByteArray.push, Array.toList_push]
    simp
  rw [e, List.getLast?_append]; simp

theorem saveIndex_last (L : LoadedIndex) : (saveIndex L).data.toList.getLast? = some 0x32 := by
  obtain ⟨ix, G, offs, ns⟩ := L
  rw [saveIndex_eq, putU64_last]; rfl

/-- Bytes of at least 16 that end with a nonzero byte are never read as a lengths record. -/
theorem readLens_none (b : ByteArray) (hs : 16 ≤ b.size) (hl : b.data.toList.getLast? = some 0x32) :
    LastResort.readLens b = none := by
  unfold LastResort.readLens
  split
  · rw [Spec.Bridge.byteArray_toList]
    unfold LastResort.decLens
    split
    · cases h : LastResort.decLensGo b.data.toList.length (b.data.toList.drop 4) with
      | none => rfl
      | some ls =>
        exfalso
        have hlen : (b.data.toList.drop 4).length = b.size - 4 := by
          rw [List.length_drop, Array.length_toList]; rfl
        rcases decLensGo_last _ _ ls h with he | he
        · rw [he] at hlen; simp at hlen; omega
        · rw [List.getLast?_drop, if_neg (by rw [Array.length_toList]; show ¬ b.size ≤ 4; omega), hl] at he
          cases he
    · rfl
  · rfl

/-- **A saved index is never read as the lengths record.** -/
theorem readLens_saveIndex (L : LoadedIndex) : LastResort.readLens (saveIndex L) = none :=
  readLens_none _ (saveIndex_size L) (saveIndex_last L)

/-- **The index builder writes the real index whenever the genome fits** (built, saved, loaded
back and checked), never the lengths record of `LastResort`. The minimizer check on the built index
is `Spec.check3P_buildLoaded` (`Proofs/IndexBuild.lean`). -/
theorem buildIndex_eq_saveIndex (g : GenomeFile) (hf : Fits g) : buildIndex g = saveIndex (buildLoaded g) := by
  have hN : (catG g).length < 2 ^ 32 := by rw [letters_eq]; have := hf.1; omega
  obtain ⟨L', hl, hok⟩ := indexOk_loaded g hf (Spec.check3P_buildLoaded g hN)
  unfold buildIndex; simp only [readLens_saveIndex, hl, hok, ite_true]

theorem buildIndex_ne_empty (g : GenomeFile) (hf : Fits g) : buildIndex g ≠ ByteArray.empty := by
  rw [buildIndex_eq_saveIndex g hf]
  intro h
  have := saveIndex_size (buildLoaded g)
  rw [h] at this
  simp at this

end Spec.IndexFinal

#print axioms Spec.IndexFinal.indexOk_loaded
#print axioms Spec.IndexFinal.readLens_saveIndex
#print axioms Spec.IndexFinal.buildIndex_eq_saveIndex
#print axioms Spec.IndexFinal.buildIndex_ne_empty
