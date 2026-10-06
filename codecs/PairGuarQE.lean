import PairGuarQD
import MateFloor

/-!
# `pairGQC`: the fast `pairGQ` (cached partner words, global diagonal X hits)

`pscanC = pscanQ` (the cached words are the words `rejW` reads), and `hitsAtQ` lists the same
placements as the specification; hence `pairGQC` meets `pairGF_sound`'s statement.
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec MapSpec.Packed

/-! ## The partner scan with cached words -/

theorem scanWC_eq {α : Type} (R : ByteArray) (K : RP) (P : PGen) (lim : Nat) (f : Nat → Option α) :
    ∀ (k a u : Nat) (acc : List α),
      scanWC R K P lim f a k u (gword P.w u) (gword P.w (u + 1)) acc =
        scanW (fun s => if rejW R K P s lim then none else f s) a k acc
  | 0, a, u, acc => by simp only [scanWC, scanW]
  | k + 1, a, u, acc => by
    simp only [scanWC, scanW]
    have hc : (if (P.o + a) / 32 = u then gword P.w u else if (P.o + a) / 32 = u + 1 then gword P.w (u + 1)
        else gword P.w ((P.o + a) / 32)) = gword P.w ((P.o + a) / 32) := by
      split
      · next h => rw [h]
      · split
        · next h => rw [h]
        · rfl
    have hn : (if (P.o + a) / 32 = u then gword P.w (u + 1) else gword P.w ((P.o + a) / 32 + 1)) =
        gword P.w ((P.o + a) / 32 + 1) := by
      split
      · next h => rw [h]
      · rfl
    rw [hc, hn, scanWC_eq R K P lim f k (a + 1) ((P.o + a) / 32)]
    congr 1
    have hr : rejC R K P a lim (gword P.w ((P.o + a) / 32)) (gword P.w ((P.o + a) / 32 + 1)) =
        rejW R K P a lim := rfl
    rw [hr]
    cases rejW R K P a lim <;> rfl

theorem pscanC_eq (pgs2 : Array PGen) (RY RYr : ByteArray) (KY KYr : RP) (sl lo hi lim : Nat) (x : Placement) :
    pscanC pgs2 RY RYr KY KYr sl lo hi lim x = pscanQ pgs2 RY RYr KY KYr sl lo hi lim x := by
  unfold pscanC pscanQ
  simp only
  split
  · rw [scanWC_eq]
  · rw [scanWC_eq]

theorem pairsQC_eq (dc : Nat → Nat) (sl lo hi Gc : Nat) (pgs2 : Array PGen) (RY RYr : ByteArray) (KY KYr : RP)
    (swap : Bool) : pairsQC dc sl lo hi Gc pgs2 RY RYr KY KYr swap = pairsQ dc sl lo hi Gc pgs2 RY RYr KY KYr swap := by
  funext x
  unfold pairsQC pairsQ
  rw [pscanC_eq]

/-! ## The enumerated mate's hits by global diagonals -/

theorem offsOk_step (offs : Array Nat) (pgs : Array PGen) (h : offsOk offs pgs = true) (c : Nat)
    (hc : c + 1 < pgs.size) : offs[c]! + pgs[c]!.n ≤ offs[c + 1]! := by
  unfold offsOk at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h c (by omega) with h | h
  · omega
  · exact h

theorem offsOk_mono (offs : Array Nat) (pgs : Array PGen) (h : offsOk offs pgs = true) (i : Nat) :
    ∀ d, i + d < pgs.size → offs[i]! ≤ offs[i + d]!
  | 0, _ => Nat.le_refl _
  | d + 1, hd => by
    have h1 := offsOk_mono offs pgs h i d (by omega)
    have h2 := offsOk_step offs pgs h (i + d) (by omega)
    rw [← Nat.add_assoc]; omega

theorem chromOf_eq (offs : Array Nat) (x c N : Nat) (hle : ∀ i, i ≤ c → offs[i]! ≤ x)
    (hgt : ∀ i, c < i → i < N → x < offs[i]!) :
    ∀ lo hi, lo ≤ c → c < hi → hi ≤ N → chromOf offs x lo hi = c
  | lo, hi, h1, h2, h3 => by
    unfold chromOf
    split
    · next hlh =>
      simp only
      split
      · next hm =>
        have : (lo + hi) / 2 ≤ c := by
          apply Classical.byContradiction; intro hc
          have := hgt ((lo + hi) / 2) (by omega) (by omega); omega
        exact chromOf_eq offs x c N hle hgt _ _ this h2 h3
      · next hm =>
        have : c < (lo + hi) / 2 := by
          apply Classical.byContradiction; intro hc
          exact hm (hle _ (by omega))
        exact chromOf_eq offs x c N hle hgt _ _ h1 this (by omega)
    · omega
  termination_by lo hi => hi - lo
  decreasing_by all_goals omega

theorem unpack_get (pgs : Array PGen) (c : Nat) (hc : c < pgs.size) :
    (pgs.map Mz.unpack)[c]! = Mz.unpack pgs[c]! := by
  rw [getElem!_pos _ c (by simpa using hc), getElem!_pos _ c hc, Array.getElem_map]

theorem unpack_size (P : PGen) : (Mz.unpack P).size = P.n := (Mz.rep_unpack P).1.symm

theorem windowScore_fits (g : Genome) (gbs : Array ByteArray) (hg : GenomeBytes gbs g) (read : List Char)
    (w : Window) (s : Int) (h : windowScore sc0 read g w = some s) : w.chr < gbs.size ∧ w.start + w.len ≤ gbs[w.chr]!.size := by
  have hlt : w.chr < g.length := by
    rcases Nat.lt_or_ge w.chr g.length with hl | hl
    · exact hl
    · unfold windowScore windowSeq at h; rw [List.getElem?_eq_none hl] at h; cases h
  have hc1 : w.chr < gbs.size := by rw [hg.1]; exact hlt
  have he := hg.2 w.chr hc1 hlt
  refine ⟨hc1, ?_⟩
  rw [getElem!_pos gbs w.chr hc1, he.1]
  unfold windowScore windowSeq at h
  rw [List.getElem?_eq_getElem hlt] at h
  simp only at h
  split at h
  · next hfit =>
    split at hfit
    · next h3 => exact h3
    · cases hfit
  · cases h

theorem mem_candsB (need : Nat) (all : List (Array Nat)) (D : Nat) (hsup : need ≤ suppA all D 0) :
    ∀ (l prev : List (Array Nat)) (k : Nat), (∀ a ∈ prev, anyNear a D D = false) →
      (∃ arr ∈ l.take k, anyNear arr D D = true) → (∀ a ∈ l, a.toList.Pairwise (· < ·)) →
      D ∈ candsB need all prev l k
  | [], _, _, _, ⟨_, h, _⟩, _ => by simp at h
  | _ :: _, _, 0, _, ⟨_, h, _⟩, _ => by simp at h
  | arr :: rest, prev, k + 1, hp, ⟨a, ha, hb⟩, hs => by
    unfold candsB
    rw [List.mem_append]
    cases hA : anyNear arr D D
    · right
      refine mem_candsB need all D hsup rest (arr :: prev) k (fun b hb' => ?_) ⟨a, ?_, hb⟩
        (fun b hb' => hs b (List.mem_cons_of_mem _ hb'))
      · rcases List.mem_cons.1 hb' with rfl | hb'
        · exact hA
        · exact hp b hb'
      · rw [List.take_succ_cons, List.mem_cons] at ha
        rcases ha with rfl | ha
        · rw [hA] at hb; cases hb
        · exact ha
    · left
      obtain ⟨e, he, he1, he2⟩ := (anyNear_spec _ (hs arr List.mem_cons_self) _ _).1 hA
      have hD : e / 16 = D := by omega
      rw [List.mem_filterMap]
      refine ⟨e, he, ?_⟩
      rw [hD]
      have : (prev.all fun a => !anyNear a D D) = true := by
        rw [List.all_eq_true]; intro b hb'; simp [hp b hb']
      simp [this, hsup]

section gs
variable (lim : Nat) (read : List Char) (g : Genome) (pgs : Array PGen)
  (hg : GenomeBytes (pgs.map Mz.unpack) g)
  {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (E GG : ByteArray) (offs : Array Nat)
  (hcat : catOk GG offs (pgs.map Mz.unpack) = true) (hoffs : offsOk offs pgs = true)
  (Rs : ByteArray) (reads : List Char) (hrs : Encodes Rs reads) (t : Nat) (ht : t = 0 ∨ t = pgs.size)
  (hcwc : ∀ c, c < pgs.size → ∀ st len,
    cwB lim read g ⟨t + c, st, len⟩ = cwT lim reads (g ++ g) ⟨t + c, st, len⟩)
  (hm : 0 < Rs.size / 25) (hsb : sbound lim < Rs.size / 25) (hl7 : lim ≤ 7)
  (hlk : ∀ s base, s + q ≤ Rs.size →
    LookSupS GG Rs s base (LookG.look ix E Rs s base (LookG.prep ix (seedHashAt Rs s))))
  (ker : Nat → Nat → Nat)
  (hker : ∀ c st, ker c st = kerHKG Rs (packRP Rs) (pgs ++ pgs) (pgs ++ pgs) (t + c) st Rs.size lim)

include hg hrs ht hl7 hker in
theorem ker_val (c st : Nat) (hc : c < pgs.size) :
    ker c st = min (cwT lim reads (g ++ g) ⟨t + c, st, Rs.size⟩) (lim + 1) := by
  have hg2 := genomeBytes_app _ g hg
  rw [hker, kerHKG_unpack, ← cwT_kerH lim reads (g ++ g) _ Rs hg2 hrs (t + c) st Rs.size lim
    (by simp; omega) (Nat.le_refl _) (by omega)]

include hg hcat hoffs hrs ht hcwc hm hsb hl7 hlk hker in
set_option maxHeartbeats 4000000 in
theorem hitsGS_mem (w : Window) (k : Nat) :
    (w, k) ∈ hitsGS ix E offs pgs.size (fun c => pgs[c]!.n) ker t lim Rs ↔
      (∃ c, c < pgs.size ∧ w.chr = t + c) ∧ k ≤ lim ∧ cwB lim read g w = k := by
  unfold hitsGS
  simp only [List.mem_filterMap, candsC_nil]
  constructor
  · rintro ⟨D, -, hD⟩
    split at hD
    · next hcond =>
      split at hD
      · next hk =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hD
        obtain ⟨rfl, rfl⟩ := hD
        have hc := hcond.2.1
        refine ⟨⟨_, hc, rfl⟩, hk, ?_⟩
        rw [hcwc _ hc]
        have := ker_val lim g pgs hg Rs reads hrs t ht hl7 ker hker _ (D - Rs.size - offs[chromOf offs (D - Rs.size) 0 pgs.size]!) hc
        omega
      · cases hD
    · cases hD
  · rintro ⟨⟨c, hc, hwc⟩, hk, hcw⟩
    obtain ⟨wc, st, len⟩ := w
    simp only at hwc; subst hwc
    have hcT : cwT lim reads (g ++ g) ⟨t + c, st, len⟩ = k := by rw [← hcwc c hc]; exact hcw
    have hg2 := genomeBytes_app _ g hg
    have hws : windowScore sc0 reads (g ++ g) ⟨t + c, st, len⟩ = some (-(k : Int)) :=
      ((cwT_iff lim reads (g ++ g) _ (-(k : Int))).2 ⟨by omega, by rw [hcT]⟩).1
    have hfit := (windowScore_fits _ _ hg2 reads _ _ hws).2
    have hsz : (pgs.map Mz.unpack).size = pgs.size := Array.size_map ..
    have hgc : (pgs.map Mz.unpack ++ pgs.map Mz.unpack)[t + c]! = Mz.unpack pgs[c]! := by
      rw [gbs2_get _ t c (by rw [hsz]; exact ht) (by rw [hsz]; exact hc), unpack_get pgs c hc]
    simp only [hgc, unpack_size] at hfit
    have hn : Rs.size = reads.length := hrs.1
    have hgb := gapBound_sc0_zero (-(k : Int)) (by omega)
    have hcs := catOk_spec GG offs _ hcat c (by rw [hsz]; exact hc)
    rw [unpack_get pgs c hc, unpack_size] at hcs
    have hL25 := le_div_seeds Rs.size hm
    have h25 : 25 ≤ Rs.size := by
      rcases Nat.lt_or_ge Rs.size 25 with h | h
      · rw [Nat.div_eq_of_lt h] at hm; omega
      · exact h
    have hA : ∀ j, j < Rs.size / 25 →
        LookSupS GG Rs (j * (Rs.size / (Rs.size / 25))) (Rs.size - j * (Rs.size / (Rs.size / 25)))
          (LookG.look ix E Rs (j * (Rs.size / (Rs.size / 25))) (Rs.size - j * (Rs.size / (Rs.size / 25)))
            (prepG ix Rs (Rs.size / 25) (Rs.size / (Rs.size / 25)))[j]!) := by
      intro j hj
      rw [prepG_get ix Rs _ _ j hj]
      exact hlk _ _ (seed_fits Rs.size j hm hj)
    have hfitj : ∀ j, j < Rs.size / 25 → j * (Rs.size / (Rs.size / 25)) + q ≤ Rs.size :=
      fun j hj => seed_fits Rs.size j hm hj
    obtain ⟨nd, lt, hlenJ⟩ := ordG_spec ((prepG ix Rs (Rs.size / 25) (Rs.size / (Rs.size / 25))).map
      (LookG.size ix)) (Rs.size / 25)
    have hsub := List.take_sublist (sbound lim + 2) (ordG ((prepG ix Rs (Rs.size / 25)
      (Rs.size / (Rs.size / 25))).map (LookG.size ix)) (Rs.size / 25))
    generalize hJ : (ordG ((prepG ix Rs (Rs.size / 25) (Rs.size / (Rs.size / 25))).map (LookG.size ix))
      (Rs.size / 25)).take (sbound lim + 2) = J at hsub ⊢
    have hJl : sbound lim < J.length := by rw [← hJ, List.length_take, hlenJ]; omega
    have hJn : J.Nodup := hsub.nodup nd
    have hJm : ∀ j ∈ J, j < Rs.size / 25 := fun j hj => lt j (hsub.subset hj)
    generalize hmm : Rs.size / 25 = m at hm hsb hA hfitj hJm hL25 ⊢
    generalize hLs : Rs.size / m = Ls at hA hfitj hL25 ⊢
    have hkq : q ≤ reads.length / (m - 1 + 1) := by rw [← hn, show m - 1 + 1 = m by omega, hLs]; have hq : q = 25 := rfl; omega
    have hl2 : 2 ≤ reads.length / (m - 1 + 1) := by
      have : 2 ≤ q := by decide
      omega
    have hsk := sbound_mono k lim hk
    -- the window is gapless: its seeds match at `st + j·Ls`
    have hexact : ∀ (F : List Nat), F.Nodup → (∀ j ∈ F, j < m) → sbound k < F.length →
        ∃ j ∈ F, MatchAt GG (offs[c]! + st + j * Ls) Rs (j * Ls) ∧ len = Rs.size := by
      intro F hFn hFm hFl
      obtain ⟨j, hj, p, a, b, -, hmatch, hshape, ha1, -, hst, hwl⟩ :=
        coverLE (g ++ g) reads _ Rs hg2 hrs (-(k : Int)) q (by decide) (m - 1) hkq hl2 F hFn
          (fun j hj => by have := hFm j hj; omega) (by rw [sbound_def] at hFl; exact hFl) _ _ hws (Int.le_refl _)
      rw [← hn, show m - 1 + 1 = m by omega, hLs] at hmatch ha1 hst
      rw [← hn] at hwl
      rw [hgb.1, hgb.2] at hshape
      have hsa := hshape.1
      simp only at hst hwl hmatch
      rw [hgc] at hmatch
      have hjm := hFm j hj
      have hjf := hfitj j hjm
      refine ⟨j, hj, ⟨?_, fun i hi => ?_⟩, by omega⟩
      · have := hmatch.1; rw [unpack_size] at this; omega
      · have h1 := hmatch.2 i hi
        have h2 := hmatch.1; rw [unpack_size] at h2
        rw [← h1, show offs[c]! + st + j * Ls + i = offs[c]! + (p + i) by omega]
        exact hcs.2 _ (by omega)
    obtain ⟨-, -, -, hlen⟩ := hexact J hJn hJm (by omega)
    subst hlen
    have hA' : ∀ j, j < m → LookSupS GG Rs (j * Ls) (Rs.size - j * Ls)
        ((fun j => LookG.look ix E Rs (j * Ls) (Rs.size - j * Ls) (prepG ix Rs m Ls)[j]!) j) := hA
    generalize (fun j => LookG.look ix E Rs (j * Ls) (Rs.size - j * Ls) (prepG ix Rs m Ls)[j]!) = arrf at hA' ⊢
    -- every exact seed puts an anchor on the window's global diagonal
    have hanc : ∀ j, j < m → MatchAt GG (offs[c]! + st + j * Ls) Rs (j * Ls) →
        anyNear (arrf j) (offs[c]! + st + Rs.size) (offs[c]! + st + Rs.size) = true := by
      intro j hj hM
      have h1 := (hA' j hj).2 _ hM
      have hjf := hfitj j hj
      refine (anyNear_spec _ (hA' j hj).1 _ _).2 ⟨_, h1, ?_, ?_⟩ <;> omega
    have hcnt : ∀ (l : List Nat) (f : Nat → Bool),
        (l.filter f).length + (l.filter (fun x => !f x)).length = l.length := by
      intro l f; induction l with
      | nil => rfl
      | cons y l ih => by_cases hy : f y = true <;> simp [hy] <;> omega
    have hF : (J.filter fun j => !anyNear (arrf j) (offs[c]! + st + Rs.size) (offs[c]! + st + Rs.size)).length ≤
        sbound k := by
      apply Classical.byContradiction; intro hlt'
      have hsubF := List.filter_sublist (p := fun j => !anyNear (arrf j) (offs[c]! + st + Rs.size) (offs[c]! + st + Rs.size))
        (l := J)
      obtain ⟨j, hj, hM, -⟩ := hexact _ (hsubF.nodup hJn) (fun j hj => hJm j (hsubF.subset hj)) (by omega)
      have h1 := hanc j (hJm j (hsubF.subset hj)) hM
      have h2 := (List.mem_filter.1 hj).2
      rw [h1] at h2; cases h2
    have hsupp : suppA (J.map arrf) (offs[c]! + st + Rs.size) 0 =
        (J.filter fun j => anyNear (arrf j) (offs[c]! + st + Rs.size) (offs[c]! + st + Rs.size)).length := by
      unfold suppA
      rw [List.filter_map, List.length_map]
      rfl
    have hc2 := hcnt J (fun j => anyNear (arrf j) (offs[c]! + st + Rs.size) (offs[c]! + st + Rs.size))
    refine ⟨offs[c]! + st + Rs.size, ?_, ?_⟩
    · have hsup : J.length - sbound lim ≤ suppA (J.map arrf) (offs[c]! + st + Rs.size) 0 := by
        rw [hsupp]; omega
      refine mem_candsB _ _ _ hsup (J.map arrf) [] (sbound lim + 1) (fun a ha => by cases ha) ?_
        (fun a ha => by
          obtain ⟨j, hj, rfl⟩ := List.mem_map.1 ha
          exact (hA' j (hJm j hj)).1)
      apply Classical.byContradiction; intro hno
      have hall : ∀ j ∈ J.take (sbound lim + 1),
          anyNear (arrf j) (offs[c]! + st + Rs.size) (offs[c]! + st + Rs.size) = false := by
        intro j hj
        cases hb : anyNear (arrf j) (offs[c]! + st + Rs.size) (offs[c]! + st + Rs.size)
        · rfl
        · exact absurd ⟨arrf j, by rw [← List.map_take]; exact List.mem_map_of_mem hj, hb⟩ hno
      have hsl : (J.take (sbound lim + 1)).Sublist
          (J.filter fun j => !anyNear (arrf j) (offs[c]! + st + Rs.size) (offs[c]! + st + Rs.size)) := by
        have := (List.take_sublist (sbound lim + 1) J).filter
          (fun j => !anyNear (arrf j) (offs[c]! + st + Rs.size) (offs[c]! + st + Rs.size))
        rwa [List.filter_eq_self.2 (fun j hj => by simp [hall j hj])] at this
      have h1 := hsl.length_le
      rw [List.length_take] at h1
      omega
    · have hx : offs[c]! + st + Rs.size - Rs.size = offs[c]! + st := by omega
      have hco : chromOf offs (offs[c]! + st) 0 pgs.size = c := by
        refine chromOf_eq offs _ c pgs.size (fun i hi => ?_) (fun i hi1 hi2 => ?_) 0 pgs.size (Nat.zero_le _) hc
          (Nat.le_refl _)
        · have := offsOk_mono offs pgs hoffs i (c - i) (by omega)
          rw [show i + (c - i) = c by omega] at this; omega
        · have h1 := offsOk_step offs pgs hoffs c (by omega)
          have h2 := offsOk_mono offs pgs hoffs (c + 1) (i - (c + 1)) (by omega)
          rw [show c + 1 + (i - (c + 1)) = i by omega] at h2; omega
      rw [hx, hco, if_pos ⟨by omega, hc, by omega, by omega⟩]
      have hkv : ker c (offs[c]! + st - offs[c]!) = k := by
        rw [show offs[c]! + st - offs[c]! = st by omega,
          ker_val lim g pgs hg Rs reads hrs t ht hl7 ker hker c st hc, hcT]
        omega
      rw [hkv, if_pos hk, show offs[c]! + st - offs[c]! = st by omega]

end gs

set_option maxHeartbeats 1000000 in
/-- **The enumerated mate's hits by global diagonals** (`lim ≤ 7`): exactly the specification's. -/
theorem mem_hitsAtQ_mzR (lim : Nat) (hl7 : lim ≤ 7) (g : Genome) (read : List Char) (ix : Mz.MzIdx)
    (G : PGen) (offs ns : Array Nat) (R : ByteArray) (hcut : cutOk G offs ns = true)
    (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) g) (hr : Encodes R read)
    (hchk : Mz.check2P ix G = true) (l : List (Placement × Int))
    (hl : hitsAtQ lim (PkMzR.mk ix G) offs (cutAll G offs ns) R = some l)
    (x : Placement × Int) : x ∈ l ↔ x ∈ hitsBoth sc0 (-(lim : Int)) g read := by
  unfold hitsAtQ at hl
  split at hl
  · next hok =>
    split at hl
    · next hoffs =>
      have hok' := hok
      unfold fastT at hok
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨hm, hsb⟩ := hok
      simp only [Option.some.injEq] at hl
      subst hl
      generalize hpg : cutAll G offs ns = pgs at hg hoffs
      have hcat := catOk_cut G offs ns hcut
      rw [hpg] at hcat
      have hn : pgs.size = g.length := by have := hg.1; simpa using this
      have hrr : Encodes (revCompK R) (revComp read) := by rw [revCompK_eq]; exact revCompB_encodes R read hr
      have hsz : (revCompK R).size = R.size := by rw [revCompK_eq]; exact revCompB_size R
      have hlk := lookSup_pkR ix G hchk
      have hcw1 : ∀ c, c < pgs.size → ∀ st len,
          cwB lim read g ⟨0 + c, st, len⟩ = cwT lim read (g ++ g) ⟨0 + c, st, len⟩ := by
        intro c hc st len
        rw [Nat.zero_add, cwT_app_left lim read g _ (by simp only; omega)]
        unfold cwB; rw [if_pos (by simp only; omega)]
      have hcw2 : ∀ c, c < pgs.size → ∀ st len,
          cwB lim read g ⟨pgs.size + c, st, len⟩ = cwT lim (revComp read) (g ++ g) ⟨pgs.size + c, st, len⟩ := by
        intro c hc st len
        rw [hn, cwT_app_right]
        unfold cwB; rw [if_neg (by simp only; omega)]
        simp
      have key : ∀ w k, (w, k) ∈ hitsGS (PkMzR.mk ix G) ByteArray.empty offs pgs.size (fun c => pgs[c]!.n)
            (fun c st => kerHKG R (packRP R) (pgs ++ pgs) (pgs ++ pgs) c st R.size lim) 0 lim R ++
          hitsGS (PkMzR.mk ix G) ByteArray.empty offs pgs.size (fun c => pgs[c]!.n)
            (fun c st => kerHKG (revCompK R) (packRP (revCompK R)) (pgs ++ pgs) (pgs ++ pgs) (pgs.size + c) st
              (revCompK R).size lim) pgs.size lim (revCompK R) ↔ k ≤ lim ∧ cwB lim read g w = k := by
        intro w k
        rw [List.mem_append,
          hitsGS_mem lim read g pgs hg (PkMzR.mk ix G) ByteArray.empty (Mz.unpack G) offs hcat hoffs R read hr 0
            (Or.inl rfl) hcw1 hm hsb hl7 (fun s base hs => hlk R s base hs) _ (fun c st => by rw [Nat.zero_add]),
          hitsGS_mem lim read g pgs hg (PkMzR.mk ix G) ByteArray.empty (Mz.unpack G) offs hcat hoffs (revCompK R)
            (revComp read) hrr pgs.size (Or.inr rfl) hcw2 (by rw [hsz]; exact hm) (by rw [hsz]; exact hsb) hl7
            (fun s base hs => hlk _ s base hs) _ (fun c st => rfl)]
        constructor
        · rintro (⟨-, h⟩ | ⟨-, h⟩) <;> exact h
        · rintro ⟨hk, hcw⟩
          have := cwB_chr_lt lim read g w (by omega)
          by_cases hc : w.chr < pgs.size
          · left; exact ⟨⟨w.chr, hc, by omega⟩, hk, hcw⟩
          · right; exact ⟨⟨w.chr - pgs.size, by omega, by omega⟩, hk, hcw⟩
      obtain ⟨p, s⟩ := x
      rw [List.mem_map, mem_hitsBoth_T]
      have hS : ∀ st w, (strandScore g read st w = some s ∧ -(lim : Int) ≤ s) ↔
          (cwS lim read g st w ≤ lim ∧ s = -(cwS lim read g st w : Int)) := by
        intro st w; cases st
        · exact cwT_iff lim read g w s
        · exact cwT_iff lim (revComp read) g w s
      constructor
      · rintro ⟨⟨w, k⟩, hmem, he⟩
        rw [key] at hmem
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        have h3 : cwS lim read g (decB pgs.size w).2 (decB pgs.size w).1 = k := by
          rw [hn, cwS_decB]; exact hmem.2
        have h4 := (hS (decB pgs.size w).2 (decB pgs.size w).1).2 ⟨by omega, by rw [h3]⟩
        exact ⟨strandScore_allWindows g read _ _ _ h4.1, h4.1, h4.2⟩
      · rintro ⟨-, h1, h2⟩
        have h4 := (hS p.2 p.1).1 ⟨h1, h2⟩
        refine ⟨(encB pgs.size p, cwS lim read g p.2 p.1), (key _ _).2 ⟨h4.1, ?_⟩, ?_⟩
        · rw [hn]; exact cwB_encB lim read g p h4.1
        · simp only [Prod.mk.injEq]
          rw [hn, decB_encB g.length p (cwS_chr_lt lim read g p h4.1), h4.2]
          exact ⟨rfl, rfl⟩
    · exact mem_hitsAtKP3_mzR lim (by omega) g read ix G offs ns R hcut hg hr hchk l hl x
  · cases hl

section top
variable (dc : Nat → Nat) (sl lo hi Gc : Nat) (g : Genome) (m1 m2 : List Char) (ix : Mz.MzIdx) (G : PGen)
  (offs ns : Array Nat) (R1 R2 : ByteArray)
  (hcut : cutOk G offs ns = true) (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) g)
  (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hchk : Mz.check2P ix G = true)

include hcut hg h1 h2 hchk in
/-- (d) **The early-stop fast guarantee is the specification** (`pairGF_sound`'s statement). -/
theorem pairGQC_sound (hG : Gc ≤ 7) (swap : Bool) (P1 P2 : Nat) (hP1 : Gc ≤ P1) (hP2 : Gc ≤ P2)
    (r : Option PairHit) (seen : Bool) (lX : List (Placement × Int))
    (h : pairGQC dc sl lo hi Gc swap (PkMzR.mk ix G) offs (cutAll G offs ns) R1 R2 = some (r, seen, lX)) :
    (∀ x, x ∈ lX ↔ x ∈ hitsBoth sc0 (-(Gc : Int)) g (if swap then m2 else m1)) ∧
    (seen = true ↔ ∃ w ∈ properPairs sl lo hi (hitsBoth sc0 (-(P1 : Int)) g m1) (hitsBoth sc0 (-(P2 : Int)) g m2),
      -(Gc : Int) ≤ pairScoreD dc w) ∧
    (seen = true → r = pairSpecUT sc0 dc sl lo hi (-(P1 : Int)) (-(P2 : Int)) g m1 m2) ∧
    (seen = true → r = none → PairTieOk dc sl lo hi (-(P1 : Int)) (-(P2 : Int)) g m1 m2) := by
  cases hl : hitsAtQ Gc (PkMzR.mk ix G) offs (cutAll G offs ns) (if swap then R2 else R1) with
  | none => simp only [pairGQC, hl, reduceCtorEq] at h
  | some lX' =>
    simp only [pairGQC, hl, pairsQC_eq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hrX : Encodes (if swap then R2 else R1) (if swap then m2 else m1) := by cases swap <;> simpa
    have hrY : Encodes (if swap then R1 else R2) (if swap then m1 else m2) := by cases swap <;> simpa
    have hX := mem_hitsAtQ_mzR Gc hG g _ ix G offs ns _ hcut hg hrX hchk lX' hl
    generalize hRY : (if swap then R1 else R2) = RY at hrY ⊢
    generalize hpg : cutAll G offs ns = pgs at hg ⊢
    have HP := mem_pairsGF g pgs hg dc sl lo hi Gc hG m1 m2 swap RY hrY lX' hX P1 P2 hP1 hP2
    generalize hf : pairsQ dc sl lo hi Gc (pgs ++ pgs) RY (revCompK RY) (packRP RY) (packRP (revCompK RY)) swap = f
    have hAll : pairsGF dc sl lo hi Gc (pgs ++ pgs) RY (revCompK RY) (packRP RY) (packRP (revCompK RY)) swap lX' =
        lX'.flatMap f := by
      rw [← hf]
      unfold pairsGF pairsQ
      congr 1
      funext x
      rw [pscanQ_eq _ _ _ _ _ _ (by omega)]
    rw [hAll] at HP
    generalize hh1 : hitsBoth sc0 (-(P1 : Int)) g m1 = H1 at HP
    generalize hh2 : hitsBoth sc0 (-(P2 : Int)) g m2 = H2 at HP
    have hn1 : ∀ x ∈ H1, x.2 ≤ 0 := by rw [← hh1]; exact hitsBoth_nonpos _ _ _
    have hn2 : ∀ x ∈ H2, x.2 ≤ 0 := by rw [← hh2]; exact hitsBoth_nonpos _ _ _
    -- a pair of `x` scores at most `x.2`
    have hsc : ∀ x ∈ lX', ∀ p ∈ f x, pairScoreD dc p ≤ x.2 := by
      intro x hx p hp
      have hpa := (HP p).1 (List.mem_flatMap.2 ⟨x, hx, hp⟩)
      have hX' : (if swap then p.2 else p.1) = x := by rw [← hf] at hp; exact pairsQ_X _ _ _ _ _ _ _ _ _ _ _ _ _ hp
      rw [mem_properPairs] at hpa
      have e1 := hn1 _ hpa.1.1
      have e2 := hn2 _ hpa.1.2.1
      have hd : (0 : Int) ≤ (dc (fragLen p.1.1 p.2.1) : Int) := Int.natCast_nonneg _
      unfold pairScoreD
      cases swap
      · simp only [Bool.false_eq_true, if_false] at hX'; subst hX'; omega
      · simp only [if_true] at hX'; subst hX'; omega
    have hxn : ∀ x ∈ lX', x.2 ≤ 0 := fun x hx => by
      have := (hX x).1 hx; exact hitsBoth_nonpos _ _ _ x this
    generalize hl0 : lX'.filter (fun x => decide (x.2 = 0)) = l0
    generalize hl1 : lX'.filter (fun x => !decide (x.2 = 0)) = l1
    have hm0 : ∀ x ∈ l0, x ∈ lX' ∧ x.2 = 0 := fun x hx => by
      rw [← hl0, List.mem_filter] at hx; exact ⟨hx.1, by simpa using hx.2⟩
    have hm1 : ∀ x ∈ l1, x ∈ lX' := fun x hx => by
      rw [← hl1, List.mem_filter] at hx; exact hx.1
    have hcov : ∀ x ∈ lX', x ∈ l0 ++ l1 := fun x hx => by
      rw [List.mem_append, ← hl0, ← hl1, List.mem_filter, List.mem_filter]
      by_cases h0 : x.2 = 0
      · exact Or.inl ⟨hx, by simp [h0]⟩
      · exact Or.inr ⟨hx, by simp [h0]⟩
    generalize hU : l1.foldl (fun m x => max m x.2) (-(Gc : Int)) = U1
    have hU0 : U1 ≤ 0 := by
      rw [← hU]; exact foldl_max_le l1 0 (fun x hx => hxn x (hm1 x hx)) _ (by omega)
    have hU1 : ∀ x ∈ l1, x.2 ≤ U1 := by rw [← hU]; exact (foldl_max_ge l1 _).2
    obtain ⟨D, hI, hD, hrest⟩ := goP2_spec dc f U1 hU0 l0 l1
      (fun x hx p hp => by have := hsc x (hm0 x hx).1 p hp; have := (hm0 x hx).2; omega)
      (fun x hx p hp => by have := hsc x (hm1 x hx) p hp; have := hU1 x hx; omega)
    generalize hs : goP dc f U1 l1 (goP dc f 0 l0 (none, false)) = s at hI hrest
    have hA := ansOk dc sl lo hi H1 H2 (by rw [← hh1]; exact hitsBoth_scoreFun _ _ _ _)
      (by rw [← hh2]; exact hitsBoth_scoreFun _ _ _ _) (-(Gc : Int)) (lX'.flatMap f) HP D s hI
      (fun p hp => by
        obtain ⟨x, hx, hpx⟩ := hD p hp
        rw [List.mem_append] at hx
        exact List.mem_flatMap.2 ⟨x, by rcases hx with hx | hx; exact (hm0 x hx).1; exact hm1 x hx, hpx⟩)
      (fun p hp => by
        obtain ⟨x, hx, hpx⟩ := List.mem_flatMap.1 hp
        exact hrest x (hcov x hx) p hpx)
    unfold pairSpecUT PairTieOk pairSpecUT
    rw [hh1, hh2]
    refine ⟨hX, hA.1, hA.2, fun hsn hr => ⟨by rw [← hA.2 hsn]; exact hr, ?_⟩⟩
    obtain ⟨w, hw, -⟩ := hA.1.1 hsn
    exact ⟨w, hw⟩

theorem hitsAtQ_some (lim : Nat) (ix : PkMzR) (offs : Array Nat) (pgs : Array PGen) (R : ByteArray)
    (h : fastT lim R = true) : ∃ l, hitsAtQ lim ix offs pgs R = some l := by
  unfold hitsAtQ
  rw [if_pos h]
  split
  · exact ⟨_, rfl⟩
  · exact hitsAtKP3_some lim ix ByteArray.empty offs pgs R h

theorem pairGQC_some (dc : Nat → Nat) (sl lo hi Gc : Nat) (swap : Bool) (ix : PkMzR) (offs : Array Nat)
    (pgs : Array PGen) (R1 R2 : ByteArray) (h : fastT Gc (if swap then R2 else R1) = true) :
    ∃ v, pairGQC dc sl lo hi Gc swap ix offs pgs R1 R2 = some v := by
  obtain ⟨l, hl⟩ := hitsAtQ_some Gc ix offs pgs _ h
  unfold pairGQC
  simp only [hl]
  exact ⟨_, rfl⟩

end top

end MapSpec.Fast

#print axioms MapSpec.Fast.pscanC_eq
#print axioms MapSpec.Fast.hitsGS_mem
#print axioms MapSpec.Fast.candsC_eq
#print axioms MapSpec.Fast.mem_hitsAtQ_mzR
#print axioms MapSpec.Fast.pairGQC_sound
#print axioms MapSpec.Fast.pairGQC_some
