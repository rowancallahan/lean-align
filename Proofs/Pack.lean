import Proofs.Index

/-! # The genome packer is right (`Proofs/Index.lean`'s `packAll`, `offsOf`)

`PB.push` keeps an invariant (`Inv`): the 17-byte blocks so far, their flags (1 only when every
letter of the block is ACGT), the 2-bit codes, the letter being filled, and the runs of other
bytes (`ExInv`). `finish_raw`: the finished genome reads back every byte (letters must number
fewer than `2^32`: the runs store places as `UInt32`). `genomeChecks`: on any packed genome that
reads the chromosomes one after the other, `cutOk` and `chromsOk` hold for `buildLoaded`'s
offsets and lengths. -/
open MapSpec MapSpec.Fast MapSpec.Packed

namespace Spec.Pack

theorem bget (b : ByteArray) (i : Nat) : b.get! i = b.data[i]! := by cases b; rfl

theorem foldl_list {β} (f : β → UInt8 → β) (s : β) (b : ByteArray) : b.foldl f s = b.data.toList.foldl f s := by
  cases b with
  | mk a =>
  simp only [ByteArray.foldl, ByteArray.foldlM, ByteArray.size, Nat.le_refl, dite_true, Nat.sub_zero]
  suffices ∀ n j s, a.size - j = n → (ByteArray.foldlM.loop (m := Id) (fun x y => pure (f x y)) ⟨a⟩ a.size (Nat.le_refl _) n j s).run = (a.toList.drop j).foldl f s by
    simpa using this a.size 0 s (by omega)
  intro n
  induction n with
  | zero =>
    intro j s h; unfold ByteArray.foldlM.loop
    split
    · omega
    · rw [List.drop_eq_nil_of_le (show a.toList.length ≤ j by simp; omega)]; rfl
  | succ n ih =>
    intro j s h
    unfold ByteArray.foldlM.loop
    have hj : j < a.size := by omega
    rw [dif_pos hj]
    rw [List.drop_eq_getElem_cons (by simp; omega)]
    have := ih (j+1) (f s a[j]) (by omega)
    simp only [List.foldl_cons, Array.getElem_toList]
    rw [← this]
    rfl

theorem get_push (b : ByteArray) (x : UInt8) (p : Nat) :
    (b.push x).get! p = if p < b.size then b.get! p else if p = b.size then x else 0 := by
  cases b with
  | mk a =>
    simp only [bget, ByteArray.push, ByteArray.size]
    by_cases h1 : p < a.size
    · rw [if_pos h1]; grind
    · rw [if_neg h1]; by_cases h2 : p = a.size
      · rw [if_pos h2]; subst h2; grind
      · rw [if_neg h2, getElem!_neg _ p (by simp; omega)]; rfl

theorem get_set (b : ByteArray) (j : Nat) (x : UInt8) (p : Nat) :
    (b.set! j x).get! p = if p = j ∧ j < b.size then x else b.get! p := by
  cases b with
  | mk a =>
    simp only [bget, ByteArray.set!, ByteArray.size]
    split <;> grind

theorem size_set (b : ByteArray) (j : Nat) (x : UInt8) : (b.set! j x).size = b.size := by
  cases b; simp [ByteArray.set!, ByteArray.size]

theorem aget_push (a : Array UInt32) (x : UInt32) (p : Nat) :
    (a.push x)[p]! = if p < a.size then a[p]! else if p = a.size then x else 0 := by
  split
  · grind
  · split
    · subst_vars; grind
    · rw [getElem!_neg _ p (by simp; omega)]; rfl

theorem aget_set (a : Array UInt32) (j : Nat) (x : UInt32) (p : Nat) :
    (a.set! j x)[p]! = if p = j ∧ j < a.size then x else a[p]! := by
  split <;> grind

def W1 (s : PB) : ByteArray := if s.n % 64 == 0 then s.w.push 0 else s.w
def Cur1 (s : PB) (v : UInt8) : UInt8 := s.cur ||| ((c2 v).toUInt8 <<< (2 * (s.n % 4)).toUInt8)
def F1 (s : PB) (v : UInt8) : UInt8 := if !acgt v then 0 else s.f
def Fp (s : PB) : Nat := if s.n % 64 == 0 then s.w.size else s.fpos
def W2 (s : PB) (v : UInt8) : ByteArray := if s.n % 4 == 3 then (W1 s).push (Cur1 s v) else W1 s
def W3 (s : PB) (v : UInt8) : ByteArray := if s.n % 64 == 63 then (W2 s v).set! (Fp s) (F1 s v) else W2 s v
def ExS (n : Nat) (prev : UInt8) (ex : Array UInt32) (v : UInt8) : Array UInt32 :=
  if !(!acgt v) then ex else if n > 0 && prev == v then ex.set! (ex.size - 2) (n + 1).toUInt32
      else ((ex.push n.toUInt32).push (n + 1).toUInt32).push v.toUInt32
def Ex1 (s : PB) (v : UInt8) : Array UInt32 := ExS s.n s.prev s.ex v

theorem push_eq (s : PB) (v : UInt8) : s.push v =
    { n := s.n + 1, w := W3 s v, cur := if s.n % 4 == 3 then 0 else Cur1 s v,
      f := if s.n % 64 == 63 then 1 else F1 s v, fpos := Fp s, ex := Ex1 s v, prev := v } := by
  obtain ⟨n, w, cur, f, fpos, ex, prev⟩ := s
  simp only [PB.push, W3, W2, W1, Cur1, F1, Fp, Ex1, ExS]
  by_cases h1 : n % 4 == 3 <;> by_cases h2 : n % 64 == 63 <;> simp only [h1, h2, ite_true] <;> rfl

def cpos (i : Nat) : Nat := 17 * (i / 64) + 1 + i % 64 / 4
def wsz (n : Nat) : Nat := 17 * (n / 64) + (if n % 64 = 0 then 0 else 1 + n % 64 / 4)

def wvg (g : Nat → UInt8) (s : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => wvg g s m + c2N (g (s + m)) * 4 ^ m

theorem wvg_lt (g : Nat → UInt8) (s m : Nat) : wvg g s m < 4 ^ m := by
  induction m with
  | zero => simp [wvg]
  | succ m ih =>
    have := c2N_lt (g (s + m))
    rw [wvg, Nat.pow_succ]
    have : c2N (g (s + m)) * 4 ^ m ≤ 3 * 4 ^ m := Nat.mul_le_mul_right _ (by omega)
    omega

theorem wvg_dig (g : Nat → UInt8) (s m t : Nat) (ht : t < m) : dig (wvg g s m) t = c2N (g (s + t)) := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [wvg]
    have hx := wvg_lt g s m
    have hc := c2N_lt (g (s + m))
    by_cases e : t = m
    · subst e
      unfold dig
      rw [Nat.add_mul_div_right _ _ (Nat.pow_pos (by omega)), Nat.div_eq_of_lt hx, Nat.zero_add,
        Nat.mod_eq_of_lt hc]
    · have ht' : t < m := by omega
      rw [← ih ht']
      unfold dig
      have h4 : 4 ^ m = 4 ^ t * (4 * 4 ^ (m - t - 1)) := by
        rw [← Nat.pow_succ', ← Nat.pow_add]; congr 1; omega
      rw [h4, ← Nat.mul_assoc, Nat.mul_comm _ (4 ^ t), Nat.mul_assoc,
        Nat.add_mul_div_left _ _ (Nat.pow_pos (by omega)), ← Nat.mul_assoc, Nat.mul_comm _ 4,
        Nat.mul_assoc, Nat.add_mul_mod_self_left]

theorem or_shift_nat : ∀ x, x < 64 → ∀ c, c < 4 → ∀ m, m < 4 → x < 4 ^ m →
    (x.toUInt8 ||| (c.toUInt8 <<< (2 * m).toUInt8)).toNat = x + c * 4 ^ m := by decide

theorem cur1_toNat (s : PB) (v : UInt8) (h : s.cur.toNat < 4 ^ (s.n % 4)) :
    (Cur1 s v).toNat = s.cur.toNat + c2N v * 4 ^ (s.n % 4) := by
  have hm : s.n % 4 < 4 := Nat.mod_lt _ (by omega)
  have h64 : s.cur.toNat < 64 := by
    have : 4 ^ (s.n % 4) ≤ 4 ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have : (4:Nat) ^ 3 = 64 := rfl
    omega
  have e1 : (c2 v).toUInt8 = (c2N v).toUInt8 := by
    apply UInt8.toNat_inj.1; rw [UInt64.toNat_toUInt8, c2_toNat, Nat.toUInt8, UInt8.toNat_ofNat']
  have := or_shift_nat s.cur.toNat h64 (c2N v) (c2N_lt v) (s.n % 4) hm h
  rw [show s.cur.toNat.toUInt8 = s.cur by simp] at this
  unfold Cur1; rw [e1]; exact this



theorem wsz_step (n : Nat) : wsz (n + 1) = wsz n + (if n % 64 = 0 then 1 else 0) + (if n % 4 = 3 then 1 else 0) := by
  unfold wsz; split <;> split <;> split <;> omega

theorem cpos_lt (n i : Nat) (h : i < 4 * (n / 4)) : cpos i < wsz n := by
  unfold cpos wsz; split <;> omega

theorem cpos_ne (i j : Nat) : cpos i ≠ 17 * j := by unfold cpos; omega

theorem size_W1 (s : PB) : (W1 s).size = s.w.size + (if s.n % 64 = 0 then 1 else 0) := by
  unfold W1; by_cases h : s.n % 64 = 0 <;> simp [h]

theorem size_W2 (s : PB) (v : UInt8) : (W2 s v).size = (W1 s).size + (if s.n % 4 = 3 then 1 else 0) := by
  unfold W2; by_cases h : s.n % 4 = 3 <;> simp [h]

theorem size_W3 (s : PB) (v : UInt8) : (W3 s v).size = (W2 s v).size := by
  unfold W3; split <;> simp [size_set]

/-- reading `W3` below the old size, away from the flag being written -/
theorem W3_old (s : PB) (v : UInt8) (p : Nat) (hp : p < s.w.size) (hf : s.n % 64 = 63 → p ≠ Fp s) :
    (W3 s v).get! p = s.w.get! p := by
  have h1 : (W1 s).get! p = s.w.get! p := by
    unfold W1; split
    · rw [get_push, if_pos hp]
    · rfl
  have h2 : (W2 s v).get! p = s.w.get! p := by
    unfold W2; split
    · rw [get_push, if_pos (by rw [size_W1]; omega), h1]
    · exact h1
  unfold W3; split
  · rename_i hh; rw [get_set, if_neg (fun h => hf (by simpa using hh) h.1), h2]
  · exact h2

theorem toU32 (n : Nat) (h : n < 2 ^ 32) : n.toUInt32.toNat = n := by
  rw [Nat.toUInt32, UInt32.toNat_ofNat', Nat.mod_eq_of_lt h]

def st (ex : Array UInt32) (k : Nat) : Nat := (ex[3 * k]!).toNat
def en (ex : Array UInt32) (k : Nat) : Nat := (ex[3 * k + 1]!).toNat
def by' (ex : Array UInt32) (k : Nat) : Nat := (ex[3 * k + 2]!).toNat
def cnt (ex : Array UInt32) : Nat := ex.size / 3

/-- `ex` lists the maximal-or-not runs of non-ACGT bytes of `g` below `n`, increasing. -/
structure ExInv (g : Nat → UInt8) (n : Nat) (ex : Array UInt32) : Prop where
  exm : ex.size % 3 = 0
  r1 : ∀ k < cnt ex, st ex k < en ex k ∧ en ex k ≤ n
  r2 : ∀ k, k + 1 < cnt ex → en ex k ≤ st ex (k + 1)
  r3 : ∀ k < cnt ex, ∀ i, st ex k ≤ i → i < en ex k → (g i).toNat = by' ex k
  r4 : ∀ i < n, acgt (g i) = false → ∃ k < cnt ex, st ex k ≤ i ∧ i < en ex k
  r5 : 0 < n → acgt (g (n - 1)) = false → 0 < cnt ex ∧ en ex (cnt ex - 1) = n

theorem exStep (g : Nat → UInt8) (n : Nat) (prev : UInt8) (ex : Array UInt32) (I : ExInv g n ex)
    (hp : prev = if n = 0 then 65 else g (n - 1)) (hn : n + 1 < 2 ^ 32) :
    ExInv g (n + 1) (ExS n prev ex (g n)) := by
  unfold ExS
  by_cases ha : acgt (g n) = true
  · simp only [ha, Bool.not_true, Bool.not_false, ite_true]
    exact ⟨I.exm, fun k hk => ⟨(I.r1 k hk).1, by have := (I.r1 k hk).2; omega⟩, I.r2, I.r3,
      fun i hi hg => if e : i = n then by subst e; rw [ha] at hg; cases hg else I.r4 i (by omega) hg,
      fun _ hg => by rw [show n + 1 - 1 = n by omega, ha] at hg; cases hg⟩
  have ha' : acgt (g n) = false := by simpa using ha
  simp only [ha', Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_false]
  by_cases hm : n > 0 ∧ prev = g n
  · obtain ⟨h0, hpv⟩ := hm
    rw [if_pos (by simp [h0, hpv])]
    have hprev : g (n - 1) = g n := by rw [← hpv, hp, if_neg (by omega)]
    obtain ⟨hc, hl⟩ := I.r5 h0 (by rw [hprev, ha'])
    have hsz : ex.size = 3 * cnt ex := by have := I.exm; unfold cnt; omega
    have hidx : ex.size - 2 = 3 * (cnt ex - 1) + 1 := by omega
    have ecnt : cnt (ex.set! (ex.size - 2) (n + 1).toUInt32) = cnt ex := by simp [cnt]
    have est : ∀ k, st (ex.set! (ex.size - 2) (n + 1).toUInt32) k = st ex k := by
      intro k; unfold st; rw [aget_set, if_neg (by omega)]
    have eby : ∀ k, by' (ex.set! (ex.size - 2) (n + 1).toUInt32) k = by' ex k := by
      intro k; unfold by'; rw [aget_set, if_neg (by omega)]
    have een : ∀ k, en (ex.set! (ex.size - 2) (n + 1).toUInt32) k =
        if k = cnt ex - 1 then n + 1 else en ex k := by
      intro k; unfold en; rw [aget_set]
      by_cases e : k = cnt ex - 1
      · rw [if_pos ⟨by omega, by omega⟩, if_pos e, toU32 _ hn]
      · rw [if_neg (by omega), if_neg e]
    refine ⟨by simp [I.exm], ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk; rw [ecnt] at hk; rw [est, een]
      have := I.r1 k hk
      split <;> omega
    · intro k hk; rw [ecnt] at hk; rw [est, een, if_neg (by omega)]; exact I.r2 k hk
    · intro k hk i h1 h2; rw [ecnt] at hk; rw [est] at h1; rw [een] at h2; rw [eby]
      by_cases e : k = cnt ex - 1
      · rw [if_pos e] at h2
        by_cases ei : i < n
        · exact I.r3 k hk i h1 (by rw [e, hl]; exact ei)
        · have := I.r3 k hk (n - 1) (by have := (I.r1 k hk).1; rw [e, hl] at this; subst e; omega)
            (by rw [e, hl]; omega)
          rw [show i = n by omega, ← hprev, this]
      · rw [if_neg e] at h2; exact I.r3 k hk i h1 h2
    · intro i hi hg; rw [ecnt]
      by_cases e : i = n
      · refine ⟨cnt ex - 1, by omega, ?_, ?_⟩
        · rw [est]; have := (I.r1 (cnt ex - 1) (by omega)).1; omega
        · rw [een, if_pos rfl]; omega
      · obtain ⟨k, hk, h1, h2⟩ := I.r4 i (by omega) hg
        refine ⟨k, hk, by rw [est]; exact h1, ?_⟩
        rw [een]; split <;> omega
    · intro _ _; rw [ecnt, een, if_pos rfl]; exact ⟨hc, rfl⟩
  · rw [if_neg (by
      intro h; apply hm; simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h; exact h)]
    have hsz : ex.size = 3 * cnt ex := by have := I.exm; unfold cnt; omega
    let ex' := ((ex.push n.toUInt32).push (n + 1).toUInt32).push (g n).toNat.toUInt32
    have ev : (g n).toUInt32 = (g n).toNat.toUInt32 := by
      apply UInt32.toNat_inj.1; simp
    rw [ev]
    have ecnt : cnt ex' = cnt ex + 1 := by simp [ex', cnt]; omega
    have get3 : ∀ j, ex'[j]! = if j < ex.size then ex[j]! else if j = ex.size then n.toUInt32
        else if j = ex.size + 1 then (n + 1).toUInt32 else if j = ex.size + 2 then (g n).toNat.toUInt32 else 0 := by
      intro j; simp only [ex', aget_push, Array.size_push]
      repeat' split
      all_goals first | rfl | (exfalso; omega) | (subst_vars; first | rfl | (exfalso; omega))
    have gl : (g n).toNat < 256 := UInt8.toNat_lt _
    have est : ∀ k, st ex' k = if k < cnt ex then st ex k else if k = cnt ex then n else 0 := by
      intro k; unfold st; rw [get3]
      by_cases e : k < cnt ex
      · rw [if_pos (by omega), if_pos e]
      · by_cases e2 : k = cnt ex
        · rw [if_neg (by omega), if_pos (by omega), if_neg e, if_pos e2, toU32 _ (by omega)]
        · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg e, if_neg e2]; rfl
    have een : ∀ k, en ex' k = if k < cnt ex then en ex k else if k = cnt ex then n + 1 else 0 := by
      intro k; unfold en; rw [get3]
      by_cases e : k < cnt ex
      · rw [if_pos (by omega), if_pos e]
      · by_cases e2 : k = cnt ex
        · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg e, if_pos e2, toU32 _ hn]
        · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg e, if_neg e2]; rfl
    have eby : ∀ k, by' ex' k = if k < cnt ex then by' ex k else if k = cnt ex then (g n).toNat else 0 := by
      intro k; unfold by'; rw [get3]
      by_cases e : k < cnt ex
      · rw [if_pos (by omega), if_pos e]
      · by_cases e2 : k = cnt ex
        · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg e, if_pos e2,
            toU32 _ (by omega)]
        · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg e, if_neg e2]; rfl
    show ExInv g (n + 1) ex'
    refine ⟨by simp [ex']; omega, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk; rw [ecnt] at hk; rw [est, een]
      by_cases e : k < cnt ex
      · rw [if_pos e, if_pos e]; have := I.r1 k e; omega
      · rw [if_neg e, if_neg e, if_pos (by omega), if_pos (by omega)]; omega
    · intro k hk; rw [ecnt] at hk; rw [est, een, if_pos (by omega)]
      by_cases e : k + 1 < cnt ex
      · rw [if_pos e]; exact I.r2 k e
      · rw [if_neg e, if_pos (by omega)]; exact (I.r1 k (by omega)).2
    · intro k hk i h1 h2; rw [ecnt] at hk; rw [est] at h1; rw [een] at h2; rw [eby]
      by_cases e : k < cnt ex
      · rw [if_pos e] at h1 h2 ⊢; exact I.r3 k e i h1 h2
      · rw [if_neg e, if_pos (by omega)] at h1 h2 ⊢
        rw [show i = n by omega]
    · intro i hi hg; rw [ecnt]
      by_cases e : i = n
      · refine ⟨cnt ex, by omega, ?_, ?_⟩
        · rw [est, if_neg (by omega), if_pos rfl]; omega
        · rw [een, if_neg (by omega), if_pos rfl]; omega
      · obtain ⟨k, hk, h1, h2⟩ := I.r4 i (by omega) hg
        exact ⟨k, by omega, by rw [est, if_pos hk]; exact h1, by rw [een, if_pos hk]; exact h2⟩
    · intro _ _; rw [ecnt, een, if_neg (by omega), if_pos (by omega)]; exact ⟨by omega, rfl⟩


structure Inv (g : Nat → UInt8) (n : Nat) (s : PB) : Prop where
  hn : s.n = n
  wsize : s.w.size = wsz n
  fpos : n % 64 ≠ 0 → s.fpos = 17 * (n / 64)
  flag0 : n % 64 ≠ 0 → s.w.get! (17 * (n / 64)) = 0
  flagOk : ∀ i < 64 * (n / 64), s.w.get! (17 * (i / 64)) = 1 → acgt (g i) = true
  fOk : s.f = 1 → ∀ i, 64 * (n / 64) ≤ i → i < n → acgt (g i) = true
  code : ∀ i < 4 * (n / 4), dig (s.w.get! (cpos i)).toNat (i % 4) = c2N (g i)
  cur : s.cur.toNat = wvg g (4 * (n / 4)) (n % 4)
  ex : ExInv g n s.ex
  prev : s.prev = if n = 0 then 65 else g (n - 1)

theorem F1_one (s : PB) (v : UInt8) (h : F1 s v = 1) : acgt v = true ∧ s.f = 1 := by
  unfold F1 at h
  by_cases a : acgt v = true
  · simp [a] at h; exact ⟨a, h⟩
  · simp [a] at h

theorem step (g : Nat → UInt8) (n : Nat) (s : PB) (I : Inv g n s) (hn : n + 1 < 2 ^ 32) :
    Inv g (n + 1) (s.push (g n)) := by
  rw [push_eq]
  have hsn := I.hn
  have hcur : s.cur.toNat < 4 ^ (s.n % 4) := by rw [I.cur, hsn]; exact wvg_lt _ _ _
  have ecur : (Cur1 s (g n)).toNat = wvg g (4 * (n / 4)) (n % 4 + 1) := by
    rw [cur1_toNat s (g n) hcur, I.cur, hsn, wvg, show 4 * (n / 4) + n % 4 = n by omega]
  have hFp : n % 64 ≠ 0 → Fp s = 17 * (n / 64) := by
    intro h; simp [Fp, hsn, h, I.fpos h]
  constructor
  · simp [hsn]
  · simp only; rw [size_W3, size_W2, size_W1, I.wsize, wsz_step, hsn]
  · intro h; simp only [Fp, hsn]
    by_cases h0 : n % 64 = 0
    · simp [h0, I.wsize, wsz]; omega
    · simp [h0, I.fpos h0]; omega
  · intro h
    simp only
    by_cases h0 : n % 64 = 0
    · have e1 : (n + 1) / 64 = n / 64 := by omega
      have hw : s.w.size = 17 * (n / 64) := by rw [I.wsize]; simp [wsz, h0]
      simp only [W3, W2, W1, hsn, beq_iff_eq, eq_true h0, eq_false (show ¬ n % 64 = 63 by omega),
        eq_false (show ¬ n % 4 = 3 by omega), ite_true, ite_false, e1]
      rw [← hw, get_push, if_neg (by omega), if_pos rfl]
    · have e1 : (n + 1) / 64 = n / 64 := by omega
      rw [e1, W3_old s _ _ (by rw [I.wsize]; unfold wsz; rw [if_neg h0]; omega) (by rw [hsn]; omega)]
      exact I.flag0 h0
  · intro i hi hf
    simp only at hf
    by_cases hi' : i < 64 * (n / 64)
    · rw [W3_old s _ _ (by rw [I.wsize]; unfold wsz; split <;> omega)
        (fun h63 => by rw [hFp (by rw [hsn] at h63; omega)]; omega)] at hf
      exact I.flagOk i hi' hf
    · have h63 : n % 64 = 63 := by omega
      have hp : Fp s = 17 * (i / 64) := by rw [hFp (by omega)]; congr 1; omega
      have hlt : Fp s < (W2 s (g n)).size := by
        rw [size_W2, size_W1, I.wsize, hFp (by omega)]; unfold wsz; rw [if_neg (by omega)]; omega
      simp only [W3, hsn, beq_iff_eq, eq_true h63, ite_true] at hf
      rw [← hp, get_set, if_pos ⟨rfl, hlt⟩] at hf
      obtain ⟨ha, hf1⟩ := F1_one s _ hf
      by_cases e : i = n
      · rw [e]; exact ha
      · exact I.fOk hf1 i (by omega) (by omega)
  · intro hf i h1 h2
    simp only at hf
    by_cases h63 : n % 64 = 63
    · omega
    · simp only [hsn, beq_iff_eq, eq_false h63, ite_false] at hf
      obtain ⟨ha, hf1⟩ := F1_one s _ hf
      by_cases e : i = n
      · rw [e]; exact ha
      · exact I.fOk hf1 i (by omega) (by omega)
  · intro i hi
    simp only
    by_cases hi' : i < 4 * (n / 4)
    · rw [W3_old s _ _ (by rw [I.wsize]; exact cpos_lt n i hi')
        (fun h63 => by rw [hFp (by rw [hsn] at h63; omega)]; exact cpos_ne _ _)]
      exact I.code i hi'
    · have h3 : n % 4 = 3 := by omega
      have h0 : n % 64 ≠ 0 := by omega
      have hc : cpos i = s.w.size := by rw [I.wsize]; unfold wsz cpos; rw [if_neg h0]; omega
      have hW2 : (W2 s (g n)).get! (cpos i) = Cur1 s (g n) := by
        simp only [W2, W1, hsn, beq_iff_eq, eq_true h3, eq_false h0, ite_true, ite_false]
        rw [hc, get_push, if_neg (by omega), if_pos rfl]
      have hW3 : (W3 s (g n)).get! (cpos i) = Cur1 s (g n) := by
        unfold W3; split
        · rw [get_set, if_neg (fun h => cpos_ne i (n / 64) (by rw [h.1, hFp h0])), hW2]
        · exact hW2
      rw [hW3, ecur, wvg_dig _ _ _ _ (by omega), show 4 * (n / 4) + i % 4 = i by omega]
  · simp only
    by_cases h3 : n % 4 = 3
    · simp [hsn, h3, show (n + 1) % 4 = 0 by omega, wvg]
    · simp only [hsn, beq_iff_eq, eq_false h3, ite_false]
      rw [ecur, show (n + 1) / 4 = n / 4 by omega, show (n + 1) % 4 = n % 4 + 1 by omega]
  · exact exStep g n s.prev s.ex I.ex (by rw [I.prev]) hn |> fun h => by simpa [Ex1, hsn] using h
  · simp [hsn]


/-! ## Start and fold -/

theorem init_inv (g : Nat → UInt8) (cap : Nat) : Inv g 0 (PB.init cap) := by
  have e : ByteArray.emptyWithCapacity (17 * (cap / 64 + 1)) = ByteArray.empty := rfl
  refine ⟨rfl, by simp [PB.init, wsz, e], by simp, by simp, by simp, fun _ i h1 h2 => by omega,
    by simp, by simp [PB.init, wvg], ⟨by simp [PB.init], ?_, ?_, ?_, ?_, ?_⟩, by simp [PB.init]⟩ <;>
    simp [PB.init, cnt]

theorem fold_inv (g : Nat → UInt8) : ∀ (L : List UInt8) (n : Nat) (s : PB), Inv g n s →
    (∀ j, j < L.length → g (n + j) = L[j]!) → n + L.length < 2 ^ 32 →
    Inv g (n + L.length) (L.foldl PB.push s) := by
  intro L
  induction L with
  | nil => intro n s I _ _; simpa using I
  | cons v L ih =>
    intro n s I hg hn
    simp only [List.foldl_cons, List.length_cons]
    have hv : v = g n := by have := hg 0 (by simp); simpa using this.symm
    rw [hv, show n + (L.length + 1) = n + 1 + L.length by omega]
    refine ih (n + 1) _ (step g n s I (by simp at hn; omega)) (fun j hj => ?_) (by simp at hn; omega)
    have := hg (j + 1) (by simp; omega)
    rw [show n + (j + 1) = n + 1 + j by omega] at this
    simpa using this

/-! ## Bytes of `UInt32`s -/

theorem or4 (a b c d : Nat) (ha : a < 256) (hb : b < 256) (hc : c < 256) (hd : d < 256) :
    ((a ||| b <<< 8) ||| c <<< 16) ||| d <<< 24 = a + 256 * b + 65536 * c + 16777216 * d := by
  have s8 : b <<< 8 = 256 * b := by rw [Nat.shiftLeft_eq]; omega
  have s16 : c <<< 16 = 65536 * c := by rw [Nat.shiftLeft_eq]; omega
  have s24 : d <<< 24 = 16777216 * d := by rw [Nat.shiftLeft_eq]; omega
  have e1 : b <<< 8 ||| a = b <<< 8 + a := (Nat.shiftLeft_add_eq_or_of_lt (by omega) b).symm
  have e2 : c <<< 16 ||| (b <<< 8 + a) = c <<< 16 + (b <<< 8 + a) :=
    (Nat.shiftLeft_add_eq_or_of_lt (by rw [s8]; omega) c).symm
  have e3 : d <<< 24 ||| (c <<< 16 + (b <<< 8 + a)) = d <<< 24 + (c <<< 16 + (b <<< 8 + a)) :=
    (Nat.shiftLeft_add_eq_or_of_lt (by rw [s8, s16]; omega) d).symm
  rw [Nat.or_comm a, e1, Nat.or_comm _ (c <<< 16), e2, Nat.or_comm _ (d <<< 24), e3, s8, s16, s24]; omega

theorem rd32 (b0 b1 b2 b3 : UInt8) :
    (b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)).toNat =
      b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat := by
  have h0 := UInt8.toNat_lt b0; have h1 := UInt8.toNat_lt b1
  have h2 := UInt8.toNat_lt b2; have h3 := UInt8.toNat_lt b3
  simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32]
  rw [show (8 : UInt32).toNat % 32 = 8 from rfl, show (16 : UInt32).toNat % 32 = 16 from rfl,
    show (24 : UInt32).toNat % 32 = 24 from rfl]
  rw [Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega), Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega),
    Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega)]
  exact or4 _ _ _ _ h0 h1 h2 h3

theorem byte32 (x : UInt32) (k : Nat) (hk : k < 32) : (x >>> k.toUInt32).toUInt8.toNat = x.toNat / 2 ^ k % 256 := by
  simp only [UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  rw [show k.toUInt32.toNat % 32 = k by rw [toU32 k (by omega)]; omega]

def pk (b : ByteArray) (x : UInt32) : ByteArray :=
  (((b.push x.toUInt8).push (x >>> 8).toUInt8).push (x >>> 16).toUInt8).push (x >>> 24).toUInt8

theorem pk_size (b : ByteArray) (x : UInt32) : (pk b x).size = b.size + 4 := by simp [pk]

theorem pk_old (b : ByteArray) (x : UInt32) (p : Nat) (h : p < b.size) : (pk b x).get! p = b.get! p := by
  simp only [pk, get_push, ByteArray.size_push]
  rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos h]

theorem u32_pk_old (b : ByteArray) (x : UInt32) (j : Nat) (h : 4 * j + 3 < b.size) : u32 (pk b x) j = u32 b j := by
  unfold u32; dsimp only
  rw [pk_old b x _ (by omega), pk_old b x (4 * j + 1) (by omega), pk_old b x (4 * j + 2) (by omega),
    pk_old b x (4 * j + 3) (by omega)]

theorem pk_new (b : ByteArray) (x : UInt32) :
    (pk b x).get! b.size = x.toUInt8 ∧ (pk b x).get! (b.size + 1) = (x >>> 8).toUInt8 ∧
    (pk b x).get! (b.size + 2) = (x >>> 16).toUInt8 ∧ (pk b x).get! (b.size + 3) = (x >>> 24).toUInt8 := by
  simp (disch := omega) only [pk, get_push, ByteArray.size_push, if_pos, if_neg, and_self, ite_true]

theorem u32_pk_new (b : ByteArray) (x : UInt32) (h : b.size % 4 = 0) : u32 (pk b x) (b.size / 4) = x.toNat := by
  unfold u32; dsimp only
  rw [show 4 * (b.size / 4) = b.size by omega]
  obtain ⟨p0, p1, p2, p3⟩ := pk_new b x
  rw [p0, p1, p2, p3, rd32]
  have e1 := byte32 x 8 (by omega); have e2 := byte32 x 16 (by omega); have e3 := byte32 x 24 (by omega)
  simp only [show (8 : Nat).toUInt32 = 8 from rfl, show (16 : Nat).toUInt32 = 16 from rfl,
    show (24 : Nat).toUInt32 = 24 from rfl] at e1 e2 e3
  rw [e1, e2, e3, UInt32.toNat_toUInt8]
  have := UInt32.toNat_lt x
  omega

theorem pack32_eq (a : Array UInt32) : pack32 a = a.foldl pk (ByteArray.emptyWithCapacity (4 * a.size)) := by
  simp [pack32]; rfl

theorem pk_fold (L : List UInt32) : ∀ b : ByteArray, b.size % 4 = 0 →
    (L.foldl pk b).size = b.size + 4 * L.length ∧
    (∀ j, 4 * j + 3 < b.size → u32 (L.foldl pk b) j = u32 b j) ∧
    (∀ j, j < L.length → u32 (L.foldl pk b) (b.size / 4 + j) = L[j]!.toNat) := by
  induction L with
  | nil => intro b _; simp
  | cons x L ih =>
    intro b hb
    obtain ⟨h1, h2, h3⟩ := ih (pk b x) (by rw [pk_size]; omega)
    simp only [List.foldl_cons, List.length_cons]
    refine ⟨by rw [h1, pk_size]; omega, fun j hj => by rw [h2 j (by rw [pk_size]; omega), u32_pk_old b x j hj], ?_⟩
    intro j hj
    by_cases e : j = 0
    · subst e; rw [h2 _ (by rw [pk_size]; omega), Nat.add_zero, u32_pk_new b x hb]; simp
    · have := h3 (j - 1) (by omega)
      rw [pk_size, show (b.size + 4) / 4 + (j - 1) = b.size / 4 + j by omega] at this
      rw [this]
      rw [show j = (j - 1) + 1 by omega]; simp

theorem pack32_spec (a : Array UInt32) : (pack32 a).size = 4 * a.size ∧ ∀ j, j < a.size → u32 (pack32 a) j = a[j]!.toNat := by
  have e : ByteArray.emptyWithCapacity (4 * a.size) = ByteArray.empty := rfl
  rw [pack32_eq, e, ← Array.foldl_toList]
  obtain ⟨h1, -, h3⟩ := pk_fold a.toList ByteArray.empty (by simp)
  refine ⟨by rw [h1]; simp, fun j hj => ?_⟩
  have := h3 j (by simpa using hj)
  rw [show ByteArray.empty.size / 4 + j = j by simp] at this
  rw [this, getElem!_pos a.toList j (by simpa using hj), getElem!_pos a j hj]
  simp

/-! ## The binary search -/

theorem exFind_spec (ex : ByteArray) (i C : Nat) (hmono : ∀ a b, a ≤ b → b < C → u32 ex (3 * a) ≤ u32 ex (3 * b)) :
    ∀ f lo hi, lo ≤ hi → hi ≤ C → hi - lo < 2 ^ f → (∀ k < lo, u32 ex (3 * k) ≤ i) →
      (∀ k, hi ≤ k → k < C → i < u32 ex (3 * k)) →
      (∀ k < exFind ex i f lo hi, u32 ex (3 * k) ≤ i) ∧
      (∀ k, exFind ex i f lo hi ≤ k → k < C → i < u32 ex (3 * k)) ∧ exFind ex i f lo hi ≤ C := by
  intro f
  induction f with
  | zero =>
    intro lo hi h1 h2 h3 hl hh
    simp only [exFind]
    exact ⟨hl, fun k hk hc => hh k (by simp at h3; omega) hc, by omega⟩
  | succ f ih =>
    intro lo hi h1 h2 h3 hl hh
    simp only [exFind]
    by_cases hlt : lo < hi
    · rw [if_pos hlt]
      split
      · rename_i hm
        apply ih _ _ (by omega) h2 (by rw [Nat.pow_succ] at h3; omega) _ hh
        intro k hk
        exact Nat.le_trans (hmono k _ (by omega) (by omega)) hm
      · rename_i hm
        apply ih _ _ (by omega) (by omega) (by rw [Nat.pow_succ] at h3; omega) hl
        intro k hk hc
        exact Nat.lt_of_lt_of_le (by omega) (hmono _ k hk hc)
    · rw [if_neg hlt]
      exact ⟨hl, fun k hk hc => hh k (by omega) hc, by omega⟩


/-! ## The finished genome spells `g` -/

theorem code_eq (P : PGen) (i : Nat) : (P.code i).toNat = dig (P.w.get! (cpos i)).toNat (i % 4) := by
  unfold PGen.code cpos
  have e1 : i >>> 6 = i / 64 := by rw [Nat.shiftRight_eq_div_pow]
  have e2 : (i >>> 2) &&& 15 = i % 64 / 4 := by
    rw [Nat.shiftRight_eq_div_pow, show (15 : Nat) = 2 ^ 4 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [e1, e2]
  generalize P.w.get! (17 * (i / 64) + 1 + i % 64 / 4) = x
  have e3 : ((i.toUInt8 &&& 3) <<< 1).toNat = 2 * (i % 4) := by
    have h3 : (i.toUInt8 &&& 3).toNat = i % 4 := by
      rw [UInt8.toNat_and, show (3 : UInt8).toNat = 2 ^ 2 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
      simp
    rw [UInt8.toNat_shiftLeft, h3, Nat.shiftLeft_eq]
    simp; omega
  unfold dig
  rw [UInt8.toNat_and, UInt8.toNat_shiftRight, e3, Nat.mod_eq_of_lt (by omega : 2 * (i % 4) < 8),
    show (3 : UInt8).toNat = 2 ^ 2 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
    Nat.pow_mul]

theorem st_ge (ex : Array UInt32) (g : Nat → UInt8) (n : Nat) (I : ExInv g n ex) :
    ∀ k, k < cnt ex → k ≤ st ex k := by
  intro k
  induction k with
  | zero => intro _; omega
  | succ k ih =>
    intro hk
    have := ih (by omega); have := (I.r1 k (by omega)).1; have := I.r2 k hk
    omega

theorem st_mono (ex : Array UInt32) (g : Nat → UInt8) (n : Nat) (I : ExInv g n ex) :
    ∀ a b, a ≤ b → b < cnt ex → st ex a ≤ st ex b := by
  intro a b hab
  induction b with
  | zero => intro _; rw [show a = 0 by omega]; exact Nat.le_refl _
  | succ b ih =>
    intro hb
    by_cases e : a = b + 1
    · rw [e]; exact Nat.le_refl _
    · have := ih (by omega) (by omega); have := (I.r1 b (by omega)).1; have := I.r2 b hb
      omega

theorem cnt_le (ex : Array UInt32) (g : Nat → UInt8) (n : Nat) (I : ExInv g n ex) : cnt ex ≤ n := by
  by_cases h : cnt ex = 0
  · omega
  · have := st_ge ex g n I (cnt ex - 1) (by omega)
    have := I.r1 (cnt ex - 1) (by omega)
    omega

/-- Where the finished genome's code bytes are. -/
def wF (s : PB) : ByteArray := if s.n % 4 == 0 then s.w else s.w.push s.cur

theorem finish_w (s : PB) : s.finish.w = wF s := rfl

theorem wF_old (s : PB) (p : Nat) (h : p < s.w.size) : (wF s).get! p = s.w.get! p := by
  unfold wF; split
  · rfl
  · rw [get_push, if_pos h]

theorem wF_size (g : Nat → UInt8) (n : Nat) (s : PB) (I : Inv g n s) :
    (wF s).size = 17 * (n / 64) + (if n % 64 = 0 then 0 else 1 + (n % 64 + 3) / 4) := by
  unfold wF; rw [I.hn]
  by_cases h : n % 4 = 0
  · simp only [beq_iff_eq, eq_true h, ite_true, I.wsize, wsz]; split <;> omega
  · simp only [beq_iff_eq, eq_false h, ite_false, ByteArray.size_push, I.wsize, wsz]; split <;> omega

theorem wF_code (g : Nat → UInt8) (n : Nat) (s : PB) (I : Inv g n s) (i : Nat) (hi : i < n) :
    dig ((wF s).get! (cpos i)).toNat (i % 4) = c2N (g i) ∧ cpos i < (wF s).size := by
  rw [wF_size g n s I]
  by_cases h : i < 4 * (n / 4)
  · rw [wF_old s _ (by rw [I.wsize]; exact cpos_lt n i h)]
    exact ⟨I.code i h, by have := cpos_lt n i h; unfold wsz at this; unfold cpos at *; split <;> split at this <;> omega⟩
  · have h4 : n % 4 ≠ 0 := by omega
    have hc : cpos i = s.w.size := by rw [I.wsize]; unfold wsz cpos; rw [if_neg (by omega)]; omega
    have hv : (wF s).get! (cpos i) = s.cur := by
      unfold wF; rw [I.hn]; simp only [beq_iff_eq, eq_false h4, ite_false]; rw [hc, get_push, if_neg (by omega), if_pos rfl]
    refine ⟨?_, by unfold cpos; rw [if_neg (by omega)]; omega⟩
    rw [hv, I.cur, wvg_dig _ _ _ _ (by omega), show 4 * (n / 4) + i % 4 = i by omega]

theorem wF_flag (g : Nat → UInt8) (n : Nat) (s : PB) (I : Inv g n s) (i : Nat) (hi : i < n)
    (hf : (wF s).get! (17 * (i / 64)) = 1) : acgt (g i) = true := by
  by_cases h : i < 64 * (n / 64)
  · rw [wF_old s _ (by rw [I.wsize]; unfold wsz; split <;> omega)] at hf
    exact I.flagOk i h hf
  · have h0 : n % 64 ≠ 0 := by omega
    rw [wF_old s _ (by rw [I.wsize]; unfold wsz; rw [if_neg h0]; omega), show i / 64 = n / 64 by omega,
      I.flag0 h0] at hf
    cases hf

theorem finish_raw (g : Nat → UInt8) (n : Nat) (s : PB) (I : Inv g n s) (hn : n < 2 ^ 32) (i : Nat) (hi : i < n) :
    s.finish.raw i = g i := by
  have hcode : (s.finish.code i).toNat = c2N (g i) := by
    rw [code_eq, finish_w]; exact (wF_code g n s I i hi).1
  have hlet : acgt (g i) = true → letter (s.finish.code i) = g i := fun ha =>
    ((letter_iff (g i) _ ha (by rw [hcode]; exact c2N_lt _)).2 hcode.symm).symm
  rw [raw_eq, finish_w, Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 6 = 64 from rfl]
  split
  · rename_i hf; exact hlet (wF_flag g n s I i hi (by simpa using hf))
  · -- the runs
    have E := I.ex
    obtain ⟨hps, hpu⟩ := pack32_spec s.ex
    have hsz : s.ex.size = 3 * cnt s.ex := by have := E.exm; unfold cnt; omega
    have hC : len32 (pack32 s.ex) / 3 = cnt s.ex := by unfold len32; rw [hps]; unfold cnt; omega
    have hS : ∀ k, k < cnt s.ex → u32 (pack32 s.ex) (3 * k) = st s.ex k := fun k hk => by
      rw [hpu _ (by omega)]; rfl
    have hcl := cnt_le s.ex g n E
    obtain ⟨hlo, hhi, hle⟩ := exFind_spec (pack32 s.ex) i (cnt s.ex)
      (fun a b hab hb => by rw [hS a (by omega), hS b hb]; exact st_mono s.ex g n E a b hab hb)
      64 0 (cnt s.ex) (Nat.zero_le _) (Nat.le_refl _)
      (Nat.lt_of_le_of_lt (by omega) (Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by omega) (by omega))))
      (fun k hk => by omega) (fun k hk hc => by omega)
    unfold PGen.slow
    simp only [show (PB.finish s).ex = pack32 s.ex from rfl, hC]
    generalize ht : exFind (pack32 s.ex) i 64 0 (cnt s.ex) = t at hlo hhi hle
    have hen : ∀ k, k < cnt s.ex → u32 (pack32 s.ex) (3 * k + 1) = en s.ex k := fun k hk => by
      rw [hpu _ (by omega)]; rfl
    have hby : ∀ k, k < cnt s.ex → u32 (pack32 s.ex) (3 * k + 2) = by' s.ex k := fun k hk => by
      rw [hpu _ (by omega)]; rfl
    split
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      rw [hby _ (by omega)]
      have h1 : st s.ex (t - 1) ≤ i := by rw [← hS _ (by omega)]; exact hlo _ (by omega)
      have h2 : i < en s.ex (t - 1) := by rw [← hen _ (by omega)]; exact hc.2
      rw [← E.r3 (t - 1) (by omega) i h1 h2]; simp
    · rename_i hc
      apply hlet
      rcases Bool.eq_false_or_eq_true (acgt (g i)) with hna | hna
      · exact hna
      exfalso
      obtain ⟨k, hk, h1, h2⟩ := E.r4 i hi hna
      have hkt : k < t := by
        by_cases hkt : k < t
        · exact hkt
        · have := hhi k (by omega) hk; rw [hS k hk] at this; omega
      apply hc
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨by omega, ?_⟩
      rw [hen _ (by omega)]
      by_cases e : k = t - 1
      · rw [← e]; exact h2
      · have h3 := E.r2 k (by omega)
        have h4 : st s.ex (k + 1) ≤ i := by rw [← hS _ (by omega)]; exact hlo _ (by omega)
        omega


theorem code_congr (P P' : PGen) (i : Nat) (h : P'.w.get! (cpos i) = P.w.get! (cpos i)) : P'.code i = P.code i := by
  unfold PGen.code
  have e1 : i >>> 6 = i / 64 := by rw [Nat.shiftRight_eq_div_pow]
  have e2 : (i >>> 2) &&& 15 = i % 64 / 4 := by
    rw [Nat.shiftRight_eq_div_pow, show (15 : Nat) = 2 ^ 4 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [e1, e2]; unfold cpos at h; rw [h]

/-- Two packed genomes with the same runs and the same block bytes at `i` agree at `i`. -/
theorem raw_congr (P P' : PGen) (i : Nat) (hex : P'.ex = P.ex)
    (hf : P'.w.get! (17 * (i / 64)) = P.w.get! (17 * (i / 64))) (hc : P'.w.get! (cpos i) = P.w.get! (cpos i)) :
    P'.raw i = P.raw i := by
  have hs : P'.slow i = P.slow i := by unfold PGen.slow; rw [hex, code_congr P P' i hc]
  rw [raw_eq, raw_eq, Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 6 = 64 from rfl, hf, code_congr P P' i hc, hs]

/-! ## All chromosomes -/

def catL : List ByteArray → List UInt8
  | [] => []
  | b :: r => b.data.toList ++ catL r

def offL : Nat → List ByteArray → List Nat
  | _, [] => []
  | m, b :: r => m :: offL (m + b.size) r

theorem catL_length : ∀ L : List ByteArray, (catL L).length = (L.map (·.size)).sum
  | [] => rfl
  | b :: r => by simp [catL, catL_length r]

theorem offL_length : ∀ (L : List ByteArray) m, (offL m L).length = L.length
  | [], _ => rfl
  | b :: r, m => by simp [offL, offL_length r]

theorem dl_len (b : ByteArray) : b.data.toList.length = b.size := by rw [Array.length_toList]; rfl

theorem dl_get (b : ByteArray) (j : Nat) (hj : j < b.size) (L : List UInt8) :
    (b.data.toList ++ L)[j]! = b.get! j := by
  rw [getElem!_pos _ j (by rw [List.length_append, dl_len]; omega), List.getElem_append_left (by rw [dl_len]; exact hj),
    Array.getElem_toList, bget, getElem!_pos b.data j hj]

theorem offL_spec : ∀ (L : List ByteArray) (m c : Nat) (hc : c < L.length),
    m ≤ (offL m L)[c]! ∧ (offL m L)[c]! - m + L[c].size ≤ (catL L).length ∧
    ∀ j, j < L[c].size → (catL L)[(offL m L)[c]! - m + j]! = L[c].get! j
  | [], _, _, hc => by simp at hc
  | b :: r, m, c, hc => by
    cases c with
    | zero =>
      simp only [offL, catL, List.getElem!_cons_zero, List.getElem_cons_zero, List.length_append, Nat.sub_self,
        Nat.zero_add, dl_len]
      exact ⟨Nat.le_refl _, by omega, fun j hj => dl_get b j hj _⟩
    | succ c =>
      have hc' : c < r.length := by simp at hc; omega
      obtain ⟨h1, h2, h3⟩ := offL_spec r (m + b.size) c hc'
      simp only [offL, catL, List.getElem!_cons_succ, List.getElem_cons_succ, List.length_append, dl_len]
      generalize ho : (offL (m + b.size) r)[c]! = o at h1 h2 h3
      refine ⟨by omega, by omega, fun j hj => ?_⟩
      have hl : o - (m + b.size) + j < (catL r).length := by omega
      rw [getElem!_pos _ _ (by rw [List.length_append, dl_len]; omega), List.getElem_append_right (by rw [dl_len]; omega)]
      rw [← h3 j hj, getElem!_pos (catL r) _ hl]; congr 1; rw [dl_len]; omega

theorem offsOf_eq (gbs : Array ByteArray) : Index.offsOf gbs = (offL 0 gbs.toList).toArray := by
  unfold Index.offsOf
  rw [← Array.foldl_toList]
  suffices ∀ (L : List ByteArray) (o : Array Nat) (m : Nat),
      (L.foldl (fun (x : Array Nat × Nat) g => (x.1.push x.2, x.2 + g.size)) (o, m)).1 = o ++ (offL m L).toArray by
    simpa using this gbs.toList #[] 0
  intro L
  induction L with
  | nil => intro o m; simp [offL]
  | cons b r ih => intro o m; simp only [List.foldl_cons, offL]; rw [ih]; simp

theorem packAll_eq (gbs : Array ByteArray) :
    Index.packAll gbs = ((catL gbs.toList).foldl PB.push (PB.init (gbs.foldl (· + ·.size) 0))).finish := by
  unfold Index.packAll
  congr 1
  rw [← Array.foldl_toList]
  generalize PB.init _ = s0
  have e : (fun s (g : ByteArray) => g.foldl PB.push s) = (fun s (g : ByteArray) => g.data.toList.foldl PB.push s) := by
    funext s g; exact foldl_list _ _ _
  rw [e]
  induction gbs.toList generalizing s0 with
  | nil => rfl
  | cons b r ih => simp only [List.foldl_cons, catL, List.foldl_append]; exact ih _


/-- The bytes of all chromosomes, one after the other. -/
def catG (byteGenome : GenomeFile) : List UInt8 := catL (byteGenome.map (·.2)).toList

/-- Bytes of blocks for `N` letters. -/
def wBytes (N : Nat) : Nat := 17 * (N / 64) + (if N % 64 = 0 then 0 else 1 + (N % 64 + 3) / 4)

/-- The packed genome `buildLoaded` makes spells `catG`, and its block bytes for each letter are in
`G.w`. -/
theorem packAll_spec (byteGenome : GenomeFile) (hN : (catG byteGenome).length < 2 ^ 32) :
    let G := Index.packAll (byteGenome.map (·.2))
    G.n = (catG byteGenome).length ∧ G.o = 0 ∧
    (∀ i, i < G.n → G.raw i = (catG byteGenome)[i]! ∧ 17 * (i / 64) < G.w.size ∧ cpos i < G.w.size) ∧
    G.w.size = wBytes (catG byteGenome).length ∧ G.ex.size ≤ 12 * (catG byteGenome).length := by
  intro G
  have hG : G = _ := packAll_eq _
  generalize hL : catL (byteGenome.map (·.2)).toList = L at hG
  have hL' : catG byteGenome = L := hL
  rw [hL'] at hN ⊢
  have I := fold_inv (fun i => L[i]!) L 0 _ (init_inv _ (Array.foldl (fun x1 x2 => x1 + x2.size) 0 (byteGenome.map (·.2))))
    (fun j _ => by simp) (by simpa using hN)
  rw [Nat.zero_add] at I
  rw [hG]
  refine ⟨I.hn, rfl, fun i hi => ?_, by rw [finish_w, wF_size _ _ _ I]; rfl, ?_⟩
  · have hi' : i < L.length := by rw [show (PB.finish _).n = _ from I.hn] at hi; exact hi
    refine ⟨finish_raw _ _ _ I hN i hi', ?_, ?_⟩
    · rw [finish_w, wF_size _ _ _ I]; split <;> omega
    · rw [finish_w]; exact (wF_code _ _ _ I i hi').2
  · show (pack32 _).size ≤ _
    rw [(pack32_spec _).1]
    have h1 := cnt_le _ _ _ I.ex
    have h2 := I.ex.exm
    unfold cnt at h1
    omega

theorem eqRunP_of (P : PGen) (b : ByteArray) : ∀ k i, (∀ j, i ≤ j → j < i + k → P.get j = b.get! j) →
    Index.eqRunP P b i k = true := by
  intro k
  induction k with
  | zero => intro i _; rfl
  | succ k ih =>
    intro i h
    simp only [Index.eqRunP, Bool.and_eq_true, beq_iff_eq]
    exact ⟨h i (Nat.le_refl _) (by omega), ih (i + 1) fun j h1 h2 => h j (by omega) (by omega)⟩

/-- **The genome checks pass** on any packed genome (window at 0) that spells the chromosomes one
after the other, with `buildLoaded`'s offsets and lengths. -/
theorem genomeChecks (byteGenome : GenomeFile) (G : PGen) (hn : G.n = (catG byteGenome).length) (ho : G.o = 0)
    (hr : ∀ i, i < G.n → G.raw i = (catG byteGenome)[i]!) :
    cutOk G (Index.offsOf (byteGenome.map (·.2))) ((byteGenome.map (·.2)).map (·.size)) = true ∧
    Index.chromsOk byteGenome G (Index.offsOf (byteGenome.map (·.2))) ((byteGenome.map (·.2)).map (·.size)) = true := by
  unfold catG at hn hr
  have hsp := offL_spec (byteGenome.map (·.2)).toList 0
  have hoffs : ∀ c, c < byteGenome.size → (Index.offsOf (byteGenome.map (·.2)))[c]! = (offL 0 (byteGenome.map (·.2)).toList)[c]! := by
    intro c hc; rw [offsOf_eq]; simp
  have hns : ∀ c, c < byteGenome.size → ((byteGenome.map (·.2)).map (·.size))[c]! = byteGenome[c]!.2.size := by
    intro c hc; rw [getElem!_pos _ c (by simpa using hc), getElem!_pos _ c hc]; simp
  have hlen : ∀ c (hc : c < byteGenome.size), ((byteGenome.map (·.2)).toList)[c]'(by simpa using hc) = byteGenome[c]!.2 := by
    intro c hc; rw [getElem!_pos _ c hc]; simp
  constructor
  · simp only [cutOk, Bool.and_eq_true, beq_iff_eq, ho, List.all_eq_true, List.mem_range, decide_eq_true_eq, true_and]
    intro c hc
    have hc' : c < byteGenome.size := by simpa using hc
    obtain ⟨-, h2, -⟩ := hsp c (by simpa using hc')
    rw [hoffs c hc', hns c hc', hn, ← hlen c hc']
    exact Nat.le_trans (by omega) h2
  · simp only [Index.chromsOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range]
    refine ⟨by simp, fun c hc => ?_⟩
    have hc' : c < byteGenome.size := by simpa using hc
    obtain ⟨-, h2, h3⟩ := hsp c (by simpa using hc')
    rw [cutAll_get _ _ _ c hc]
    have hv : ∀ j, (view G (Index.offsOf (byteGenome.map (·.2)))[c]! ((byteGenome.map (·.2)).map (·.size))[c]!).get j =
        if j < byteGenome[c]!.2.size then G.raw (G.o + (Index.offsOf (byteGenome.map (·.2)))[c]! + j) else 0 := by
      intro j; rw [hns c hc']; rfl
    have hvn : (view G (Index.offsOf (byteGenome.map (·.2)))[c]! ((byteGenome.map (·.2)).map (·.size))[c]!).n =
        byteGenome[c]!.2.size := by rw [hns c hc']; rfl
    simp only [Index.chromOk, Bool.and_eq_true, beq_iff_eq, hvn]
    refine ⟨trivial, eqRunP_of _ _ _ 0 fun j _ hj => ?_⟩
    simp only [Nat.zero_add] at hj
    rw [hlen c hc'] at h2 h3
    rw [hv, if_pos hj, hr _ (by rw [ho, hoffs c hc', hn]; omega), ho, hoffs c hc', ← h3 j hj]
    congr 1; omega

end Spec.Pack

#print axioms Spec.Pack.genomeChecks
#print axioms Spec.Pack.packAll_spec
