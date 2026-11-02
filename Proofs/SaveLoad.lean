import Proofs.Pack
import Proofs.Aligner

/-! # Save, then load (`Proofs/Aligner.lean`'s `saveIndex` / `loadIndex`)

Each writer (`putU64`, `putNat`, `putNats`, `putBytes`, `putMz`, `putPGen`) leaves its bytes as a
prefix (`Pre`) of everything written after, and its reader at that place gets the value back
(numbers must fit 64 bits). `loadIndex_saveIndex`: loading the saved bytes gives the same small
fields, `offs`, `ns`, and the saved bytes themselves as `G.w`, `ix.offs`, `ix.sl` (`ix.ob` the place
of the offsets). `save_w`, `save_sl`, `save_offs`: those bytes start with `G.w`, hold `ix.sl` from
slot `m`, and offset `b` plus `m` at `UInt32` `ob + b`. -/
open MapSpec MapSpec.Fast

namespace Spec.SaveLoad
open Spec.Pack

/-- `a` is a prefix of `bs`. -/
def Pre (a bs : ByteArray) : Prop := a.size ≤ bs.size ∧ ∀ i, i < a.size → bs.get! i = a.get! i

theorem Pre.trans {a b c : ByteArray} (h1 : Pre a b) (h2 : Pre b c) : Pre a c :=
  ⟨Nat.le_trans h1.1 h2.1, fun i hi => by rw [h2.2 i (by have := h1.1; omega), h1.2 i hi]⟩

theorem Pre.refl (a : ByteArray) : Pre a a := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem pre_push (b : ByteArray) (x : UInt8) : Pre b (b.push x) :=
  ⟨by simp, fun i hi => by rw [get_push, if_pos hi]⟩

/-! ## `UInt64` -/

def u64acc (bs : ByteArray) (p : Nat) (k : Nat) : UInt64 :=
  (List.range k).foldl (fun x i => x ||| ((bs.get! (p + i)).toUInt64 <<< (8 * i).toUInt64)) 0

def putK (b : ByteArray) (x : UInt64) (k : Nat) : ByteArray :=
  (List.range k).foldl (fun b i => b.push (x >>> (8 * i).toUInt64).toUInt8) b

theorem putK_spec (b : ByteArray) (x : UInt64) : ∀ k, (putK b x k).size = b.size + k ∧ Pre b (putK b x k) ∧
    ∀ i, i < k → (putK b x k).get! (b.size + i) = (x >>> (8 * i).toUInt64).toUInt8 := by
  intro k
  induction k with
  | zero => exact ⟨rfl, Pre.refl _, fun i hi => by omega⟩
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have e : putK b x (k + 1) = (putK b x k).push (x >>> (8 * k).toUInt64).toUInt8 := by
      simp [putK, List.range_succ, List.foldl_append]
    rw [e]
    refine ⟨by simp [h1]; omega, h2.trans (pre_push _ _), fun i hi => ?_⟩
    rw [get_push]
    by_cases e2 : i < k
    · rw [if_pos (by omega)]; exact h3 i e2
    · rw [if_neg (by omega), if_pos (by omega), show i = k by omega]

theorem byte64 (x : UInt64) (i : Nat) (hi : i < 8) :
    ((x >>> (8 * i).toUInt64).toUInt8.toUInt64 <<< (8 * i).toUInt64).toNat = x.toNat / 2 ^ (8 * i) % 256 * 2 ^ (8 * i) := by
  have h8 : (8 * i).toUInt64.toNat = 8 * i := by
    rw [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  rw [UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, h8,
    Nat.mod_eq_of_lt (by omega : 8 * i < 64), Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  apply Nat.mod_eq_of_lt
  have : x.toNat / 2 ^ (8 * i) % 256 < 256 := Nat.mod_lt _ (by omega)
  have h2 : 2 ^ (8 * i) * 256 ≤ 2 ^ 64 := by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega)
  calc _ < 256 * 2 ^ (8 * i) := Nat.mul_lt_mul_of_pos_right this (Nat.pow_pos (by omega))
    _ ≤ 2 ^ 64 := by rw [Nat.mul_comm]; exact h2

theorem u64acc_spec (bs : ByteArray) (p : Nat) (x : UInt64) (hb : ∀ i, i < 8 → bs.get! (p + i) = (x >>> (8 * i).toUInt64).toUInt8) :
    ∀ k, k ≤ 8 → (u64acc bs p k).toNat = x.toNat % 2 ^ (8 * k) := by
  intro k
  induction k with
  | zero => intro _; simp [u64acc, Nat.mod_one]
  | succ k ih =>
    intro hk
    have e : u64acc bs p (k + 1) = u64acc bs p k ||| ((bs.get! (p + k)).toUInt64 <<< (8 * k).toUInt64) := by
      simp [u64acc, List.range_succ, List.foldl_append]
    rw [e, UInt64.toNat_or, hb k (by omega), byte64 x k (by omega), ih (by omega)]
    have hlt : x.toNat % 2 ^ (8 * k) < 2 ^ (8 * k) := Nat.mod_lt _ (Nat.pow_pos (by omega))
    rw [Nat.or_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt hlt]
    rw [show 8 * (k + 1) = 8 * k + 8 by omega, Nat.pow_add, Nat.mod_mul]
    rw [show (2 : Nat) ^ 8 = 256 from rfl]
    omega


theorem putU64_eq (b : ByteArray) (x : UInt64) : Index.putU64 b x = putK b x 8 := rfl

theorem putU64_size (b : ByteArray) (x : UInt64) : (Index.putU64 b x).size = b.size + 8 :=
  (putK_spec b x 8).1

theorem pre_putU64 (b : ByteArray) (x : UInt64) : Pre b (Index.putU64 b x) := (putK_spec b x 8).2.1

theorem putNat_size (b : ByteArray) (x : Nat) : (Index.putNat b x).size = b.size + 8 := putU64_size _ _

theorem pre_putNat (b : ByteArray) (x : Nat) : Pre b (Index.putNat b x) := pre_putU64 _ _

theorem rdU64_put (b bs : ByteArray) (x : UInt64) (h : Pre (Index.putU64 b x) bs) :
    Index.rdU64 bs b.size = some (x, b.size + 8) := by
  obtain ⟨hs, hp, hb⟩ := putK_spec b x 8
  have hsz : b.size + 8 ≤ bs.size := by have := h.1; rw [putU64_eq] at this; omega
  unfold Index.rdU64
  rw [if_pos hsz]
  have := u64acc_spec bs b.size x (fun i hi => by
    rw [h.2 _ (by rw [putU64_eq, hs]; omega), putU64_eq, hb i hi]) 8 (Nat.le_refl _)
  have e : u64acc bs b.size 8 = x := by
    apply UInt64.toNat_inj.1; rw [this]; exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)
  rw [← e]; rfl

theorem rdNat_put (b bs : ByteArray) (x : Nat) (hx : x < 2 ^ 64) (h : Pre (Index.putNat b x) bs) :
    Index.rdNat bs b.size = some (x, b.size + 8) := by
  have := rdU64_put b bs x.toUInt64 h
  show (do let v ← Index.rdU64 bs; pure v.toNat : Index.Rd Nat) b.size = _
  simp only [bind, StateT.bind, this, pure, StateT.pure, Option.bind_some]
  rw [show x.toUInt64.toNat = x by rw [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hx]]


theorem foldl_putNat (L : List Nat) : ∀ b : ByteArray, (L.foldl Index.putNat b).size = b.size + 8 * L.length ∧
    Pre b (L.foldl Index.putNat b) := by
  induction L with
  | nil => intro b; exact ⟨by simp, Pre.refl _⟩
  | cons x L ih =>
    intro b
    obtain ⟨h1, h2⟩ := ih (Index.putNat b x)
    simp only [List.foldl_cons, List.length_cons]
    exact ⟨by rw [h1, putNat_size]; omega, (pre_putNat b x).trans h2⟩

theorem rdNatsGo_put (bs : ByteArray) (L : List Nat) (hL : ∀ x ∈ L, x < 2 ^ 64) :
    ∀ (b : ByteArray) (acc : Array Nat), Pre (L.foldl Index.putNat b) bs →
      Index.rdNatsGo bs L.length acc b.size = some (acc ++ L.toArray, b.size + 8 * L.length) := by
  induction L with
  | nil => intro b acc _; simp [Index.rdNatsGo]; rfl
  | cons x L ih =>
    intro b acc h
    simp only [List.foldl_cons] at h
    have hx := rdNat_put b bs x (hL x (by simp)) ((foldl_putNat L _).2.trans h)
    have := ih (fun y hy => hL y (by simp [hy])) (Index.putNat b x) (acc.push x) h
    rw [putNat_size] at this
    simp only [List.length_cons, Index.rdNatsGo, bind, StateT.bind, hx, Option.bind_some, this]
    simp; omega

theorem putNats_size (b : ByteArray) (xs : Array Nat) : (Index.putNats b xs).size = b.size + 8 + 8 * xs.size := by
  unfold Index.putNats; rw [← Array.foldl_toList, (foldl_putNat _ _).1, putNat_size]; simp

theorem pre_putNats (b : ByteArray) (xs : Array Nat) : Pre b (Index.putNats b xs) := by
  unfold Index.putNats; rw [← Array.foldl_toList]; exact (pre_putNat _ _).trans (foldl_putNat _ _).2

theorem rdNats_put (b bs : ByteArray) (xs : Array Nat) (hn : xs.size < 2 ^ 64) (hx : ∀ x ∈ xs, x < 2 ^ 64)
    (h : Pre (Index.putNats b xs) bs) : Index.rdNats bs b.size = some (xs, b.size + 8 + 8 * xs.size) := by
  have h' : Pre (xs.toList.foldl Index.putNat (Index.putNat b xs.size)) bs := by
    unfold Index.putNats at h; rwa [← Array.foldl_toList] at h
  have hn' := rdNat_put b bs xs.size hn ((foldl_putNat _ _).2.trans h')
  have hg := rdNatsGo_put bs xs.toList (fun x hx' => hx x (by simpa using hx')) _ (Array.emptyWithCapacity xs.size) h'
  rw [putNat_size] at hg
  have hsz : b.size + 8 + 8 * xs.size ≤ bs.size := by
    have := h.1; rw [putNats_size] at this; exact this
  unfold Index.rdNats
  simp only [bind, StateT.bind, hn', Option.bind_some, get, getThe, MonadStateOf.get, StateT.get, pure,
    StateT.pure]
  rw [if_pos hsz]
  simp only [Array.length_toList] at hg
  rw [hg]; simp

theorem putBytes_size (b x : ByteArray) : (Index.putBytes b x).size = b.size + 8 + x.size := by
  simp [Index.putBytes, putNat_size]

theorem pre_putBytes0 (b x : ByteArray) : Pre (Index.putNat b x.size) (Index.putBytes b x) := by
  refine ⟨by rw [putBytes_size, putNat_size]; omega, fun i hi => ?_⟩
  unfold Index.putBytes
  rw [bget, bget, ByteArray.data_append, getElem!_pos _ i (by simp; omega), getElem!_pos _ i hi, Array.getElem_append_left]

theorem pre_putBytes (b x : ByteArray) : Pre b (Index.putBytes b x) := (pre_putNat b x.size).trans (pre_putBytes0 b x)

theorem rdBytes_put (b bs x : ByteArray) (hn : x.size < 2 ^ 64) (h : Pre (Index.putBytes b x) bs) :
    Index.rdBytes bs b.size = some (x, b.size + 8 + x.size) := by
  have hn' := rdNat_put b bs x.size hn ((pre_putBytes0 b x).trans h)
  have hsz : b.size + 8 + x.size ≤ bs.size := by have := h.1; rw [putBytes_size] at this; exact this
  unfold Index.rdBytes
  simp only [bind, StateT.bind, hn', Option.bind_some, get, getThe, MonadStateOf.get, StateT.get, pure,
    StateT.pure, set, MonadStateOf.set, StateT.set]
  rw [if_pos hsz]
  show some (bs.extract (b.size + 8) (b.size + 8 + x.size), b.size + 8 + x.size) = _
  congr
  apply ByteArray.ext_getElem (by simp; omega)
  intro i hi hi'
  have := h.2 (b.size + 8 + i) (by rw [putBytes_size]; omega)
  rw [ByteArray.getElem_extract]
  have e1 := bget bs (b.size + 8 + i)
  have e2 := bget (Index.putBytes b x) (b.size + 8 + i)
  rw [getElem!_pos _ _ (by simp; omega)] at e1
  unfold Index.putBytes at e2
  rw [ByteArray.data_append, getElem!_pos _ _ (by simp [putNat_size]; omega),
    Array.getElem_append_right (by simp [putNat_size])] at e2
  simp only [ByteArray.getElem_eq_getElem_data]
  have e3 := e1.symm.trans (this.trans e2)
  rw [e3]
  congr 1
  have : (Index.putNat b x.size).data.size = b.size + 8 := putNat_size _ _
  omega


/-! ## Readers ending where the next writer starts -/

theorem rdNat_put' (b bs : ByteArray) (x : Nat) (hx : x < 2 ^ 64) (h : Pre (Index.putNat b x) bs) :
    Index.rdNat bs b.size = some (x, (Index.putNat b x).size) := by
  rw [rdNat_put b bs x hx h, putNat_size]

theorem rdU64_put' (b bs : ByteArray) (x : UInt64) (h : Pre (Index.putU64 b x) bs) :
    Index.rdU64 bs b.size = some (x, (Index.putU64 b x).size) := by
  rw [rdU64_put b bs x h, putU64_size]

theorem rdNats_put' (b bs : ByteArray) (xs : Array Nat) (hn : xs.size < 2 ^ 64) (hx : ∀ x ∈ xs, x < 2 ^ 64)
    (h : Pre (Index.putNats b xs) bs) : Index.rdNats bs b.size = some (xs, (Index.putNats b xs).size) := by
  rw [rdNats_put b bs xs hn hx h, putNats_size]

theorem rdBytes_put' (b bs x : ByteArray) (hn : x.size < 2 ^ 64) (h : Pre (Index.putBytes b x) bs) :
    Index.rdBytes bs b.size = some (x, (Index.putBytes b x).size) := by
  rw [rdBytes_put b bs x hn h, putBytes_size]

/-- Every number `putMz` writes fits 64 bits. -/
def MzFits (ix : Mz.MzIdx) (ob : Nat) : Prop :=
  ix.k < 2 ^ 64 ∧ ix.B < 2 ^ 64 ∧ ix.w < 2 ^ 64 ∧ ix.c < 2 ^ 64 ∧ ix.kb < 2 ^ 64 ∧ ix.kf < 2 ^ 64 ∧
  ix.T < 2 ^ 64 ∧ ix.t < 2 ^ 64 ∧ ix.kbM < 2 ^ 64 ∧ ix.fM < 2 ^ 64 ∧ ix.tM < 2 ^ 64 ∧
  ix.pm.size < 2 ^ 64 ∧ (∀ x ∈ ix.pm, x < 2 ^ 64) ∧ ix.bsh < 2 ^ 64 ∧ ix.ash < 2 ^ 64 ∧ ix.fsh < 2 ^ 64 ∧
  ob < 2 ^ 64 ∧ ix.sw < 2 ^ 64 ∧ ix.runs.size < 2 ^ 64 ∧ (∀ x ∈ ix.runs, x < 2 ^ 64)

theorem rdMz_put (b bs : ByteArray) (ix : Mz.MzIdx) (ob : Nat) (hf : MzFits ix ob) (h : Pre (Index.putMz b ix ob) bs) :
    Index.rdMz bs b.size = some ({ ix with offs := bs, ob := ob, sl := bs }, (Index.putMz b ix ob).size) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20⟩ := hf
  obtain ⟨b1, eb1⟩ : ∃ x, Index.putNat b ix.k = x := ⟨_, rfl⟩
  obtain ⟨b2, eb2⟩ : ∃ x, Index.putNat b1 ix.B = x := ⟨_, rfl⟩
  obtain ⟨b3, eb3⟩ : ∃ x, Index.putNat b2 ix.w = x := ⟨_, rfl⟩
  obtain ⟨b4, eb4⟩ : ∃ x, Index.putNat b3 ix.c = x := ⟨_, rfl⟩
  obtain ⟨b5, eb5⟩ : ∃ x, Index.putNat b4 ix.kb = x := ⟨_, rfl⟩
  obtain ⟨b6, eb6⟩ : ∃ x, Index.putNat b5 ix.kf = x := ⟨_, rfl⟩
  obtain ⟨b7, eb7⟩ : ∃ x, Index.putNat b6 ix.T = x := ⟨_, rfl⟩
  obtain ⟨b8, eb8⟩ : ∃ x, Index.putU64 b7 ix.kmU = x := ⟨_, rfl⟩
  obtain ⟨b9, eb9⟩ : ∃ x, Index.putNat b8 ix.t = x := ⟨_, rfl⟩
  obtain ⟨b10, eb10⟩ : ∃ x, Index.putU64 b9 ix.tmU = x := ⟨_, rfl⟩
  obtain ⟨b11, eb11⟩ : ∃ x, Index.putNat b10 ix.kbM = x := ⟨_, rfl⟩
  obtain ⟨b12, eb12⟩ : ∃ x, Index.putNat b11 ix.fM = x := ⟨_, rfl⟩
  obtain ⟨b13, eb13⟩ : ∃ x, Index.putNat b12 ix.tM = x := ⟨_, rfl⟩
  obtain ⟨b14, eb14⟩ : ∃ x, Index.putNats b13 ix.pm = x := ⟨_, rfl⟩
  obtain ⟨b15, eb15⟩ : ∃ x, Index.putNat b14 ix.bsh = x := ⟨_, rfl⟩
  obtain ⟨b16, eb16⟩ : ∃ x, Index.putNat b15 ix.ash = x := ⟨_, rfl⟩
  obtain ⟨b17, eb17⟩ : ∃ x, Index.putNat b16 ix.fsh = x := ⟨_, rfl⟩
  obtain ⟨b18, eb18⟩ : ∃ x, Index.putNat b17 ob = x := ⟨_, rfl⟩
  obtain ⟨b19, eb19⟩ : ∃ x, Index.putNat b18 ix.sw = x := ⟨_, rfl⟩
  obtain ⟨b20, eb20⟩ : ∃ x, Index.putNats b19 ix.runs = x := ⟨_, rfl⟩
  have e : Index.putMz b ix ob = b20 := by
    simp only [Index.putMz, List.foldl, eb1, eb2, eb3, eb4, eb5, eb6, eb7, eb8, eb9, eb10, eb11, eb12, eb13, eb14, eb15, eb16, eb17, eb18, eb19, eb20]
  rw [e] at h ⊢
  have p20 : Pre b20 bs := h
  have p19 : Pre b19 bs := Pre.trans (b := b20) (by rw [← eb20]; exact pre_putNats _ _) p20
  have p18 : Pre b18 bs := Pre.trans (b := b19) (by rw [← eb19]; exact pre_putNat _ _) p19
  have p17 : Pre b17 bs := Pre.trans (b := b18) (by rw [← eb18]; exact pre_putNat _ _) p18
  have p16 : Pre b16 bs := Pre.trans (b := b17) (by rw [← eb17]; exact pre_putNat _ _) p17
  have p15 : Pre b15 bs := Pre.trans (b := b16) (by rw [← eb16]; exact pre_putNat _ _) p16
  have p14 : Pre b14 bs := Pre.trans (b := b15) (by rw [← eb15]; exact pre_putNat _ _) p15
  have p13 : Pre b13 bs := Pre.trans (b := b14) (by rw [← eb14]; exact pre_putNats _ _) p14
  have p12 : Pre b12 bs := Pre.trans (b := b13) (by rw [← eb13]; exact pre_putNat _ _) p13
  have p11 : Pre b11 bs := Pre.trans (b := b12) (by rw [← eb12]; exact pre_putNat _ _) p12
  have p10 : Pre b10 bs := Pre.trans (b := b11) (by rw [← eb11]; exact pre_putNat _ _) p11
  have p9 : Pre b9 bs := Pre.trans (b := b10) (by rw [← eb10]; exact pre_putU64 _ _) p10
  have p8 : Pre b8 bs := Pre.trans (b := b9) (by rw [← eb9]; exact pre_putNat _ _) p9
  have p7 : Pre b7 bs := Pre.trans (b := b8) (by rw [← eb8]; exact pre_putU64 _ _) p8
  have p6 : Pre b6 bs := Pre.trans (b := b7) (by rw [← eb7]; exact pre_putNat _ _) p7
  have p5 : Pre b5 bs := Pre.trans (b := b6) (by rw [← eb6]; exact pre_putNat _ _) p6
  have p4 : Pre b4 bs := Pre.trans (b := b5) (by rw [← eb5]; exact pre_putNat _ _) p5
  have p3 : Pre b3 bs := Pre.trans (b := b4) (by rw [← eb4]; exact pre_putNat _ _) p4
  have p2 : Pre b2 bs := Pre.trans (b := b3) (by rw [← eb3]; exact pre_putNat _ _) p3
  have p1 : Pre b1 bs := Pre.trans (b := b2) (by rw [← eb2]; exact pre_putNat _ _) p2
  have r1 := rdNat_put' b bs _ f1 (by rw [eb1]; exact p1)
  rw [eb1] at r1
  have r2 := rdNat_put' b1 bs _ f2 (by rw [eb2]; exact p2)
  rw [eb2] at r2
  have r3 := rdNat_put' b2 bs _ f3 (by rw [eb3]; exact p3)
  rw [eb3] at r3
  have r4 := rdNat_put' b3 bs _ f4 (by rw [eb4]; exact p4)
  rw [eb4] at r4
  have r5 := rdNat_put' b4 bs _ f5 (by rw [eb5]; exact p5)
  rw [eb5] at r5
  have r6 := rdNat_put' b5 bs _ f6 (by rw [eb6]; exact p6)
  rw [eb6] at r6
  have r7 := rdNat_put' b6 bs _ f7 (by rw [eb7]; exact p7)
  rw [eb7] at r7
  have r8 := rdU64_put' b7 bs _ (by rw [eb8]; exact p8)
  rw [eb8] at r8
  have r9 := rdNat_put' b8 bs _ f8 (by rw [eb9]; exact p9)
  rw [eb9] at r9
  have r10 := rdU64_put' b9 bs _ (by rw [eb10]; exact p10)
  rw [eb10] at r10
  have r11 := rdNat_put' b10 bs _ f9 (by rw [eb11]; exact p11)
  rw [eb11] at r11
  have r12 := rdNat_put' b11 bs _ f10 (by rw [eb12]; exact p12)
  rw [eb12] at r12
  have r13 := rdNat_put' b12 bs _ f11 (by rw [eb13]; exact p13)
  rw [eb13] at r13
  have r14 := rdNats_put' b13 bs _ f12 f13 (by rw [eb14]; exact p14)
  rw [eb14] at r14
  have r15 := rdNat_put' b14 bs _ f14 (by rw [eb15]; exact p15)
  rw [eb15] at r15
  have r16 := rdNat_put' b15 bs _ f15 (by rw [eb16]; exact p16)
  rw [eb16] at r16
  have r17 := rdNat_put' b16 bs _ f16 (by rw [eb17]; exact p17)
  rw [eb17] at r17
  have r18 := rdNat_put' b17 bs _ f17 (by rw [eb18]; exact p18)
  rw [eb18] at r18
  have r19 := rdNat_put' b18 bs _ f18 (by rw [eb19]; exact p19)
  rw [eb19] at r19
  have r20 := rdNats_put' b19 bs _ f19 f20 (by rw [eb20]; exact p20)
  rw [eb20] at r20
  simp only [Index.rdMz, bind, StateT.bind, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16,
    r17, r18, r19, r20, Option.bind_some, pure, StateT.pure]


theorem pre_putMz (b : ByteArray) (ix : Mz.MzIdx) (ob : Nat) : Pre b (Index.putMz b ix ob) := by
  generalize hbs : Index.putMz b ix ob = bs
  have h : Pre (Index.putMz b ix ob) bs := by rw [hbs]; exact Pre.refl _
  obtain ⟨b1, eb1⟩ : ∃ x, Index.putNat b ix.k = x := ⟨_, rfl⟩
  obtain ⟨b2, eb2⟩ : ∃ x, Index.putNat b1 ix.B = x := ⟨_, rfl⟩
  obtain ⟨b3, eb3⟩ : ∃ x, Index.putNat b2 ix.w = x := ⟨_, rfl⟩
  obtain ⟨b4, eb4⟩ : ∃ x, Index.putNat b3 ix.c = x := ⟨_, rfl⟩
  obtain ⟨b5, eb5⟩ : ∃ x, Index.putNat b4 ix.kb = x := ⟨_, rfl⟩
  obtain ⟨b6, eb6⟩ : ∃ x, Index.putNat b5 ix.kf = x := ⟨_, rfl⟩
  obtain ⟨b7, eb7⟩ : ∃ x, Index.putNat b6 ix.T = x := ⟨_, rfl⟩
  obtain ⟨b8, eb8⟩ : ∃ x, Index.putU64 b7 ix.kmU = x := ⟨_, rfl⟩
  obtain ⟨b9, eb9⟩ : ∃ x, Index.putNat b8 ix.t = x := ⟨_, rfl⟩
  obtain ⟨b10, eb10⟩ : ∃ x, Index.putU64 b9 ix.tmU = x := ⟨_, rfl⟩
  obtain ⟨b11, eb11⟩ : ∃ x, Index.putNat b10 ix.kbM = x := ⟨_, rfl⟩
  obtain ⟨b12, eb12⟩ : ∃ x, Index.putNat b11 ix.fM = x := ⟨_, rfl⟩
  obtain ⟨b13, eb13⟩ : ∃ x, Index.putNat b12 ix.tM = x := ⟨_, rfl⟩
  obtain ⟨b14, eb14⟩ : ∃ x, Index.putNats b13 ix.pm = x := ⟨_, rfl⟩
  obtain ⟨b15, eb15⟩ : ∃ x, Index.putNat b14 ix.bsh = x := ⟨_, rfl⟩
  obtain ⟨b16, eb16⟩ : ∃ x, Index.putNat b15 ix.ash = x := ⟨_, rfl⟩
  obtain ⟨b17, eb17⟩ : ∃ x, Index.putNat b16 ix.fsh = x := ⟨_, rfl⟩
  obtain ⟨b18, eb18⟩ : ∃ x, Index.putNat b17 ob = x := ⟨_, rfl⟩
  obtain ⟨b19, eb19⟩ : ∃ x, Index.putNat b18 ix.sw = x := ⟨_, rfl⟩
  obtain ⟨b20, eb20⟩ : ∃ x, Index.putNats b19 ix.runs = x := ⟨_, rfl⟩
  have e : Index.putMz b ix ob = b20 := by
    simp only [Index.putMz, List.foldl, eb1, eb2, eb3, eb4, eb5, eb6, eb7, eb8, eb9, eb10, eb11, eb12, eb13, eb14, eb15, eb16, eb17, eb18, eb19, eb20]
  rw [e] at h
  have p20 : Pre b20 bs := h
  have p19 : Pre b19 bs := Pre.trans (b := b20) (by rw [← eb20]; exact pre_putNats _ _) p20
  have p18 : Pre b18 bs := Pre.trans (b := b19) (by rw [← eb19]; exact pre_putNat _ _) p19
  have p17 : Pre b17 bs := Pre.trans (b := b18) (by rw [← eb18]; exact pre_putNat _ _) p18
  have p16 : Pre b16 bs := Pre.trans (b := b17) (by rw [← eb17]; exact pre_putNat _ _) p17
  have p15 : Pre b15 bs := Pre.trans (b := b16) (by rw [← eb16]; exact pre_putNat _ _) p16
  have p14 : Pre b14 bs := Pre.trans (b := b15) (by rw [← eb15]; exact pre_putNat _ _) p15
  have p13 : Pre b13 bs := Pre.trans (b := b14) (by rw [← eb14]; exact pre_putNats _ _) p14
  have p12 : Pre b12 bs := Pre.trans (b := b13) (by rw [← eb13]; exact pre_putNat _ _) p13
  have p11 : Pre b11 bs := Pre.trans (b := b12) (by rw [← eb12]; exact pre_putNat _ _) p12
  have p10 : Pre b10 bs := Pre.trans (b := b11) (by rw [← eb11]; exact pre_putNat _ _) p11
  have p9 : Pre b9 bs := Pre.trans (b := b10) (by rw [← eb10]; exact pre_putU64 _ _) p10
  have p8 : Pre b8 bs := Pre.trans (b := b9) (by rw [← eb9]; exact pre_putNat _ _) p9
  have p7 : Pre b7 bs := Pre.trans (b := b8) (by rw [← eb8]; exact pre_putU64 _ _) p8
  have p6 : Pre b6 bs := Pre.trans (b := b7) (by rw [← eb7]; exact pre_putNat _ _) p7
  have p5 : Pre b5 bs := Pre.trans (b := b6) (by rw [← eb6]; exact pre_putNat _ _) p6
  have p4 : Pre b4 bs := Pre.trans (b := b5) (by rw [← eb5]; exact pre_putNat _ _) p5
  have p3 : Pre b3 bs := Pre.trans (b := b4) (by rw [← eb4]; exact pre_putNat _ _) p4
  have p2 : Pre b2 bs := Pre.trans (b := b3) (by rw [← eb3]; exact pre_putNat _ _) p3
  have p1 : Pre b1 bs := Pre.trans (b := b2) (by rw [← eb2]; exact pre_putNat _ _) p2
  exact Pre.trans (b := b1) (by rw [← eb1]; exact pre_putNat _ _) p1

theorem putPGen_eq (b : ByteArray) (G : PGen) :
    Index.putPGen b G = Index.putBytes (Index.putNat (Index.putNat b G.n) G.o) G.ex := rfl

theorem pre_putPGen (b : ByteArray) (G : PGen) : Pre b (Index.putPGen b G) := by
  rw [putPGen_eq]; exact (pre_putNat _ _).trans ((pre_putNat _ _).trans (pre_putBytes _ _))

theorem rdPGen_put (b bs : ByteArray) (G : PGen) (hn : G.n < 2 ^ 64) (ho : G.o < 2 ^ 64) (he : G.ex.size < 2 ^ 64)
    (h : Pre (Index.putPGen b G) bs) :
    Index.rdPGen bs b.size = some ({ G with w := bs }, (Index.putPGen b G).size) := by
  obtain ⟨b1, eb1⟩ : ∃ x, Index.putNat b G.n = x := ⟨_, rfl⟩
  obtain ⟨b2, eb2⟩ : ∃ x, Index.putNat b1 G.o = x := ⟨_, rfl⟩
  obtain ⟨b3, eb3⟩ : ∃ x, Index.putBytes b2 G.ex = x := ⟨_, rfl⟩
  have e : Index.putPGen b G = b3 := by simp only [Index.putPGen, eb1, eb2, eb3]
  rw [e] at h ⊢
  have p2 : Pre b2 bs := Pre.trans (b := b3) (by rw [← eb3]; exact pre_putBytes _ _) h
  have p1 : Pre b1 bs := Pre.trans (b := b2) (by rw [← eb2]; exact pre_putNat _ _) p2
  have r1 := rdNat_put' b bs _ hn (by rw [eb1]; exact p1)
  rw [eb1] at r1
  have r2 := rdNat_put' b1 bs _ ho (by rw [eb2]; exact p2)
  rw [eb2] at r2
  have r3 := rdBytes_put' b2 bs _ he (by rw [eb3]; exact h)
  rw [eb3] at r3
  simp only [Index.rdPGen, bind, StateT.bind, r1, r2, r3, Option.bind_some, pure, StateT.pure]

/-! ## Padding and the bucket offsets -/

theorem pad_spec (b : ByteArray) (a : Nat) : ∀ k, (Nat.fold k (fun _ _ b => b.push 0) b).size = b.size + k ∧
    Pre b (Nat.fold k (fun _ _ (b : ByteArray) => b.push 0) b) := by
  intro k
  induction k with
  | zero => exact ⟨rfl, Pre.refl _⟩
  | succ k ih =>
    rw [Nat.fold_succ]
    exact ⟨by rw [ByteArray.size_push, ih.1]; omega, ih.2.trans (pre_push _ _)⟩

theorem pad_size (b : ByteArray) (a : Nat) : (Index.pad b a).size = b.size + (a - b.size % a) % a :=
  (pad_spec b a _).1

theorem pre_pad (b : ByteArray) (a : Nat) : Pre b (Index.pad b a) := (pad_spec b a _).2

theorem pad_mod (b : ByteArray) (a : Nat) (ha : 0 < a) : (Index.pad b a).size % a = 0 := by
  rw [pad_size]
  have := Nat.mod_lt b.size ha
  by_cases h : b.size % a = 0
  · rw [h, Nat.sub_zero, Nat.mod_self, Nat.add_zero]; exact h
  · rw [Nat.mod_eq_of_lt (show a - b.size % a < a by omega)]
    have := Nat.div_add_mod b.size a
    rw [show b.size + (a - b.size % a) = a * (b.size / a + 1) by rw [Nat.mul_add]; omega]
    exact Nat.mul_mod_right _ _

theorem pre_append (a c : ByteArray) : Pre a (a ++ c) :=
  ⟨by simp, fun i hi => by rw [bget, bget, ByteArray.data_append, getElem!_pos _ i (by simp; omega),
    getElem!_pos _ i hi, Array.getElem_append_left]⟩

theorem get_append_right (a c : ByteArray) (i : Nat) (hi : i < c.size) : (a ++ c).get! (a.size + i) = c.get! i := by
  rw [bget, bget, ByteArray.data_append, getElem!_pos _ _ (by simp; omega), getElem!_pos _ i hi,
    Array.getElem_append_right (by simp)]
  congr 1; simp

theorem getU32_u32 (B : ByteArray) (i : Nat) : getU32 B i = u32 B i := rfl

theorem putOffs_spec (b offs : ByteArray) (m : Nat) : ∀ k,
    (Nat.fold k (fun i _ b => pk b (getU32 offs i + m).toUInt32) b).size = b.size + 4 * k ∧
    Pre b (Nat.fold k (fun i _ b => pk b (getU32 offs i + m).toUInt32) b) ∧
    (b.size % 4 = 0 → ∀ i, i < k →
      getU32 (Nat.fold k (fun i _ b => pk b (getU32 offs i + m).toUInt32) b) (b.size / 4 + i) = (getU32 offs i + m) % 2 ^ 32) := by
  intro k
  induction k with
  | zero => exact ⟨rfl, Pre.refl _, fun _ i hi => by omega⟩
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [Nat.fold_succ]
    refine ⟨by rw [pk_size, h1]; omega, h2.trans ⟨by rw [pk_size]; omega, fun i hi => pk_old _ _ i hi⟩, fun hb i hi => ?_⟩
    rw [getU32_u32]
    by_cases e : i < k
    · rw [u32_pk_old _ _ _ (by rw [h1]; omega), ← getU32_u32, h3 hb i e]
    · rw [show b.size / 4 + i = (Nat.fold k (fun i _ b => pk b (getU32 offs i + m).toUInt32) b).size / 4 by rw [h1]; omega,
        u32_pk_new _ _ (by rw [h1]; omega), show i = k by omega]
      simp [Nat.toUInt32, UInt32.toNat_ofNat']

theorem putOffs_eq (b offs : ByteArray) (m : Nat) :
    Index.putOffs b offs m = Nat.fold (offs.size / 4) (fun i _ b => pk b (getU32 offs i + m).toUInt32) b := rfl


/-! ## Save, then load -/

/-- Where `ix.sl` starts, in slots of `ix.sw` bytes. -/
def mOf (ix : Mz.MzIdx) (G : PGen) : Nat := (Index.pad G.w ix.sw).size / ix.sw

/-- Where the bucket offsets start, in `UInt32`s. -/
def obOf (ix : Mz.MzIdx) (G : PGen) : Nat := (Index.pad (Index.pad G.w ix.sw ++ ix.sl) 4).size / 4

/-- The bytes before the small fields. -/
def bigOf (ix : Mz.MzIdx) (G : PGen) : ByteArray :=
  Index.putOffs (Index.pad (Index.pad G.w ix.sw ++ ix.sl) 4) ix.offs (mOf ix G)

theorem saveIndex_eq (ix : Mz.MzIdx) (G : PGen) (offs ns : Array Nat) :
    saveIndex (ix, G, offs, ns) = Index.putU64 (Index.putNat (Index.putNats (Index.putNats
      (Index.putPGen (Index.putMz (bigOf ix G) ix (obOf ix G)) G) offs) ns) (bigOf ix G).size) Index.magic := by
  have e : ∀ c, ByteArray.emptyWithCapacity c ++ G.w = G.w := fun c => ByteArray.empty_append
  simp only [saveIndex, e]; rfl

/-- What the loader reads back: the small fields, and the saved bytes as `G.w`, `ix.offs`, `ix.sl`. -/
theorem loadIndex_saveIndex (ix : Mz.MzIdx) (G : PGen) (offs ns : Array Nat) (hf : MzFits ix (obOf ix G))
    (hn : G.n < 2 ^ 64) (ho : G.o < 2 ^ 64) (he : G.ex.size < 2 ^ 64)
    (hos : offs.size < 2 ^ 64) (hoe : ∀ x ∈ offs, x < 2 ^ 64) (hns : ns.size < 2 ^ 64) (hne : ∀ x ∈ ns, x < 2 ^ 64)
    (hbig : (bigOf ix G).size < 2 ^ 64) :
    loadIndex (saveIndex (ix, G, offs, ns)) =
      some ({ ix with offs := saveIndex (ix, G, offs, ns), ob := obOf ix G, sl := saveIndex (ix, G, offs, ns) },
        { G with w := saveIndex (ix, G, offs, ns) }, offs, ns) := by
  generalize hS : saveIndex (ix, G, offs, ns) = S
  rw [saveIndex_eq] at hS
  obtain ⟨b1, eb1⟩ : ∃ x, Index.putMz (bigOf ix G) ix (obOf ix G) = x := ⟨_, rfl⟩
  obtain ⟨b2, eb2⟩ : ∃ x, Index.putPGen b1 G = x := ⟨_, rfl⟩
  obtain ⟨b3, eb3⟩ : ∃ x, Index.putNats b2 offs = x := ⟨_, rfl⟩
  obtain ⟨b4, eb4⟩ : ∃ x, Index.putNats b3 ns = x := ⟨_, rfl⟩
  obtain ⟨b5, eb5⟩ : ∃ x, Index.putNat b4 (bigOf ix G).size = x := ⟨_, rfl⟩
  rw [eb1, eb2, eb3, eb4, eb5] at hS
  have hsz : S.size = b4.size + 16 := by rw [← hS, putU64_size, ← eb5, putNat_size]
  have p5 : Pre b5 S := by rw [← hS]; exact pre_putU64 _ _
  have p4 : Pre b4 S := Pre.trans (b := b5) (by rw [← eb5]; exact pre_putNat _ _) p5
  have p3 : Pre b3 S := Pre.trans (b := b4) (by rw [← eb4]; exact pre_putNats _ _) p4
  have p2 : Pre b2 S := Pre.trans (b := b3) (by rw [← eb3]; exact pre_putNats _ _) p3
  have p1 : Pre b1 S := Pre.trans (b := b2) (by rw [← eb2]; exact pre_putPGen _ _) p2
  have r0 := rdNat_put' b4 S _ hbig (by rw [eb5]; exact p5)
  rw [eb5] at r0
  have r00 := rdU64_put' b5 S Index.magic (by rw [hS]; exact Pre.refl _)
  rw [hS] at r00
  have r1 := rdMz_put (bigOf ix G) S ix _ hf (by rw [eb1]; exact p1)
  rw [eb1] at r1
  have r2 := rdPGen_put b1 S G hn ho he (by rw [eb2]; exact p2)
  rw [eb2] at r2
  have r3 := rdNats_put' b2 S offs hos hoe (by rw [eb3]; exact p3)
  rw [eb3] at r3
  have r4 := rdNats_put' b3 S ns hns hne (by rw [eb4]; exact p4)
  rw [eb4] at r4
  unfold loadIndex
  rw [if_neg (by omega), show S.size - 16 = b4.size by omega]
  simp only [StateT.run', bind, StateT.bind, r0, r00, r1, r2, r3, r4, Option.bind_some, pure, StateT.pure,
    get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set, StateT.set, bne_self_eq_false, Bool.false_eq_true,
    ite_false, show b4.size + 16 - 16 = b4.size by omega, hsz]
  rfl


theorem u32_pre {a bs : ByteArray} (P : Pre a bs) {i : Nat} (h : 4 * i + 3 < a.size) : u32 bs i = u32 a i := by
  unfold u32; dsimp only
  rw [P.2 _ (by omega), P.2 _ (by omega), P.2 _ (by omega), P.2 _ (by omega)]

theorem pre_big_save (ix : Mz.MzIdx) (G : PGen) (offs ns : Array Nat) : Pre (bigOf ix G) (saveIndex (ix, G, offs, ns)) := by
  rw [saveIndex_eq]
  exact (pre_putMz _ _ _).trans ((pre_putPGen _ _).trans ((pre_putNats _ _).trans ((pre_putNats _ _).trans
    ((pre_putNat _ _).trans (pre_putU64 _ _)))))

theorem pre_pad2_big (ix : Mz.MzIdx) (G : PGen) : Pre (Index.pad (Index.pad G.w ix.sw ++ ix.sl) 4) (bigOf ix G) := by
  unfold bigOf; rw [putOffs_eq]; exact (putOffs_spec _ _ _ _).2.1

/-- The saved bytes start with `G.w`. -/
theorem save_w (ix : Mz.MzIdx) (G : PGen) (offs ns : Array Nat) : Pre G.w (saveIndex (ix, G, offs, ns)) :=
  (pre_pad _ _).trans ((pre_append _ _).trans ((pre_pad _ _).trans ((pre_pad2_big ix G).trans (pre_big_save ix G offs ns))))

/-- Slot bytes: byte `j` of `ix.sl` is byte `sw · m + j` of the saved bytes. -/
theorem save_sl (ix : Mz.MzIdx) (G : PGen) (offs ns : Array Nat) (hsw : 0 < ix.sw) (j : Nat) (hj : j < ix.sl.size) :
    (saveIndex (ix, G, offs, ns)).get! (ix.sw * mOf ix G + j) = ix.sl.get! j := by
  have hm : ix.sw * mOf ix G = (Index.pad G.w ix.sw).size := by
    unfold mOf; have := pad_mod G.w ix.sw hsw; have := Nat.div_add_mod (Index.pad G.w ix.sw).size ix.sw; omega
  have P := (pre_pad (Index.pad G.w ix.sw ++ ix.sl) 4).trans ((pre_pad2_big ix G).trans (pre_big_save ix G offs ns))
  rw [hm, P.2 _ (by simp; omega), get_append_right _ _ _ hj]

/-- Bucket offsets: `UInt32` `ob + b` of the saved bytes is offset `b` plus `m` (mod `2^32`). -/
theorem save_offs (ix : Mz.MzIdx) (G : PGen) (offs ns : Array Nat) (b : Nat) (hb : b < ix.offs.size / 4) :
    getU32 (saveIndex (ix, G, offs, ns)) (obOf ix G + b) = (getU32 ix.offs b + mOf ix G) % 2 ^ 32 := by
  have P := pre_big_save ix G offs ns
  obtain ⟨h1, -, h3⟩ := putOffs_spec (Index.pad (Index.pad G.w ix.sw ++ ix.sl) 4) ix.offs (mOf ix G) (ix.offs.size / 4)
  have hmod := pad_mod (Index.pad G.w ix.sw ++ ix.sl) 4 (by omega)
  have := h3 hmod b hb
  rw [← putOffs_eq] at h1 this
  unfold obOf
  rw [← this, getU32_u32, getU32_u32]
  apply u32_pre P
  unfold bigOf; rw [h1]; omega

end Spec.SaveLoad

#print axioms Spec.SaveLoad.loadIndex_saveIndex
#print axioms Spec.SaveLoad.save_offs
