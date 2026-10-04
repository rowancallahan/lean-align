import CsrIndex                   -- getU32 / setU32, LookupComplete, mapWith_eq_mapSpec
import MapperMzWords              -- pool: word codes, hash bijection, loops

/-!
# Codec `MzIndex`: minimizer index of 25-letter seeds, certified by a checker

Memory: only the *minimizer place* of each ACGT 25-letter window is indexed
(about 1/3 of the places for `k = 21`), one unboxed `Nat` slot (8 bytes)
per indexed place, holding the place and a tag; so ~3 bytes per genome
letter instead of 8–16.  A lookup reads one bucket and never the genome
(except near non-ACGT letters).

* Seed code `v = wc R s 25`.  `mini ix v` = leftmost offset `o < w`
  (`w = 26 - k`) minimizing `hsh` (a bijection on `[0, 4^k)`) of the k-word
  at `o` — a function of the seed's letters only.  Every place `p` where an
  ACGT seed occurs thus has its minimizer place `p + o` indexed (`checkComp`).
* Buckets: CSR over `h >>> kb` (`2^B` buckets, `offs` = LE `UInt32`s),
  `h = hsh (k-word)`, `kb = 2k - B`.  Slot = `pos · 2^T + tag`, tag fields:
  `key = h mod 2^kb`, `bef`/`aft` = codes of the `w-1` letters before/after
  the k-word, `flag` (0 when those letters are ACGT inside the chromosome).
* Lookup of an ACGT seed: entries of bucket `h >>> kb` whose key equals
  `h mod 2^kb` (so the k-word equals the seed's, by the bijection), whose
  last `o` letters of `bef` equal the seed's first `o` letters and whose
  first `w-1-o` letters of `aft` equal the seed's last ones; flagged
  entries are compared with the genome instead.  A seed with another
  letter is looked up through the places of that letter (`odd`).

Nothing about the index is trusted.  `check ix G` verifies the parameters,
every entry against the genome (`checkSound`), that every ACGT window's
minimizer place is indexed (`checkComp`), and the `odd` lists
(`checkOddPos`, `increasing`).  Then (`lookupSeed_mem`, `lookupSeed_sorted`)

    p ∈ lookupSeed ix G R s  ↔  p + 25 ≤ G.size ∧ ∀ i < 25, G[p+i] = R[s+i]

and the result is strictly increasing; over a byte genome this gives
`LookupComplete` and the mapping theorem `mapWithMz_eq_mapSpec`.
-/

namespace MapSpec.Mz

/-- Seed length. -/
def q : Nat := 25

/-! ## The index -/

structure MzIdx where
  /-- minimizer word length -/
  k : Nat
  /-- bucket bits -/
  B : Nat
  /-- `q + 1 - k` (checked) -/
  w : Nat
  /-- key bits `2k - B` (checked) -/
  kb : Nat
  /-- tag bits `kb + 4(w-1) + 1` (checked) -/
  T : Nat
  /-- `4^k - 1` (checked) -/
  kmU : UInt64
  /-- `2^kb - 1`, `4^(w-1) - 1`, `2^T - 1` (checked) -/
  kbM : Nat
  fM : Nat
  tM : Nat
  /-- `pm[i] = 4^i - 1` for `i ≤ w` (checked) -/
  pm : Array Nat
  /-- `2^B + 1` LE `UInt32` bucket offsets -/
  offs : ByteArray
  /-- slot `pos · 2^T + tag` per entry -/
  sl : Array Nat
  /-- `odd[v]`: places of byte `v` (not ACGT), increasing -/
  odd : Array (Array Nat)
deriving Inhabited

namespace MzIdx

variable (ix : MzIdx)

@[inline] def loB (b : Nat) : Nat := getU32 ix.offs b
@[inline] def hiB (b : Nat) : Nat := getU32 ix.offs (b + 1)
@[inline] def posOf (e : Nat) : Nat := e >>> ix.T
@[inline] def tagOf (e : Nat) : Nat := e &&& ix.tM
@[inline] def keyF (tg : Nat) : Nat := tg &&& ix.kbM
@[inline] def befF (tg : Nat) : Nat := (tg >>> ix.kb) &&& ix.fM
@[inline] def aftF (tg : Nat) : Nat := (tg >>> (ix.kb + 2 * (ix.w - 1))) &&& ix.fM
@[inline] def flagF (tg : Nat) : Nat := tg >>> (ix.kb + 4 * (ix.w - 1))
@[inline] def hsh (x : Nat) : Nat := hashU x ix.kmU
/-- The k-word at offset `o` of the q-word with code `v`. -/
@[inline] def sub (v o : Nat) : Nat := (v >>> (2 * (q - o - ix.k))) &&& ix.kmU.toNat

/-- Leftmost `o ∈ [o, w)` with the least hash (best so far `bo`, `bh`). -/
def miniGo (v : Nat) (o bo bh : Nat) : Nat :=
  if o < ix.w then
    let h := ix.hsh (ix.sub v o)
    if h < bh then miniGo v (o + 1) o h else miniGo v (o + 1) bo bh
  else bo
termination_by ix.w - o

/-- Minimizer offset of the q-word with code `v`. -/
@[inline] def mini (v : Nat) : Nat := ix.miniGo v 1 0 (ix.hsh (ix.sub v 0))

end MzIdx

/-! ## Lookup -/

/-- Entry `t` matches the seed `R[s, s+q)` (minimizer offset `o`, key `key`,
first `o` letters `bw`, last `w-1-o` letters `aw`). -/
@[inline] def okAt (ix : MzIdx) (G R : ByteArray) (s o key bw aw t : Nat) : Bool :=
  let e := ix.sl[t]!
  let pos := ix.posOf e
  let tg := ix.tagOf e
  ix.keyF tg == key && decide (o ≤ pos) &&
    (if ix.flagF tg = 0 then (ix.befF tg &&& ix.pm[o]!) == bw && (ix.aftF tg >>> (2 * o)) == aw
     else decide (pos - o + q ≤ G.size) && eqRun G R (pos - o) s q)

/-- Places `pos - o` of the matching entries `t ∈ [t, hi)`. -/
def scan (ix : MzIdx) (G R : ByteArray) (s o key bw aw hi : Nat) (t : Nat) (acc : Array Nat) :
    Array Nat :=
  if t < hi then
    scan ix G R s o key bw aw hi (t + 1)
      (if okAt ix G R s o key bw aw t then acc.push (ix.posOf ix.sl[t]! - o) else acc)
  else acc
termination_by hi - t

/-- Place `ps[t] - o` is where the seed `R[s, s+q)` occurs. -/
@[inline] def okOdd (G R : ByteArray) (ps : Array Nat) (o s t : Nat) : Bool :=
  decide (o ≤ ps[t]!) && decide (ps[t]! - o + q ≤ G.size) && eqRun G R (ps[t]! - o) s q

/-- Places `x - o` (`x ∈ ps[t ..]`) where the seed `R[s, s+q)` occurs. -/
def scanOdd (G R : ByteArray) (ps : Array Nat) (o s : Nat) (t : Nat) (acc : Array Nat) : Array Nat :=
  if t < ps.size then
    scanOdd G R ps o s (t + 1) (if okOdd G R ps o s t then acc.push (ps[t]! - o) else acc)
  else acc
termination_by ps.size - t

/-- Lookup of an ACGT seed `R[s, s+q)` whose code `v = wc R s q` the caller
already has (`lookupSeed_eq_lookupCode`). -/
def lookupCode (ix : MzIdx) (G R : ByteArray) (s v : Nat) : Array Nat :=
  let o := ix.mini v
  let h := ix.hsh (ix.sub v o)
  let b := h >>> ix.kb
  scan ix G R s o (h &&& ix.kbM) (v >>> (2 * (q - o))) (v &&& ix.pm[ix.w - 1 - o]!) (ix.hiB b)
    (ix.loB b) #[]

/-- Places `p` (increasing) with `G[p, p+q) = R[s, s+q)`. -/
def lookupSeed (ix : MzIdx) (G R : ByteArray) (s : Nat) : Array Nat :=
  let u := firstOdd R s (s + q)
  if u = s + q then lookupCode ix G R s (wcGo R s (s + q) 0)
  else scanOdd G R ix.odd[(R.get! u).toNat]! (u - s) s 0 #[]

/-! ## Checker -/

def checkParams (ix : MzIdx) : Bool :=
  decide (0 < ix.k) && decide (ix.k ≤ q) && decide (ix.k ≤ 31) && decide (ix.B ≤ 2 * ix.k) &&
  ix.w == q + 1 - ix.k && ix.kb == 2 * ix.k - ix.B && ix.T == ix.kb + 4 * (ix.w - 1) + 1 &&
  ix.kmU.toNat == 2 ^ (2 * ix.k) - 1 && ix.kbM == 2 ^ ix.kb - 1 &&
  ix.fM == 2 ^ (2 * (ix.w - 1)) - 1 && ix.tM == 2 ^ ix.T - 1 &&
  (List.range (ix.w + 1)).all (fun i => ix.pm[i]! == 2 ^ (2 * i) - 1)

/-- Bucket of the k-word at place `x`. -/
@[inline] def bkt (ix : MzIdx) (G : ByteArray) (x : Nat) : Nat := ix.hsh (wc G x ix.k) >>> ix.kb

/-- Entry `t` of bucket `b` (which ends at `hi`) is right. -/
def entryOk (ix : MzIdx) (G : ByteArray) (b hi t : Nat) : Bool :=
  let e := ix.sl[t]!
  let pos := ix.posOf e
  let tg := ix.tagOf e
  let h := ix.hsh (wcGo G pos (pos + ix.k) 0)
  let w1 := ix.w - 1
  decide (pos + ix.k ≤ G.size) && allA G pos (pos + ix.k) && (h >>> ix.kb) == b &&
    ix.keyF tg == (h &&& ix.kbM) &&
    (ix.flagF tg != 0 ||
      (decide (w1 ≤ pos) && decide (pos + ix.k + w1 ≤ G.size) &&
        allA G (pos - w1) pos && allA G (pos + ix.k) (pos + ix.k + w1) &&
        ix.befF tg == wcGo G (pos - w1) pos 0 && ix.aftF tg == wcGo G (pos + ix.k) (pos + ix.k + w1) 0)) &&
    (decide (hi ≤ t + 1) || decide (pos < ix.posOf ix.sl[t + 1]!))

def checkBucket (ix : MzIdx) (G : ByteArray) (b hi : Nat) : (n t : Nat) → Bool
  | 0, _ => true
  | n + 1, t => entryOk ix G b hi t && checkBucket ix G b hi n (t + 1)

/-- Every entry of buckets `b, b+1, …` (`n` of them). -/
def checkSound (ix : MzIdx) (G : ByteArray) : (n b : Nat) → Bool
  | 0, _ => true
  | n + 1, b =>
    checkBucket ix G b (ix.hiB b) (ix.hiB b - ix.loB b) (ix.loB b) && checkSound ix G n (b + 1)

/-- The minimizer place of every ACGT window at `p, p+1, …` (`n` of them) is
indexed.  `fill[b]` is a hint for the next entry of bucket `b`; `last = 1 +`
the last minimizer place found (0: none). -/
def checkComp (ix : MzIdx) (G : ByteArray) (fill : ByteArray) (last : Nat) : (n p : Nat) → Bool
  | 0, _ => true
  | n + 1, p =>
    if allA G p (p + q) then
      let pm := p + ix.mini (wcGo G p (p + q) 0)
      if pm + 1 = last then checkComp ix G fill last n (p + 1)
      else
        let b := ix.hsh (wcGo G pm (pm + ix.k) 0) >>> ix.kb
        let t := getU32 fill b
        decide (ix.loB b ≤ t) && decide (t < ix.hiB b) && ix.posOf ix.sl[t]! == pm &&
          checkComp ix G (setU32 fill b (t + 1)) (pm + 1) n (p + 1)
    else checkComp ix G fill last n (p + 1)

/-- Every place `p, p+1, …` (`n` of them) holding a byte `v` other than ACGT is
`odd[v][cur[v]]` (`cur` is only a hint). -/
def checkOddPos (ix : MzIdx) (G : ByteArray) (cur : Array Nat) : (n p : Nat) → Bool
  | 0, _ => true
  | n + 1, p =>
    let v := (G.get! p).toNat
    if acgt (G.get! p) then checkOddPos ix G cur n (p + 1)
    else ix.odd[v]![cur[v]!]! == p && decide (cur[v]! < ix.odd[v]!.size) &&
      checkOddPos ix G (cur.set! v (cur[v]! + 1)) n (p + 1)

def increasing (a : Array Nat) : (n i : Nat) → Bool
  | 0, _ => true
  | n + 1, i => decide (a[i]! < a[i + 1]!) && increasing a n (i + 1)

/-- The runtime checker. -/
def check (ix : MzIdx) (G : ByteArray) : Bool :=
  checkParams ix && checkSound ix G (2 ^ ix.B) 0 &&
    checkComp ix G ix.offs 0 (G.size + 1 - q) 0 &&
    checkOddPos ix G (Array.replicate 256 0) G.size 0 &&
    (List.range 256).all fun v => increasing ix.odd[v]! (ix.odd[v]!.size - 1) 0

/-! ## Builder (fast; not trusted — `check` certifies its output) -/

/-- `n` zero bytes, capacity `n`. -/
def zeros (n : Nat) : ByteArray := Id.run do
  let mut B := ByteArray.emptyWithCapacity n
  for _ in [0:n] do B := B.push 0
  return B

def mkIdx (k B : Nat) : MzIdx :=
  let w := q + 1 - k
  let kb := 2 * k - B
  let T := kb + 4 * (w - 1) + 1
  { k, B, w, kb, T, kmU := (2 ^ (2 * k) - 1).toUInt64, kbM := 2 ^ kb - 1,
    fM := 2 ^ (2 * (w - 1)) - 1, tM := 2 ^ T - 1,
    pm := (Array.range (w + 1)).map fun i => 2 ^ (2 * i) - 1,
    offs := .empty, sl := #[], odd := #[] }

/-- Slot of minimizer place `pm` (with k-word hash `h`). -/
def slotAt (ix : MzIdx) (G : ByteArray) (pm h : Nat) : Nat :=
  let w1 := ix.w - 1
  let good := decide (w1 ≤ pm) && decide (pm + ix.k + w1 ≤ G.size) &&
    allA G (pm - w1) pm && allA G (pm + ix.k) (pm + ix.k + w1)
  let tag := if good then
      (h &&& ix.kbM) + 2 ^ ix.kb * (wcGo G (pm - w1) pm 0 + 2 ^ (2 * w1) * wcGo G (pm + ix.k) (pm + ix.k + w1) 0)
    else (h &&& ix.kbM) + 2 ^ (ix.kb + 4 * w1)
  pm * 2 ^ ix.T + tag

/-- Minimizer places of the ACGT windows, increasing, each with its hash. -/
def build (G : ByteArray) (k B : Nat) : MzIdx := Id.run do
  let ix0 := mkIdx k B
  let nb := 2 ^ B
  let mut cnt := zeros (4 * (nb + 1))
  let mut last := 0
  for p in [0:G.size + 1 - q] do
    if allA G p (p + q) then
      let pm := p + ix0.mini (wcGo G p (p + q) 0)
      if pm + 1 != last then
        last := pm + 1
        let b := ix0.hsh (wcGo G pm (pm + k) 0) >>> ix0.kb
        cnt := setU32 cnt (b + 1) (getU32 cnt (b + 1) + 1)
  for b in [0:nb] do cnt := setU32 cnt (b + 1) (getU32 cnt (b + 1) + getU32 cnt b)
  let mut fill := cnt
  let mut sl : Array Nat := Array.replicate (getU32 cnt nb) 0
  last := 0
  for p in [0:G.size + 1 - q] do
    if allA G p (p + q) then
      let pm := p + ix0.mini (wcGo G p (p + q) 0)
      if pm + 1 != last then
        last := pm + 1
        let h := ix0.hsh (wcGo G pm (pm + k) 0)
        let b := h >>> ix0.kb
        let t := getU32 fill b
        fill := setU32 fill b (t + 1)
        sl := sl.set! t (slotAt ix0 G pm h)
  let mut odd : Array (Array Nat) := Array.replicate 256 #[]
  for p in [0:G.size] do
    if !acgt (G.get! p) then odd := odd.modify (G.get! p).toNat (·.push p)
  return { ix0 with offs := cnt, sl, odd }

end MapSpec.Mz

/-! ## Proof -/

namespace MapSpec.Mz

/-- Seed `R[s, s+q)` occurs at place `p` of `G`. -/
def Occurs (G R : ByteArray) (s p : Nat) : Prop :=
  p + q ≤ G.size ∧ ∀ i < q, G.get! (p + i) = R.get! (s + i)

/-- What `checkParams` guarantees. -/
structure Good (ix : MzIdx) : Prop where
  k_pos : 0 < ix.k
  k_le : ix.k ≤ q
  k_le31 : ix.k ≤ 31
  B_le : ix.B ≤ 2 * ix.k
  w_eq : ix.w = q + 1 - ix.k
  kb_eq : ix.kb = 2 * ix.k - ix.B
  kmU_eq : ix.kmU.toNat = 2 ^ (2 * ix.k) - 1
  kbM_eq : ix.kbM = 2 ^ ix.kb - 1
  fM_eq : ix.fM = 2 ^ (2 * (ix.w - 1)) - 1
  pm_eq : ∀ i, i ≤ ix.w → ix.pm[i]! = 2 ^ (2 * i) - 1

theorem good_of_checkParams (ix : MzIdx) (h : checkParams ix = true) : Good ix := by
  simp only [checkParams, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, _, h8, h9, h10, _, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h8, h9, h10, fun i hi => h12 i (by omega)⟩

section
variable {ix : MzIdx} (hg : Good ix)
include hg

theorem hsh_eq (x : Nat) : ix.hsh x = x * HC.toNat % 2 ^ (2 * ix.k) :=
  hashU_eq x ix.k ix.kmU hg.kmU_eq (by have := hg.k_le31; omega)

theorem hsh_lt (x : Nat) : ix.hsh x < 2 ^ (2 * ix.k) := by
  rw [hsh_eq hg]; exact Nat.mod_lt _ (Nat.pow_pos (by omega))

theorem hsh_inj (x y : Nat) (hx : x < 4 ^ ix.k) (hy : y < 4 ^ ix.k) (h : ix.hsh x = ix.hsh y) :
    x = y := by
  rw [hsh_eq hg, hsh_eq hg] at h
  rw [four_pow] at hx hy
  exact hash_inj ix.k x y (by have := hg.k_le31; omega) hx hy h

theorem bucket_lt (x : Nat) : ix.hsh x >>> ix.kb < 2 ^ ix.B := by
  rw [shiftRight_eq, Nat.div_lt_iff_lt_mul (Nat.pow_pos (by omega)), ← Nat.pow_add, hg.kb_eq,
    show ix.B + (2 * ix.k - ix.B) = 2 * ix.k by have := hg.B_le; omega]
  exact hsh_lt hg x

/-- The k-word at offset `o` of a seed's code is the code of the seed's k-word. -/
theorem sub_wc (R : ByteArray) (s o : Nat) (ho : o + ix.k ≤ q) :
    ix.sub (wc R s q) o = wc R (s + o) ix.k := by
  unfold MzIdx.sub
  rw [hg.kmU_eq, and_mask_eq, shiftRight_eq, ← four_pow, ← four_pow]
  have h1 := wc_div R s (o + ix.k) (q - o - ix.k)
  rw [show o + ix.k + (q - o - ix.k) = q by omega] at h1
  rw [h1, wc_mod]

omit hg in
/-- The first `o` letters of a seed. -/
theorem seed_bef (R : ByteArray) (s o : Nat) (ho : o ≤ q) : wc R s q >>> (2 * (q - o)) = wc R s o := by
  rw [shiftRight_eq, ← four_pow]
  have h1 := wc_div R s o (q - o)
  rwa [show o + (q - o) = q by omega] at h1

/-- The last `w-1-o` letters of a seed. -/
theorem seed_aft (R : ByteArray) (s o : Nat) (ho : o < ix.w) :
    wc R s q &&& ix.pm[ix.w - 1 - o]! = wc R (s + o + ix.k) (ix.w - 1 - o) := by
  have hw := hg.w_eq; have hk := hg.k_le
  rw [hg.pm_eq _ (by omega), and_mask_eq, ← four_pow]
  have h1 := wc_mod R s (o + ix.k) (ix.w - 1 - o)
  rwa [show o + ix.k + (ix.w - 1 - o) = q by omega, ← Nat.add_assoc] at h1

/-- The last `o` letters of the `w-1` letters before place `pos`. -/
theorem flank_bef (G : ByteArray) (pos o : Nat) (ho : o < ix.w) (hp : ix.w - 1 ≤ pos) :
    wc G (pos - (ix.w - 1)) (ix.w - 1) &&& ix.pm[o]! = wc G (pos - o) o := by
  rw [hg.pm_eq _ (by omega), and_mask_eq, ← four_pow]
  have h1 := wc_mod G (pos - (ix.w - 1)) (ix.w - 1 - o) o
  rwa [show ix.w - 1 - o + o = ix.w - 1 by omega,
    show pos - (ix.w - 1) + (ix.w - 1 - o) = pos - o by omega] at h1

omit hg in
/-- The first `w-1-o` letters of the `w-1` letters after the k-word at `pos`. -/
theorem flank_aft (G : ByteArray) (pos o : Nat) (ho : o < ix.w) :
    wc G (pos + ix.k) (ix.w - 1) >>> (2 * o) = wc G (pos + ix.k) (ix.w - 1 - o) := by
  rw [shiftRight_eq, ← four_pow]
  have h1 := wc_div G (pos + ix.k) (ix.w - 1 - o) o
  rwa [show ix.w - 1 - o + o = ix.w - 1 by omega] at h1

end

/-! ### Minimizer offset -/

theorem miniGo_lt (ix : MzIdx) (v : Nat) :
    ∀ n o bo bh, ix.w - o = n → bo < ix.w → ix.miniGo v o bo bh < ix.w := by
  intro n
  induction n with
  | zero => intro o bo bh hn hb; rw [MzIdx.miniGo, if_neg (by omega)]; exact hb
  | succ n ih =>
    intro o bo bh hn hb
    rw [MzIdx.miniGo, if_pos (by omega)]
    dsimp only
    split
    · exact ih _ _ _ (by omega) (by omega)
    · exact ih _ _ _ (by omega) hb

theorem mini_lt {ix : MzIdx} (hg : Good ix) (v : Nat) : ix.mini v < ix.w := by
  have := hg.w_eq; have := hg.k_le
  exact miniGo_lt ix v _ 1 0 _ rfl (by omega)


/-! ### Checker loops -/

theorem checkBucket_spec (ix : MzIdx) (G : ByteArray) (b hi : Nat) :
    ∀ n t, checkBucket ix G b hi n t = true → ∀ t', t ≤ t' → t' < t + n → entryOk ix G b hi t' = true := by
  intro n
  induction n with
  | zero => intro t _ t' h1 h2; omega
  | succ n ih =>
    intro t h t' h1 h2
    rw [checkBucket, Bool.and_eq_true] at h
    by_cases ht : t' = t
    · subst ht; exact h.1
    · exact ih (t + 1) h.2 t' (by omega) (by omega)

theorem checkSound_spec (ix : MzIdx) (G : ByteArray) :
    ∀ n b, checkSound ix G n b = true → ∀ b', b ≤ b' → b' < b + n →
      ∀ t, ix.loB b' ≤ t → t < ix.hiB b' → entryOk ix G b' (ix.hiB b') t = true := by
  intro n
  induction n with
  | zero => intro b _ b' h1 h2; omega
  | succ n ih =>
    intro b h b' h1 h2 t ht1 ht2
    rw [checkSound, Bool.and_eq_true] at h
    by_cases hb : b' = b
    · subst hb; exact checkBucket_spec ix G b' _ _ _ h.1 t ht1 (by omega)
    · exact ih (b + 1) h.2 b' (by omega) (by omega) t ht1 ht2

/-- Place `x` (its k-word's bucket `bkt`) is an entry of the index. -/
def InIdx (ix : MzIdx) (G : ByteArray) (x : Nat) : Prop :=
  ∃ t, ix.loB (bkt ix G x) ≤ t ∧ t < ix.hiB (bkt ix G x) ∧ ix.posOf ix.sl[t]! = x

theorem wcGo_zero (B : ByteArray) (i n : Nat) : wcGo B i (i + n) 0 = wc B i n := by
  rw [wcGo_eq]; simp

theorem checkComp_spec (ix : MzIdx) (G : ByteArray) :
    ∀ n p fill last, checkComp ix G fill last n p = true → (last = 0 ∨ InIdx ix G (last - 1)) →
      ∀ p', p ≤ p' → p' < p + n → (∀ i < q, acgt (G.get! (p' + i)) = true) →
        InIdx ix G (p' + ix.mini (wc G p' q)) := by
  intro n
  induction n with
  | zero => intro p _ _ _ _ p' h1 h2; omega
  | succ n ih =>
    intro p fill last h hl p' h1 h2 hA
    rw [checkComp] at h
    split at h
    · next hall =>
      rw [wcGo_zero] at h
      dsimp only at h
      split at h
      · next heq =>
        by_cases hp : p' = p
        · subst hp
          rcases hl with hl | hl
          · omega
          · rwa [← heq, Nat.add_sub_cancel] at hl
        · exact ih (p + 1) fill last h hl p' (by omega) (by omega) hA
      · next hne =>
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
        obtain ⟨⟨⟨h3, h4⟩, h5⟩, h6⟩ := h
        rw [wcGo_zero] at h3 h4 h5 h6
        have hin : InIdx ix G (p + ix.mini (wc G p q)) := ⟨_, h3, h4, h5⟩
        by_cases hp : p' = p
        · subst hp; exact hin
        · exact ih (p + 1) _ _ h6 (Or.inr (by rwa [Nat.add_sub_cancel])) p' (by omega) (by omega) hA
    · next hall =>
      by_cases hp : p' = p
      · subst hp; exact absurd ((allA_iff G q p').mpr hA) hall
      · exact ih (p + 1) fill last h hl p' (by omega) (by omega) hA

theorem checkOddPos_spec (ix : MzIdx) (G : ByteArray) :
    ∀ n p cur, checkOddPos ix G cur n p = true → ∀ x, p ≤ x → x < p + n → acgt (G.get! x) = false →
      ∃ t, t < (ix.odd[(G.get! x).toNat]!).size ∧ (ix.odd[(G.get! x).toNat]!)[t]! = x := by
  intro n
  induction n with
  | zero => intro p _ _ x h1 h2; omega
  | succ n ih =>
    intro p cur h x h1 h2 hx
    rw [checkOddPos] at h
    split at h
    · next ha =>
      by_cases hp : x = p
      · subst hp; rw [hx] at ha; exact absurd ha (by simp)
      · exact ih (p + 1) cur h x (by omega) (by omega) hx
    · next ha =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
      obtain ⟨⟨h3, h4⟩, h5⟩ := h
      by_cases hp : x = p
      · subst hp; exact ⟨_, h4, h3⟩
      · exact ih (p + 1) _ h5 x (by omega) (by omega) hx

theorem increasing_spec (a : Array Nat) :
    ∀ n i, increasing a n i = true → ∀ j, i ≤ j → j < i + n → a[j]! < a[j + 1]! := by
  intro n
  induction n with
  | zero => intro i _ j h1 h2; omega
  | succ n ih =>
    intro i h j h1 h2
    rw [increasing, Bool.and_eq_true, decide_eq_true_eq] at h
    by_cases hj : j = i
    · subst hj; exact h.1
    · exact ih (i + 1) h.2 j (by omega) (by omega)

/-- Steps increasing on `[lo, hi)` ⇒ increasing. -/
theorem lt_of_steps (f : Nat → Nat) (lo hi : Nat) (h : ∀ j, lo ≤ j → j + 1 < hi → f j < f (j + 1)) :
    ∀ d i, lo ≤ i → i + d + 1 < hi → f i < f (i + d + 1) := by
  intro d
  induction d with
  | zero => intro i h1 h2; exact h i h1 (by omega)
  | succ d ih =>
    intro i h1 h2
    have := ih i h1 (by omega)
    have := h (i + d + 1) (by omega) (by omega)
    rw [show i + (d + 1) + 1 = i + d + 1 + 1 by omega]; omega

theorem pairwise_range' (P : Nat → Nat → Prop) :
    ∀ n a, (∀ i j, a ≤ i → i < j → j < a + n → P i j) → (List.range' a n).Pairwise P := by
  intro n
  induction n with
  | zero => intro a _; simp
  | succ n ih =>
    intro a h
    rw [List.range'_succ, List.pairwise_cons]
    refine ⟨fun j hj => ?_, ih (a + 1) fun i j h1 h2 h3 => h i j (by omega) h2 (by omega)⟩
    rw [List.mem_range'_1] at hj
    exact h a j (by omega) (by omega) (by omega)

/-! ### Scans -/

theorem mem_filterMap_ite (P : Nat → Bool) (f : Nat → Nat) (a n x : Nat) :
    x ∈ (List.range' a n).filterMap (fun t => if P t then some (f t) else none) ↔
      ∃ t, a ≤ t ∧ t < a + n ∧ P t = true ∧ f t = x := by
  simp only [List.mem_filterMap, List.mem_range'_1]
  constructor
  · rintro ⟨t, ⟨h1, h2⟩, h3⟩
    split at h3
    · next hp => exact ⟨t, h1, h2, hp, Option.some.inj h3⟩
    · cases h3
  · rintro ⟨t, h1, h2, h3, h4⟩
    exact ⟨t, ⟨h1, h2⟩, by rw [if_pos h3, h4]⟩

theorem pairwise_filterMap_ite (P : Nat → Bool) (f : Nat → Nat) (a n : Nat)
    (h : ∀ i j, a ≤ i → i < j → j < a + n → P i = true → P j = true → f i < f j) :
    ((List.range' a n).filterMap (fun t => if P t then some (f t) else none)).Pairwise (· < ·) := by
  rw [List.pairwise_filterMap]
  apply pairwise_range'
  intro i j h1 h2 h3 b1 hb1 b2 hb2
  by_cases p1 : P i = true
  · by_cases p2 : P j = true
    · rw [if_pos p1] at hb1; rw [if_pos p2] at hb2
      cases hb1; cases hb2
      exact h i j h1 h2 h3 p1 p2
    · rw [if_neg p2] at hb2; cases hb2
  · rw [if_neg p1] at hb1; cases hb1

theorem scan_toList (ix : MzIdx) (G R : ByteArray) (s o key bw aw hi : Nat) :
    ∀ n t acc, hi - t = n →
      (scan ix G R s o key bw aw hi t acc).toList = acc.toList ++ (List.range' t n).filterMap
        (fun t => if okAt ix G R s o key bw aw t then some (ix.posOf ix.sl[t]! - o) else none) := by
  intro n
  induction n with
  | zero => intro t acc hn; rw [scan, if_neg (by omega)]; simp
  | succ n ih =>
    intro t acc hn
    rw [scan, if_pos (by omega), ih (t + 1) _ (by omega), List.range'_succ, List.filterMap_cons]
    split <;> simp

theorem scanOdd_toList (G R : ByteArray) (ps : Array Nat) (o s : Nat) :
    ∀ n t acc, ps.size - t = n →
      (scanOdd G R ps o s t acc).toList = acc.toList ++ (List.range' t n).filterMap
        (fun t => if okOdd G R ps o s t then some (ps[t]! - o) else none) := by
  intro n
  induction n with
  | zero => intro t acc hn; rw [scanOdd, if_neg (by omega)]; simp
  | succ n ih =>
    intro t acc hn
    rw [scanOdd, if_pos (by omega), ih (t + 1) _ (by omega), List.range'_succ, List.filterMap_cons]
    split <;> simp


/-! ### Entries -/

/-- What `entryOk` says about entry `t` (place `pos`, tag `tg`). -/
theorem entryOk_spec {ix : MzIdx} {G : ByteArray} {b hi t : Nat} (h : entryOk ix G b hi t = true)
    (pos tg : Nat) (hpos : pos = ix.posOf ix.sl[t]!) (htg : tg = ix.tagOf ix.sl[t]!) :
    pos + ix.k ≤ G.size ∧ (∀ i < ix.k, acgt (G.get! (pos + i)) = true) ∧
    ix.hsh (wc G pos ix.k) >>> ix.kb = b ∧ ix.keyF tg = (ix.hsh (wc G pos ix.k) &&& ix.kbM) ∧
    (ix.flagF tg = 0 → ix.w - 1 ≤ pos ∧ pos + ix.k + (ix.w - 1) ≤ G.size ∧
      (∀ i < ix.w - 1, acgt (G.get! (pos - (ix.w - 1) + i)) = true) ∧
      (∀ i < ix.w - 1, acgt (G.get! (pos + ix.k + i)) = true) ∧
      ix.befF tg = wc G (pos - (ix.w - 1)) (ix.w - 1) ∧ ix.aftF tg = wc G (pos + ix.k) (ix.w - 1)) ∧
    (t + 1 < hi → pos < ix.posOf ix.sl[t + 1]!) := by
  subst hpos htg
  unfold entryOk at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq,
    and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  rw [wcGo_zero] at h3 h4
  refine ⟨h1, (allA_iff G _ _).mp h2, h3, h4, fun hf => ?_, fun ht => ?_⟩
  · rcases h5 with h5 | ⟨f1, f2, f3, f4, f5, f6⟩
    · exact absurd hf h5
    · rw [allA_iff' G _ _ (by omega), show ix.posOf ix.sl[t]! - (ix.posOf ix.sl[t]! - (ix.w - 1)) = ix.w - 1 by omega] at f3
      rw [wcGo_zero' G _ _ (by omega), show ix.posOf ix.sl[t]! - (ix.posOf ix.sl[t]! - (ix.w - 1)) = ix.w - 1 by omega] at f5
      rw [wcGo_zero] at f6
      exact ⟨f1, f2, f3, (allA_iff G _ _).mp f4, f5, f6⟩
  · rcases h6 with h6 | h6
    · omega
    · exact h6

/-! ### The lookup -/

section
variable {ix : MzIdx} {G : ByteArray} (hc : check ix G = true)
include hc

theorem good_of_check : Good ix := by
  simp only [check, Bool.and_eq_true] at hc
  exact good_of_checkParams ix hc.1.1.1.1

theorem sound_of_check : ∀ b, b < 2 ^ ix.B → ∀ t, ix.loB b ≤ t → t < ix.hiB b →
    entryOk ix G b (ix.hiB b) t = true := by
  simp only [check, Bool.and_eq_true] at hc
  intro b hb t h1 h2
  exact checkSound_spec ix G _ 0 hc.1.1.1.2 b (by omega) (by omega) t h1 h2

theorem comp_of_check (p : Nat) (hp : p + q ≤ G.size) (hA : ∀ i < q, acgt (G.get! (p + i)) = true) :
    InIdx ix G (p + ix.mini (wc G p q)) := by
  simp only [check, Bool.and_eq_true] at hc
  exact checkComp_spec ix G _ 0 _ 0 hc.1.1.2 (Or.inl rfl) p (by omega) (by omega) hA

theorem odd_of_check (x : Nat) (hx : x < G.size) (ha : acgt (G.get! x) = false) :
    ∃ t, t < (ix.odd[(G.get! x).toNat]!).size ∧ (ix.odd[(G.get! x).toNat]!)[t]! = x := by
  simp only [check, Bool.and_eq_true] at hc
  exact checkOddPos_spec ix G _ 0 _ hc.1.2 x (by omega) (by omega) ha

theorem odd_increasing (v : Nat) (hv : v < 256) :
    ∀ j, j + 1 < (ix.odd[v]!).size → (ix.odd[v]!)[j]! < (ix.odd[v]!)[j + 1]! := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  intro j hj
  exact increasing_spec _ _ 0 (hc.2 v hv) j (by omega) (by omega)

/-- **Soundness of a bucket hit** (tag path or genome check). -/
theorem okAt_occurs (R : ByteArray) (s : Nat) (hR : ∀ i < q, acgt (R.get! (s + i)) = true)
    (t : Nat) (o : Nat) (ho : o < ix.w)
    (ht1 : ix.loB (ix.hsh (wc R (s + o) ix.k) >>> ix.kb) ≤ t)
    (ht2 : t < ix.hiB (ix.hsh (wc R (s + o) ix.k) >>> ix.kb))
    (hok : okAt ix G R s o (ix.hsh (wc R (s + o) ix.k) &&& ix.kbM) (wc R s q >>> (2 * (q - o)))
      (wc R s q &&& ix.pm[ix.w - 1 - o]!) t = true)
    (pos : Nat) (hpos : ix.posOf ix.sl[t]! = pos) :
    Occurs G R s (pos - o) := by
  have hg := good_of_check hc
  have hw := hg.w_eq; have hk := hg.k_le; have hk0 := hg.k_pos
  have he := sound_of_check hc _ (bucket_lt hg _) t ht1 ht2
  obtain ⟨e1, e2, e3, e4, e5, -⟩ := entryOk_spec he pos _ hpos.symm rfl
  unfold okAt at hok
  simp only [hpos, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  generalize ix.tagOf ix.sl[t]! = tg at e4 e5 hok
  generalize hh : ix.hsh (wc R (s + o) ix.k) = h at hok e3
  obtain ⟨⟨hkey, hop⟩, hrest⟩ := hok
  split at hrest
  · next hf =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hrest
    obtain ⟨hb, ha⟩ := hrest
    obtain ⟨f1, f2, f3, f4, f5, f6⟩ := e5 hf
    -- the k-word
    have hhash : ix.hsh (wc G pos ix.k) = h := by
      have m1 : ix.hsh (wc G pos ix.k) % 2 ^ ix.kb = h % 2 ^ ix.kb := by
        rw [← and_mask_eq, ← and_mask_eq, ← hg.kbM_eq, ← e4, hkey]
      have m2 : ix.hsh (wc G pos ix.k) / 2 ^ ix.kb = h / 2 ^ ix.kb := by
        rw [← shiftRight_eq, ← shiftRight_eq, e3]
      rw [← Nat.div_add_mod (ix.hsh (wc G pos ix.k)) (2 ^ ix.kb), m1, m2, Nat.div_add_mod]
    have hcode := hsh_inj hg _ _ (wc_lt G pos ix.k) (wc_lt R (s + o) ix.k) (hhash.trans hh.symm)
    have hmid := eq_of_wc G R pos (s + o) ix.k e2
      (fun i hi => by have := hR (o + i) (by omega); rwa [← Nat.add_assoc] at this) hcode
    -- the first o letters
    rw [f5, flank_bef hg G pos o ho f1, seed_bef R s o (by omega)] at hb
    have hbef := eq_of_wc G R (pos - o) s o
      (fun i hi => by
        have := f3 (ix.w - 1 - o + i) (by omega)
        rwa [show pos - (ix.w - 1) + (ix.w - 1 - o + i) = pos - o + i by omega] at this)
      (fun i hi => hR i (by omega)) hb
    -- the last w-1-o letters
    rw [f6, flank_aft G pos o ho, seed_aft hg R s o ho] at ha
    have haft := eq_of_wc G R (pos + ix.k) (s + o + ix.k) (ix.w - 1 - o)
      (fun i hi => f4 i (by omega))
      (fun i hi => by have := hR (o + ix.k + i) (by omega); rwa [← Nat.add_assoc, ← Nat.add_assoc] at this) ha
    refine ⟨by omega, fun i hi => ?_⟩
    by_cases h1 : i < o
    · exact hbef i h1
    · by_cases h2 : i < o + ix.k
      · have := hmid (i - o) (by omega)
        rwa [show pos + (i - o) = pos - o + i by omega, show s + o + (i - o) = s + i by omega] at this
      · have := haft (i - o - ix.k) (by omega)
        rwa [show pos + ix.k + (i - o - ix.k) = pos - o + i by omega,
          show s + o + ix.k + (i - o - ix.k) = s + i by omega] at this
  · next hf =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hrest
    obtain ⟨hsz, heq⟩ := hrest
    exact ⟨hsz, (eqRun_iff G R q _ _).mp heq⟩

/-- **Lookup.**  Through an index that passes the checker, the lookup of the
seed `R[s, s+25)` returns exactly the places where it occurs in `G`. -/
theorem lookupSeed_mem (R : ByteArray) (s p : Nat) :
    p ∈ (lookupSeed ix G R s).toList ↔ Occurs G R s p := by
  have hg := good_of_check hc
  have hw := hg.w_eq; have hk := hg.k_le; have hk0 := hg.k_pos
  obtain ⟨u1, u2, u3, u4⟩ := firstOdd_spec R q s
  unfold lookupSeed lookupCode
  dsimp only
  split
  · next hu =>
    have hR : ∀ i < q, acgt (R.get! (s + i)) = true := fun i hi => u3 (s + i) (by omega) (by omega)
    rw [wcGo_zero]
    have ho := mini_lt hg (wc R s q)
    rw [sub_wc hg R s _ (by omega)]
    rw [scan_toList ix G R s _ _ _ _ _ _ _ #[] rfl, Array.toList_empty, List.nil_append,
      mem_filterMap_ite]
    constructor
    · rintro ⟨t, h1, h2, hok, rfl⟩
      exact okAt_occurs hc R s hR t _ ho h1 (by omega) hok _ rfl
    · intro hocc
      obtain ⟨hsz, heq⟩ := hocc
      have hA : ∀ i < q, acgt (G.get! (p + i)) = true := fun i hi => by rw [heq i hi]; exact hR i hi
      have hcode : wc G p q = wc R s q := wc_congr G R p s q heq
      obtain ⟨t, h1, h2, h3⟩ := comp_of_check hc p hsz hA
      rw [hcode] at h1 h2 h3
      generalize hop : ix.mini (wc R s q) = o at h1 h2 h3 ho ⊢
      have hkw : wc G (p + o) ix.k = wc R (s + o) ix.k :=
        wc_congr G R _ _ _ fun i hi => by
          have := heq (o + i) (by omega); rwa [← Nat.add_assoc, ← Nat.add_assoc] at this
      unfold bkt at h1 h2
      rw [hkw] at h1 h2
      refine ⟨t, h1, by omega, ?_, by omega⟩
      have he := sound_of_check hc _ (bucket_lt hg _) t h1 h2
      obtain ⟨e1, e2, e3, e4, e5, -⟩ := entryOk_spec he _ _ h3.symm rfl
      unfold okAt
      simp only [h3, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
      generalize ix.tagOf ix.sl[t]! = tg at e4 e5 ⊢
      refine ⟨⟨by rw [e4, hkw], by omega⟩, ?_⟩
      split
      · next hf =>
        obtain ⟨f1, f2, f3, f4, f5, f6⟩ := e5 hf
        simp only [Bool.and_eq_true, beq_iff_eq]
        rw [f5, f6, flank_bef hg G _ o ho f1, flank_aft G _ o ho, seed_bef R s o (by omega),
          seed_aft hg R s o ho, show p + o - o = p from by omega]
        refine ⟨wc_congr G R p s o fun i hi => heq i (by omega), wc_congr G R _ _ _ fun i hi => ?_⟩
        have := heq (o + ix.k + i) (by omega)
        rwa [← Nat.add_assoc, ← Nat.add_assoc, ← Nat.add_assoc, ← Nat.add_assoc] at this
      · simp only [Bool.and_eq_true, decide_eq_true_eq]
        rw [show p + o - o = p from by omega]
        exact ⟨hsz, (eqRun_iff G R q p s).mpr heq⟩
  · next hu =>
    have hlt : firstOdd R s (s + q) < s + q := by omega
    have hodd := u4 hlt
    generalize firstOdd R s (s + q) = u at hlt hodd u1 u2
    rw [scanOdd_toList G R _ _ s _ 0 #[] rfl, Array.toList_empty, List.nil_append,
      mem_filterMap_ite]
    constructor
    · rintro ⟨t, -, -, hok, rfl⟩
      simp only [okOdd, Bool.and_eq_true, decide_eq_true_eq] at hok
      exact ⟨hok.1.2, (eqRun_iff G R q _ _).mp hok.2⟩
    · intro hocc
      obtain ⟨hsz, heq⟩ := hocc
      have hx := heq (u - s) (by omega)
      rw [show s + (u - s) = u by omega] at hx
      obtain ⟨t, h1, h2⟩ := odd_of_check hc (p + (u - s)) (by omega) (by rw [hx]; exact hodd)
      rw [hx] at h1 h2
      refine ⟨t, by omega, by omega, ?_, by omega⟩
      simp only [okOdd, Bool.and_eq_true, decide_eq_true_eq, h2]
      rw [show p + (u - s) - (u - s) = p by omega]
      exact ⟨⟨by omega, hsz⟩, (eqRun_iff G R q p s).mpr heq⟩

/-- **Order.**  The places come out strictly increasing. -/
theorem lookupSeed_sorted (R : ByteArray) (s : Nat) :
    (lookupSeed ix G R s).toList.Pairwise (· < ·) := by
  have hg := good_of_check hc
  unfold lookupSeed lookupCode
  dsimp only
  split
  · rw [scan_toList ix G R s _ _ _ _ _ _ _ #[] rfl, Array.toList_empty, List.nil_append]
    apply pairwise_filterMap_ite
    intro i j hi hij hj ok1 _
    have hge : ix.mini (wcGo R s (s + q) 0) ≤ ix.posOf ix.sl[i]! := by
      unfold okAt at ok1; simp only [Bool.and_eq_true, decide_eq_true_eq] at ok1; exact ok1.1.2
    have hst := lt_of_steps (fun t => ix.posOf ix.sl[t]!) _ _ (fun j h1 h2 =>
      (entryOk_spec (sound_of_check hc _ (bucket_lt hg _) j h1 (by omega)) _ _ rfl rfl).2.2.2.2.2 h2)
      (j - i - 1) i hi (by omega)
    rw [show i + (j - i - 1) + 1 = j by omega] at hst
    omega
  · rw [scanOdd_toList G R _ _ s _ 0 #[] rfl, Array.toList_empty, List.nil_append]
    apply pairwise_filterMap_ite
    intro i j hi hij hj ok1 _
    simp only [okOdd, Bool.and_eq_true, decide_eq_true_eq] at ok1
    have hst := lt_of_steps (fun t => ix.odd[(R.get! (firstOdd R s (s + q))).toNat]![t]!) 0 _
      (fun j _ h2 => odd_increasing hc _ (UInt8.toNat_lt _) j h2) (j - i - 1) i (by omega) (by omega)
    rw [show i + (j - i - 1) + 1 = j by omega] at hst
    omega

end

/-- An ACGT seed with known code: `lookupCode` is `lookupSeed`. -/
theorem lookupSeed_eq_lookupCode (ix : MzIdx) (G R : ByteArray) (s : Nat)
    (hR : ∀ i < q, acgt (R.get! (s + i)) = true) :
    lookupSeed ix G R s = lookupCode ix G R s (wc R s q) := by
  obtain ⟨u1, u2, -, u4⟩ := firstOdd_spec R q s
  unfold lookupSeed
  dsimp only
  have hu : firstOdd R s (s + q) = s + q := by
    by_cases hlt : firstOdd R s (s + q) < s + q
    · have h := u4 hlt
      have := hR (firstOdd R s (s + q) - s) (by omega)
      rw [show s + (firstOdd R s (s + q) - s) = firstOdd R s (s + q) by omega] at this
      rw [this] at h; cases h
    · omega
  rw [if_pos hu, wcGo_zero]

/-! ## Byte genome: `LookupComplete` and the mapping theorem -/

/-- One byte per letter. -/
def wordBytes (word : List Char) : ByteArray := (word.map fun ch => ch.val.toUInt8).toByteArray

/-- Every place `(c, p)` where the 25-letter `word` occurs (one index per chromosome). -/
def mzLookup (idxs : Array MzIdx) (gb : ByteGenome) (word : List Char) : List (Nat × Nat) :=
  (List.range gb.size).flatMap fun c =>
    (lookupSeed idxs[c]! gb[c]!.bytes (wordBytes word) 0).toList.map (c, ·)

def checkAll (idxs : Array MzIdx) (gb : ByteGenome) : Bool :=
  (List.range gb.size).all fun c => check idxs[c]! gb[c]!.bytes

/-- Map one read through minimizer indexes (seeds looked up in the index,
windows scored by the proved codec). -/
def mapWithMz (sc : AlignmentSpec.Scoring) (T : Int) (gb : ByteGenome) (idxs : Array MzIdx)
    (read : List Char) : Option (Window × Int) :=
  mapWith (mzLookup idxs gb) (kernelScore sc read (decodeGenome gb)) q T (errBound sc T)
    (decodeGenome gb) read

theorem toChar_inj (a b : UInt8) (h : toChar a = toChar b) : a = b := by
  have := congrArg (fun ch : Char => ch.val.toNat) h
  simp only [toChar_val_toNat] at this
  exact UInt8.toNat_inj.mp this

/-- The bytes of a word of a decoded chromosome are the chromosome's bytes. -/
theorem wordBytes_get (B : ByteArray) (p : Nat) (hp : p + q ≤ B.size) (i : Nat) (hi : i < q) :
    (wordBytes (wordAt (decodeBytes B) q p)).get! i = B.get! (p + i) := by
  have hw := wordAt_decodeBytes B p q hp
  have hasc : ∀ ch ∈ wordAt (decodeBytes B) q p, ch.val.toNat < 256 := by
    intro ch hch
    rw [hw, List.mem_map] at hch
    obtain ⟨j, -, rfl⟩ := hch
    rw [toChar_val_toNat]; exact UInt8.toNat_lt _
  have hdec := decodeBytes_toByteArray _ hasc
  have hlen : i < (decodeBytes (wordBytes (wordAt (decodeBytes B) q p))).length := by
    unfold wordBytes; rw [hdec, hw]; simp [hi]
  apply toChar_inj
  rw [← getElem_decodeBytes _ i hlen]
  have : (decodeBytes (wordBytes (wordAt (decodeBytes B) q p)))[i] =
      (wordAt (decodeBytes B) q p)[i]'(by rw [hw]; simp [hi]) := by
    unfold wordBytes; simp only [hdec]
  rw [this]
  simp only [hw, List.getElem_map, List.getElem_range]

/-- **Completeness.**  Indexes that pass the checker report every place every
25-letter word of the genome occurs. -/
theorem checkAll_complete (idxs : Array MzIdx) (gb : ByteGenome) (hchk : checkAll idxs gb = true) :
    LookupComplete (decodeGenome gb) q (mzLookup idxs gb) := by
  intro c chromosome p hch hp
  rw [getElem?_decodeGenome] at hch
  split at hch
  · next hc =>
    cases hch
    simp only [checkAll, List.all_eq_true, List.mem_range] at hchk
    have hcc := hchk c hc
    rw [getElem!_pos gb c hc] at hcc
    simp only [length_decodeBytes] at hp
    simp only [mzLookup, List.mem_flatMap, List.mem_range, List.mem_map]
    refine ⟨c, hc, p, ?_, rfl⟩
    rw [getElem!_pos gb c hc, lookupSeed_mem hcc]
    exact ⟨hp, fun i hi => by rw [Nat.zero_add, ← wordAt, wordBytes_get _ p hp i hi]⟩
  · cases hch

/-- **Mapping.**  Through minimizer indexes that pass the checker, the mapper
gives the specification's answer. -/
theorem mapWithMz_eq_mapSpec (sc : AlignmentSpec.Scoring) (hv : ValidScoring sc) (T : Int)
    (gb : ByteGenome) (idxs : Array MzIdx) (hchk : checkAll idxs gb = true) (read : List Char) :
    mapWithMz sc T gb idxs read = mapSpec sc T (decodeGenome gb) read :=
  mapWith_eq_mapSpec _ _ q sc hv T _ read (checkAll_complete idxs gb hchk) (kernelScore_eq sc read _)

end MapSpec.Mz

#print axioms MapSpec.Mz.lookupSeed_mem
#print axioms MapSpec.Mz.lookupSeed_sorted
#print axioms MapSpec.Mz.lookupSeed_eq_lookupCode
#print axioms MapSpec.Mz.checkAll_complete
#print axioms MapSpec.Mz.mapWithMz_eq_mapSpec
