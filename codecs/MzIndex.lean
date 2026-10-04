import CsrIndex                   -- getU32 / setU32, LookupComplete, mapWith_eq_mapSpec
import MapperMzWords              -- pool: word codes, hash bijection, loops

/-!
# Codec `MzIndex`: minimizer index of 25-letter seeds, certified by a checker

Memory: only the *minimizer place* of each ACGT 25-letter window is indexed
(0.34 / 0.41 / 0.51 of the places for `k = 21 / 22 / 23` on chr1 and chr21),
one 8-byte slot per indexed place (place and tag, kept as the bits of a
`Float` in a `FloatArray`), so 2.7–4.1 bytes per letter plus the bucket
offsets, instead of 8–16.  A lookup reads one bucket and never the genome
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
  letter is looked up through the maximal runs of non-ACGT letters (`runs`):
  its first such letter, if not its first letter, is where a run starts;
  else its first ACGT letter is where a run ends; else it lies in a run.

Nothing about the index is trusted.  `check ix G` verifies the parameters,
every entry against the genome (`checkSound`), that every ACGT window's
minimizer place is indexed (`checkComp`), and the runs (`checkRuns`,
`checkCover`).  Then (`lookupSeed_mem`, `lookupSeed_sorted`)

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
  /-- shifts of the `aft` and `flag` fields (`kb + 2(w-1)`, `kb + 4(w-1)`; any
  values work: the checker compares the fields with the genome) -/
  ash : Nat
  fsh : Nat
  /-- `2^B + 1` LE `UInt32` bucket offsets -/
  offs : ByteArray
  /-- slot `pos · 2^T + tag` per entry, stored as the bits of a `Float`
  (`FloatArray`: unboxed 8 bytes, and unlike an `Array` it is not walked
  element by element when shared with a `Task`) -/
  sl : FloatArray
  /-- the maximal runs `[runs[2i], runs[2i+1])` of non-ACGT bytes, increasing -/
  runs : Array Nat
deriving Inhabited

namespace MzIdx

variable (ix : MzIdx)

/-- Slot of entry `t` (nothing is assumed about how the bits got there). -/
@[inline] def slot (t : Nat) : Nat := (ix.sl.get! t).toBits.toNat
@[inline] def ra (i : Nat) : Nat := ix.runs[2 * i]!
@[inline] def rb (i : Nat) : Nat := ix.runs[2 * i + 1]!
@[inline] def nr : Nat := ix.runs.size / 2
@[inline] def loB (b : Nat) : Nat := getU32 ix.offs b
@[inline] def hiB (b : Nat) : Nat := getU32 ix.offs (b + 1)
@[inline] def posOf (e : Nat) : Nat := e >>> ix.T
@[inline] def tagOf (e : Nat) : Nat := e &&& ix.tM
@[inline] def keyF (tg : Nat) : Nat := tg &&& ix.kbM
@[inline] def befF (tg : Nat) : Nat := (tg >>> ix.kb) &&& ix.fM
@[inline] def aftF (tg : Nat) : Nat := (tg >>> ix.ash) &&& ix.fM
@[inline] def flagF (tg : Nat) : Nat := tg >>> ix.fsh
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
@[inline] def okAt (ix : MzIdx) (G R : ByteArray) (s o key bw aw pmo o2 t : Nat) : Bool :=
  let e := (ix.slot t)
  -- the key is the low `kb` bits of the slot: one mask for a non-matching entry
  (e &&& ix.kbM) == key &&
    (let pos := ix.posOf e
     let tg := ix.tagOf e
     decide (o ≤ pos) &&
      (if ix.flagF tg = 0 then (ix.befF tg &&& pmo) == bw && (ix.aftF tg >>> o2) == aw
       else decide (pos - o + q ≤ G.size) && eqRun G R (pos - o) s q))

/-- Places `pos - o` of the matching entries `t ∈ [t, hi)`. -/
def scan (ix : MzIdx) (G R : ByteArray) (s o key bw aw pmo o2 hi : Nat) (t : Nat) (acc : Array Nat) :
    Array Nat :=
  if t < hi then
    scan ix G R s o key bw aw pmo o2 hi (t + 1)
      (if okAt ix G R s o key bw aw pmo o2 t then acc.push (ix.posOf (ix.slot t) - o) else acc)
  else acc
termination_by hi - t

/-- Run end `x = runs[2i + side]`: the seed `R[s, s+q)` occurs at `x - d`. -/
@[inline] def okEdge (ix : MzIdx) (G R : ByteArray) (side d s i : Nat) : Bool :=
  let x := ix.runs[2 * i + side]!
  decide (d ≤ x) && decide (x - d + q ≤ G.size) && eqRun G R (x - d) s q

/-- Places `runs[2i + side] - d` (`i ∈ [i, nr)`) where the seed occurs. -/
def scanEdge (ix : MzIdx) (G R : ByteArray) (side d s : Nat) (i : Nat) (acc : Array Nat) :
    Array Nat :=
  if i < ix.nr then
    scanEdge ix G R side d s (i + 1)
      (if okEdge ix G R side d s i then acc.push (ix.runs[2 * i + side]! - d) else acc)
  else acc
termination_by ix.nr - i

@[inline] def okIn (G R : ByteArray) (s p : Nat) : Bool := decide (p + q ≤ G.size) && eqRun G R p s q

/-- Places `p ∈ [p, stop)` where the seed occurs. -/
def scanRange (G R : ByteArray) (s stop : Nat) (p : Nat) (acc : Array Nat) : Array Nat :=
  if p < stop then scanRange G R s stop (p + 1) (if okIn G R s p then acc.push p else acc) else acc
termination_by stop - p

/-- Places inside the runs `i, i+1, …` where the seed occurs. -/
def scanInside (ix : MzIdx) (G R : ByteArray) (s : Nat) (i : Nat) (acc : Array Nat) : Array Nat :=
  if i < ix.nr then scanInside ix G R s (i + 1) (scanRange G R s (ix.rb i + 1 - q) (ix.ra i) acc)
  else acc
termination_by ix.nr - i

/-- Lookup of an ACGT seed `R[s, s+q)` whose code `v = wc R s q` the caller
already has (`lookupSeed_eq_lookupCode`). -/
def lookupCode (ix : MzIdx) (G R : ByteArray) (s v : Nat) : Array Nat :=
  let o := ix.mini v
  let h := ix.hsh (ix.sub v o)
  let b := h >>> ix.kb
  scan ix G R s o (h &&& ix.kbM) (v >>> (2 * (q - o))) (v &&& ix.pm[ix.w - 1 - o]!) ix.pm[o]! (2 * o)
    (ix.hiB b) (ix.loB b) #[]

/-- Places `p` (increasing) with `G[p, p+q) = R[s, s+q)`. -/
def lookupSeed (ix : MzIdx) (G R : ByteArray) (s : Nat) : Array Nat :=
  let u := firstOdd R s (s + q)
  if u = s + q then lookupCode ix G R s (wcGo R s (s + q) 0)
  else if s < u then scanEdge ix G R 0 (u - s) s 0 #[]
  else
    let u2 := firstAcgt R s (s + q)
    if u2 < s + q then scanEdge ix G R 1 (u2 - s) s 0 #[]
    else scanInside ix G R s 0 #[]

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
  let e := (ix.slot t)
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
    (decide (hi ≤ t + 1) || decide (pos < ix.posOf (ix.slot (t + 1))))

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
        decide (ix.loB b ≤ t) && decide (t < ix.hiB b) && ix.posOf (ix.slot t) == pm &&
          checkComp ix G (setU32 fill b (t + 1)) (pm + 1) n (p + 1)
    else checkComp ix G fill last n (p + 1)

/-- Run `i` is a maximal run of non-ACGT bytes, before run `i + 1`. -/
def runOk (ix : MzIdx) (G : ByteArray) (i : Nat) : Bool :=
  let a := ix.ra i
  let b := ix.rb i
  decide (a < b) && decide (b ≤ G.size) && allNot G a b &&
    (decide (b = G.size) || acgt (G.get! b)) && (decide (a = 0) || acgt (G.get! (a - 1))) &&
    (decide (ix.nr ≤ i + 1) || decide (b < ix.ra (i + 1)))

def checkRuns (ix : MzIdx) (G : ByteArray) : (n i : Nat) → Bool
  | 0, _ => true
  | n + 1, i => runOk ix G i && checkRuns ix G n (i + 1)

/-- Skip the runs ending at or before `x` (a hint for `checkCover`). -/
def advance (ix : MzIdx) (x : Nat) : (fuel c : Nat) → Nat
  | 0, c => c
  | fuel + 1, c => if c < ix.nr && ix.rb c ≤ x then advance ix x fuel (c + 1) else c

/-- Every non-ACGT place `x, x+1, …` (`n` of them) lies in a run. -/
def checkCover (ix : MzIdx) (G : ByteArray) (c : Nat) : (n x : Nat) → Bool
  | 0, _ => true
  | n + 1, x =>
    if acgt (G.get! x) then checkCover ix G c n (x + 1)
    else
      let c := advance ix x ix.nr c
      decide (c < ix.nr) && decide (ix.ra c ≤ x) && decide (x < ix.rb c) && checkCover ix G c n (x + 1)

/-- The runtime checker. -/
def check (ix : MzIdx) (G : ByteArray) : Bool :=
  checkParams ix && checkSound ix G (2 ^ ix.B) 0 &&
    checkComp ix G ix.offs 0 (G.size + 1 - q) 0 &&
    checkRuns ix G ix.nr 0 && checkCover ix G 0 G.size 0

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
    ash := kb + 2 * (w - 1), fsh := kb + 4 * (w - 1),
    offs := .empty, sl := .empty, runs := #[] }

/-- Slot of minimizer place `pm` (with k-word hash `h`). -/
def slotAt (ix : MzIdx) (G : ByteArray) (pm h : Nat) : Nat :=
  let w1 := ix.w - 1
  let good := decide (w1 ≤ pm) && decide (pm + ix.k + w1 ≤ G.size) &&
    allA G (pm - w1) pm && allA G (pm + ix.k) (pm + ix.k + w1)
  let tag := if good then
      (h &&& ix.kbM) + 2 ^ ix.kb * (wcGo G (pm - w1) pm 0 + 2 ^ (2 * w1) * wcGo G (pm + ix.k) (pm + ix.k + w1) 0)
    else (h &&& ix.kbM) + 2 ^ (ix.kb + 4 * w1)
  pm * 2 ^ ix.T + tag

/-- Fold `f` over the minimizer places of the ACGT windows (increasing, each
once) with the hash of their k-word; rolling window code. -/
@[specialize] def foldMins {α : Type} (ix0 : MzIdx) (G : ByteArray) (init : α)
    (f : α → Nat → Nat → α) : α := Id.run do
  let mask := 2 ^ (2 * q) - 1
  let mut x := 0
  let mut good := 0
  let mut last := 0
  let mut acc := init
  for p in [0:G.size] do
    let c := G.get! p
    if acgt c then x := (x * 4 + byteCode c) &&& mask; good := good + 1 else good := 0
    if good ≥ q then
      let o := ix0.mini x
      let pm := p + 1 - q + o
      if pm + 1 != last then
        last := pm + 1
        acc := f acc pm (ix0.hsh (ix0.sub x o))
  return acc

/-- The slots `pos · 2^T + tag` must stay below `2^63`: choose `B` with
`log2 G.size + T ≤ 63`, `T = 2k - B + 4(25 - k) + 1` (else `check` fails). -/
def build (G : ByteArray) (k B : Nat) : MzIdx := Id.run do
  let ix0 := mkIdx k B
  let nb := 2 ^ B
  let mut cnt := foldMins ix0 G (zeros (4 * (nb + 1))) fun cnt _ h =>
    let b := h >>> ix0.kb
    setU32 cnt (b + 1) (getU32 cnt (b + 1) + 1)
  for b in [0:nb] do cnt := setU32 cnt (b + 1) (getU32 cnt (b + 1) + getU32 cnt b)
  let total := getU32 cnt nb
  let mut sl0 := FloatArray.emptyWithCapacity total
  for _ in [0:total] do sl0 := sl0.push 0
  let (_, sl) := foldMins ix0 G (cnt, sl0) fun (fill, sl) pm h =>
    let b := h >>> ix0.kb
    let t := getU32 fill b
    (setU32 fill b (t + 1), sl.set! t (Float.ofBits (slotAt ix0 G pm h).toUInt64))
  let mut runs : Array Nat := #[]
  for p in [0:G.size] do
    let odd := !acgt (G.get! p)
    if odd && (p == 0 || acgt (G.get! (p - 1))) then runs := runs.push p
    if odd && (p + 1 == G.size || acgt (G.get! (p + 1))) then runs := runs.push (p + 1)
  return { ix0 with offs := cnt, sl, runs }

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
  T_eq : ix.T = ix.kb + 4 * (ix.w - 1) + 1
  tM_eq : ix.tM = 2 ^ ix.T - 1
  pm_eq : ∀ i, i ≤ ix.w → ix.pm[i]! = 2 ^ (2 * i) - 1

theorem good_of_checkParams (ix : MzIdx) (h : checkParams ix = true) : Good ix := by
  simp only [checkParams, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h8, h9, h10, h7, h11, fun i hi => h12 i (by omega)⟩

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

/-- The key of a slot's tag is the slot's low `kb` bits. -/
theorem keyF_tagOf (e : Nat) : ix.keyF (ix.tagOf e) = e &&& ix.kbM := by
  unfold MzIdx.keyF MzIdx.tagOf
  rw [hg.kbM_eq, hg.tM_eq, and_mask_eq, and_mask_eq, and_mask_eq,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by rw [hg.T_eq]; omega))]

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
  ∃ t, ix.loB (bkt ix G x) ≤ t ∧ t < ix.hiB (bkt ix G x) ∧ ix.posOf (ix.slot t) = x

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

/-- What `runOk` says about run `i`. -/
theorem runOk_spec {ix : MzIdx} {G : ByteArray} {i : Nat} (h : runOk ix G i = true) :
    ix.ra i < ix.rb i ∧ ix.rb i ≤ G.size ∧
    (∀ x, ix.ra i ≤ x → x < ix.rb i → acgt (G.get! x) = false) ∧
    (ix.rb i = G.size ∨ acgt (G.get! (ix.rb i)) = true) ∧
    (ix.ra i = 0 ∨ acgt (G.get! (ix.ra i - 1)) = true) ∧
    (i + 1 < ix.nr → ix.rb i < ix.ra (i + 1)) := by
  unfold runOk at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have h3' := allNot_spec G (ix.rb i - ix.ra i) (ix.ra i)
    (by rw [show ix.ra i + (ix.rb i - ix.ra i) = ix.rb i by omega]; exact h3)
  refine ⟨h1, h2, fun x hx1 hx2 => h3' x hx1 (by omega), h4, h5, fun hi => ?_⟩
  rcases h6 with h6 | h6
  · omega
  · exact h6

theorem checkRuns_spec (ix : MzIdx) (G : ByteArray) :
    ∀ n i, checkRuns ix G n i = true → ∀ j, i ≤ j → j < i + n → runOk ix G j = true := by
  intro n
  induction n with
  | zero => intro i _ j h1 h2; omega
  | succ n ih =>
    intro i h j h1 h2
    rw [checkRuns, Bool.and_eq_true] at h
    by_cases hj : j = i
    · subst hj; exact h.1
    · exact ih (i + 1) h.2 j (by omega) (by omega)

theorem checkCover_spec (ix : MzIdx) (G : ByteArray) :
    ∀ n x c, checkCover ix G c n x = true → ∀ y, x ≤ y → y < x + n → acgt (G.get! y) = false →
      ∃ i, i < ix.nr ∧ ix.ra i ≤ y ∧ y < ix.rb i := by
  intro n
  induction n with
  | zero => intro x _ _ y h1 h2; omega
  | succ n ih =>
    intro x c h y h1 h2 hy
    rw [checkCover] at h
    split at h
    · next ha =>
      by_cases hx : y = x
      · subst hx; rw [hy] at ha; cases ha
      · exact ih (x + 1) c h y (by omega) (by omega) hy
    · next ha =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨h3, h4⟩, h5⟩, h6⟩ := h
      by_cases hx : y = x
      · subst hx; exact ⟨_, h3, h4, h5⟩
      · exact ih (x + 1) _ h6 y (by omega) (by omega) hy

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

theorem scan_toList (ix : MzIdx) (G R : ByteArray) (s o key bw aw pmo o2 hi : Nat) :
    ∀ n t acc, hi - t = n →
      (scan ix G R s o key bw aw pmo o2 hi t acc).toList = acc.toList ++ (List.range' t n).filterMap
        (fun t => if okAt ix G R s o key bw aw pmo o2 t then some (ix.posOf (ix.slot t) - o) else none) := by
  intro n
  induction n with
  | zero => intro t acc hn; rw [scan, if_neg (by omega)]; simp
  | succ n ih =>
    intro t acc hn
    rw [scan, if_pos (by omega), ih (t + 1) _ (by omega), List.range'_succ, List.filterMap_cons]
    split <;> simp

theorem scanEdge_toList (ix : MzIdx) (G R : ByteArray) (side d s : Nat) :
    ∀ n i acc, ix.nr - i = n →
      (scanEdge ix G R side d s i acc).toList = acc.toList ++ (List.range' i n).filterMap
        (fun i => if okEdge ix G R side d s i then some (ix.runs[2 * i + side]! - d) else none) := by
  intro n
  induction n with
  | zero => intro i acc hn; rw [scanEdge, if_neg (by omega)]; simp
  | succ n ih =>
    intro i acc hn
    rw [scanEdge, if_pos (by omega), ih (i + 1) _ (by omega), List.range'_succ, List.filterMap_cons]
    split <;> simp

theorem scanRange_toList (G R : ByteArray) (s stop : Nat) :
    ∀ n p acc, stop - p = n →
      (scanRange G R s stop p acc).toList = acc.toList ++ (List.range' p n).filterMap
        (fun p => if okIn G R s p then some p else none) := by
  intro n
  induction n with
  | zero => intro p acc hn; rw [scanRange, if_neg (by omega)]; simp
  | succ n ih =>
    intro p acc hn
    rw [scanRange, if_pos (by omega), ih (p + 1) _ (by omega), List.range'_succ, List.filterMap_cons]
    split <;> simp

/-- Places tried inside run `i`. -/
def inRun (ix : MzIdx) (G R : ByteArray) (s i : Nat) : List Nat :=
  (List.range' (ix.ra i) (ix.rb i + 1 - q - ix.ra i)).filterMap
    (fun p => if okIn G R s p then some p else none)

theorem scanInside_toList (ix : MzIdx) (G R : ByteArray) (s : Nat) :
    ∀ n i acc, ix.nr - i = n →
      (scanInside ix G R s i acc).toList = acc.toList ++ (List.range' i n).flatMap (inRun ix G R s) := by
  intro n
  induction n with
  | zero => intro i acc hn; rw [scanInside, if_neg (by omega)]; simp
  | succ n ih =>
    intro i acc hn
    rw [scanInside, if_pos (by omega), ih (i + 1) _ (by omega), List.range'_succ, List.flatMap_cons,
      scanRange_toList G R s _ _ _ _ rfl]
    simp [inRun]

/-! ### Entries -/

/-- What `entryOk` says about entry `t` (place `pos`, tag `tg`). -/
theorem entryOk_spec {ix : MzIdx} {G : ByteArray} {b hi t : Nat} (h : entryOk ix G b hi t = true)
    (pos tg : Nat) (hpos : pos = ix.posOf (ix.slot t)) (htg : tg = ix.tagOf (ix.slot t)) :
    pos + ix.k ≤ G.size ∧ (∀ i < ix.k, acgt (G.get! (pos + i)) = true) ∧
    ix.hsh (wc G pos ix.k) >>> ix.kb = b ∧ ix.keyF tg = (ix.hsh (wc G pos ix.k) &&& ix.kbM) ∧
    (ix.flagF tg = 0 → ix.w - 1 ≤ pos ∧ pos + ix.k + (ix.w - 1) ≤ G.size ∧
      (∀ i < ix.w - 1, acgt (G.get! (pos - (ix.w - 1) + i)) = true) ∧
      (∀ i < ix.w - 1, acgt (G.get! (pos + ix.k + i)) = true) ∧
      ix.befF tg = wc G (pos - (ix.w - 1)) (ix.w - 1) ∧ ix.aftF tg = wc G (pos + ix.k) (ix.w - 1)) ∧
    (t + 1 < hi → pos < ix.posOf (ix.slot (t + 1))) := by
  subst hpos htg
  unfold entryOk at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq,
    and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  rw [wcGo_zero] at h3 h4
  refine ⟨h1, (allA_iff G _ _).mp h2, h3, h4, fun hf => ?_, fun ht => ?_⟩
  · rcases h5 with h5 | ⟨f1, f2, f3, f4, f5, f6⟩
    · exact absurd hf h5
    · rw [allA_iff' G _ _ (by omega), show ix.posOf (ix.slot t) - (ix.posOf (ix.slot t) - (ix.w - 1)) = ix.w - 1 by omega] at f3
      rw [wcGo_zero' G _ _ (by omega), show ix.posOf (ix.slot t) - (ix.posOf (ix.slot t) - (ix.w - 1)) = ix.w - 1 by omega] at f5
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

theorem run_of_check : ∀ i, i < ix.nr → runOk ix G i = true := by
  simp only [check, Bool.and_eq_true] at hc
  intro i hi
  exact checkRuns_spec ix G _ 0 hc.1.2 i (by omega) (by omega)

theorem cover_of_check (y : Nat) (hy : y < G.size) (ha : acgt (G.get! y) = false) :
    ∃ i, i < ix.nr ∧ ix.ra i ≤ y ∧ y < ix.rb i := by
  simp only [check, Bool.and_eq_true] at hc
  exact checkCover_spec ix G _ 0 0 hc.2 y (by omega) (by omega) ha

/-- A non-ACGT place after an ACGT one starts a run. -/
theorem run_start (x : Nat) (hx : x < G.size) (h0 : 0 < x) (ha : acgt (G.get! x) = false)
    (hb : acgt (G.get! (x - 1)) = true) : ∃ i, i < ix.nr ∧ ix.ra i = x := by
  obtain ⟨i, hi, h1, h2⟩ := cover_of_check hc x hx ha
  obtain ⟨-, -, r3, -⟩ := runOk_spec (run_of_check hc i hi)
  refine ⟨i, hi, ?_⟩
  by_cases he : ix.ra i = x
  · exact he
  · have := r3 (x - 1) (by omega) (by omega); rw [hb] at this; cases this

/-- An ACGT place after a non-ACGT one ends a run. -/
theorem run_end (x : Nat) (hx : x < G.size) (h0 : 0 < x) (ha : acgt (G.get! x) = true)
    (hb : acgt (G.get! (x - 1)) = false) : ∃ i, i < ix.nr ∧ ix.rb i = x := by
  obtain ⟨i, hi, h1, h2⟩ := cover_of_check hc (x - 1) (by omega) hb
  obtain ⟨-, -, r3, -⟩ := runOk_spec (run_of_check hc i hi)
  refine ⟨i, hi, ?_⟩
  by_cases he : ix.rb i = x
  · exact he
  · have := r3 x (by omega) (by omega); rw [ha] at this; cases this

/-- A non-ACGT window lies in one run. -/
theorem run_inside (p : Nat) (hp : p + q ≤ G.size) (ha : ∀ j < q, acgt (G.get! (p + j)) = false) :
    ∃ i, i < ix.nr ∧ ix.ra i ≤ p ∧ p + q ≤ ix.rb i := by
  obtain ⟨i, hi, h1, h2⟩ := cover_of_check hc p (by unfold q at hp; omega)
    (by simpa using ha 0 (by decide))
  obtain ⟨-, r2, -, r4, -⟩ := runOk_spec (run_of_check hc i hi)
  refine ⟨i, hi, h1, ?_⟩
  by_cases hlt : p + q ≤ ix.rb i
  · exact hlt
  · rcases r4 with r4 | r4
    · omega
    · have := ha (ix.rb i - p) (by omega)
      rw [show p + (ix.rb i - p) = ix.rb i by omega, r4] at this; cases this

theorem runs_increasing : ∀ i j, i < j → j < ix.nr → ix.ra i < ix.ra j ∧ ix.rb i < ix.ra j := by
  have step : ∀ t, 0 ≤ t → t + 1 < ix.nr → ix.ra t < ix.ra (t + 1) := fun t _ ht => by
    obtain ⟨r1, -, -, -, -, r6⟩ := runOk_spec (run_of_check hc t (by omega))
    have := r6 ht; omega
  intro i j hij hj
  have hra := lt_of_steps ix.ra 0 ix.nr step (j - i - 1) i (by omega) (by omega)
  rw [show i + (j - i - 1) + 1 = j by omega] at hra
  obtain ⟨-, -, -, -, -, r6⟩ := runOk_spec (run_of_check hc i (by omega))
  have h1 := r6 (by omega)
  refine ⟨hra, ?_⟩
  by_cases hj1 : j = i + 1
  · subst hj1; exact h1
  · have := lt_of_steps ix.ra 0 ix.nr step (j - i - 2) (i + 1) (by omega) (by omega)
    rw [show i + 1 + (j - i - 2) + 1 = j by omega] at this; omega

theorem rb_increasing (i j : Nat) (hij : i < j) (hj : j < ix.nr) : ix.rb i < ix.rb j := by
  have := (runs_increasing hc i j hij hj).2
  obtain ⟨r1, -⟩ := runOk_spec (run_of_check hc j hj)
  omega

/-- **Soundness of a bucket hit** (tag path or genome check). -/
theorem okAt_occurs (R : ByteArray) (s : Nat) (hR : ∀ i < q, acgt (R.get! (s + i)) = true)
    (t : Nat) (o : Nat) (ho : o < ix.w)
    (ht1 : ix.loB (ix.hsh (wc R (s + o) ix.k) >>> ix.kb) ≤ t)
    (ht2 : t < ix.hiB (ix.hsh (wc R (s + o) ix.k) >>> ix.kb))
    (hok : okAt ix G R s o (ix.hsh (wc R (s + o) ix.k) &&& ix.kbM) (wc R s q >>> (2 * (q - o)))
      (wc R s q &&& ix.pm[ix.w - 1 - o]!) ix.pm[o]! (2 * o) t = true)
    (pos : Nat) (hpos : ix.posOf (ix.slot t) = pos) :
    Occurs G R s (pos - o) := by
  have hg := good_of_check hc
  have hw := hg.w_eq; have hk := hg.k_le; have hk0 := hg.k_pos
  have he := sound_of_check hc _ (bucket_lt hg _) t ht1 ht2
  obtain ⟨e1, e2, e3, e4, e5, -⟩ := entryOk_spec he pos _ hpos.symm rfl
  rw [keyF_tagOf hg] at e4
  unfold okAt at hok
  simp only [hpos, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  generalize ix.tagOf (ix.slot t) = tg at e5 hok
  generalize hh : ix.hsh (wc R (s + o) ix.k) = h at hok e3
  obtain ⟨hkey, hop, hrest⟩ := hok
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
    rw [scan_toList ix G R s _ _ _ _ _ _ _ _ _ #[] rfl, Array.toList_empty, List.nil_append,
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
      rw [keyF_tagOf hg] at e4
      unfold okAt
      simp only [h3, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
      generalize ix.tagOf (ix.slot t) = tg at e5 ⊢
      refine ⟨by rw [e4, hkw], by omega, ?_⟩
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
    generalize firstOdd R s (s + q) = u at hlt hodd u1 u2 u3 ⊢
    split
    · -- a run of non-ACGT letters starts at `p + (u - s)`
      next hsu =>
      rw [scanEdge_toList ix G R 0 (u - s) s _ 0 #[] rfl, Array.toList_empty, List.nil_append,
        mem_filterMap_ite]
      constructor
      · rintro ⟨i, -, -, hok, rfl⟩
        simp only [okEdge, Bool.and_eq_true, decide_eq_true_eq] at hok
        exact ⟨hok.1.2, (eqRun_iff G R q _ _).mp hok.2⟩
      · rintro ⟨hsz, heq⟩
        have hx := heq (u - s) (by omega)
        rw [show s + (u - s) = u by omega] at hx
        have hx1 := heq (u - s - 1) (by omega)
        rw [show s + (u - s - 1) = u - 1 by omega, show p + (u - s - 1) = p + (u - s) - 1 by omega] at hx1
        have hb := u3 (u - 1) (by omega) (by omega)
        obtain ⟨i, hi, hra⟩ := run_start hc (p + (u - s)) (by omega) (by omega)
          (by rw [hx]; exact hodd) (by rw [hx1]; exact hb)
        unfold MzIdx.ra at hra
        refine ⟨i, by omega, by omega, ?_, ?_⟩
        · simp only [okEdge, Bool.and_eq_true, decide_eq_true_eq, Nat.add_zero, hra]
          rw [show p + (u - s) - (u - s) = p by omega]
          exact ⟨⟨by omega, hsz⟩, (eqRun_iff G R q p s).mpr heq⟩
        · simp only [Nat.add_zero, hra]; omega
    · next hsu =>
      have hus : u = s := by omega
      subst hus
      obtain ⟨v1, v2, v3, v4⟩ := firstAcgt_spec R q u
      generalize firstAcgt R u (u + q) = u2 at v1 v2 v3 v4 ⊢
      split
      · -- a run of non-ACGT letters ends at `p + (u2 - u)`
        next hv =>
        have hA2 := v4 hv
        have hs2 : u < u2 := by
          by_cases h' : u2 = u
          · subst h'; rw [hA2] at hodd; cases hodd
          · omega
        rw [scanEdge_toList ix G R 1 (u2 - u) u _ 0 #[] rfl, Array.toList_empty, List.nil_append,
          mem_filterMap_ite]
        constructor
        · rintro ⟨i, -, -, hok, rfl⟩
          simp only [okEdge, Bool.and_eq_true, decide_eq_true_eq] at hok
          exact ⟨hok.1.2, (eqRun_iff G R q _ _).mp hok.2⟩
        · rintro ⟨hsz, heq⟩
          have hx := heq (u2 - u) (by omega)
          rw [show u + (u2 - u) = u2 by omega] at hx
          have hx1 := heq (u2 - u - 1) (by omega)
          rw [show u + (u2 - u - 1) = u2 - 1 by omega,
            show p + (u2 - u - 1) = p + (u2 - u) - 1 by omega] at hx1
          have hb := v3 (u2 - 1) (by omega) (by omega)
          obtain ⟨i, hi, hrb⟩ := run_end hc (p + (u2 - u)) (by omega) (by omega)
            (by rw [hx]; exact hA2) (by rw [hx1]; exact hb)
          unfold MzIdx.rb at hrb
          refine ⟨i, by omega, by omega, ?_, ?_⟩
          · simp only [okEdge, Bool.and_eq_true, decide_eq_true_eq, hrb]
            rw [show p + (u2 - u) - (u2 - u) = p by omega]
            exact ⟨⟨by omega, hsz⟩, (eqRun_iff G R q p u).mpr heq⟩
          · simp only [hrb]; omega
      · -- no ACGT letter: inside a run
        next hv =>
        have hall : ∀ j < q, acgt (R.get! (u + j)) = false := fun j hj => v3 (u + j) (by omega) (by omega)
        rw [scanInside_toList ix G R u _ 0 #[] rfl, Array.toList_empty, List.nil_append,
          List.mem_flatMap]
        constructor
        · rintro ⟨i, -, hp⟩
          unfold inRun at hp
          rw [mem_filterMap_ite] at hp
          obtain ⟨p', -, -, hok, rfl⟩ := hp
          simp only [okIn, Bool.and_eq_true, decide_eq_true_eq] at hok
          exact ⟨hok.1, (eqRun_iff G R q _ _).mp hok.2⟩
        · rintro ⟨hsz, heq⟩
          have hG : ∀ j < q, acgt (G.get! (p + j)) = false := fun j hj => by rw [heq j hj]; exact hall j hj
          obtain ⟨i, hi, h1, h2⟩ := run_inside hc p hsz hG
          refine ⟨i, List.mem_range'_1.mpr ⟨by omega, by omega⟩, ?_⟩
          unfold inRun
          rw [mem_filterMap_ite]
          refine ⟨p, h1, by omega, ?_, rfl⟩
          simp only [okIn, Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨hsz, (eqRun_iff G R q p u).mpr heq⟩

/-- **Order.**  The places come out strictly increasing. -/
theorem lookupSeed_sorted (R : ByteArray) (s : Nat) :
    (lookupSeed ix G R s).toList.Pairwise (· < ·) := by
  have hg := good_of_check hc
  unfold lookupSeed lookupCode
  dsimp only
  split
  · rw [scan_toList ix G R s _ _ _ _ _ _ _ _ _ #[] rfl, Array.toList_empty, List.nil_append]
    apply pairwise_filterMap_ite
    intro i j hi hij hj ok1 _
    have hge : ix.mini (wcGo R s (s + q) 0) ≤ ix.posOf (ix.slot i) := by
      unfold okAt at ok1; simp only [Bool.and_eq_true, decide_eq_true_eq] at ok1; exact ok1.2.1
    have hst := lt_of_steps (fun t => ix.posOf (ix.slot t)) _ _ (fun j h1 h2 =>
      (entryOk_spec (sound_of_check hc _ (bucket_lt hg _) j h1 (by omega)) _ _ rfl rfl).2.2.2.2.2 h2)
      (j - i - 1) i hi (by omega)
    rw [show i + (j - i - 1) + 1 = j by omega] at hst
    omega
  · split
    · rw [scanEdge_toList ix G R 0 _ s _ 0 #[] rfl, Array.toList_empty, List.nil_append]
      apply pairwise_filterMap_ite
      intro i j hi hij hj ok1 _
      simp only [okEdge, Bool.and_eq_true, decide_eq_true_eq, Nat.add_zero] at ok1 ⊢
      have := (runs_increasing hc i j hij (by omega)).1
      unfold MzIdx.ra at this
      omega
    · split
      · rw [scanEdge_toList ix G R 1 _ s _ 0 #[] rfl, Array.toList_empty, List.nil_append]
        apply pairwise_filterMap_ite
        intro i j hi hij hj ok1 _
        simp only [okEdge, Bool.and_eq_true, decide_eq_true_eq] at ok1
        have := rb_increasing hc i j hij (by omega)
        unfold MzIdx.rb at this
        omega
      · rw [scanInside_toList ix G R s _ 0 #[] rfl, Array.toList_empty, List.nil_append,
          List.pairwise_flatMap]
        refine ⟨fun i _ => ?_, ?_⟩
        · unfold inRun
          exact pairwise_filterMap_ite _ _ _ _ fun _ _ _ hab _ _ _ => hab
        · apply pairwise_range'
          intro i j hi hij hj x hx y hy
          unfold inRun at hx hy
          rw [mem_filterMap_ite] at hx hy
          obtain ⟨_, hx1, hx2, -, rfl⟩ := hx
          obtain ⟨_, hy1, -, -, rfl⟩ := hy
          have := (runs_increasing hc i j hij (by omega)).2
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
