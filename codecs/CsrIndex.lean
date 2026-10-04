import SeedMapper                 -- `LookupComplete`
import MapperBytes                -- pool: byte genome and word codes

/-!
# Codec `CsrIndex`: compact k-mer index with a certified completeness checker

The genome is one `ByteArray` per chromosome (`ByteGenome`).  The index is
CSR over the 2-bit codes of `l0`-letter words (`codeOfWord`: A0 C1 G2 T3,
anything else 0; collisions are allowed):

* `offs` — `4^l0 + 1` little-endian `UInt32`s; bucket `h` is the entry range
  `offs[h] ..< offs[h+1]`;
* `pos` — one little-endian `UInt32` per entry: a global coordinate
  `starts[c] + p`, turned back into `(c, p)` by `locate`.

Nothing about how the index is built or stored is trusted.  `checkIndex idx gb`
looks at every place `(c, p)` of the genome and checks that bucket
`code(word at (c, p))` holds an entry equal to `(c, p)`; the theorem
`checkIndex_complete` turns `checkIndex idx gb = true` into
`LookupComplete (decodeGenome gb) idx.l0 idx.lookup`, which is all the mapper
needs (`mapWith_eq_mapSpec`).  So the index may come from the fast builder
below, from disk, or from anywhere.
-/

namespace MapSpec

/-! ## The algorithm -/

/-- Little-endian `UInt32` number `i` of a byte array. -/
@[inline] def getU32 (B : ByteArray) (i : Nat) : Nat :=
  let j := 4 * i
  ((B.get! j).toUInt32 ||| ((B.get! (j + 1)).toUInt32 <<< 8) |||
    ((B.get! (j + 2)).toUInt32 <<< 16) ||| ((B.get! (j + 3)).toUInt32 <<< 24)).toNat

@[inline] def setU32 (B : ByteArray) (i v : Nat) : ByteArray :=
  let j := 4 * i
  let v := v.toUInt32
  ((((B.set! j v.toUInt8).set! (j + 1) (v >>> 8).toUInt8).set! (j + 2) (v >>> 16).toUInt8).set!
    (j + 3) (v >>> 24).toUInt8)

def zeroDouble (n : Nat) : (fuel : Nat) → ByteArray → ByteArray
  | 0, B => B
  | f + 1, B => if B.size < n then zeroDouble n f (B ++ B) else B

/-- `n` zero bytes (by doubling, so `memcpy` does the work). -/
def zeroBytes (n : Nat) : ByteArray :=
  (zeroDouble n 64 (ByteArray.mk (Array.replicate 4096 0))).extract 0 n

structure CsrIndex where
  l0 : Nat
  /-- global coordinate of each chromosome's first letter -/
  starts : Array Nat
  /-- `4^l0 + 1` LE `UInt32` bucket offsets -/
  offs : ByteArray
  /-- LE `UInt32` global coordinates -/
  pos : ByteArray
deriving Inhabited

/-- Largest `c` in `lo ..< hi` with `starts[c] ≤ x` (binary search, fuel-bounded). -/
def locateAux (starts : Array Nat) (x : Nat) : (fuel lo hi : Nat) → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if hi ≤ lo + 1 then lo
    else
      let mid := (lo + hi) / 2
      if starts[mid]! ≤ x then locateAux starts x fuel mid hi else locateAux starts x fuel lo mid

/-- Global coordinate ↦ (chromosome, start). -/
@[inline] def locate (starts : Array Nat) (x : Nat) : Nat × Nat :=
  let c := locateAux starts x 64 0 starts.size
  (c, x - starts[c]!)

namespace CsrIndex

@[inline] def lo (idx : CsrIndex) (h : Nat) : Nat := getU32 idx.offs h
@[inline] def hi (idx : CsrIndex) (h : Nat) : Nat := getU32 idx.offs (h + 1)

/-- The place stored at entry `t`. -/
@[inline] def entry (idx : CsrIndex) (t : Nat) : Nat × Nat := locate idx.starts (getU32 idx.pos t)

/-- Every place in the word's bucket.  (A mapper can instead walk the entries
`idx.lo h ..< idx.hi h` with `h = byteWordCode read q l0`; see `mem_lookup`.) -/
def lookup (idx : CsrIndex) (word : List Char) : List (Nat × Nat) :=
  let h := codeOfWord word
  (List.range' (idx.lo h) (idx.hi h - idx.lo h)).map idx.entry

end CsrIndex

/-! ### Builder (fast; not trusted — `checkIndex` certifies its output) -/

def chromStarts (gb : ByteGenome) : Array Nat := Id.run do
  let mut s : Array Nat := Array.emptyWithCapacity gb.size
  let mut x := 0
  for bc in gb do
    s := s.push x
    x := x + bc.bytes.size
  return s

@[inline] def bumpU32 (B : ByteArray) (i : Nat) : ByteArray := setU32 B i (getU32 B i + 1)

/-- Count the words at places `p .. p+k` into slot `h+1` (`h` rolling). -/
def countRun (B : ByteArray) (l0 M : Nat) (offs : ByteArray) : (k p h : Nat) → ByteArray
  | 0, _, h => bumpU32 offs (h + 1)
  | k + 1, p, h =>
    countRun B l0 M (bumpU32 offs (h + 1)) k (p + 1) ((h * 4 + byteCode (B.get! (p + l0))) % M)

/-- Place the words at `p .. p+k` (global coordinate `base + p`) into their buckets. -/
def fillRun (B : ByteArray) (l0 M base : Nat) (fill pos : ByteArray) :
    (k p h : Nat) → ByteArray × ByteArray
  | 0, p, h =>
    let t := getU32 fill h
    (setU32 fill h (t + 1), setU32 pos t (base + p))
  | k + 1, p, h =>
    let t := getU32 fill h
    fillRun B l0 M base (setU32 fill h (t + 1)) (setU32 pos t (base + p)) k (p + 1)
      ((h * 4 + byteCode (B.get! (p + l0))) % M)

def prefixSum (offs : ByteArray) : (k h : Nat) → ByteArray
  | 0, _ => offs
  | k + 1, h => prefixSum (setU32 offs (h + 1) (getU32 offs (h + 1) + getU32 offs h)) k (h + 1)

def buildCsr (l0 : Nat) (gb : ByteGenome) : CsrIndex := Id.run do
  assert! 0 < l0
  let M := 4 ^ l0
  let starts := chromStarts gb
  let mut offs := zeroBytes (4 * (M + 1))
  let mut total := 0
  for bc in gb do
    let B := bc.bytes
    if l0 ≤ B.size then
      offs := countRun B l0 M offs (B.size - l0) 0 (initCode B l0)
      total := total + (B.size + 1 - l0)
  offs := prefixSum offs M 0
  let mut fill := offs
  let mut pos := zeroBytes (4 * total)
  for c in [0:gb.size] do
    let B := gb[c]!.bytes
    if l0 ≤ B.size then
      (fill, pos) := fillRun B l0 M starts[c]! fill pos (B.size - l0) 0 (initCode B l0)
  return { l0, starts, offs, pos }

/-! ### Checker -/

/-- `byteWordCode B p k` computed without building a list. -/
def codeLoop (B : ByteArray) (p : Nat) : (k acc i : Nat) → Nat
  | 0, acc, _ => acc
  | k + 1, acc, i => codeLoop B p k (acc * 4 + byteCode (B.get! (p + i))) (i + 1)


/-- Place `(c, p)`, whose word has code `h`, is the entry `inv[p - base]` of bucket `h`. -/
@[inline] def checkAt (idx : CsrIndex) (c : Nat) (inv : ByteArray) (base p h : Nat) : Bool :=
  let t := getU32 inv (p - base)
  let e := idx.entry t
  decide (idx.lo h ≤ t) && decide (t < idx.hi h) && decide (e.1 = c) && decide (e.2 = p)

/-- `checkAt` at places `p .. p+k` of one chromosome, rolling the code `h`. -/
def verifyRun (idx : CsrIndex) (c : Nat) (B inv : ByteArray) (base M : Nat) : (k p h : Nat) → Bool
  | 0, p, h => checkAt idx c inv base p h
  | k + 1, p, h =>
    checkAt idx c inv base p h &&
      verifyRun idx c B inv base M k (p + 1) ((h * 4 + byteCode (B.get! (p + idx.l0))) % M)

/-- Places `j*sz .. min((j+1)*sz - 1, last)` of one chromosome (one parallel piece). -/
def verifyPiece (idx : CsrIndex) (c : Nat) (B inv : ByteArray) (last sz j : Nat) : Bool :=
  let p0 := j * sz
  decide (last < p0) ||
    verifyRun idx c B inv p0 (4 ^ idx.l0) (min (sz - 1) (last - p0)) p0 (codeLoop B p0 idx.l0 0 0)

/-- `verifyRun` over all places `0 .. last` of one chromosome, cut into
`chunks` pieces checked in parallel tasks; piece `j` reads `invs[j]`. -/
def verifyChrom (idx : CsrIndex) (chunks c : Nat) (B : ByteArray) (invs : Array ByteArray) : Bool :=
  if idx.l0 ≤ B.size then
    let last := B.size - idx.l0
    let sz := last / chunks + 1
    let tasks := (List.range chunks).map fun j =>
      Task.spawn fun _ => verifyPiece idx c B invs[j]! last sz j
    decide (0 < chunks) && tasks.all Task.get
  else true

/-- Checks every place of the genome against inverse positions:
`invs[c][j]` holds, as LE `UInt32`s, the entry of each place of piece `j` of
chromosome `c`.  Nothing is assumed about `invs`. -/
def verifyIndex (idx : CsrIndex) (gb : ByteGenome) (chunks : Nat) (invs : Array (Array ByteArray)) :
    Bool :=
  decide (0 < idx.l0) &&
    (List.range gb.size).all fun c => verifyChrom idx chunks c gb[c]!.bytes invs[c]!

/-- Scan entries `t .. t+k`; write those whose place falls in pieces
`lo ..< lo + arrs.size` (piece `g = c * chunks + j`) into `arrs`. -/
def inverseRun (idx : CsrIndex) (ns : Array Nat) (chunks lo : Nat) (arrs : Array ByteArray) :
    (k t : Nat) → Array ByteArray
  | 0, _ => arrs
  | k + 1, t =>
    let e := idx.entry t
    let n := ns[e.1]!
    let arrs :=
      if e.1 < ns.size && idx.l0 ≤ n && e.2 + idx.l0 ≤ n then
        let sz := (n - idx.l0) / chunks + 1
        let j := e.2 / sz
        let g := e.1 * chunks + j
        if lo ≤ g && g < lo + arrs.size then arrs.modify (g - lo) (setU32 · (e.2 - j * sz) t) else arrs
      else arrs
    inverseRun idx ns chunks lo arrs k (t + 1)

/-- Inverse positions from the index itself (not trusted), `tasks` parallel
scans of the entries, each filling its own range of pieces. -/
def inversePositions (idx : CsrIndex) (gb : ByteGenome) (chunks tasks : Nat) :
    Array (Array ByteArray) :=
  let ns := gb.map (·.bytes.size)
  let G := gb.size * chunks
  let per := G / tasks + 1
  let pieceBytes (g : Nat) : ByteArray :=
    let n := ns[g / chunks]!
    if idx.l0 ≤ n then zeroBytes (4 * ((n - idx.l0) / chunks + 1)) else ByteArray.empty
  let ts := (List.range tasks).map fun k => Task.spawn fun _ =>
    let lo := k * per
    let arrs := ((List.range per).filter (lo + · < G)).toArray.map (pieceBytes <| lo + ·)
    inverseRun idx ns chunks lo arrs (idx.pos.size / 4) 0
  let flat := ts.foldl (fun acc t => acc ++ t.get) #[]
  (Array.range gb.size).map fun c => (Array.range chunks).map fun j => flat[c * chunks + j]!

def checkIndex (idx : CsrIndex) (gb : ByteGenome) (chunks := 16) (tasks := 4) : Bool :=
  verifyIndex idx gb chunks (inversePositions idx gb chunks tasks)

/-! ### Checker, bucket order (`checkIndexM`)

Walks the buckets in order; for each entry `t` of bucket `h` whose place
`(c, p)` has word code `h`, sets mark byte `p` of chromosome `c` to 1.  Then
every place must be marked.  Two random memory accesses per entry (genome,
mark) and one byte of scratch per letter. -/

/-- Entry `t` sits in bucket `h` and is a place whose word has code `h`. -/
@[inline] def entryOk (idx : CsrIndex) (gb : ByteGenome) (h t : Nat) : Bool :=
  let e := idx.entry t
  let B := gb[e.1]!.bytes
  decide (e.1 < gb.size) && decide (e.2 + idx.l0 ≤ B.size) && codeLoop B e.2 idx.l0 0 0 == h

def markRun (idx : CsrIndex) (gb : ByteGenome) (h : Nat) (marks : Array ByteArray) :
    (k t : Nat) → Array ByteArray
  | 0, _ => marks
  | k + 1, t =>
    let e := idx.entry t
    markRun idx gb h (if entryOk idx gb h t then marks.modify e.1 (·.set! e.2 1) else marks) k (t + 1)

def markBuckets (idx : CsrIndex) (gb : ByteGenome) (marks : Array ByteArray) :
    (k h : Nat) → Array ByteArray
  | 0, _ => marks
  | k + 1, h => markBuckets idx gb (markRun idx gb h marks (idx.hi h - idx.lo h) (idx.lo h)) k (h + 1)

/-- Mark bytes `p .. p+k` are all 1. -/
def allMarked (mark : ByteArray) : (k p : Nat) → Bool
  | 0, p => mark.get! p == 1
  | k + 1, p => mark.get! p == 1 && allMarked mark k (p + 1)

def checkIndexM (idx : CsrIndex) (gb : ByteGenome) : Bool :=
  let marks := markBuckets idx gb (gb.map fun bc => zeroBytes bc.bytes.size) (4 ^ idx.l0) 0
  (List.range gb.size).all fun c =>
    let n := gb[c]!.bytes.size
    if idx.l0 ≤ n then allMarked marks[c]! (n - idx.l0) 0 else true

/-- Map one read through a CSR index (seeds looked up in the index, windows
scored by the proved codec). -/
def mapWithCsr (sc : AlignmentSpec.Scoring) (T : Int) (gb : ByteGenome) (idx : CsrIndex)
    (read : List Char) : Option (Window × Int) :=
  mapWith idx.lookup (kernelScore sc read (decodeGenome gb)) idx.l0 T (errBound sc T)
    (decodeGenome gb) read

/-! ## The theorems

    checkIndex idx gb = true →
      LookupComplete (decodeGenome gb) idx.l0 idx.lookup                     (checkIndex_complete)
    checkIndex idx gb = true → c < gb.size → p + idx.l0 ≤ gb[c].bytes.size →
      ∃ t, idx.lo h ≤ t < idx.hi h ∧ idx.entry t = (c, p),
      h = byteWordCode gb[c].bytes p idx.l0                                  (checkIndex_bucket)
    (c, p) ∈ idx.lookup word ↔
      ∃ t, idx.lo h ≤ t < idx.hi h ∧ idx.entry t = (c, p),  h = codeOfWord word   (mem_lookup)

    checkIndex idx gb = true →
      mapWithCsr sc T gb idx read = mapSpec sc T (decodeGenome gb) read      (mapWithCsr_eq_mapSpec)

for every index `idx` (however built or loaded), byte genome `gb`, read,
threshold `T` and scoring with `ValidScoring sc`.  The
genome they are about is `decodeGenome gb`; for an ASCII genome `g`,
`decodeGenome (encodeGenome g) = g` (`decodeGenome_encodeGenome`). -/

/-! ## Proof -/

namespace CsrIndex

/-- Place `(c, p)` is an entry of bucket `h`. -/
def InBucket (idx : CsrIndex) (h c p : Nat) : Prop :=
  ∃ t, idx.lo h ≤ t ∧ t < idx.hi h ∧ idx.entry t = (c, p)

theorem mem_lookup (idx : CsrIndex) (word : List Char) (c p : Nat) :
    (c, p) ∈ idx.lookup word ↔ idx.InBucket (codeOfWord word) c p := by
  simp only [lookup, InBucket, List.mem_map, List.mem_range'_1]
  constructor
  · rintro ⟨t, ⟨h1, h2⟩, h3⟩; exact ⟨t, h1, by omega, h3⟩
  · rintro ⟨t, h1, h2, h3⟩; exact ⟨t, ⟨h1, by omega⟩, h3⟩

end CsrIndex

theorem checkAt_spec (idx : CsrIndex) (c : Nat) (inv : ByteArray) (base p h : Nat)
    (hc : checkAt idx c inv base p h = true) : idx.InBucket h c p := by
  simp only [checkAt, Bool.and_eq_true, decide_eq_true_eq] at hc
  exact ⟨_, hc.1.1.1, hc.1.1.2, Prod.ext hc.1.2 hc.2⟩

theorem verifyRun_spec (idx : CsrIndex) (c : Nat) (B inv : ByteArray) (base M : Nat)
    (hM : M = 4 ^ idx.l0) (hl : 0 < idx.l0) :
    ∀ k p h, verifyRun idx c B inv base M k p h = true → p + k + idx.l0 ≤ B.size →
      h = codeOfWord (wordAt (decodeBytes B) idx.l0 p) →
      ∀ q, p ≤ q → q ≤ p + k → idx.InBucket (codeOfWord (wordAt (decodeBytes B) idx.l0 q)) c q := by
  intro k
  induction k with
  | zero =>
    intro p h hv _ hh q h1 h2
    rw [show q = p by omega, ← hh]; exact checkAt_spec idx c inv base p h hv
  | succ k ih =>
    intro p h hv hsz hh q h1 h2
    simp only [verifyRun, Bool.and_eq_true] at hv
    by_cases hq : q = p
    · subst hq; rw [← hh]; exact checkAt_spec idx c inv base q h hv.1
    · apply ih (p + 1) _ hv.2 (by omega) _ q (by omega) (by omega)
      have hlen : p + idx.l0 < (decodeBytes B).length := by rw [length_decodeBytes]; omega
      rw [codeOfWord_wordAt_succ _ _ _ hl hlen, hh, hM, getElem_decodeBytes, charCode_toChar]

theorem codeLoop_eq (B : ByteArray) (p : Nat) : ∀ k acc i,
    codeLoop B p k acc i = (List.range' i k).foldl (fun h j => h * 4 + byteCode (B.get! (p + j))) acc := by
  intro k
  induction k with
  | zero => intro acc i; rfl
  | succ k ih => intro acc i; simp only [codeLoop, ih, List.range'_succ, List.foldl_cons]

theorem codeLoop_byteWordCode (B : ByteArray) (p l0 : Nat) :
    codeLoop B p l0 0 0 = byteWordCode B p l0 := by
  rw [codeLoop_eq, byteWordCode, List.range_eq_range']

theorem verifyChrom_spec (idx : CsrIndex) (chunks c : Nat) (B : ByteArray) (invs : Array ByteArray)
    (hl : 0 < idx.l0) (hv : verifyChrom idx chunks c B invs = true) (p : Nat) (hp : p + idx.l0 ≤ B.size) :
    idx.InBucket (codeOfWord (wordAt (decodeBytes B) idx.l0 p)) c p := by
  unfold verifyChrom at hv
  rw [if_pos (by omega)] at hv
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_map,
    List.mem_range] at hv
  obtain ⟨hch, hall⟩ := hv
  have hdm := Nat.div_add_mod (B.size - idx.l0) chunks
  have hmod := Nat.mod_lt (B.size - idx.l0) hch
  have hsz : 0 < (B.size - idx.l0) / chunks + 1 := Nat.succ_pos _
  have hlast : B.size - idx.l0 < chunks * ((B.size - idx.l0) / chunks + 1) := by
    rw [Nat.mul_add, Nat.mul_one]; omega
  have hj1 := Nat.div_mul_le_self p ((B.size - idx.l0) / chunks + 1)
  have hj2 := Nat.lt_div_mul_add (a := p) hsz
  have hj3 : p / ((B.size - idx.l0) / chunks + 1) < chunks :=
    (Nat.div_lt_iff_lt_mul hsz).mpr (by omega)
  have hpiece := hall _ ⟨_, hj3, rfl⟩
  simp only [Task.spawn, verifyPiece, Bool.or_eq_true, decide_eq_true_eq] at hpiece
  rcases hpiece with hlt | hrun
  · omega
  · exact verifyRun_spec idx c B _ _ _ rfl hl _ _ _ hrun (by omega)
      (by rw [codeLoop_byteWordCode, byteWordCode_eq _ _ _ (by omega)]) p hj1 (by omega)

/-- **Bucket form.**  Every place of the genome is an entry of the bucket of
its word's code, the code computed from the bytes. -/
theorem verifyIndex_bucket (idx : CsrIndex) (gb : ByteGenome) (chunks : Nat)
    (invs : Array (Array ByteArray)) (hv : verifyIndex idx gb chunks invs = true) (c : Nat) (hc : c < gb.size) (p : Nat)
    (hp : p + idx.l0 ≤ gb[c].bytes.size) :
    idx.InBucket (byteWordCode gb[c].bytes p idx.l0) c p := by
  simp only [verifyIndex, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hv
  have h := verifyChrom_spec idx _ c _ _ hv.1 (hv.2 c hc) p (by rw [getElem!_pos gb c hc]; exact hp)
  rw [getElem!_pos gb c hc] at h
  rw [byteWordCode_eq _ _ _ hp]
  exact h

theorem verifyIndex_complete (idx : CsrIndex) (gb : ByteGenome) (chunks : Nat)
    (invs : Array (Array ByteArray)) (hv : verifyIndex idx gb chunks invs = true) :
    LookupComplete (decodeGenome gb) idx.l0 idx.lookup := by
  intro c chromosome p hch hp
  rw [getElem?_decodeGenome] at hch
  split at hch
  · next hc =>
    cases hch
    rw [CsrIndex.mem_lookup]
    have hp' : p + idx.l0 ≤ gb[c].bytes.size := by rw [← length_decodeBytes]; exact hp
    have := verifyIndex_bucket idx gb chunks invs hv c hc p hp'
    rwa [byteWordCode_eq _ _ _ hp'] at this
  · cases hch

/-- **Completeness.**  An index that passes the checker reports every place
every word of the genome occurs. -/
theorem checkIndex_complete (idx : CsrIndex) (gb : ByteGenome) (chunks tasks : Nat)
    (hc : checkIndex idx gb chunks tasks = true) :
    LookupComplete (decodeGenome gb) idx.l0 idx.lookup :=
  verifyIndex_complete idx gb _ _ hc

theorem checkIndex_bucket (idx : CsrIndex) (gb : ByteGenome) (chunks tasks : Nat)
    (hchk : checkIndex idx gb chunks tasks = true)
    (c : Nat) (hc : c < gb.size) (p : Nat) (hp : p + idx.l0 ≤ gb[c].bytes.size) :
    idx.InBucket (byteWordCode gb[c].bytes p idx.l0) c p :=
  verifyIndex_bucket idx gb _ _ hchk c hc p hp

/-! ### Bucket-order checker -/

theorem get!_eq (B : ByteArray) (i : Nat) : B.get! i = (B.data[i]?).getD 0 := by
  rcases B with ⟨bs⟩
  simp only [ByteArray.get!]
  rw [getElem!_def]; cases bs[i]? <;> rfl

theorem get!_set! (B : ByteArray) (i j : Nat) (v : UInt8) :
    (B.set! i v).get! j = if i = j ∧ j < B.size then v else B.get! j := by
  rcases B with ⟨bs⟩
  have hs : ({ data := bs } : ByteArray).size = bs.size := rfl
  simp only [get!_eq, ByteArray.set!, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, hs]
  by_cases h : i = j
  · subst h
    by_cases hc : i < bs.size
    · simp [hc]
    · simp [hc]
  · simp [h]

theorem modify_get! (A : Array ByteArray) (i c : Nat) (f : ByteArray → ByteArray) :
    (A.modify i f)[c]! = if i = c ∧ c < A.size then f A[c]! else A[c]! := by
  rw [getElem!_def, getElem!_def, Array.getElem?_modify]
  by_cases h : i = c
  · subst h
    by_cases hc : i < A.size
    · simp [hc]
    · simp [hc]
  · simp [h]

/-- Every mark 1 is a place found in the bucket of its word. -/
def MarksGood (idx : CsrIndex) (gb : ByteGenome) (marks : Array ByteArray) : Prop :=
  ∀ c p, marks[c]!.get! p = 1 → (hc : c < gb.size) → p + idx.l0 ≤ gb[c].bytes.size →
    idx.InBucket (byteWordCode gb[c].bytes p idx.l0) c p

theorem markRun_good (idx : CsrIndex) (gb : ByteGenome) (h : Nat) : ∀ k t marks,
    MarksGood idx gb marks → idx.lo h ≤ t → t + k ≤ idx.hi h →
    MarksGood idx gb (markRun idx gb h marks k t) := by
  intro k
  induction k with
  | zero => intro t marks hg _ _; exact hg
  | succ k ih =>
    intro t marks hg hlo hhi
    simp only [markRun]
    apply ih (t + 1) _ _ (by omega) (by omega)
    split
    · next hok =>
      simp only [entryOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
      obtain ⟨⟨hc1, hp1⟩, hcode⟩ := hok
      intro c p hm hc hp
      rw [modify_get!] at hm
      split at hm
      · next hcc =>
        obtain ⟨rfl, hcs⟩ := hcc
        rw [get!_set!] at hm
        split at hm
        · next hpp =>
          obtain ⟨rfl, -⟩ := hpp
          rw [getElem!_pos gb _ hc1, codeLoop_byteWordCode] at hcode
          rw [hcode]
          exact ⟨t, hlo, by omega, rfl⟩
        · exact hg _ _ hm hc hp
      · exact hg _ _ hm hc hp
    · exact hg

theorem markBuckets_good (idx : CsrIndex) (gb : ByteGenome) : ∀ k h marks,
    MarksGood idx gb marks → MarksGood idx gb (markBuckets idx gb marks k h) := by
  intro k
  induction k with
  | zero => intro h marks hg; exact hg
  | succ k ih =>
    intro h marks hg
    apply ih (h + 1)
    by_cases hle : idx.lo h ≤ idx.hi h
    · exact markRun_good idx gb h _ _ marks hg (Nat.le_refl _) (by omega)
    · rw [Nat.sub_eq_zero_of_le (by omega)]; exact hg

def AllZero (B : ByteArray) : Prop := ∀ i, B.get! i = 0

theorem allZero_append (A B : ByteArray) (ha : AllZero A) (hb : AllZero B) : AllZero (A ++ B) := by
  intro i
  have h1 := ha i
  have h2 := hb (i - A.size)
  rw [get!_eq] at h1 h2 ⊢
  rw [ByteArray.data_append, Array.getElem?_append]
  split
  · exact h1
  · exact h2

theorem allZero_zeroDouble (n : Nat) : ∀ f B, AllZero B → AllZero (zeroDouble n f B) := by
  intro f
  induction f with
  | zero => intro B hb; exact hb
  | succ f ih =>
    intro B hb
    simp only [zeroDouble]
    split
    · exact ih _ (allZero_append B B hb hb)
    · exact hb

theorem zeroBytes_get! (n i : Nat) : (zeroBytes n).get! i = 0 := by
  have h0 : AllZero (ByteArray.mk (Array.replicate 4096 0)) := by
    intro j
    rw [get!_eq]
    simp only [Array.getElem?_replicate]
    split <;> rfl
  have h := allZero_zeroDouble n 64 _ h0
  rw [get!_eq, zeroBytes, ByteArray.data_extract, Array.getElem?_extract]
  split
  · have := h (0 + i); rw [get!_eq] at this; exact this
  · rfl

theorem initMarks_get! (gb : ByteGenome) (c p : Nat) :
    (gb.map fun bc => zeroBytes bc.bytes.size)[c]!.get! p = 0 := by
  rw [getElem!_def, Array.getElem?_map]
  cases gb[c]? with
  | none => rfl
  | some bc => exact zeroBytes_get! _ _

theorem allMarked_spec (mark : ByteArray) : ∀ k p, allMarked mark k p = true →
    ∀ q, p ≤ q → q ≤ p + k → mark.get! q = 1 := by
  intro k
  induction k with
  | zero => intro p hm q h1 h2; simp only [allMarked, beq_iff_eq] at hm; rw [show q = p by omega]; exact hm
  | succ k ih =>
    intro p hm q h1 h2
    simp only [allMarked, Bool.and_eq_true, beq_iff_eq] at hm
    by_cases hq : q = p
    · rw [hq]; exact hm.1
    · exact ih (p + 1) hm.2 q (by omega) (by omega)

theorem checkIndexM_complete (idx : CsrIndex) (gb : ByteGenome) (hchk : checkIndexM idx gb = true) :
    LookupComplete (decodeGenome gb) idx.l0 idx.lookup := by
  intro c chromosome p hch hp
  rw [getElem?_decodeGenome] at hch
  split at hch
  · next hc =>
    cases hch
    rw [CsrIndex.mem_lookup]
    have hp' : p + idx.l0 ≤ gb[c].bytes.size := by rw [← length_decodeBytes]; exact hp
    show idx.InBucket (codeOfWord (wordAt (decodeBytes gb[c].bytes) idx.l0 p)) c p
    rw [← byteWordCode_eq _ _ _ hp']
    simp only [checkIndexM, List.all_eq_true, List.mem_range] at hchk
    have hgood := markBuckets_good idx gb (4 ^ idx.l0) 0 (gb.map fun bc => zeroBytes bc.bytes.size)
      (by intro c p hm; rw [initMarks_get!] at hm; cases hm)
    have h1 := hchk c hc
    rw [getElem!_pos gb c hc, if_pos (by omega)] at h1
    exact hgood c p (allMarked_spec _ _ 0 h1 p (by omega) (by omega)) hc hp'
  · cases hch

/-- **Mapping.**  Through an index that passes the checker, the mapper gives
the specification's answer. -/
theorem mapWithCsr_eq_mapSpec (sc : AlignmentSpec.Scoring) (hv : ValidScoring sc) (T : Int)
    (gb : ByteGenome) (idx : CsrIndex) (hchk : checkIndex idx gb = true) (read : List Char) :
    mapWithCsr sc T gb idx read = mapSpec sc T (decodeGenome gb) read :=
  mapWith_eq_mapSpec _ _ idx.l0 sc hv T _ read (checkIndex_complete idx gb _ _ hchk)
    (kernelScore_eq sc read _)

end MapSpec

#print axioms MapSpec.mapWithCsr_eq_mapSpec
#print axioms MapSpec.checkIndex_complete
#print axioms MapSpec.checkIndex_bucket
#print axioms MapSpec.CsrIndex.mem_lookup
#print axioms MapSpec.decodeGenome_encodeGenome
#print axioms MapSpec.windowSeq_decodeGenome
#print axioms MapSpec.byteWordCode_eq
