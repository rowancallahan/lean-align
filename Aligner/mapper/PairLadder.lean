import PairHitsKP
import PairBox

/-!
# Codec `pairUKP`: pair-level uniqueness (`pairSpecUT`), fast path + cap ladder

The proper-pair mode (Rowan, 2026-10-05):

* **Fast path.**  Each mate's genome search at its cap (`mapFastGBKP`).  Both unique
  bests `a`, `b`, a proper pair, distance cost `0` at their fragment: `(a, b)` is the
  answer (`fastU_ok`).
* **Ladder.**  Otherwise every hit within caps `0, 4, 8, …` (`hitsAtKP`), the mate
  with the cheaper lookups first (`costP`; when it has no hit, the other mate is not
  searched at that rung).  At the first rung with a proper pair `w` of score `W`, the
  hits that matter have penalty `≤ −W` (branch and bound, `pairSpecUT_bnb`): when the
  rung's caps cover that, `bestPairD` of the rung's lists is the answer; otherwise the
  lists at caps `min(P, −W)` are.  At the full caps, the lists at the caps are the answer.

    pairUKP … = pairSpecUT sc0 dc sl lo hi (−P1) (−P2) g m1 m2               (pairUKP_mz_eq)

The answer kinds (`UKind`): mapped, `pairTie` (proper pairs exist, no unique best),
none (no proper pair within the caps).
-/

namespace MapSpec.Fast

open MapSpec AlignmentSpec

/-! ## List facts -/

/-! ## The best proper pair of a list (by score) -/

@[inline] def topStep (dc : Nat → Nat) (a b : PairHit) : PairHit :=
  if pairScoreD dc a < pairScoreD dc b then b else a

def topW (dc : Nat → Nat) : List PairHit → Option PairHit
  | [] => none
  | p :: ps => some (ps.foldl (topStep dc) p)

theorem foldl_top_mem (dc : Nat → Nat) : ∀ (ps : List PairHit) (a : PairHit), ps.foldl (topStep dc) a ∈ a :: ps
  | [], _ => List.mem_cons_self
  | b :: ps, a => by
    simp only [List.foldl_cons, topStep]
    split
    · exact List.mem_cons_of_mem _ (foldl_top_mem dc ps b)
    · rcases List.mem_cons.mp (foldl_top_mem dc ps a) with h | h
      · rw [h]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

theorem topW_mem (dc : Nat → Nat) (ps : List PairHit) (w : PairHit) (h : topW dc ps = some w) : w ∈ ps := by
  cases ps with
  | nil => cases h
  | cons p ps =>
    simp only [topW, Option.some.injEq] at h
    subst h; exact foldl_top_mem dc ps p

/-! ## The ladder over any exact hit lists -/

section ladder
variable (dc : Nat → Nat) (sl lo hi P1 P2 : Nat) (g : Genome) (m1 m2 : List Char)
  (hf : Bool → Nat → List (Placement × Int))
  (hs1 : ∀ c, c ≤ P1 → ∀ x, x ∈ hf true c ↔ x ∈ hitsBoth sc0 (-(c : Int)) g m1)
  (hs2 : ∀ c, c ≤ P2 → ∀ x, x ∈ hf false c ↔ x ∈ hitsBoth sc0 (-(c : Int)) g m2)

include hs1 hs2

end ladder

/-! ## Fast path -/

/-! ## Production: packed whole genome -/

/-- Hits of a read at cap `c`: `hitsAtKP`, or the specification for reads too short for
its seed bound. -/
def hitsKPF {L Pp : Type} [LookG L Pp] [Inhabited Pp] (ix : L) (G : ByteArray) (offs : Array Nat)
    (pgs : Array PGen) (R : ByteArray) (c : Nat) : List (Placement × Int) :=
  match hitsAtKP c ix G offs pgs R with
  | some l => l
  | none => hitsBoth sc0 (-(c : Int)) (decodeGenomeB (pgs.map Mz.unpack)) (decodeBytes R)

/-- Answer kind `pairTie`: proper pairs within the caps, none of them the unique best. -/
def PairTieOk (dc : Nat → Nat) (sl lo hi : Nat) (T1 T2 : Int) (g : Genome) (m1 m2 : List Char) : Prop :=
  pairSpecUT sc0 dc sl lo hi T1 T2 g m1 m2 = none ∧
    ∃ w, w ∈ properPairs sl lo hi (hitsBoth sc0 T1 g m1) (hitsBoth sc0 T2 g m2)

theorem hitsBoth_seqs (T : Int) (g g' : Genome) (read : List Char) (h : g.map (·.seq) = g'.map (·.seq)) :
    hitsBoth sc0 T g read = hitsBoth sc0 T g' read := by
  have hl : g.length = g'.length := by simpa using congrArg List.length h
  have hc : ∀ c : Nat, (g[c]?).map (fun x : Chromosome => x.seq) = (g'[c]?).map (fun x : Chromosome => x.seq) := by
    intro c; rw [← List.getElem?_map, ← List.getElem?_map, h]
  have hws : windowSeq g = windowSeq g' := by
    funext w
    unfold windowSeq
    have := hc w.chr
    cases h1 : g[w.chr]? <;> cases h2 : g'[w.chr]? <;> simp_all
  have haw : allWindows g = allWindows g' := by
    unfold allWindows
    rw [hl]
    congr 1
    funext c
    have := hc c
    cases h1 : g[c]? <;> cases h2 : g'[c]? <;> simp_all
  unfold hitsBoth windowScore
  rw [hws, haw]

theorem decode_seqs (gbs : Array ByteArray) (g : Genome) (hg : GenomeBytes gbs g) :
    (decodeGenomeB gbs).map (·.seq) = g.map (·.seq) := by
  obtain ⟨hsz, henc⟩ := hg
  unfold decodeGenomeB
  apply List.ext_getElem
  · simp [hsz]
  · intro i h1 h2
    simp only [List.getElem_map, Array.getElem_toList]
    exact decodeBytes_of_encodes _ _ (henc i (by simpa using h1) (by simpa using h2))

section top
variable (dc : Nat → Nat) (sl lo hi P1 P2 : Nat) (caps : List Nat) (a1 : Bool) (g : Genome)
  (m1 m2 : List Char) (ix : Mz.MzIdx) (G : PGen) (offs ns : Array Nat) (R1 R2 : ByteArray)
  (hcut : cutOk G offs ns = true) (hg : GenomeBytes ((cutAll G offs ns).map Mz.unpack) g)
  (h1 : Encodes R1 m1) (h2 : Encodes R2 m2) (hchk : Mz.check2P ix G = true)

include hcut hg hchk in
theorem hitsKPF_mem (R : ByteArray) (m : List Char) (hr : Encodes R m) (c : Nat) (hc : c ≤ 16)
    (x : Placement × Int) :
    x ∈ hitsKPF ((ix, G) : PkMz) ByteArray.empty offs (cutAll G offs ns) R c ↔
      x ∈ hitsBoth sc0 (-(c : Int)) g m := by
  unfold hitsKPF
  split
  · next l hl => exact mem_hitsAtKP_mz c hc g m ix G offs ns R hcut hg hr hchk l hl x
  · rw [decodeBytes_of_encodes R m hr, hitsBoth_seqs _ _ g m (decode_seqs _ g hg)]

end top

end MapSpec.Fast

