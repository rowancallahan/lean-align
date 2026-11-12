import Proofs.MapScan
import Proofs.MapJobs
/-! # `cutSlices` (Proofs/MapFast.lean): the slices it cuts are the cuts of `cutLines (4 · jobPairs)`. -/
namespace Spec.FQ.MapStream
open Spec Spec.MapFast

-- a slice: exactly `n` newlines, the last byte a newline
def IsSlice (n : Nat) (s : List UInt8) : Prop := cutLines n s = some (s, [])

theorem cutLines_self : ∀ (n : Nat) (l pre post : List UInt8), cutLines n l = some (pre, post) →
    cutLines n pre = some (pre, [])
  | 0, l, pre, post, h => by simp [cutLines] at h; obtain ⟨rfl, rfl⟩ := h; simp [cutLines]
  | n + 1, l, pre, post, h => by
    unfold cutLines at h
    cases hs : splitNl l with
    | none => simp [hs] at h
    | some p =>
      obtain ⟨c, rest⟩ := p
      have hc := splitNl_nl_free l c rest hs
      cases hr : cutLines n rest with
      | none => simp [hs, hr] at h
      | some q =>
        obtain ⟨p1, p2⟩ := q
        simp only [hs, hr, Option.bind_some, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have ih := cutLines_self n rest p1 p2 hr
        unfold cutLines
        have hsn : splitNl (c ++ newline :: p1) = some (c, p1) := splitNl_append c p1 hc
        simp [hsn, ih]

theorem isSlice_of_cut (n : Nat) (l pre post : List UInt8) (h : cutLines n l = some (pre, post)) : IsSlice n pre :=
  cutLines_self n l pre post h

theorem size_eq_length' (b : ByteArray) : b.size = b.data.toList.length := (Array.length_toList).symm

theorem data_toList_append' (a b : ByteArray) : (a ++ b).data.toList = a.data.toList ++ b.data.toList := by
  simp [ByteArray.data_append]

def need : Nat := 4 * jobPairs

-- the scan state: the first `scan` bytes of the carry hold `lines` newlines, fewer than a slice
def ScanOk (c : Carry) : Prop :=
  c.scan ≤ c.carry.size ∧ (c.carry.data.toList.take c.scan).count newline = c.lines ∧ c.lines < need

theorem go_spec : ∀ (fuel : Nat) (carry : ByteArray) (scan lines : Nat) (out : Array ByteArray),
    carry.size < fuel → ScanOk ⟨carry, scan, lines⟩ →
    ∃ ss : List (List UInt8), (∀ s ∈ ss, IsSlice need s) ∧
      (cutSlices.go need fuel carry scan lines out).2.toList.map (·.data.toList) = out.toList.map (·.data.toList) ++ ss ∧
      carry.data.toList = ss.flatten ++ (cutSlices.go need fuel carry scan lines out).1.carry.data.toList ∧
      (cutSlices.go need fuel carry scan lines out).1.carry.data.toList.count newline < need ∧
      ScanOk (cutSlices.go need fuel carry scan lines out).1
  | 0, carry, scan, lines, out, h, _ => by omega
  | fuel + 1, carry, scan, lines, out, hf, ⟨hscan, hcount, hlines⟩ => by
    simp only [] at hscan hcount hlines
    have hlist : carry.data.toList = carry.data.toList.take scan ++ L carry scan := by simp [L]
    have hgt : 0 < need - lines := by omega
    rw [cutSlices.go]
    cases hadv : advance carry (need - lines) scan with
    | mk p k =>
    simp only []
    by_cases hcut : lines + k = need
    · rw [if_pos hcut]
      have hk : k = need - lines := by omega
      have hc := cutLines_advance carry (need - lines) scan hscan
      have hge := advance_ge carry (need - lines) scan hscan
      rw [hadv] at hc hge
      simp only [hk, if_true] at hc
      have hext : cutLines (need - lines) (L carry scan) = some ((L carry scan).take (p - scan), L carry p) := by
        simpa using hc
      -- cut the whole carry
      have happ := cutLines_append_count _ (carry.data.toList.take scan) (L carry scan) need rfl (by omega)
      rw [hcount, hext] at happ
      simp only [Option.map_some] at happ
      have hpos : (L carry scan).take (p - scan) ≠ [] := by
        obtain ⟨m, hm⟩ : ∃ m, need - lines = m + 1 := ⟨need - lines - 1, by omega⟩
        rw [hm] at hext
        exact cutLines_pos m _ _ _ hext
      have hpp : scan < p := by
        rcases Nat.lt_or_ge scan p with h | h
        · exact h
        · exfalso; apply hpos; rw [show p - scan = 0 by omega]; simp
      have hT : carry.data.toList.take scan ++ L carry scan = carry.data.toList := hlist.symm
      rw [hT] at happ
      have htake : carry.data.toList.take scan ++ (L carry scan).take (p - scan) = carry.data.toList.take p := by
        obtain ⟨d, rfl⟩ : ∃ d, p = scan + d := ⟨p - scan, by omega⟩
        rw [List.take_add]; simp [L]
      rw [htake] at happ
      have hex : (carry.extract 0 p).data.toList = carry.data.toList.take p := by
        rw [extract_list]; simp [L]
      have hex2 : (carry.extract p carry.size).data.toList = L carry p := by
        rw [extract_list]; apply List.take_of_length_le; simp [L]
      have hsl : IsSlice need (carry.data.toList.take p) := isSlice_of_cut _ _ _ _ happ
      obtain ⟨ss, hss, hout, hcar, hcnt, hok⟩ := go_spec fuel (carry.extract p carry.size) 0 0 (out.push (carry.extract 0 p))
        (by simp only [ByteArray.size_extract]; omega)
        ⟨show 0 ≤ (carry.extract p carry.size).size by omega, show (List.take 0 (carry.extract p carry.size).data.toList).count newline = 0 by simp,
          show 0 < need by unfold need jobPairs; omega⟩
      refine ⟨carry.data.toList.take p :: ss, ?_, ?_, ?_, hcnt, hok⟩
      · intro s hs
        rcases List.mem_cons.1 hs with rfl | hs
        · exact hsl
        · exact hss s hs
      · rw [hout]; simp [hex]
      · rw [hex2] at hcar
        have : carry.data.toList = carry.data.toList.take p ++ L carry p := by simp [L]
        rw [List.flatten_cons, List.append_assoc, ← hcar, ← this]
    · rw [if_neg hcut]
      have hlt : k < need - lines := by
        have := advance_le carry (need - lines) scan
        rw [hadv] at this; simp only [] at this; omega
      have hcn := advance_count carry (need - lines) scan hscan (by rw [hadv]; exact hlt)
      rw [hadv] at hcn
      simp only [] at hcn
      have hcnt : carry.data.toList.count newline = lines + k := by
        rw [hlist, List.count_append, hcount]; simp [L] at hcn ⊢; omega
      refine ⟨[], by simp, by simp, by simp, ?_, ?_⟩
      · simp only []; omega
      · refine ⟨?_, ?_, ?_⟩
        · simp only []; omega
        · simp only []
          rw [List.take_of_length_le (by rw [← size_eq_length']; omega)]
          exact hcnt
        · simp only []; omega

theorem cutSlices_spec (c : Carry) (chunk : ByteArray) (hc : ScanOk c) :
    ∃ ss : List (List UInt8), (∀ s ∈ ss, IsSlice need s) ∧
      (cutSlices c chunk).2.toList.map (·.data.toList) = ss ∧
      c.carry.data.toList ++ chunk.data.toList = ss.flatten ++ (cutSlices c chunk).1.carry.data.toList ∧
      (cutSlices c chunk).1.carry.data.toList.count newline < need ∧ ScanOk (cutSlices c chunk).1 := by
  obtain ⟨carry, scan, lines⟩ := c
  obtain ⟨h1, h2, h3⟩ := hc
  simp only [] at h1 h2 h3
  have hsz : (carry ++ chunk).size = carry.size + chunk.size := ByteArray.size_append
  have hok : ScanOk ⟨carry ++ chunk, scan, lines⟩ := by
    refine ⟨by simp only []; omega, ?_, h3⟩
    simp only []
    rw [data_toList_append', List.take_append_of_le_length (by rw [← size_eq_length']; omega)]
    exact h2
  obtain ⟨ss, hss, hout, hcar, hcnt, hok'⟩ := go_spec (carry ++ chunk).size.succ (carry ++ chunk) scan lines #[] (by omega) hok
  refine ⟨ss, hss, ?_, ?_, hcnt, hok'⟩
  · simpa [cutSlices, need] using hout
  · simpa [cutSlices, need, data_toList_append'] using hcar

end Spec.FQ.MapStream
