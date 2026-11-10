/-! # `process` (Spec/Draft/MapFiles.lean) run on a list of blocks is start, one `step` per pair of blocks, end.
The loop is copied (generic in the state and the step) so that this file needs nothing of the Spec's holes; for the real
`MapState`/`mapStep` the statement is this one with `step := mapStep`, `init := mapInit settings index chrs`. -/
namespace Spec.Total.MapProcess

def process {m : Type → Type} {S : Type} [Monad m] (step : S → Option (ByteArray × ByteArray) → Option (S × ByteArray))
    (next : m (Option (ByteArray × ByteArray))) (emit : ByteArray → m Unit) :
    (fuel : Nat) → S → m (Option Unit)
  | 0, _ => pure none
  | fuel + 1, state => do
    let blocks ← next
    match step state blocks, blocks with
    | none, _ =>
      pure none
    | some (state', piece), none =>
      emit piece
      pure (some ())
    | some (state', piece), some _ =>
      emit piece
      process step next emit fuel state'

abbrev Sg := List (ByteArray × ByteArray) × List UInt8

def nextL : StateM Sg (Option (ByteArray × ByteArray)) :=
  modifyGet fun (rest, out) =>
    match rest with
    | []         => (none, ([], out))
    | b :: later => (some b, (later, out))

def emitL (piece : ByteArray) : StateM Sg Unit :=
  modify fun (rest, out) => (rest, out ++ piece.data.toList)

-- start (with the bytes `out` written so far), one step per pair of blocks, end
def fold {S : Type} (step : S → Option (ByteArray × ByteArray) → Option (S × ByteArray)) (st : S) (out : List UInt8)
    (blocks : List (ByteArray × ByteArray)) : Option (List UInt8) :=
  (blocks.foldlM (fun (sofar : S × List UInt8) (bp : ByteArray × ByteArray) =>
      (step sofar.1 (some bp)).map fun (n, piece) => (n, sofar.2 ++ piece.data.toList)) (st, out)).bind
    fun sofar => (step sofar.1 none).map fun (_, last) => sofar.2 ++ last.data.toList

theorem process_fold {S : Type} (step : S → Option (ByteArray × ByteArray) → Option (S × ByteArray)) :
    ∀ (blocks : List (ByteArray × ByteArray)) (fuel : Nat), blocks.length < fuel → ∀ (st : S) (out : List UInt8),
    let r := (process step nextL emitL fuel st).run (blocks, out)
    r.1.map (fun () => r.2.2) = fold step st out blocks
  | [], fuel, h, st, out => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at h; omega⟩
    simp only [process, nextL, emitL, fold]
    cases hs : step st none with
    | none => simp [hs, StateT.run, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, bind, StateT.bind, pure, StateT.pure]
    | some p =>
      obtain ⟨st', piece⟩ := p
      simp [hs, StateT.run, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, bind, StateT.bind, pure, StateT.pure,
        modify, modifyGetThe, MonadStateOf.modifyGet]
  | bp :: rest, fuel, h, st, out => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at h; omega⟩
    simp only [process, nextL, emitL, fold]
    cases hs : step st (some bp) with
    | none => simp [hs, StateT.run, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, bind, StateT.bind, pure, StateT.pure, List.foldlM]
    | some p =>
      obtain ⟨st', piece⟩ := p
      have ih := process_fold step rest f (by simp at h; omega) st' (out ++ piece.data.toList)
      simp only [fold] at ih
      simp [hs, StateT.run, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, bind, StateT.bind, pure, StateT.pure,
        modify, List.foldlM]
      simp only [nextL] at ih
      exact ih

#print axioms process_fold

end Spec.Total.MapProcess
