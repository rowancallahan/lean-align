import Lean
open Lean

partial def visit (env : Environment) (csimp : Std.HashMap Name (Name × Name)) (todo : Array Name)
    (seen : Std.HashSet Name) : Std.HashSet Name := Id.run do
  let mut seen := seen
  let mut todo := todo
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      let add := fun (e : Expr) (t : Array Name) => e.getUsedConstants.foldl (fun t c => if seen.contains c then t else t.push c) t
      todo := add ci.type todo
      if let some v := ci.value? (allowOpaque := true) then todo := add v todo
      match ci with
      | .inductInfo i => todo := todo ++ i.ctors
      | .ctorInfo c => todo := todo.push c.induct
      | _ => pure ()
      if let some (thm, to) := csimp.get? n then todo := (todo.push thm).push to
  return seen

unsafe def main (_args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let mods := (← IO.FS.lines "/tmp/claude-0/codemap/mods.txt").filter (· ≠ "")
  let toks := (← IO.FS.lines "/tmp/claude-0/codemap/citoks.txt").filter (· ≠ "")
  let env ← importModules (mods.map fun m => { module := m.toName }) {} (loadExts := true)
  let st := Lean.Compiler.CSimp.ext.getState env
  let mut csimp : Std.HashMap Name (Name × Name) := {}
  for (_, e) in st.map.toList do csimp := csimp.insert e.fromDeclName (e.thmName, e.toDeclName)
  let modOf := fun (n : Name) => (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!
  let isProj := fun (m : Name) => !(m.getRoot ∈ [`Init, `Std, `Lean, `Lake])
  let tokSet : Std.HashSet String := Std.HashSet.ofList toks.toList
  let mut roots : Array Name := #[]
  for (n, _) in env.constants.toList do
    match modOf n with
    | some m =>
      let ms := m.toString
      let last := n.componentsRev.headD .anonymous |>.toString
      if ms == "Main" || ms.startsWith "Spec." || ms.startsWith "Proofs." || ms.startsWith "Alignment" && (ms.startsWith "AlignmentWfa" || ms.startsWith "AlignmentCigar" || ms.startsWith "AlignmentTrace" || ms == "AlignmentCompact" || ms == "AlignmentSmallErrors" || ms == "AlignmentExchange") || ms == "WfaU3" || ms == "ProbeU32" || tokSet.contains n.toString || tokSet.contains last then
        roots := roots.push n
    | none => pure ()
  let seen := visit env csimp roots {}
  -- dead user-facing project decls, with their source ranges
  let mut out : Array String := #[]
  for (n, _) in env.constants.toList do
    if n.isInternalDetail then continue
    match modOf n with
    | some m =>
      if isProj m then
        let r := (Lean.declRangeExt.find? (level := .exported) env n).map fun r => s!"{r.range.pos.line} {r.range.endPos.line}"
        out := out.push s!"{m} {n} {r.getD "? ?"} {if seen.contains n then "LIVE" else "DEAD"}"
    | none => pure ()
  IO.FS.writeFile "/tmp/claude-0/codemap/all_decls.txt" (String.intercalate "\n" out.toList)
  IO.println s!"roots {roots.size} reached {seen.size} dead {out.size}"
