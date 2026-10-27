import Lean
import Proofs.Aligner
open Lean Elab Command

/-! Audit of everything `Spec.alignPairs_correct` and the executed code (`Spec.alignPairs`,
`Spec.buildIndex`) depend on: constants reached through types and values, plus the code that
`@[csimp]` swaps in. Reports axioms, `unsafe`, `partial` / opaque with an implementation,
`implemented_by` and `extern` outside Lean's own library (Init / Std / Lean). -/

def coreModule (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i => let m := env.header.moduleNames[i.toNat]!
              m.getRoot == `Init || m.getRoot == `Std || m.getRoot == `Lean
  | none => false

partial def reach (env : Environment) (csimp : NameMap (List Name))
    (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then reach env csimp rest seen else
    let seen := seen.insert n
    let fromCi := match env.find? n with
      | some ci => (ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants) |>.getD #[])).toList
      | none => []
    reach env csimp (fromCi ++ (csimp.find? n |>.getD []) ++ rest) seen

elab "#audit_align" : command => do
  let env ← getEnv
  -- csimp: map each replaced function to the constants of its csimp theorem
  let mut csimp : NameMap (List Name) := {}
  for (thm, ci) in env.constants.toList do
    if Lean.Compiler.CSimp.ext.getState env |>.thmNames.contains thm then
      if let some (_, lhs, _) := ci.type.eq? then
        if let some f := lhs.getAppFn.constName? then
          csimp := csimp.insert f (thm :: ci.type.getUsedConstants.toList ++ (csimp.find? f |>.getD []))
  let roots := [`Spec.alignPairs_correct, `Spec.alignPairs_end_to_end, `Spec.alignPairs, `Spec.buildIndex]
  let all := reach env csimp roots {}
  let mut bad : Array String := #[]
  let mut coreExt : Nat := 0
  for n in all.toList do
    let some ci := env.find? n | continue
    let core := coreModule env n
    if ci.isUnsafe then bad := bad.push s!"unsafe: {n}"
    if let .axiomInfo _ := ci then
      unless [``propext, ``Classical.choice, ``Quot.sound].contains n do bad := bad.push s!"axiom: {n}"
    if let .opaqueInfo _ := ci then
      unless core do bad := bad.push s!"opaque (partial?): {n}"
    if (Lean.Compiler.implementedByAttr.getParam? env n).isSome then
      if core then coreExt := coreExt + 1 else bad := bad.push s!"implemented_by: {n}"
    if isExtern env n then
      if core then coreExt := coreExt + 1 else bad := bad.push s!"extern: {n}"
  let nonCore := all.toList.filter (fun n => !coreModule env n) |>.length
  logInfo m!"audited {all.size} constants ({nonCore} outside Init/Std/Lean); core extern/implemented_by (trusted base): {coreExt}; csimp replacements followed: {csimp.size}\nfindings: {if bad.isEmpty then "none" else "\n".intercalate bad.toList}"

#audit_align
