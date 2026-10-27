import Lean
import TierOpt
import ReadTrim
import ParMap
import MzView
import MzCheckPar
import WgPacked
import LeanAlign
open Lean

def ourModule (env : Lean.Environment) (n : Lean.Name) : Option Lean.Name := do
  let idx ← env.getModuleIdxFor? n
  env.header.moduleNames[idx.toNat]?

partial def closure (env : Lean.Environment) (start : List Lean.Name) : Lean.NameSet := Id.run do
  let mut seen : Lean.NameSet := {}
  let mut stack := start
  while !stack.isEmpty do
    match stack with
    | [] => pure ()
    | n :: rest =>
      stack := rest
      if seen.contains n then continue
      seen := seen.insert n
      match env.find? n with
      | none => pure ()
      | some ci =>
        for m in ci.getUsedConstantsAsSet do
          unless seen.contains m do stack := m :: stack
        match ci with
        | .inductInfo v => stack := v.ctors ++ stack
        | .ctorInfo v => stack := v.induct :: stack
        | _ => pure ()
  return seen

def main (args : List String) : IO Unit := do
  -- args: comma-separated run-root suffixes, proof-root suffixes, module-prefix roots
  let runSfx := (args.getD 0 "").splitOn ","
  let prfSfx := (args.getD 1 "").splitOn ","
  let modRoots := (args.getD 2 "").splitOn ","
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `TierOpt}, {module := `ReadTrim}, {module := `ParMap},
    {module := `MzView}, {module := `MzCheckPar}, {module := `WgPacked}, {module := `LeanAlign}] {}
  let mut runRoots : List Lean.Name := []
  let mut prfRoots : List Lean.Name := []
  for (n, _) in env.constants.map₁.toList do
    let some mod := ourModule env n | continue
    let last := n.componentsRev.headD .anonymous |>.toString
    if runSfx.contains last then runRoots := n :: runRoots
    if prfSfx.contains last then prfRoots := n :: prfRoots
    if modRoots.any (fun p => p != "" && mod.toString.startsWith p) then runRoots := n :: runRoots
  IO.eprintln s!"run roots: {runRoots.length}, proof roots: {prfRoots.length}"
  let runSet := closure env runRoots
  let allSet := closure env (runRoots ++ prfRoots)
  for (n, _) in env.constants.map₁.toList do
    let some mod := ourModule env n | continue
    let tag := if runSet.contains n then "R" else if allSet.contains n then "P" else "-"
    IO.println s!"{mod}\t{n}\t{tag}"
