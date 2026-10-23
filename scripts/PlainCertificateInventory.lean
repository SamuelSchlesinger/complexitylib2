/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
-- upstream: local-only (independent certificate automation validation)
import Complexity.Tactic.PlainMirror
import Mathlib.Tactic.FunProp

/-!
# Independent elaborated certificate inventory

Run through `plain_certificate_inventory.py`, which supplies the complete module list and records
source identity. Every declaration whose elaborated type mentions a tidy notion remains visible.
Holdout searches remove the candidate, its recorded mirror and their indirect dependents from all
four `fun_prop` databases. Registered-rule probes are reported separately: they check registration,
not independent synthesis. Both search arms start with fresh meta/search state and equal budgets.
-/

open Lean Meta Mathlib.Meta.FunProp

namespace PlainCertificateInventory

/-- Constants mentioned by an elaborated expression, without unfolding it. -/
def constants (e : Expr) : Array Name := e.getUsedConstants

/-- Keep all tidy notions, including exact-bound predicates without a proved equivalence. -/
def tidyNames (e : Expr) : Array Name :=
  (constants e).filter fun n =>
    (n.toString.splitOn "Tidily").length > 1 || (n.toString.splitOn "Tidy").length > 1

/-- Filter both evaluated leaves and pending lazy discrimination-tree entries. -/
def filterGeneral (bad : Std.HashSet Name) (s : GeneralTheorems) : GeneralTheorems :=
  { s with theorems := { s.theorems with tries := s.theorems.tries.map fun node =>
      { node with values := node.values.filter fun t => !bad.contains t.thmName
                  pending := node.pending.filter fun t => !bad.contains t.2.thmName } } }

/-- Remove forbidden certificates independently of the mirror implementation. -/
def exclude (env : Environment) (bad : Std.HashSet Name) : Environment := Id.run do
  let env := functionTheoremsExt.modifyState env fun s =>
    { s with theorems := s.theorems.map fun _ props => props.map fun _ ts =>
        ts.filter fun t => !bad.contains t.thmOrigin.name }
  let env := lambdaTheoremsExt.modifyState env fun s =>
    { s with theorems := s.theorems.map fun _ ts => ts.filter fun t => !bad.contains t.thmName }
  let env := transitionTheoremsExt.modifyState env (filterGeneral bad)
  return morTheoremsExt.modifyState env (filterGeneral bad)

/-- Reverse proof/body dependencies of project declarations. Imported upstream declarations cannot
refer to project certificates. Type dependencies count too, conservatively. -/
def reverseDependencies (env : Environment) (modules : Std.HashSet Name) :
    Std.HashMap Name (Array Name) := Id.run do
  let mut result : Std.HashMap Name (Array Name) := {}
  for (name, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless modules.contains env.header.moduleNames[idx.toNat]! do continue
    let deps := constants ci.type ++ ((ci.value? true).map constants).getD #[]
    for dep in deps do result := result.insert dep ((result.getD dep #[]).push name)
  return result

/-- Exclude every rule whose existing proof can recover the held-out certificate. -/
def closure (reverse : Std.HashMap Name (Array Name)) (seeds : Array Name) : Std.HashSet Name :=
  Id.run do
    let mut seen : Std.HashSet Name := {}
    let mut todo := seeds
    while !todo.isEmpty do
      let n := todo.back!
      todo := todo.pop
      if seen.contains n then continue
      seen := seen.insert n
      todo := todo ++ reverse.getD n #[]
    return seen

private def field (name : String) (value : String) : String × Json := (name, toJson value)

/-- One search with fresh state; preprocessing and proof validation are outside its heartbeat cost. -/
def search (env : Environment) (type : Expr) (budget : Nat) : IO Json := do
  let opts := Lean.maxHeartbeats.set {} budget
  let action : MetaM Json := do
    let start ← IO.getNumHeartbeats
    let ctx : Mathlib.Meta.FunProp.Context := {
      disch := fun e => do
        try
          let goal ← mkFreshExprMVar e
          if ← goal.mvarId!.assumptionCore then return some (← instantiateMVars goal)
          return none
        catch _ => return none }
    let state : Mathlib.Meta.FunProp.State := {
      morTheorems := morTheoremsExt.getState (← getEnv)
      transitionTheorems := transitionTheoremsExt.getState (← getEnv) }
    let (result, _) ← (funProp type ctx).run state
    let used := (← IO.getNumHeartbeats) - start
    if let some result := result then
      check result.proof
      unless ← isDefEq (← inferType result.proof) type do throwError "wrong search proof type"
      return Json.mkObj [field "status" "success", ("heartbeats_raw", toJson used),
        ("proof_constants", toJson ((constants result.proof).map Name.toString))]
    return Json.mkObj [field "status" "failed", ("heartbeats_raw", toJson used)]
  let start ← IO.getNumHeartbeats
  try
    let context : Lean.Core.Context := {
      fileName := "certificate-search"
      fileMap := default
      options := opts
      maxHeartbeats := budget * 1000 }
    Lean.Core.CoreM.toIO' (Lean.Meta.MetaM.run' action) context { env }
  catch e =>
    return Json.mkObj [field "status" "error", field "error" e.toString,
      ("heartbeats_raw", toJson ((← IO.getNumHeartbeats) - start))]

/-- Inspect a declaration without invoking its own proof as the benchmark. -/
def describe (name : Name) : MetaM (Expr × Json × Option Name) := do
  let ci ← getConstInfo name
  let heads := tidyNames ci.type
  let mirror ← Cslib.Tactic.PlainMirror.getMirror? name
  let prop ← isProp ci.type
  let row := [field "name" name.toString, ("tidy_constants", toJson (heads.map Name.toString)),
    ("private", toJson (isPrivateName name)), ("proposition", toJson prop),
    ("type", toJson (toString (← ppExpr ci.type))),
    ("mirror", toJson (mirror.map Name.toString))]
  return (ci.type, Json.mkObj row, mirror)

/-- Inventory all project declarations, not only attributes or hand-picked public examples. -/
def main (args : List String) : IO UInt32 := do
  let [moduleFile, outputFile, budgetText, limitText] := args
    | throw <| IO.userError "expected MODULES OUTPUT HEARTBEAT_BUDGET LIMIT(0=all)"
  let budget := budgetText.toNat?.getD 200000
  let limit := limitText.toNat?.getD 0
  initSearchPath (← findSysroot)
  let names := (← IO.FS.readFile moduleFile).splitOn "\n" |>.filter (!·.isEmpty)
  let mods := names.toArray.map String.toName
  let imports := mods.map fun n => ({ module := n, importAll := true } : Import)
  let env ← importModules imports {} (loadExts := true)
  let moduleSet : Std.HashSet Name := .ofArray mods
  let reverse := reverseDependencies env moduleSet
  let mut candidates : Array Name := #[]
  for (name, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    if moduleSet.contains env.header.moduleNames[idx.toNat]! && !(tidyNames ci.type).isEmpty then
      candidates := candidates.push name
  candidates := candidates.qsort Name.quickLt
  let handle ← IO.FS.Handle.mk outputFile .write
  handle.putStrLn (Json.mkObj [("inventory_total", toJson candidates.size),
    ("module_count", toJson mods.size), ("limit", toJson limit),
    ("heartbeat_budget", toJson budget)]).compress
  let mut count := 0
  for name in candidates do
    if limit != 0 && count >= limit then break
    let ((type, info, mirror), _) ← Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run' (describe name))
      { fileName := "certificate-inventory", fileMap := default } { env }
    let seeds := #[name] ++ mirror.toArray
    let forbidden := closure reverse seeds
    let heldout := exclude env forbidden
    let mut fields := [("declaration", info), ("excluded_count", toJson forbidden.size)]
    let prop := (info.getObjValAs? Bool "proposition").toOption.getD false
    if !prop then
      fields := fields ++ [field "status" "non_proposition"]
    else
      let tidy ← search heldout type budget
      fields := fields ++ [("tidy_holdout", tidy)]
      try
        let (plain, _) ← Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run' (Cslib.Tactic.PlainMirror.plainType type))
          { fileName := "certificate-transform", fileMap := default } { env }
        let residual := tidyNames plain
        if !residual.isEmpty then
          fields := fields ++ [field "status" "unsupported_tidy", ("residual_tidy", toJson
            (residual.map Name.toString))]
        else
          let plainResult ← search heldout plain budget
          fields := fields ++ [field "status" "compared", ("plain_holdout", plainResult)]
          if mirror.isSome then
            fields := fields ++ [("plain_registration", ← search env plain budget),
              field "registration_scope" "indexing/transport only; not holdout synthesis"]
      catch e => fields := fields ++ [field "status" "transform_error", field "error" e.toString]
    handle.putStrLn (Json.mkObj fields).compress
    handle.flush
    count := count + 1
  return 0

end PlainCertificateInventory

def main := PlainCertificateInventory.main
