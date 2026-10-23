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

/-- An original declaration or a captured local certificate in its stored body. -/
structure Candidate where
  owner : Name
  target : Expr
  localPath : Option String := none

/-- Close local `have`/`let` certificate types over their actual enclosing parameters and lets.
No source-text heuristic is used and no binder or growth hypothesis is discarded. -/
partial def localCertificates (owner : Name) (e : Expr) (path : String := "body")
    (close : Expr → Expr := id) : Array Candidate := Id.run do
  match e with
  | .lam n ty body bi =>
    return localCertificates owner body (path ++ ".lambda") fun goal =>
      close (.forallE n ty goal bi)
  | .letE n ty value body nondep =>
    let here := if (tidyNames ty).isEmpty then #[] else
      #[{ owner, target := close ty, localPath := some (path ++ "." ++ n.toString) }]
    let values := localCertificates owner value (path ++ ".value") close
    let bodies := localCertificates owner body (path ++ ".let") fun goal =>
      close (.letE n ty value goal nondep)
    return here ++ values ++ bodies
  | .app f a =>
    return localCertificates owner f (path ++ ".function") close ++
      localCertificates owner a (path ++ ".argument") close
  | .mdata _ body | .proj _ _ body => return localCertificates owner body path close
  | _ => return #[]

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
def search (env : Environment) (type : Expr) (budget : Nat) (forbidden : Std.HashSet Name := {}) : IO Json := do
  let opts := Lean.maxHeartbeats.set {} budget
  let action : MetaM Json := do
    let goal ← mkFreshExprMVar type
    let tacticCode ← `(tactic| fun_prop)
    let start ← IO.getNumHeartbeats
    let (goals, _) ← Lean.Elab.runTactic goal.mvarId! tacticCode
    let used := (← IO.getNumHeartbeats) - start
    unless goals.isEmpty do
      return Json.mkObj [field "status" "failed", ("heartbeats_raw", toJson used)]
    let proof ← instantiateMVars goal
    if proof.hasExprMVar then throwError "search left unresolved metavariables"
    let leaked := (constants proof).filter forbidden.contains
    unless leaked.isEmpty do throwError "held-out certificate leaked into proof: {leaked}"
    checkWithKernel proof
    unless ← isDefEq (← inferType proof) type do throwError "wrong search proof type"
    return Json.mkObj [field "status" "success", ("heartbeats_raw", toJson used),
      ("proof_constants", toJson ((constants proof).map Name.toString))]
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
def describe (candidate : Candidate) : MetaM (Expr × Json × Option Name) := do
  let name := candidate.owner
  let type := candidate.target
  let heads := tidyNames type
  let mirror ← if candidate.localPath.isSome then pure none else
    Cslib.Tactic.PlainMirror.getMirror? name
  let prop ← isProp type
  let env ← getEnv
  let module := env.getModuleIdxFor? name |>.map fun i => env.header.moduleNames[i.toNat]!
  let identity := name.toString ++ (candidate.localPath.map ("#" ++ ·)).getD ""
  let row := [field "name" identity, field "owner" name.toString,
    ("local_path", toJson candidate.localPath), ("module", toJson (module.map Name.toString)), ("tidy_constants", toJson (heads.map Name.toString)),
    ("private", toJson (isPrivateName name)), ("proposition", toJson prop),
    ("type", toJson (toString (← ppExpr type))),
    ("mirror", toJson (mirror.map Name.toString))]
  return (type, Json.mkObj row, mirror)

/-- Inventory all project declarations, not only attributes or hand-picked public examples. -/
unsafe def main (args : List String) : IO UInt32 := do
  let [moduleFile, outputFile, budgetText, limitText] := args
    | throw <| IO.userError "expected MODULES OUTPUT HEARTBEAT_BUDGET LIMIT(0=all)"
  let budget := budgetText.toNat?.getD 200000
  let limit := limitText.toNat?.getD 0
  initSearchPath (← findSysroot)
  let names := (← IO.FS.readFile moduleFile).splitOn "\n" |>.filter (!·.isEmpty)
  let mods := names.toArray.map String.toName
  let imports := mods.map fun n => ({ module := n, importAll := true } : Import)
  enableInitializersExecution
  let env ← importModules imports {} (loadExts := true)
  let moduleSet : Std.HashSet Name := .ofArray mods
  let (pairs, _) ← Lean.Core.CoreM.toIO Cslib.Tactic.PlainMirror.mirrorPairs
    { fileName := "mirror-registry", fileMap := default } { env }
  let reverse := reverseDependencies env moduleSet
  let mut candidates : Array Candidate := #[]
  for (name, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless moduleSet.contains env.header.moduleNames[idx.toNat]! do continue
    if !(tidyNames ci.type).isEmpty then
      candidates := candidates.push { owner := name, target := ci.type }
    if let some value := ci.value? true then
      candidates := candidates ++ localCertificates name value
  candidates := candidates.qsort fun a b =>
    Name.quickLt a.owner b.owner || (a.owner == b.owner && decide (a.localPath.getD "" < b.localPath.getD ""))
  let handle ← IO.FS.Handle.mk outputFile .write
  handle.putStrLn (Json.mkObj [("inventory_total", toJson candidates.size),
    ("module_count", toJson mods.size), ("limit", toJson limit),
    ("heartbeat_budget", toJson budget),
    ("mirror_pairs", toJson (pairs.map fun (source, plain, module) =>
      (source.toString, plain.toString, module.toString)))]).compress
  let mut count := 0
  for candidate in candidates do
    if limit != 0 && count >= limit then break
    let ((type, info, mirror), _) ← Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run' (describe candidate))
      { fileName := "certificate-inventory", fileMap := default } { env }
    let seeds := #[candidate.owner] ++ mirror.toArray
    let forbidden := closure reverse seeds
    let heldout := exclude env forbidden
    let mut fields := [("declaration", info), ("excluded_count", toJson forbidden.size)]
    let prop := (info.getObjValAs? Bool "proposition").toOption.getD false
    if !prop then
      fields := fields ++ [field "status" "non_proposition"]
    else
      let tidy ← search heldout type budget forbidden
      fields := fields ++ [("tidy_holdout", tidy)]
      try
        let (plain, _) ← Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run' (Cslib.Tactic.PlainMirror.plainType type))
          { fileName := "certificate-transform", fileMap := default } { env }
        let residual := tidyNames plain
        if !residual.isEmpty then
          fields := fields ++ [field "status" "unsupported_tidy", ("residual_tidy", toJson
            (residual.map Name.toString))]
        else
          let plainResult ← search heldout plain budget forbidden
          fields := fields ++ [field "status" "compared", ("plain_holdout", plainResult)]
          if mirror.isSome then
            fields := fields ++ [("tidy_registration", ← search env type budget),
              ("plain_registration", ← search env plain budget),
              field "registration_scope" "indexing/transport only; not holdout synthesis"]
      catch e =>
        let unsupported := (tidyNames type).filter fun n =>
          !Cslib.Tactic.PlainMirror.equivalences.any (fun entry => entry.1 == n)
        if !unsupported.isEmpty then
          fields := fields ++ [field "status" "unsupported_tidy", ("residual_tidy", toJson
            (unsupported.map Name.toString)), field "error" e.toString]
        else
          fields := fields ++ [field "status" "transform_error", field "error" e.toString]
    handle.putStrLn (Json.mkObj fields).compress
    handle.flush
    count := count + 1
  return 0

end PlainCertificateInventory

unsafe def main := PlainCertificateInventory.main
