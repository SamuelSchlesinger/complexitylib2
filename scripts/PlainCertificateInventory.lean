/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
-- upstream: local-only (independent certificate automation validation)
import Lean
import Aesop
import Mathlib.Tactic.FunProp

/-!
# Independent elaborated certificate inventory

Run through `plain_certificate_inventory.py`, which supplies the complete module list and records
source identity. Every declaration whose elaborated type mentions a tidy notion remains visible.
Holdout searches remove the candidate, all compatible ordinary counterparts and their indirect dependents from all
four `fun_prop` databases. Registered-rule probes are reported separately: they check registration,
not independent synthesis. Both search arms start with fresh meta/search state and equal budgets.
-/

open Lean Meta Mathlib.Meta.FunProp

namespace PlainCertificateInventory

def equivalences : Array (Name × Name × Name) := #[
  (`Turing.MultiTapeTM.ComputableTidilyInPolyTime, `Turing.MultiTapeTM.ComputableInPolyTime,
    `Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime),
  (`Turing.MultiTapeTM.ComputableTidilyInPolySpace, `Turing.MultiTapeTM.ComputableInPolySpace,
    `Turing.MultiTapeTM.computableInPolySpace_iff_computableTidilyInPolySpace),
  (`Turing.MultiTapeTM.ComputableTidilyInSpace, `Turing.MultiTapeTM.ComputableInSpace,
    `Turing.MultiTapeTM.computableInSpace_iff_computableTidilyInSpace),
  (`Turing.MultiTapeTM.ComputableTidilyInO, `Turing.MultiTapeTM.ComputableInO,
    `Turing.MultiTapeTM.computableInO_iff_computableTidilyInO),
  (`Cslib.Complexity.ComputableTidilyInFPTTime, `Cslib.Complexity.ComputableInFPTTime,
    `Cslib.Complexity.computableInFPTTime_iff_computableTidilyInFPTTime)]

/-- Replace supported predicate occurrences, preserving all arguments and binders. Unsupported
notions are left intact so an inventory can report them rather than weaken their bounds. -/
def plainType (type : Expr) : MetaM Expr := do
  let env ← getEnv
  let result := type.replace fun e => match e with
    | .const name levels =>
      (equivalences.find? (fun entry => entry.1 == name)).map fun entry =>
        -- A monomorphic source can have a polymorphic plain counterpart. In particular,
        -- tidy polynomial space fixes both types to Type, while plain space is polymorphic.
        let targetArity := (env.find? entry.2.1).map (·.levelParams.length) |>.getD levels.length
        let targetLevels := if levels.isEmpty then List.replicate targetArity .zero else levels
        Expr.const entry.2.1 targetLevels
    | _ => none
  for entry in equivalences do
    if type.find? (·.isConstOf entry.1) |>.isSome then
      unless env.contains entry.2.2 do
        throwError "inventory requires proved equivalence {entry.2.2}"
  check result
  return result



/-- Constants mentioned by an elaborated expression, without unfolding it. -/
def constants (e : Expr) : Array Name := e.getUsedConstants

/-- Keep all tidy notions, including exact-bound predicates without a proved equivalence. -/
def tidyNames (e : Expr) : Array Name :=
  (constants e).filter fun n =>
    (n.toString.splitOn "Tidily").length > 1 || (n.toString.splitOn "Tidy").length > 1

/-- Reducible aliases that reach a tidy notion, including transitively hidden predicate names. -/
def aliasNames (env : Environment) (extraRoots : Array Name := #[]) : Std.HashSet Name := Id.run do
  let mut reverse : Std.HashMap Name (List Name) := {}
  let mut todo : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if !(tidyNames (.const name [])).isEmpty || extraRoots.contains name then
      todo := todo.push name
    if getReducibilityStatusCore env name == .reducible then
      if let some value := ci.value? then
        for dep in constants value do
          reverse := reverse.insert dep ((reverse.getD dep []).cons name)
  let mut seen : Std.HashSet Name := {}
  let mut aliases : Std.HashSet Name := {}
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if seen.contains name then continue
    seen := seen.insert name
    for aliasName in reverse.getD name [] do
      if (tidyNames (.const aliasName [])).isEmpty && !extraRoots.contains aliasName then
        aliases := aliases.insert aliasName
      todo := todo.push aliasName
  return aliases

/-- Unfold only relevant reducible aliases, preserving the base predicates and resource bounds. -/
def expandAliases (env : Environment) (aliases : Std.HashSet Name) (e : Expr) : Expr := Id.run do
  let mut e := e
  for _ in [:aliases.size + 1] do
    let expanded := e.replace fun term => match term with
      | .const name levels =>
        if aliases.contains name then
          (env.find? name).bind fun ci =>
            ci.value?.map fun value => value.instantiateLevelParams ci.levelParams levels
        else none
      | _ => none
    if expanded == e then break
    e := expanded
  return e

/-- A coarse index of ordinary plain proposition declarations by reduced result head.
Proof references are evidence, never a generated-name convention or registration authority. -/
abbrev CounterpartIndex := Std.HashMap Name (Array Name)

partial def resultHead (type : Expr) : MetaM Name :=
  forallTelescope type fun _ body => do
    let body ← withReducible (whnf body)
    if body.isForall then resultHead body else
      return body.getAppFn.constName?.getD .anonymous

def counterpartIndex (env : Environment) (modules : Std.HashSet Name)
    (plainPredicates : Array Name := equivalences.map (·.2.1)) : MetaM CounterpartIndex := do
  let mut result := {}
  let aliases := aliasNames env plainPredicates
  for (name, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless modules.contains env.header.moduleNames[idx.toNat]! do continue
    unless (tidyNames ci.type).isEmpty do continue
    let normalized := expandAliases env aliases ci.type
    unless plainPredicates.any (fun name => normalized.find? (·.isConstOf name) |>.isSome) do continue
    unless ← isProp ci.type do continue
    let type := normalized.instantiateLevelParams ci.levelParams
      (List.replicate ci.levelParams.length .zero)
    let head ← resultHead type
    result := result.insert head ((result.getD head #[]).push name)
  return result

/-- Match the complete statement, specializing universes. A nonidentical stronger target needs
a direct original proof reference before kernel-checked application with local assumptions;
this prevents a generic closure rule being mistaken for the twin of a particular primitive. -/
def counterpartFits (name : Name) (type : Expr) (original : Option Name := none) : MetaM Bool := do
  let saved ← saveState
  try
    let proof ← mkConstWithFreshMVarLevels name
    if ← isDefEq (← inferType proof) type then
      checkWithKernel (← instantiateMVars proof)
      saved.restore
      return true
    saved.restore
    let env ← getEnv
    let provenance := original.any fun source =>
      ((env.find? name).bind (·.value? true)).any fun value =>
        (constants value).contains source
    unless provenance do return false
    let success ← forallTelescopeReducing type fun xs body => do
      let goal ← mkFreshExprMVar body
      let goals ← goal.mvarId!.applyConst name
      for goal in goals do goal.assumption
      let proof ← instantiateMVars goal
      if proof.hasExprMVar then return false
      let proof ← mkLambdaFVars xs proof
      checkWithKernel proof
      return ← isDefEq (← inferType proof) type
    saved.restore
    return success
  catch _ =>
    saved.restore
    return false

/-- Preserve every compatible counterpart, including duplicates and stronger existing targets. -/
def findCounterparts (index : CounterpartIndex) (type : Expr)
    (original : Option Name := none) : MetaM (Array Name) := do
  let head ← resultHead type
  let mut compatible :=  #[]
  for name in index.getD head #[] do
    if ← counterpartFits name type original then compatible := compatible.push name
  return compatible.qsort Name.lt

/-- Filter both evaluated leaves and pending lazy discrimination-tree entries. -/
def filterGeneral (bad : Std.HashSet Name) (s : GeneralTheorems) : GeneralTheorems :=
  { s with theorems := { s.theorems with tries := s.theorems.tries.map fun node =>
      { node with values := node.values.filter fun t => !bad.contains t.thmName
                  pending := node.pending.filter fun t => !bad.contains t.2.thmName } } }

/-- Remove forbidden certificates independently of library registration code. -/
def exclude (env : Environment) (bad : Std.HashSet Name) : Environment := Id.run do
  let env := functionTheoremsExt.modifyState env fun s =>
    { s with theorems := s.theorems.map fun _ props => props.map fun _ ts =>
        ts.filter fun t => !bad.contains t.thmOrigin.name }
  let env := lambdaTheoremsExt.modifyState env fun s =>
    { s with theorems := s.theorems.map fun _ ts => ts.filter fun t => !bad.contains t.thmName }
  let env := transitionTheoremsExt.modifyState env (filterGeneral bad)
  return morTheoremsExt.modifyState env (filterGeneral bad)

/-- Kernel-check direct canonical application to the narrowed statement. Only explicit coverage
provenance may use this check without complete statement identity. -/
def canonicalSubsumes (name : Name) (type : Expr) : MetaM Bool := do
  let saved ← saveState
  try
    let success ← forallTelescopeReducing type fun xs body => do
      let goal ← mkFreshExprMVar body
      let goals ← goal.mvarId!.applyConst name
      for goal in goals do goal.assumption
      let proof ← instantiateMVars goal
      if proof.hasExprMVar then return false
      let proof ← mkLambdaFVars xs proof
      checkWithKernel proof
      return ← isDefEq (← inferType proof) type
    saved.restore
    return success
  catch _ =>
    saved.restore
    return false

/-- The direct proof head, without guessing among arbitrary proof leaves. -/
partial def directProofHead : Expr → Option Name
  | .lam _ _ body _ => directProofHead body
  | .letE _ _ value body _ => directProofHead (body.instantiate1 value)
  | .mdata _ body => directProofHead body
  | body => body.getAppFn.constName?

/-- Explicitly requested checked examples provide evidence for the few broader manual canonical
rules. Each example must match the complete narrowed statement, name its canonical as the direct
proof head, and pass a second kernel subsumption check. No source/canonical name map is stored. -/
def coverageCounterparts (coverage : Array Name) (type : Expr) :
    MetaM (Array (Name × Name)) := do
  let mut found := #[]
  for exampleName in coverage do
    unless ← counterpartFits exampleName type do continue
    let some proof := (← getConstInfo exampleName).value? true
      | throwError "coverage example lacks a proof body: {exampleName}"
    let some canonical := directProofHead proof
      | throwError "coverage example lacks a direct canonical proof head: {exampleName}"
    unless (tidyNames (← getConstInfo canonical).type).isEmpty do
      throwError "coverage canonical still has a tidy type: {canonical}"
    unless ← canonicalSubsumes canonical type do
      throwError "coverage canonical does not kernel-subsume the narrowed statement: {canonical}"
    found := found.push (canonical, exampleName)
  return found

/-- Imported global registrations only: local and scoped construction rules are not public. -/
def globalEntries {α σ : Type} (ext : SimpleScopedEnvExtension α σ) : CoreM (Array α) := do
  let state := ext.ext.toEnvExtension.getState (← getEnv)
  let globals := fun entries => entries.filterMap fun entry => match entry with
    | .global value => some value
    | .scoped _ _ => none
  return (state.importedEntries.foldl (fun es entries => es ++ globals entries) #[]) ++
    globals state.state.newEntries.toArray.reverse

/-- Report public tidy automation as an unmet boundary, independently of search outcomes. -/
def registrationBoundary : CoreM Json := do
  let env ← getEnv
  let mut rules : Std.HashSet Name := {}
  for rule in ← globalEntries functionTheoremsExt do rules := rules.insert rule.thmOrigin.name
  for rule in ← globalEntries lambdaTheoremsExt do rules := rules.insert rule.thmName
  for rule in ← globalEntries transitionTheoremsExt do rules := rules.insert rule.thmName
  for rule in ← globalEntries morTheoremsExt do rules := rules.insert rule.thmName
  let tidyRule := fun name => (env.find? name).any fun ci => !(tidyNames ci.type).isEmpty
  let funprop := rules.toArray.filter tidyRule |>.qsort Name.lt
  let properties := (← globalEntries funPropDeclsExt).map (·.funPropName)
    |>.filter fun name => !(tidyNames (.const name [])).isEmpty
  let mut aesop : Array (Name × Name) := #[]
  for (setName, _) in (← Aesop.getDeclaredRuleSets).toArray do
    let (ext, _, _, _, _) ← Aesop.Frontend.getGlobalRuleSetData setName
    for entry in ← globalEntries ext do
      if tidyRule entry.name.name then aesop := aesop.push (setName, entry.name.name)
  return Json.mkObj [
    ("status", toJson (if funprop.isEmpty && properties.isEmpty && aesop.isEmpty then
      "met" else "boundary-not-met")),
    ("global_tidy_fun_prop_rules", toJson (funprop.map Name.toString)),
    ("global_tidy_fun_prop_predicates", toJson (properties.map Name.toString)),
    ("global_tidy_aesop_rules", toJson (aesop.map fun (s, n) => (s.toString, n.toString))),
    ("scope", toJson "all imported global fun_prop databases and declared Aesop rule sets; local/scoped entries excluded")]

/-- An original declaration or a captured local certificate in its stored body. -/
structure Candidate where
  owner : Name
  target : Expr
  localPath : Option String := none

/-- Exact original identity, shared by full inventory and explicitly selected delta checks. -/
def Candidate.identity (candidate : Candidate) : String :=
  candidate.owner.toString ++ (candidate.localPath.map ("#" ++ ·)).getD ""

/-- Contextual memo state is fresh for each owner declaration. Structural equality preserves
binder names and annotations, unlike ordinary expression alpha-equivalence. -/
structure LocalWalkState where
  seen : Std.HashSet (ExprStructEq × Nat) := {}
  nextContext : Nat := 1
  visits : Nat := 0

private def freshContext : StateM LocalWalkState Nat := do
  let state ← get
  set { state with nextContext := state.nextContext + 1 }
  return state.nextContext

/-- Visit each shared node once per binder/source context, retaining captured hypotheses. -/
partial def walkLocal (normalize : Expr → Expr) (owner : Name) (e : Expr) (context : Nat)
    (path : String) (close : Expr → Expr) : StateM LocalWalkState (Array Candidate) := do
  let key := (ExprStructEq.mk e, context)
  if (← get).seen.contains key then return #[]
  modify fun state => { state with seen := state.seen.insert key, visits := state.visits + 1 }
  match e with
  | .lam n ty body bi =>
    let child ← freshContext
    walkLocal normalize owner body child (path ++ ".lambda") fun goal =>
      close (.forallE n ty goal bi)
  | .letE n ty value body nondep =>
    let here := if (tidyNames (normalize ty)).isEmpty then #[] else
      #[{ owner, target := close ty, localPath := some (path ++ "." ++ n.toString) }]
    let valueContext ← freshContext
    let values ← walkLocal normalize owner value valueContext (path ++ ".value") close
    let bodyContext ← freshContext
    let bodies ← walkLocal normalize owner body bodyContext (path ++ ".let") fun goal =>
      close (.letE n ty value goal nondep)
    return here ++ values ++ bodies
  | .app f a =>
    let fs ← walkLocal normalize owner f context (path ++ ".function") close
    let args ← walkLocal normalize owner a context (path ++ ".argument") close
    return fs ++ args
  | .mdata _ body =>
    let sourceContext ← freshContext
    walkLocal normalize owner body sourceContext path close
  | .proj _ _ body => walkLocal normalize owner body context path close
  | _ => return #[]

/-- Local certificates plus a deterministic unique-contextual-node visit count for regressions. -/
def localCertificatesWithStats (normalize : Expr → Expr) (owner : Name) (e : Expr) :
    Array Candidate × LocalWalkState :=
  if (tidyNames (normalize e)).isEmpty then (#[], {}) else
    (walkLocal normalize owner e 0 "body" id).run {}

/-- Close every unique local certificate over its actual enclosing parameters and lets. -/
def localCertificates (normalize : Expr → Expr) (owner : Name) (e : Expr) : Array Candidate :=
  (localCertificatesWithStats normalize owner e).1

/-- Reverse proof/body dependencies of project declarations. Imported upstream declarations cannot
refer to project certificates. Type dependencies count too, conservatively. -/
def reverseDependencies (env : Environment) (modules : Std.HashSet Name) :
    Std.HashMap Name (List Name) := Id.run do
  let mut result : Std.HashMap Name (List Name) := {}
  for (name, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless modules.contains env.header.moduleNames[idx.toNat]! do continue
    let deps := constants ci.type ++ ((ci.value? true).map constants).getD #[]
    for dep in deps do result := result.insert dep (name :: result.getD dep [])
  return result

/-- Exclude every rule whose existing proof can recover the held-out certificate. -/
def closure (reverse : Std.HashMap Name (List Name)) (seeds : Array Name) : Std.HashSet Name :=
  Id.run do
    let mut seen : Std.HashSet Name := {}
    let mut todo := seeds
    while !todo.isEmpty do
      let n := todo.back!
      todo := todo.pop
      if seen.contains n then continue
      seen := seen.insert n
      todo := todo ++ (reverse.getD n []).toArray
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
def describe (aliases : Std.HashSet Name) (index : CounterpartIndex)
    (coverage : Array Name) (candidate : Candidate) : MetaM (Expr × Json × Array Name) := do
  let name := candidate.owner
  let type := candidate.target
  let heads := tidyNames (expandAliases (← getEnv) aliases type)
  let plain? ← try pure (some (← plainType (expandAliases (← getEnv) aliases type)))
    catch _ => pure none
  let (ordinary, covered, lookupError) : Array Name × Array (Name × Name) × Option String ←
    if candidate.localPath.isSome || plain?.isNone then pure (#[], #[], none) else do
      try
        let plain := plain?.get!
        let ordinary ← findCounterparts index plain (some name)
        let covered ← coverageCounterparts coverage plain
        pure (ordinary, covered, none)
      catch error => pure (#[], #[], some (← error.toMessageData.toString))
  let counterparts := (Std.HashSet.ofArray (ordinary ++ covered.map (·.1))).toArray.qsort Name.lt
  let prop ← isProp type
  let env ← getEnv
  let module := env.getModuleIdxFor? name |>.map fun i => env.header.moduleNames[i.toNat]!
  let identity := candidate.identity
  let row := [field "name" identity, field "owner" name.toString,
    ("local_path", toJson candidate.localPath), ("module", toJson (module.map Name.toString)), ("tidy_constants", toJson (heads.map Name.toString)),
    ("private", toJson (isPrivateName name)), ("proposition", toJson prop),
    ("type", toJson (toString (← ppExpr type))),
    ("counterparts", toJson (counterparts.map Name.toString)),
    ("counterpart_lookup_error", toJson lookupError),
    ("counterpart_ambiguity", toJson (decide (counterparts.size > 1))),
    ("coverage_derived_manual_stronger", toJson (covered.map fun (canonical, exampleName) =>
      (canonical.toString, exampleName.toString))),
    ("counterpart_evidence", Json.arr (counterparts.map fun target => Json.mkObj [
      ("name", toJson target.toString),
      ("matching", toJson (if covered.any (·.1 == target) then
        "coverage-derived/manual stronger; checked example and kernel subsumption; no search" else
        "whole-statement kernel matching or provenance-gated direct subsumption; no search")),
      ("direct_original_proof_reference", toJson (((env.find? target).bind (·.value? true)).any
        fun value => (constants value).contains name)),
      ("source_module", toJson (env.getModuleIdxFor? target |>.map fun idx =>
        env.header.moduleNames[idx.toNat]!.toString))]))]
  return (type, Json.mkObj row, counterparts)

/-- Inventory all project declarations, not only attributes or hand-picked public examples. -/
unsafe def main (args : List String) : IO UInt32 := do
  let (moduleFile, outputFile, budgetText, limitText, selectionFile, coverageFile) ← match args with
    | [a, b, c, d] => pure (a, b, c, d, none, none)
    | [a, b, c, d, e] => pure (a, b, c, d, some e, none)
    | [a, b, c, d, e, f] => pure (a, b, c, d, if e.isEmpty then none else some e, some f)
    | _ => throw <| IO.userError "expected MODULES OUTPUT HEARTBEAT_BUDGET LIMIT [SELECTION_JSON [COVERAGE_DECLARATIONS_JSON]]"
  let selection ← match selectionFile with
    | none => pure none
    | some file => do
      let parsed : Except String (Array String) :=
        (Json.parse (← IO.FS.readFile file)).bind fromJson?
      match parsed with
      | .error message => throw <| IO.userError message
      | .ok names =>
        if names.isEmpty then throw <| IO.userError "empty explicit selection"
        if (Std.HashSet.ofArray names).size != names.size then
          throw <| IO.userError "duplicate explicit selection names"
        pure (some names)
  let coverage : Array Name ← match coverageFile with
    | none => pure #[]
    | some file =>
      match (Json.parse (← IO.FS.readFile file)).bind (fromJson? (α := Array String)) with
      | .ok names =>
        if (Std.HashSet.ofArray names).size != names.size then
          throw <| IO.userError "duplicate coverage declaration names"
        pure (names.map String.toName)
      | .error message => throw <| IO.userError message
  let budget := budgetText.toNat?.getD 200000
  let limit := limitText.toNat?.getD 0
  initSearchPath (← findSysroot)
  let names := (← IO.FS.readFile moduleFile).splitOn "\n" |>.filter (!·.isEmpty)
  let mods := names.toArray.map String.toName
  let imports := mods.map fun n => ({ module := n, importAll := true } : Import)
  enableInitializersExecution
  let env ← importModules imports {} (loadExts := true)
  IO.eprintln s!"inventory: imported {mods.size} modules with private declarations"
  let moduleSet : Std.HashSet Name := .ofArray mods
  for name in coverage do
    let some ci := env.find? name | throw <| IO.userError s!"missing coverage example: {name}"
    unless ci.value? true |>.isSome do throw <| IO.userError s!"coverage proof unavailable: {name}"
    let some idx := env.getModuleIdxFor? name | throw <| IO.userError s!"coverage module unknown: {name}"
    unless moduleSet.contains env.header.moduleNames[idx.toNat]! do
      throw <| IO.userError s!"coverage example not in source inventory: {name}"
  let (boundary, _) ← Lean.Core.CoreM.toIO registrationBoundary
    { fileName := "public-registration-boundary", fileMap := default } { env }
  let aliases := aliasNames env
  IO.eprintln s!"inventory: indexed {aliases.size} reducible tidy aliases"
  let normalize := expandAliases env aliases
  let (index, _) ← Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run' (counterpartIndex env moduleSet))
    { fileName := "ordinary-counterparts", fileMap := default } { env }
  let reverse := reverseDependencies env moduleSet
  IO.eprintln s!"inventory: indexed {reverse.size} reverse dependency targets"
  let mut candidates : Array Candidate := #[]
  for (name, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless moduleSet.contains env.header.moduleNames[idx.toNat]! do continue
    if !(tidyNames (normalize ci.type)).isEmpty then
      candidates := candidates.push { owner := name, target := ci.type }
    if let some value := ci.value? true then
      candidates := candidates ++ localCertificates normalize name value
  candidates := candidates.qsort fun a b =>
    Name.quickLt a.owner b.owner || (a.owner == b.owner && decide (a.localPath.getD "" < b.localPath.getD ""))
  let inventoryTotal := candidates.size
  if let some names := selection then
    let known : Std.HashSet String := .ofArray (candidates.map Candidate.identity)
    let missing := names.filter fun name => !known.contains name
    unless missing.isEmpty do throw <| IO.userError s!"selected identities not found: {missing}"
    let chosen : Std.HashSet String := .ofArray names
    candidates := candidates.filter fun candidate => chosen.contains candidate.identity
  IO.eprintln s!"inventory: discovered {inventoryTotal} statements; selecting {candidates.size}"
  let handle ← IO.FS.Handle.mk outputFile .write
  handle.putStrLn (Json.mkObj [("inventory_total", toJson inventoryTotal),
    ("selected_total", toJson candidates.size), ("selection", toJson selection),
    ("module_count", toJson mods.size), ("limit", toJson limit),
    ("heartbeat_budget", toJson budget), ("registration_boundary", boundary),
    ("coverage_declarations", toJson (coverage.map Name.toString)),
    ("counterpart_lookup", toJson "ordinary elaborated declarations; whole-statement kernel matching or proof-provenance subsumption; all compatible targets excluded")]).compress
  let mut count := 0
  for candidate in candidates do
    if limit != 0 && count >= limit then break
    let ((type, info, counterparts), _) ← Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run' (describe aliases index coverage candidate))
      { fileName := "certificate-inventory", fileMap := default } { env }
    let seeds := #[candidate.owner] ++ counterparts
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
        let (plain, _) ← Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run' (plainType (normalize type)))
          { fileName := "certificate-transform", fileMap := default } { env }
        let residual := tidyNames plain
        if !residual.isEmpty then
          fields := fields ++ [field "status" "unsupported_tidy", ("residual_tidy", toJson
            (residual.map Name.toString))]
        else
          let plainResult ← search heldout plain budget forbidden
          fields := fields ++ [field "status" "compared", ("plain_holdout", plainResult)]
          if !counterparts.isEmpty then
            fields := fields ++ [("tidy_registration", ← search env type budget),
              ("plain_registration", ← search env plain budget),
              field "registration_scope" "indexing/transport only; not holdout synthesis"]
      catch e =>
        let unsupported := (tidyNames (normalize type)).filter fun n =>
          !equivalences.any (fun entry => entry.1 == n)
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
