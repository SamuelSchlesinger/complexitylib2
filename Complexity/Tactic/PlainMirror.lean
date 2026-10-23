/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public meta import Lean
public meta import Mathlib.Tactic.FunProp
public import Complexity.Tactic.PolyTime.Init

/-!
# Plain counterparts of computability certificates

`@[plain_mirror]` transports an elaborated theorem along the established plain/tidy equivalences,
including hypotheses under binders. It does not invent an equivalence for exact resource bounds.
The generated proof is checked by Lean, and registered function-property rules retain their search
priority. Apply the attribute after the source rule's registrations.

## Main definitions

* `Cslib.Tactic.PlainMirror.plainType`: the supported transformation of elaborated statements.
* `Cslib.Tactic.PlainMirror.getMirror?`: find the generated counterpart of a source certificate.
* `plain_mirror`: derive a named plain counterpart of an existing certificate.
-/

public meta section

open Lean Meta Elab

initialize registerTraceClass `Meta.Tactic.plain_mirror

namespace Cslib.Tactic.PlainMirror

/-- Supported triples: tidy predicate, plain predicate and proved plain-to-tidy equivalence.
An entry is usable only in an environment importing its equivalence theorem. -/
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
        Expr.const entry.2.1 levels
    | _ => none
  for entry in equivalences do
    if type.find? (·.isConstOf entry.1) |>.isSome then
      unless env.contains entry.2.2 do
        throwError "plain mirror requires equivalence {entry.2.2}"
  check result
  return result

/-- The conventional counterpart name, replacing tidy predicate and certificate components. -/
def mirrorName (name : Name) : Name :=
  (name.toString.replace "ComputableTidily" "Computable"
    |>.replace "computableTidily" "computable").toName

private initialize mirrors :
    SimplePersistentEnvExtension (Name × Name × Name) (Std.HashMap Name (Name × Name)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun state (source, target, sourceModule) =>
      state.insert source (target, sourceModule)
    addImportedFn := fun entries => entries.foldl (fun state es =>
      es.foldl (fun state (source, target, sourceModule) =>
        state.insert source (target, sourceModule)) state) {}
  }

/-- Look up the exact recorded counterpart, including mirrors from imported modules. -/
def getMirror? (source : Name) : CoreM (Option Name) := do
  return ((mirrors.getState (← getEnv)).get? source).map Prod.fst

/-- Deterministic registry entries: original name, plain counterpart and original source module.
This distinguishes retained machine sources from clients during a later namespace migration. -/
def mirrorPairs : CoreM (Array (Name × Name × Name)) := do
  return (mirrors.getState (← getEnv)).toArray.map (fun (source, target, sourceModule) =>
    (source, target, sourceModule)) |>.qsort (fun a b => Name.lt a.1 b.1)

private def globalEntries {α σ : Type} (ext : SimpleScopedEnvExtension α σ) : CoreM (Array α) := do
  let state := ext.ext.toEnvExtension.getState (← getEnv)
  let collect := fun entries => entries.filterMap fun entry => match entry with
    | .global value => some value
    | .scoped _ _ => none
  return (state.importedEntries.foldl (fun es entries => es ++ collect entries) #[]) ++
    collect state.state.newEntries.toArray

open Mathlib.Meta.FunProp in
private def registerFunProp (source target : Name) (kind : AttributeKind) : MetaM Unit := do
  let functions ← globalEntries functionTheoremsExt
  let lambdas ← globalEntries lambdaTheoremsExt
  let morphisms ← globalEntries morTheoremsExt
  let transitions ← globalEntries transitionTheoremsExt
  if functions.any (·.thmOrigin.name == target) || lambdas.any (·.thmName == target) ||
      morphisms.any (·.thmName == target) || transitions.any (·.thmName == target) then
    return
  if let some rule := functions.find? (·.thmOrigin.name == source) then
    Mathlib.Meta.FunProp.addTheorem target kind rule.priority
  else if lambdas.any (·.thmName == source) then
    Mathlib.Meta.FunProp.addTheorem target kind
  else if let some rule := morphisms.find? (·.thmName == source) then
    Mathlib.Meta.FunProp.addTheorem target kind rule.priority
  else if let some rule := transitions.find? (·.thmName == source) then
    Mathlib.Meta.FunProp.addTheorem target kind rule.priority

private def mirroredApply {α : Type} (rule : Aesop.Rule α) (target : Name) :
    MetaM (Aesop.Rule α) := do
  let .apply (.const _) transparency := rule.tac
    | throwError "unsupported Aesop builder for plain mirror {rule.name.name}"
  if rule.pattern?.isSome then
    throwError "an explicit Aesop pattern requires a separately checked plain counterpart"
  let indexingMode ← match rule.indexingMode with
    | .unindexed => pure .unindexed
    | .target _ => Aesop.IndexingMode.targetMatchingConclusion (← getConstInfo target).type
    | _ => throwError "unsupported Aesop indexing mode for plain mirror {rule.name.name}"
  let name : Aesop.RuleName := {
    name := target
    builder := rule.name.builder
    phase := rule.name.phase
    scope := rule.name.scope }
  return { rule with name, indexingMode, tac := .apply (.const target) transparency }

private def registerAesop (source target : Name) (kind : AttributeKind) : MetaM Unit := do
  let (ext, _, _, _, _) ← Aesop.Frontend.getGlobalRuleSetData `PolyTime
  let entries ← globalEntries ext
  for entry in entries do
    if entry.name.name == source then
      let mirrored ← match entry with
        | .safeRule rule => pure (.safeRule (← mirroredApply rule target))
        | .unsafeRule rule => pure (.unsafeRule (← mirroredApply rule target))
        | .normRule rule => pure (.normRule (← mirroredApply rule target))
        | _ => throwError "unsupported Aesop rule form for plain mirror {source}"
      unless entries.any (·.name == mirrored.name) do ext.add mirrored kind

private def registerRules (source target : Name) (kind : AttributeKind) : MetaM Unit := do
  registerFunProp source target kind
  for (_key, name, eager) in ← globalEntries Cslib.Tactic.certificateExt do
    if name == source then
      let key ← forallTelescope (← getConstInfo target).type fun _ conclusion =>
        Cslib.Tactic.efficiencyKey conclusion
      let existing := (Cslib.Tactic.certificateExt.getState (← getEnv)).getD key #[]
      unless existing.any (·.1 == target) do
        Cslib.Tactic.certificateExt.add (key, target, eager) kind
  registerAesop source target kind

private def existingCovers (target : Name) (type : Expr) : MetaM Unit := do
  forallTelescope type fun xs conclusion => do
    let goal ← mkFreshExprMVar conclusion
    let premises ← goal.mvarId!.apply (← mkConstWithFreshMVarLevels target)
    for premise in premises do
      unless ← premise.isAssigned do premise.assumption
    let proof ← mkLambdaFVars xs (← instantiateMVars goal)
    check proof
    unless ← isDefEq (← inferType proof) type do
      throwError "existing counterpart {target} does not cover the full statement"

/-- Derive and kernel-check a counterpart, transporting the full proposition rather than its
conclusion alone. An existing counterpart must directly cover the full statement using only
its supplied hypotheses; this preserves stronger universe-polymorphic interfaces. -/
def mirrorDeclaration (source target : Name) (kind : AttributeKind := .global) :
    MetaM Unit := do
  let info ← getConstInfo source
  unless ← isProp info.type do
    throwError "plain mirror expects a proposition-valued declaration"
  let type ← plainType info.type
  if type.find? (fun e => match e with
      | .const name _ => (name.toString.splitOn "Tidily").length > 1
      | _ => false) |>.isSome then
    throwError "{source} retains an unsupported tidy notion after transformation"
  if type == info.type then
    throwError "{source} has no supported tidy predicate"
  if let some existing := (← getEnv).find? target then
    let existingType ← inferType (← mkConstWithFreshMVarLevels existing.name)
    unless ← isDefEq existingType type do
      existingCovers existing.name type
  else
    let mut thms : SimpTheorems := {}
    for entry in equivalences do
      if info.type.find? (·.isConstOf entry.1) |>.isSome then
        thms ← thms.addConst entry.2.2
    let ctx ← Simp.mkContext {} (simpTheorems := #[thms])
    let (result, _) ← simp type ctx
    unless ← isDefEq result.expr info.type do
      throwError "cannot transport {source} across the supported equivalences"
    let value ← mkEqMPR (← result.getProof) (mkConst source (info.levelParams.map .param))
    addDecl (.thmDecl { name := target, levelParams := info.levelParams, type, value })
    addDocStringCore target s!"Plain counterpart of `{source}`, derived by proved equivalences."
  registerRules source target kind
  let env ← getEnv
  let sourceModule := match env.getModuleIdxFor? source with
    | some idx => env.header.moduleNames[idx]!
    | none => env.mainModule
  modifyEnv (mirrors.addEntry · (source, target, sourceModule))

private def mirrorModules (modules : Array Name) : MetaM Unit := do
  let env ← getEnv
  let candidates := env.constants.toList.filterMap fun (name, info) => do
    let isTheorem : Bool := match info with
      | .thmInfo _ | .axiomInfo _ => true
      | _ => false
    unless isTheorem do none
    let idx ← env.getModuleIdxFor? name
    if !modules.contains env.header.moduleNames[idx]! || isPrivateName name then none
    else if info.type.find? (fun e => equivalences.any (fun entry => e.isConstOf entry.1))
        |>.isSome then some name else none
  if candidates.isEmpty then
    throwError "plain mirror source selection contains no supported statements"
  let mut count : Nat := 0
  for source in candidates.toArray.qsort Name.lt do
    let saved ← saveState
    try
      mirrorDeclaration source (mirrorName source)
      count := count + 1
    catch ex =>
      saved.restore
      trace[Meta.Tactic.plain_mirror] "skipped {source}: {ex.toMessageData}"
  if count == 0 then throwError "plain mirror derived no selected statements"
  trace[Meta.Tactic.plain_mirror] "derived {count} of {candidates.length} statements"

end Cslib.Tactic.PlainMirror

/-- Derive a plain counterpart; an explicit name overrides conventional tidy-name replacement. -/
syntax (name := plainMirror) "plain_mirror" (ppSpace ident)? : attr

initialize registerBuiltinAttribute {
  name := `plainMirror
  descr := "transport a computability certificate to the corresponding plain predicates"
  applicationTime := .afterCompilation
  add := fun source stx kind => MetaM.run' do
    let target := if stx[1].isNone then Cslib.Tactic.PlainMirror.mirrorName source
      else stx[1][0].getId
    Cslib.Tactic.PlainMirror.mirrorDeclaration source target kind
}

/-- Emit the source-to-counterpart registry as deterministic JSON for coordinated migrations. -/
syntax (name := mirrorPairsCommand) "#mirror_pairs" : command

elab_rules : command
  | `(#mirror_pairs) => do
    let entries ← Command.liftCoreM Cslib.Tactic.PlainMirror.mirrorPairs
    let json := Json.arr (entries.map fun (source, target, sourceModule) => Json.mkObj [
      ("original", toJson source.toString), ("plain", toJson target.toString),
      ("module", toJson sourceModule.toString)])
    logInfo json.compress

/-- Derive supported counterparts from an explicit list of generic calculus source modules. -/
syntax (name := plainMirrorSources) "plain_mirror_sources" "[" ident,* "]" : command

elab_rules : command
  | `(plain_mirror_sources [$modules:ident,*]) => Command.liftTermElabM do
    Cslib.Tactic.PlainMirror.mirrorModules (modules.getElems.map (·.getId))

/-- Refresh mirror registrations after source rule annotations, preserving eager premises and
Aesop apply priorities without duplicating existing entries. -/
syntax (name := plainMirrorRegistrations) "plain_mirror_registrations" : command

elab_rules : command
  | `(plain_mirror_registrations) => Command.liftTermElabM do
    for (source, target, _) in ← Cslib.Tactic.PlainMirror.mirrorPairs do
      Cslib.Tactic.PlainMirror.registerRules source target .global
