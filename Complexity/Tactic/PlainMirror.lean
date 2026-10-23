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

private initialize mirrors : SimplePersistentEnvExtension (Name × Name) (Std.HashMap Name Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun state (source, target) => state.insert source target
    addImportedFn := fun entries => entries.foldl (fun state es =>
      es.foldl (fun state (source, target) => state.insert source target) state) {}
  }

/-- Look up the exact recorded counterpart, including mirrors from imported modules. -/
def getMirror? (source : Name) : CoreM (Option Name) := do
  return (mirrors.getState (← getEnv)).get? source

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
  if let some rule := functions.find? (·.thmOrigin.name == source) then
    Mathlib.Meta.FunProp.addTheorem target kind rule.priority
  else if lambdas.any (·.thmName == source) then
    Mathlib.Meta.FunProp.addTheorem target kind
  else if let some rule := morphisms.find? (·.thmName == source) then
    Mathlib.Meta.FunProp.addTheorem target kind rule.priority
  else if let some rule := transitions.find? (·.thmName == source) then
    Mathlib.Meta.FunProp.addTheorem target kind rule.priority

/-- Derive and kernel-check a counterpart, transporting the full proposition rather than its
conclusion alone. An existing counterpart must have a definitionally equal statement. -/
def mirrorDeclaration (source target : Name) (kind : AttributeKind := .global) :
    MetaM Unit := do
  let info ← getConstInfo source
  unless ← isProp info.type do
    throwError "plain mirror expects a proposition-valued declaration"
  let type ← plainType info.type
  if type == info.type then
    throwError "{source} has no supported tidy predicate"
  if let some existing := (← getEnv).find? target then
    unless ← isDefEq existing.type type do
      throwError "existing counterpart {target} has a different statement"
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
  registerFunProp source target kind
  modifyEnv (mirrors.addEntry · (source, target))

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
