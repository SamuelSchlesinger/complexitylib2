/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

/-!
# Mechanical audit for formal abstracts

A formal abstract (`*Abstract.lean`) introduces self-contained definitions and headline theorem
statements whose proofs delegate to a bridge module (`*Bridge.lean`). To verify that a reader
only needs to inspect the abstract file itself:

1. Every public definition and theorem statement in the abstract namespace is traversed
   transitively (following `type` for all declarations, and `value?` for non-theorems, including
   private and equation-compiler helper definitions).
2. Any reference to an internal `Complexity.*` or `ComplexityTests.*` declaration outside the
   abstract namespace (and outside any explicitly allowlisted foundational modules) is rejected.
3. Every theorem and definition in the abstract namespace is audited with `collectAxioms` to
   ensure it depends only on `propext`, `Classical.choice`, and `Quot.sound`.

Adapted from `scripts/CheckAbstract.lean` in `edemaine/lean-canny`.
-/

namespace ComplexityTests.Abstracts

open Lean Elab Command

/-- Recover the user-facing name of a declaration, stripping any `_private.<mod>.0.` prefix
added by Lean for `private` definitions or equation-compiler matchers. -/
def userFacingName (name : Name) : Name :=
  privateToUserName name

/-- Determine whether `name` (after stripping any `_private` prefix) lies inside `ns`. -/
def inAbstractNamespace (ns name : Name) : Bool :=
  ns.isPrefixOf (userFacingName name)

/-- Audit all declarations in `abstractNamespace`: reject transitive dependencies on internal
`Complexity.*` or `ComplexityTests.*` modules in public definitions and theorem statements, and
reject non-standard axioms in proofs. -/
def checkAbstract (abstractNamespace : Name) (allowedModules : Array Name := #[]) :
    CommandElabM Unit := do
  let env := (← getEnv).setExporting false
  let allowedAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut pending : Array (Name × Name) := #[]
  let mut roots : Nat := 0
  let mut abstractModules : Std.HashSet Name := {}
  for (name, info) in env.constants.toList do
    if inAbstractNamespace abstractNamespace name then
      if let some idx := env.getModuleIdxFor? name then
        abstractModules := abstractModules.insert env.header.moduleNames[idx.toNat]!
      for ax in ← collectAxioms name do
        unless allowedAxioms.contains ax do
          throwError "abstract audit: `{userFacingName name}` depends on disallowed axiom `{ax}`"
      unless name.isInternalDetail do
        if info.isUnsafe || info matches .opaqueInfo _ then
          throwError
            "abstract audit: `{userFacingName name}` is `opaque`, `partial`, or `unsafe`"
        roots := roots + 1
        for c in info.type.getUsedConstants do
          pending := pending.push (name, c)
        if let .inductInfo val := info then
          for ctor in val.ctors do
            pending := pending.push (name, ctor)
        if !info.isTheorem then
          if let some value := info.value? (allowOpaque := true) then
            for c in value.getUsedConstants do
              pending := pending.push (name, c)
  if roots == 0 then
    throwError "abstract audit: no declarations found in namespace `{abstractNamespace}`"
  let mut visited : Std.HashSet Name := {}
  while !pending.isEmpty do
    let (root, name) := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    let isSameAbstractModule := match env.getModuleIdxFor? name with
      | none => true
      | some idx => abstractModules.contains env.header.moduleNames[idx.toNat]!
    if isSameAbstractModule then
      unless inAbstractNamespace abstractNamespace name do
        throwError
          "abstract audit: `{userFacingName root}` depends on declaration `{userFacingName name}` \
           outside `{abstractNamespace}`"
      if let some info := env.find? name then
        if info.isUnsafe || info matches .opaqueInfo _ then
          throwError
            "abstract audit: `{userFacingName root}` depends on `opaque`, `partial`, or `unsafe` \
             declaration `{userFacingName name}`"
        for c in info.type.getUsedConstants do
          pending := pending.push (root, c)
        if let .inductInfo val := info then
          for ctor in val.ctors do
            pending := pending.push (root, ctor)
        if !info.isTheorem then
          if let some value := info.value? (allowOpaque := true) then
            for c in value.getUsedConstants do
              pending := pending.push (root, c)
    else if let some idx := env.getModuleIdxFor? name then
      let owner := env.header.moduleNames[idx.toNat]!
      let isLocalRepo := (`Complexity).isPrefixOf owner || (`ComplexityTests).isPrefixOf owner
      if isLocalRepo && !allowedModules.contains owner then
        throwError
          "abstract audit: `{userFacingName root}` depends on implementation declaration \
           `{userFacingName name}` from `{owner}`"

/-- `#check_abstract Namespace` verifies that all public definitions and theorem statements in
`Namespace` are self-contained (referencing only `Namespace` and upstream `Mathlib`/`Cslib`
background libraries) and depend only on standard axioms.

Use `#check_abstract Namespace allowing [Mod1, Mod2]` to permit references to specified core
model modules in `Complexity.*`. -/
syntax (name := checkAbstractCmd)
  "#check_abstract " ident (" allowing " "[" ident,* "]")? : command

@[command_elab checkAbstractCmd]
def elabCheckAbstract : CommandElab
  | `(#check_abstract $ns:ident) =>
    checkAbstract ns.getId #[]
  | `(#check_abstract $ns:ident allowing [$[$mods:ident],*]) =>
    checkAbstract ns.getId (mods.map (·.getId))
  | _ => throwUnsupportedSyntax

end ComplexityTests.Abstracts
