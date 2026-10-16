/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Aesop
public import Mathlib.Tactic.FunProp

/-!
# Rule sets and certificates for polynomial-time programs

`polytime` searches the Aesop rule set `PolyTime`. A certificate for a named program is registered
with `@[program_certificate]`. Certificates are indexed by their efficiency predicate and by the
constant at the head of the program, looking through an output encoding. A goal's certificates
are looked up using its own program head, so similarly implemented algorithms do not unfold into
each other's rules.
Certificates are also registered with `fun_prop`, so the same annotation supports
calls inside larger functional programs.

The certificate index is adapted from the cslib `crypto` branch. Both computation predicates use
separate input and output encodings. `Tactic.PPT` combines the `PPT` and `PolyTime`
rule sets for closed probabilistic programs; machine witnesses remain behind their certificates.

## Main definitions

* `program_certificate`: register a named efficiency theorem before its implementation unfolds.

Aesop's index cannot see inside the program, which is a function, so the lookup is a single tactic
rule for each efficiency predicate rather than one `apply` rule for each certificate.

## References

Adapted from `Cslib/Tactic/PolyTime/Init.lean` on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, sharing routine-call matching between both tactics.
-/

public section

declare_aesop_rule_sets [PolyTime, PPT]

end

public meta section

open Lean Meta Elab Tactic

namespace Cslib.Tactic

/-- The constant naming a program body, and whether it was found under an output encoding. An
application of an encoding is looked through, and so is `List.replicate n true`, the simp-normal
form of a unary encoding. -/
def programHead? (body : Expr) : Option (Name × Bool) :=
  let body := body.consumeMData
  if body.isAppOf `DFunLike.coe then
    body.getAppArgs.back!.consumeMData.getAppFn.constName?.map (·, true)
  else if body.isAppOfArity ``List.replicate 3 && body.getAppArgs.back!.isConstOf ``Bool.true then
    body.getAppArgs[1]!.consumeMData.getAppFn.constName?.map (·, true)
  else
    body.getAppFn.constName?.map (·, false)

/-- The efficiency predicate and program head of an efficiency statement, and whether the program
returns its result under an encoding. `IsPPT` statements are indexed under `IsPPTOn`, which they
unfold to. A certificate stated under an encoding only applies to goals stated the same way. -/
def efficiencyKey (statement : Expr) : MetaM (Name × Name × Bool) := do
  let statement := statement.consumeMData
  let some predicate := statement.getAppFn.constName?
    | throwError "expected an efficiency statement"
  let argument := if predicate == `Turing.MultiTapeTM.ComputableTidilyInPolyTime then
    statement.getAppArgs[2]! else statement.getAppArgs.back!
  let program ← Core.betaReduce (← etaExpand argument)
  let some (head, encoded) ← lambdaTelescope program fun _ body => pure (programHead? body)
    | throwError "the program body is not an application of a constant"
  let predicate := if predicate == `Cslib.Probability.IsPPT then
    `Cslib.Probability.IsPPTOn else predicate
  return (predicate, head, encoded)

/-- Registered certificates, indexed by efficiency predicate and program head. Each certificate
carries the hypotheses to solve as soon as it is applied. -/
initialize certificateExt : SimpleScopedEnvExtension ((Name × Name × Bool) × Name × Array Name)
    (Std.HashMap (Name × Name × Bool) (Array (Name × Array Name))) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun certificates (key, entry) =>
      certificates.insert key ((certificates.getD key #[]).push entry)
    initial := {}
  }

/-- `@[program_certificate]` registers an efficiency certificate for `polytime` and `ppt`. Its
conclusion must be a `ComputableTidilyInPolyTime`, `IsPPTOn` or `IsPPT` statement whose program
body applies a constant, possibly under an output encoding.
Certificates are also registered with `fun_prop` for use in larger compositions.

`@[program_certificate h₁ … hₙ]` additionally solves the hypotheses `h₁ … hₙ` immediately after the
certificate is applied. This is needed when such a hypothesis determines an encoding that other
hypotheses mention, so that proof search does not reach those goals with the encoding unknown. -/
syntax (name := programCertificate) "program_certificate" (ppSpace ident)* : attr

initialize registerBuiltinAttribute {
  name := `programCertificate
  descr := "an efficiency certificate used by `polytime` and `ppt`, indexed by program head"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    unless stx.isOfKind ``programCertificate do throwUnsupportedSyntax
    let eager := stx[1].getArgs.map (·.getId)
    let key ← MetaM.run' <| forallTelescope (← getConstInfo declName).type fun _ conclusion =>
      efficiencyKey conclusion
    if key.1 == `Turing.MultiTapeTM.ComputableTidilyInPolyTime ||
        key.1 == `Cslib.Probability.IsPPTOn then
      Attribute.add declName `fun_prop .missing kind
    certificateExt.add (key, declName, eager) kind
}

/-- Solve the goal tagged `name`, or else one whose tag ends in `name` as for `case`, by proof
search: `PolyTime` rules for a polynomial-time goal, and both rule sets otherwise. -/
def solveTagged (name : Name) : TacticM Unit := do
  let goals ← getGoals
  let some goal ← (do
      if let some goal ← goals.findM? fun goal => return (← goal.getTag) == name then
        return some goal
      goals.findM? fun goal => return name.isSuffixOf (← goal.getTag))
    | throwError "no goal named `{name}`"
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let tag := mkIdent name
  if target.isAppOf `Turing.MultiTapeTM.ComputableTidilyInPolyTime then
    evalTactic (← `(tactic| case $tag:ident => solve | aesop (rule_sets := [PolyTime])))
  else
    evalTactic (← `(tactic| case $tag:ident => solve | aesop (rule_sets := [PPT, PolyTime])))

/-- Expose every matching named certificate as an Aesop alternative. Eager premises are solved
before exposing the remaining obligations, while different certificates keep independent
metavariable assignments until the surrounding proof search has also succeeded. -/
def applyCertificates (predicate : Name) : Aesop.RuleTac := fun input => input.goal.withContext do
  let target := (← instantiateMVars (← input.goal.getType)).consumeMData
  unless target.isAppOf predicate do throwError "expected an efficiency goal for {predicate}"
  let key ← efficiencyKey target
  let initial ← saveState
  let mut applications := #[]
  for (certificate, eager) in (certificateExt.getState (← getEnv)).getD key #[] do
    try
      let goals ← (Lean.Elab.Tactic.run input.goal <|
          Term.withoutErrToSorry <| withoutRecover do
        liftMetaTactic fun goal => goal.applyConst certificate
        eager.forM solveTagged).run'
      let goals ← goals.toArray.mapM (Aesop.mvarIdToSubgoal input.goal)
      applications := applications.push {
        goals
        postState := ← saveState
        scriptSteps? := none
        successProbability? := none }
    catch _ => pure ()
    finally initial.restore
  if applications.isEmpty then throwError "no certificate for `{key.2.1}` applies"
  return ⟨applications⟩

/-- Apply a rule with known arguments, leaving all remaining hypotheses as goals. -/
private def applyWithArguments (rule : Name) (arguments : Array (Name × Expr)) : TacticM Unit := do
  let mut proof ← mkConstWithFreshMVarLevels rule
  let mut type ← inferType proof
  while let .forallE name domain body _ := type do
    let arg ← match arguments.find? (fun argument => argument.1 == name) with
      | some (_, value) => pure value
      | none => mkFreshExprMVar domain
    unless ← isDefEq (← inferType arg) domain do throwError "argument type mismatch"
    proof := mkApp proof arg
    type := body.instantiate1 arg
    if name == arguments.back!.1 then
      replaceMainGoal (← (← getMainGoal).apply proof)
      return
  throwError "argument not found"

/-- Expose tuple components before higher-order unification matches a subroutine call. -/
private partial def prepareArgument (domain type : Expr) : MetaM Expr := do
  let type ← whnf type
  if type.isAppOf ``Prod then
    let args := type.getAppArgs
    let left ← prepareArgument domain args[0]!
    let right ← prepareArgument domain args[1]!
    withLocalDeclD `input domain fun input => do
      mkLambdaFVars #[input] (← mkAppM ``Prod.mk #[mkApp left input, mkApp right input])
  else
    mkFreshExprMVar (← mkArrow domain type)

/-- Apply a local routine certificate through a composition rule, preparing tuple arguments
with `polytime`. Predicate parameters select the program; rule parameter names select the
argument and certificate, and `argumentGoal` names the remaining preparation obligation.
Failed candidates restore all assignments before another input encoding is tried. -/
def applyKnownCall (predicate : Name) (programIndex : Nat) (rule : Name)
    (argumentName certificateName argumentGoal : Name) : TacticM Unit :=
  withMainContext <| Term.withoutErrToSorry <| withoutRecover do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    unless target.isAppOf predicate do throwError "expected an efficiency goal for {predicate}"
    let program := target.getAppArgs[programIndex]!
    if program.hasExprMVar then throwError "the called program is not determined"
    let head ← lambdaTelescope (← Core.betaReduce (← etaExpand program)) fun _ body =>
      pure body.getAppFn
    for decl in ← getLCtx do
      if decl.isImplementationDetail || !decl.type.isAppOf predicate then continue
      let certified := decl.type.getAppArgs[programIndex]!
      let called ← lambdaTelescope (← Core.betaReduce (← etaExpand certified)) fun _ body =>
        pure body.getAppFn
      unless called == head do continue
      let saved ← saveState
      try
        let argument ← prepareArgument target.getAppArgs[0]! decl.type.getAppArgs[0]!
        let composed ← withLocalDeclD `input target.getAppArgs[0]! fun input =>
          mkLambdaFVars #[input] (mkApp certified (mkApp argument input))
        unless ← isDefEq (← withReducible (reduce composed)) program do
          throwError "the certificate does not match this call"
        applyWithArguments rule #[(argumentName, argument), (certificateName, decl.toExpr)]
        if ← (← getGoals).anyM (fun goal => do isDefEq (← goal.getType) target) then
          throwError "composition made no progress"
        solveTagged argumentGoal
        return
      catch _ => saved.restore
    throwError "no applicable local routine certificate"

end Cslib.Tactic
