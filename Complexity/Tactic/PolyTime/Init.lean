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
constant at the head of the program, looking through an output encoding. A goal is matched against
the certificates for its own program head before proof search unfolds the program, so similarly
implemented algorithms do not unfold into each other's rules.
Deterministic certificates are also registered with `fun_prop`, so the same annotation supports
calls inside larger functional programs.

The certificate index is adapted from the cslib `crypto` branch. The computation predicate has
separate input and output encodings in v2. The `PPT` rule set and probabilistic indexing conventions
are reserved compatibility hooks for the crypto interface; v2 does not yet provide a `ppt` tactic
or probabilistic machine realizations.

## Main definitions

* `program_certificate`: register a named efficiency theorem before its implementation unfolds.

Aesop's index cannot see inside the program, which is a function, so the lookup is a single tactic
rule for each efficiency predicate rather than one `apply` rule for each certificate.
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
Deterministic certificates are also registered with `fun_prop` for use in larger compositions.

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
    if key.1 == `Turing.MultiTapeTM.ComputableTidilyInPolyTime then
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

/-- Apply a certificate registered for the program in the main goal, trying each certificate for
its head in registration order. -/
def applyCertificate (predicate : Name) : TacticM Unit := withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf predicate do throwError "expected an efficiency goal for {predicate}"
  let key ← efficiencyKey target
  for (certificate, eager) in (certificateExt.getState (← getEnv)).getD key #[] do
    let saved ← saveState
    try
      liftMetaTactic fun goal => goal.applyConst certificate
      eager.forM solveTagged
      return
    catch _ =>
      saved.restore
  throwError "no certificate for `{key.2.1}` applies"

end Cslib.Tactic
