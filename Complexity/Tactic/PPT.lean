/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Tactic.PolyTime
public import Complexity.Computability.Probabilistic.PPT.Capture
public import Complexity.Computability.Probabilistic.Sampling

/-!
# Certifying functional probabilistic programs

`ppt` combines the proved closed PPT rules with deterministic `polytime` automation. Programs
use ordinary `do` notation, captured inputs and conditionals. Named and local certificates are
tried before generic composition, and tuple arguments are prepared with the shared routine-call
matcher. Every proof supplies the uniform strict fair-coin machine contract of `IsPPTOn`.

Unknown algorithms need certificates. Fair-bit sampling is the only primitive here. Sampling
uniform bitstrings of runtime length, probabilistic loops and oracle PPT need further rules.

## Main definitions

* `ppt`: prove a closed encoded PPT certificate using the `PPT` and `PolyTime` Aesop rule sets.

## References

Adapted from `Cslib/Tactic/PPT.lean` on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the common machine realization and tidy calculus.
-/

public section

namespace Cslib.Tactic.PPT

open Lean Meta Elab Tactic Probability

/-- Prepare local probabilistic routine calls through the same matcher as deterministic calls. -/
@[aesop safe -40 tactic (rule_sets := [PPT])]
private meta def pptKnownCall : TacticM Unit :=
  Cslib.Tactic.applyKnownCall ``IsPPTOn 4 ``IsPPTOn.preprocess `prepare `hprogram `hprepare

/-- Use a named certificate before unfolding its program. -/
@[aesop safe -30 tactic (rule_sets := [PPT])]
private meta def pptCertificate : TacticM Unit :=
  Cslib.Tactic.applyCertificate ``IsPPTOn

/-- Let compositional rules finish a goal before exposing individual monadic binds. -/
@[aesop safe -20 tactic (rule_sets := [PPT])]
private meta def pptFunProp : TacticM Unit :=
  withMainContext <| Term.withoutErrToSorry <| withoutRecover do
    unless (← getMainTarget).isAppOf ``IsPPTOn do
      throwError "expected an encoded-input PPT goal"
    evalTactic (← `(tactic| solve | fun_prop (config := { maxSteps := 128 })))

attribute [program_certificate]
  Turing.MultiTapeTM.ComputableTidilyInPolyTime.isPPTOn
  isPPTOn_uniform_bool

/-- Let either the sampler or continuation determine the intermediate encoding. Commit only
after both premises are proved, so an unsuitable choice cannot hide the other order. -/
@[aesop safe 10 tactic (rule_sets := [PPT])]
private meta def pptCaptured : TacticM Unit :=
  withMainContext <| focus <| Term.withoutErrToSorry <| withoutRecover do
    let target := (← Core.betaReduce (← instantiateMVars (← getMainTarget))).consumeMData
    unless target.isAppOf ``IsPPTOn do throwError "expected an encoded-input PPT goal"
    let isBind ← lambdaTelescope target.getAppArgs.back! fun _ body => do
      if body.isAppOf ``Bind.bind then return true
      if body.isAppOf ``Functor.map then return false
      throwError "expected probabilistic sequencing"
    let (rule, sampler, continuation) := if isBind then
      (``IsPPTOn.bind_with, `hfirst, `hsecond) else (``IsPPTOn.map_with, `hprogram, `hf)
    for samplerFirst in [true, false] do
      let saved ← saveState
      try
        liftMetaTactic fun goal => goal.applyConst rule
        Cslib.Tactic.solveTagged (if samplerFirst then sampler else continuation)
        Cslib.Tactic.solveTagged (if samplerFirst then continuation else sampler)
        return
      catch _ => saved.restore
    throwError "no compatible encoding for the sampler and continuation"

/-- Certify a probabilistic program using proved sampling, composition and deterministic rules. -/
macro "ppt" : tactic => `(tactic| solve | aesop (rule_sets := [PPT, PolyTime]))

end Cslib.Tactic.PPT
