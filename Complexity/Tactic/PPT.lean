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
public import Complexity.Computability.Probabilistic.Adaptive
public import Complexity.Computability.Probabilistic.Parameter
public import Complexity.Computability.Probabilistic.Memoize

/-!
# Certifying functional probabilistic programs

`ppt` combines the proved closed PPT rules with deterministic `polytime` automation. Programs
use ordinary `do` notation, captured inputs and conditionals. Named and local certificates are
reused, and tuple arguments are prepared with the shared routine-call
matcher. Every proof supplies the uniform strict fair-coin machine contract of `IsPPTOn`.
`IsPPT` goals and local certificates expose the standard unary-parameter/word encoding
automatically.

Unknown algorithms need certificates. Fair bits, uniform words with efficiently computed unary
lengths, memoized closed samplers and bounded loops with constant state growth are certified here.
General loop invariants
use `IsPPTOn.iterate_spec`; oracle PPT needs further rules.

## Main definitions

* `ppt`: prove a closed encoded PPT certificate using the `PPT` and `PolyTime` Aesop rule sets.

## References

Adapted from `Cslib/Tactic/PPT.lean` on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the common machine realization and tidy calculus.
-/

public section

namespace Cslib.Tactic.PPT

open Lean Meta Elab Tactic Probability

attribute [aesop norm unfold (rule_sets := [PPT])] IsPPT

/-- Prepare local probabilistic routine calls through the same matcher as deterministic calls. -/
@[aesop safe -40 tactic (rule_sets := [PPT])]
private meta def pptKnownCall : TacticM Unit :=
  Cslib.Tactic.applyKnownCall ``IsPPTOn 4 ``IsPPTOn.preprocess `prepare `hprogram `hprepare

/-- Expose named probabilistic certificates as search alternatives. -/
@[aesop unsafe 99% tactic (rule_sets := [PPT])]
private meta def pptCertificate : Aesop.RuleTac :=
  Cslib.Tactic.applyCertificates ``IsPPTOn

/-- Let compositional rules finish a goal before exposing individual monadic binds. -/
@[aesop safe -20 tactic (rule_sets := [PPT])]
private meta def pptFunProp : TacticM Unit :=
  withMainContext <| Term.withoutErrToSorry <| withoutRecover do
    unless (← getMainTarget).isAppOf ``IsPPTOn do
      throwError "expected an encoded-input PPT goal"
    evalTactic (← `(tactic| solve | fun_prop (config := { maxSteps := 128 })))

attribute [program_certificate]
  Turing.MultiTapeTM.ComputableTidilyInPolyTime.isPPTOn
  Turing.MultiTapeTM.ComputableTidilyInPolyTime.sampleList
  isPPTOn_uniform_bool
  IsPPTOn.memoize

/-- Expose probabilistic sequencing to Aesop's joint search, retaining alternatives for the
intermediate encoding until both the sampler and continuation have been proved. -/
@[aesop unsafe 80% tactic (rule_sets := [PPT])]
private meta def pptCaptured : TacticM Unit :=
  withMainContext <| Term.withoutErrToSorry <| withoutRecover do
    let target := (← Core.betaReduce (← instantiateMVars (← getMainTarget))).consumeMData
    unless target.isAppOf ``IsPPTOn do throwError "expected an encoded-input PPT goal"
    let rule ← lambdaTelescope target.getAppArgs.back! fun _ body => do
      if body.isAppOf ``Bind.bind then return ``IsPPTOn.bind_with
      if body.isAppOf ``Functor.map then return ``IsPPTOn.map_with
      throwError "expected probabilistic sequencing"
    liftMetaTactic fun goal => goal.applyConst rule

attribute [aesop unsafe 80% apply (rule_sets := [PPT])] IsPPTOn.cond IsPPTOn.ite

attribute [aesop unsafe 80% apply (rule_sets := [PPT])]
  IsPPTOn.iterate_of_length_le IsPPTOn.iterate_of_bounded_growth

/-- Certify a probabilistic program using proved sampling, composition and deterministic rules. -/
macro "ppt" : tactic => `(tactic| solve | aesop (rule_sets := [PPT, PolyTime]))

end Cslib.Tactic.PPT
