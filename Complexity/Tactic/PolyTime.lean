/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
public import Complexity.Tactic.PolyTime.Init

/-!
# Synthesizing polynomial-time certificates

Adapted from the cslib `crypto` branch: named certificates are tried before their implementations
are unfolded. `fun_prop` handles composition; Aesop chooses loop rules and uses local growth
contracts. Every rule proves the tidy machine predicate, with fixed machines and polynomial
bounds across all encoded inputs. Unknown algorithms still require certificates.

## Main definitions

* `polytime`: prove a polynomial-time certificate using the `PolyTime` Aesop rule set.

## References

Adapted from `Cslib/Tactic/PolyTime.lean` on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the existing tidy calculus.
-/

public section

namespace Cslib.Tactic.PolyTime

open Turing.MultiTapeTM

-- A fixed finite input type admits a lookup machine for any fixed encodings. This does not
-- certify a uniform family whose input type grows with a runtime parameter.
attribute [aesop safe apply (rule_sets := [PolyTime])]
  ComputableTidilyInPolyTime.of_finite

-- Boolean scans hide the element encoding in their result. Resolve the list certificate before
-- searching for a joint callback certificate, including when the callback captures local values.
attribute [program_certificate hlist]
  ComputableTidilyInPolyTime.anyWithInput ComputableTidilyInPolyTime.allWithInput
  ComputableTidilyInPolyTime.mapToBitsWithInput
  ComputableTidilyInPolyTime.bitsFoldlWithInput
attribute [program_certificate] ComputableTidilyInPolyTime.bitsStrictMajorityWithInput

-- Expose inner table and loop obligations to Aesop when composition alone cannot finish them.
attribute [program_certificate hvalues] ComputableTidilyInPolyTime.pi_update'
attribute [program_certificate]
  ComputableTidilyInPolyTime.bitsReverseWithInput ComputableTidilyInPolyTime.listReverseWithInput

-- Require the growth contract before exploring encodings on alternative computation branches.
-- Each contract keeps the evidence that must agree on a bound or an encoding in one search.
attribute [program_certificate hbound hcompute]
  ComputableTidilyInPolyTime.foldlWithInput_of_bounded_growth
attribute [program_certificate hbound]
  ComputableTidilyInPolyTime.iterateWithInput_of_bounded_growth

open Lean Meta Elab Tactic in
/-- Synthesize a list interface once the list and element encodings are determined. -/
@[aesop safe tactic (rule_sets := [PolyTime])
  (index := [target ListEncoding _ _, target SizedListEncoding _ _])]
private meta def polytimeListInstance : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  if target.hasExprMVar then throwError "encoding is not yet determined"
  goal.assign (← synthInstance target)
  replaceMainGoal []

-- Computed finite tables use the ordinary application rule. Its function-valued head cannot
-- be registered as a `fun_prop` theorem, so Aesop supplies this closure step.
attribute [aesop unsafe 75% apply (rule_sets := [PolyTime])]
  ComputableTidilyInPolyTime.pi_apply'

/-- Expose local routine certificates and their argument obligations as search alternatives. -/
-- Equal priority lets argument goals run before expensive alternatives at the parent goal.
@[aesop unsafe 100% tactic (rule_sets := [PolyTime])]
private meta def polytimeKnownCall : Aesop.RuleTac :=
  Cslib.Tactic.applyKnownCall ``ComputableTidilyInPolyTime 2
    ``ComputableTidilyInPolyTime.comp `g `hf

open Lean Meta Elab Tactic in
/-- Test whether any local routine certificate applies to the current goal. -/
private meta def hasLocalCall (goal : MVarId) : MetaM Bool := do
  try
    discard <| (polytimeKnownCall { (default : Aesop.RuleTacInput) with goal }).run' {}
    pure true
  catch _ => pure false

open Lean Meta Elab Tactic in
/-- Commit to decomposition only when no local certificate supplies an alternative. The matcher
restores the caller's state and leaves argument preparation open, so this tests applicability
without choosing an intermediate encoding. -/
private meta def withoutLocalCall (tactic : TacticM Unit) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  unless (← goal.getType).consumeMData.isAppOf ``ComputableTidilyInPolyTime do
    throwError "expected a polynomial-time goal"
  if ← hasLocalCall goal then throwError "a local certificate is an alternative to decomposition"
  tactic

open Lean Meta Elab Tactic in
/-- Retain decomposition as an alternative when a local certificate competes with it. -/
private meta def withLocalCall (tactic : TacticM Unit) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  unless (← goal.getType).consumeMData.isAppOf ``ComputableTidilyInPolyTime do
    throwError "expected a polynomial-time goal"
  unless ← hasLocalCall goal do throwError "no competing local certificate"
  tactic

/-- Expose named deterministic certificates as search alternatives. -/
@[aesop unsafe 99% tactic (rule_sets := [PolyTime])]
private meta def polytimeCertificate : Aesop.RuleTac :=
  Cslib.Tactic.applyCertificates ``ComputableTidilyInPolyTime

open Lean Meta Elab Tactic in
/-- Decompose constructors before generic composition can guess intermediate encodings. -/
private meta def polytimeConstruct (guard : TacticM Unit → TacticM Unit) : TacticM Unit :=
  withMainContext do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    unless target.isAppOf ``ComputableTidilyInPolyTime do
      throwError "expected a polynomial-time goal"
    let rawBits := target.getAppArgs[4]!.isConstOf ``encBits
    let program ← Core.betaReduce (← etaExpand target.getAppArgs[2]!)
    let rule ← lambdaTelescope program fun _ body => do
      if body.isAppOf ``HAppend.hAppend || body.isAppOf ``List.append then
        return if rawBits then ``ComputableTidilyInPolyTime.bitsAppend
          else ``ComputableTidilyInPolyTime.listAppend'
      if body.isAppOf ``List.cons then
        return if rawBits then ``ComputableTidilyInPolyTime.bitsCons
          else ``ComputableTidilyInPolyTime.cons'
      if body.isAppOf ``Prod.mk then return ``ComputableTidilyInPolyTime.prod
      throwError "expected a constructor"
    guard <| liftMetaTactic fun goal => goal.applyConst rule

open Lean Meta Elab Tactic in
/-- Let compositional certificates finish a goal before trying loop specifications. -/
private meta def polytimeFunProp : TacticM Unit :=
  withMainContext <| Term.withoutErrToSorry <| withoutRecover do
    unless (← getMainTarget).consumeMData.isAppOf ``ComputableTidilyInPolyTime do
      throwError "expected a polynomial-time goal"
    -- A failed compositional attempt must leave time for the specification rules.
    evalTactic (← `(tactic| solve | fun_prop (config := { maxSteps := 256 })))

/-- Expose a negated guard to loop rules when compositional proof search needs their help. -/
@[aesop unsafe 80% apply (rule_sets := [PolyTime])]
theorem bool_not_rule {α : Type} {input : α ↪ List Bool} {guard : α → Bool}
    (hguard : ComputableTidilyInPolyTime guard input encBool) :
    ComputableTidilyInPolyTime (fun a => !(guard a)) input encBool :=
  ComputableTidilyInPolyTime.bool_not.comp hguard

/-- Fix a raw bit list's encoding and expose the two growth cases before proof search. -/
theorem foldl_bits_rule {γ β : Type} {encIn : γ ↪ List Bool} {encB : β ↪ List Bool}
    {list : γ → List Bool} {init : γ → β} {step : β → Bool → β}
    (hlist : ComputableTidilyInPolyTime list encIn encBits)
    (hinit : ComputableTidilyInPolyTime init encIn encB)
    (hstep : ComputableTidilyInPolyTime (fun pair : β × Bool => step pair.1 pair.2)
      (encPair encB encBool) encB) {growth : ℕ}
    (hgrowth : ∀ state, (encB (step state false)).length ≤ (encB state).length + growth ∧
      (encB (step state true)).length ≤ (encB state).length + growth) :
    ComputableTidilyInPolyTime (fun x => (list x).foldl step (init x)) encIn encB :=
  ComputableTidilyInPolyTime.foldl_of_bounded_growth hlist hinit hstep
    (fun state bit => by cases bit; exacts [(hgrowth state).1, (hgrowth state).2])

/-- Fix a framed list's encoding before proof search infers the element encoding. -/
theorem foldl_list_rule {γ α β : Type} {encIn : γ ↪ List Bool}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {list : γ → List α} {init : γ → β} {step : β → α → β}
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA))
    (hinit : ComputableTidilyInPolyTime init encIn encB)
    (hstep : ComputableTidilyInPolyTime (fun pair : β × α => step pair.1 pair.2)
      (encPair encB encA) encB) {growth : ℕ}
    (hgrowth : ∀ state value, (encB (step state value)).length ≤ (encB state).length + growth) :
    ComputableTidilyInPolyTime (fun x => (list x).foldl step (init x)) encIn encB :=
  ComputableTidilyInPolyTime.foldl_of_bounded_growth hlist hinit hstep hgrowth

open Lean Meta Elab Tactic in
/-- Resolve the traversed list's encoding before certifying the step. Try a nonincreasing state
bound first, committing to it only after its growth obligation has been proved. -/
private meta def polytimeFold (guard : TacticM Unit → TacticM Unit) : TacticM Unit :=
  withMainContext <| Term.withoutErrToSorry <| withoutRecover do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    unless target.isAppOf ``ComputableTidilyInPolyTime do
      throwError "expected a polynomial-time goal"
    let program ← Core.betaReduce (← etaExpand target.getAppArgs[2]!)
    let isFold ← lambdaTelescope program fun _ body => pure (body.isAppOf ``List.foldl)
    unless isFold do throwError "expected a list fold"
    guard do
      for rule in [``foldl_bits_rule, ``foldl_list_rule] do
        let saved ← saveState
        try
          liftMetaTactic fun goal => goal.applyConst rule
          evalTactic (← `(tactic| case hlist => solve |
            aesop (config := { terminal := true, assumptionTransparency := .reducible })
              (rule_sets := [PolyTime])))
          let afterList ← saveState
          try
            evalTactic (← `(tactic| case growth => exact 0))
            Cslib.Tactic.solveTagged `hgrowth
          catch _ =>
            afterList.restore
          return
        catch _ => saved.restore
      throwError "no supported list encoding"

open Lean Meta Elab Tactic in
/-- Apply the bounded-growth iteration rule once the goal is seen to be an iteration. -/
private meta def polytimeIterate (guard : TacticM Unit → TacticM Unit) : TacticM Unit :=
  withMainContext do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    unless target.isAppOf ``ComputableTidilyInPolyTime do
      throwError "expected a polynomial-time goal"
    let program ← Core.betaReduce (← etaExpand target.getAppArgs[2]!)
    let isIter ← lambdaTelescope program fun _ body => pure (body.isAppOf ``Nat.iterate)
    unless isIter do throwError "expected an iteration"
    guard <| liftMetaTactic fun goal =>
      goal.applyConst ``ComputableTidilyInPolyTime.iterate_of_bounded_growth

attribute [aesop safe apply (rule_sets := [PolyTime])] Nat.le_refl

attribute [aesop norm simp (rule_sets := [PolyTime])] forall_and

-- Aesop can use local identity certificates for changes of representation.
attribute [aesop unsafe 80% apply (rule_sets := [PolyTime])]
  ComputableTidilyInPolyTime.fstWithEncoding
  ComputableTidilyInPolyTime.sndWithEncoding

-- Keep inexpensive structural successes and failures when no local certificate competes.
-- Aesop postpones safe rules that assign encoding metavariables. Complementary guards avoid
-- duplicating those alternatives while retaining decomposition if a local certificate fails.
@[aesop safe -25 tactic (rule_sets := [PolyTime])]
private meta def polytimeConstructFast : Lean.Elab.Tactic.TacticM Unit :=
  polytimeConstruct withoutLocalCall

@[aesop safe -20 tactic (rule_sets := [PolyTime])]
private meta def polytimeFunPropFast : Lean.Elab.Tactic.TacticM Unit :=
  withoutLocalCall polytimeFunProp

@[aesop safe 50 tactic (rule_sets := [PolyTime])]
private meta def polytimeFoldFast : Lean.Elab.Tactic.TacticM Unit :=
  polytimeFold withoutLocalCall

@[aesop safe tactic (rule_sets := [PolyTime])]
private meta def polytimeIterateFast : Lean.Elab.Tactic.TacticM Unit :=
  polytimeIterate withoutLocalCall

@[aesop unsafe 95% tactic (rule_sets := [PolyTime])]
private meta def polytimeConstructAlternative : Lean.Elab.Tactic.TacticM Unit :=
  polytimeConstruct withLocalCall

@[aesop unsafe 90% tactic (rule_sets := [PolyTime])]
private meta def polytimeFunPropAlternative : Lean.Elab.Tactic.TacticM Unit :=
  withLocalCall polytimeFunProp

@[aesop unsafe 85% tactic (rule_sets := [PolyTime])]
private meta def polytimeFoldAlternative : Lean.Elab.Tactic.TacticM Unit :=
  polytimeFold withLocalCall

@[aesop unsafe 85% tactic (rule_sets := [PolyTime])]
private meta def polytimeIterateAlternative : Lean.Elab.Tactic.TacticM Unit :=
  polytimeIterate withLocalCall

/-- Prove a polynomial-time certificate from known routines and controlled loop rules. -/
-- Unfold only reducible aliases when comparing assumptions. Ordinary program definitions may
-- contain large fixed enumerations; their named certificates should be tried before unfolding.
macro "polytime" : tactic => `(tactic| solve |
  aesop (config := { terminal := true, assumptionTransparency := .reducible })
    (rule_sets := [PolyTime]))

end Cslib.Tactic.PolyTime
