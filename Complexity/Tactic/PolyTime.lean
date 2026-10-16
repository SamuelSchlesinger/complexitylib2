/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
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

/-- Supply the called algorithm's local certificate before inferring its tuple arguments. -/
@[aesop safe -40 tactic (rule_sets := [PolyTime])]
private meta def polytimeKnownCall : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.applyKnownCall ``ComputableTidilyInPolyTime 2
    ``ComputableTidilyInPolyTime.comp `g `hf `hg

/-- Reuse a named routine's certificate before unfolding it. -/
@[aesop safe -30 tactic (rule_sets := [PolyTime])]
private meta def polytimeCertificate : Lean.Elab.Tactic.TacticM Unit :=
  Cslib.Tactic.applyCertificate ``ComputableTidilyInPolyTime

open Lean Meta Elab Tactic in
/-- Decompose constructors before generic composition can guess intermediate encodings. -/
@[aesop safe -25 tactic (rule_sets := [PolyTime])]
private meta def polytimeConstruct : TacticM Unit := withMainContext do
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
  liftMetaTactic fun goal => goal.applyConst rule

open Lean Meta Elab Tactic in
/-- Let compositional certificates finish a goal before trying loop specifications. -/
@[aesop safe -20 tactic (rule_sets := [PolyTime])]
private meta def polytimeFunProp : TacticM Unit :=
  withMainContext <| Term.withoutErrToSorry <| withoutRecover do
    unless (← getMainTarget).isAppOf ``ComputableTidilyInPolyTime do
      throwError "expected a polynomial-time goal"
    -- Aesop normalizes `headD` and `getD` to optional lookup; restore the certified operation.
    evalTactic (← `(tactic| try simp only [← List.getD_eq_getElem?_getD]))
    -- A failed compositional attempt must leave time for the specification rules.
    evalTactic (← `(tactic| solve | fun_prop (config := { maxSteps := 128 })))

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
@[aesop safe 50 tactic (rule_sets := [PolyTime])]
private meta def polytimeFold : TacticM Unit :=
  withMainContext <| Term.withoutErrToSorry <| withoutRecover do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    unless target.isAppOf ``ComputableTidilyInPolyTime do
      throwError "expected a polynomial-time goal"
    let program ← Core.betaReduce (← etaExpand target.getAppArgs[2]!)
    let isFold ← lambdaTelescope program fun _ body => pure (body.isAppOf ``List.foldl)
    unless isFold do throwError "expected a list fold"
    for rule in [``foldl_bits_rule, ``foldl_list_rule] do
      for zeroGrowth in [true, false] do
        let saved ← saveState
        try
          if zeroGrowth then
            let rule := mkIdent rule
            evalTactic (← `(tactic| apply $rule:ident (growth := 0)))
          else liftMetaTactic fun goal => goal.applyConst rule
          evalTactic (← `(tactic| case hlist => solve | aesop (rule_sets := [PolyTime])))
          if zeroGrowth then Cslib.Tactic.solveTagged `hgrowth
          return
        catch _ => saved.restore
    throwError "no supported list encoding"

attribute [aesop safe apply (rule_sets := [PolyTime])] Nat.le_refl

attribute [aesop norm simp (rule_sets := [PolyTime])] forall_and

attribute [aesop safe apply (index := [unindexed]) (rule_sets := [PolyTime])]
  ComputableTidilyInPolyTime.iterate_of_bounded_growth

/-- Prove a polynomial-time certificate from known routines and controlled loop rules. -/
macro "polytime" : tactic => `(tactic| solve | aesop (rule_sets := [PolyTime]))

end Cslib.Tactic.PolyTime
