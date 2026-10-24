/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Complexity.Tactic.PolyTime.Init

/-!
# Synthesizing polynomial-time certificates

Adapted from the cslib `crypto` branch: named certificates are tried before their implementations
are unfolded. `fun_prop` handles composition; Aesop chooses loop rules and uses local growth
contracts. Plain and internal tidy goals use separate rules, with fixed machines and polynomial
bounds across all encoded inputs. Plain search applies plain statements directly; it does not
lower a goal or restate its hypotheses tidily. Unknown algorithms still require certificates.

## Main definitions

* `polytime`: prove a polynomial-time certificate using the `PolyTime` Aesop rule set.

## References

Adapted from Cslib/Tactic/PolyTime.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the existing tidy calculus.
-/

public section

namespace Cslib.Tactic.PolyTime

open Turing.MultiTapeTM

-- These plain rules keep the public search in its own predicate. Their machine proofs may use
-- tidy witnesses, but the search never installs a transition between the two goal families.
private theorem plainBitsAppend {α : Type} {encIn : α ↪ List Bool} {f g : α → List Bool}
    (hf : ComputableInPolyTime f encIn encBits) (hg : ComputableInPolyTime g encIn encBits) :
    ComputableInPolyTime (fun a => f a ++ g a) encIn encBits :=
  .of_tidy (ComputableTidilyInPolyTime.bitsAppend hf.tidy hg.tidy)

private theorem plainBitsCons {α : Type} {encIn : α ↪ List Bool}
    {f : α → Bool} {g : α → List Bool}
    (hf : ComputableInPolyTime f encIn encBool) (hg : ComputableInPolyTime g encIn encBits) :
    ComputableInPolyTime (fun a => f a :: g a) encIn encBits :=
  .of_tidy (ComputableTidilyInPolyTime.bitsCons hf.tidy hg.tidy)

private theorem plainListAppend {α β : Type} {encIn : α ↪ List Bool} {enc : β ↪ List Bool}
    {f g : α → List β} (hf : ComputableInPolyTime f encIn (encList enc))
    (hg : ComputableInPolyTime g encIn (encList enc)) :
    ComputableInPolyTime (fun a => f a ++ g a) encIn (encList enc) :=
  .of_tidy (ComputableTidilyInPolyTime.listAppend' hf.tidy hg.tidy)

private theorem plainListCons {α β : Type} {encIn : α ↪ List Bool} {enc : β ↪ List Bool}
    {f : α → β} {g : α → List β} (hf : ComputableInPolyTime f encIn enc)
    (hg : ComputableInPolyTime g encIn (encList enc)) :
    ComputableInPolyTime (fun a => f a :: g a) encIn (encList enc) :=
  .of_tidy (ComputableTidilyInPolyTime.cons' hf.tidy hg.tidy)

@[aesop safe apply (rule_sets := [PolyTime])]
private theorem plainBoolNot {α : Type} {encIn : α ↪ List Bool} {f : α → Bool}
    (hf : ComputableInPolyTime f encIn encBool) :
    ComputableInPolyTime (fun a => !(f a)) encIn encBool :=
  ComputableInPolyTime.bool_not.comp hf

@[aesop unsafe 75% apply (rule_sets := [PolyTime])]
private theorem plainPiApply {α Index Value : Type} [Fintype Index]
    {input : α ↪ List Bool} {enc : Value ↪ List Bool} {indexEncoding : Index ↪ List Bool}
    {values : α → Index → Value} {index : α → Index}
    (hvalues : ComputableInPolyTime values input (encPi enc))
    (hindex : ComputableInPolyTime index input indexEncoding) :
    ComputableInPolyTime (fun a => values a (index a)) input enc :=
  .of_tidy (ComputableTidilyInPolyTime.pi_apply' hvalues.tidy hindex.tidy)

@[aesop unsafe 80% apply (rule_sets := [PolyTime])]
private theorem plainFstWithEncoding {α β γ : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {encC : γ ↪ List Bool} {output : α ↪ List Bool} {f : γ → α × β}
    (hf : ComputableInPolyTime f encC (encPair encA encB))
    (h : ComputableInPolyTime (fun a => a) encA output) :
    ComputableInPolyTime (fun p => (f p).1) encC output := h.comp hf.fst'

@[aesop unsafe 80% apply (rule_sets := [PolyTime])]
private theorem plainSndWithEncoding {α β γ : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {encC : γ ↪ List Bool} {output : β ↪ List Bool} {f : γ → α × β}
    (hf : ComputableInPolyTime f encC (encPair encA encB))
    (h : ComputableInPolyTime (fun a => a) encB output) :
    ComputableInPolyTime (fun p => (f p).2) encC output := h.comp hf.snd'

attribute [aesop safe apply (rule_sets := [PolyTime])] ComputableInPolyTime.of_finite

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

open Lean Meta in
/-- Select the certificate family before searching, keeping plain goals in the plain calculus. -/
private meta def polytimePredicate (target : Expr) : MetaM Name := do
  let target := (← instantiateMVars target).consumeMData
  if target.isAppOf ``ComputableInPolyTime then return ``ComputableInPolyTime
  if target.isAppOf ``ComputableTidilyInPolyTime then return ``ComputableTidilyInPolyTime
  throwError "expected a polynomial-time goal"

/-- Expose local routine certificates and their argument obligations as search alternatives. -/
-- Equal priority lets argument goals run before expensive alternatives at the parent goal.
@[aesop unsafe 100% tactic (rule_sets := [PolyTime])]
private meta def polytimeKnownCall : Aesop.RuleTac := fun input => do
  let predicate ← input.goal.withContext do polytimePredicate (← input.goal.getType)
  Cslib.Tactic.applyKnownCall predicate 2 (predicate ++ `comp) `g `hf input

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
  discard <| polytimePredicate (← goal.getType)
  if ← hasLocalCall goal then throwError "a local certificate is an alternative to decomposition"
  tactic

open Lean Meta Elab Tactic in
/-- Retain decomposition as an alternative when a local certificate competes with it. -/
private meta def withLocalCall (tactic : TacticM Unit) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  discard <| polytimePredicate (← goal.getType)
  unless ← hasLocalCall goal do throwError "no competing local certificate"
  tactic

/-- Expose named deterministic certificates as search alternatives. -/
@[aesop unsafe 99% tactic (rule_sets := [PolyTime])]
private meta def polytimeCertificate : Aesop.RuleTac := fun input => do
  let predicate ← input.goal.withContext do polytimePredicate (← input.goal.getType)
  Cslib.Tactic.applyCertificates predicate input

open Lean Meta Elab Tactic in
/-- Decompose constructors before generic composition can guess intermediate encodings. -/
private meta def polytimeConstruct (guard : TacticM Unit → TacticM Unit) : TacticM Unit :=
  withMainContext do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    let predicate ← polytimePredicate target
    let plain := predicate == ``ComputableInPolyTime
    let rawBits := target.getAppArgs[4]!.isConstOf ``encBits
    let program ← Core.betaReduce (← etaExpand target.getAppArgs[2]!)
    let rule ← lambdaTelescope program fun _ body => do
      if body.isAppOf ``HAppend.hAppend || body.isAppOf ``List.append then
        return if plain then (if rawBits then ``plainBitsAppend else ``plainListAppend)
          else if rawBits then ``ComputableTidilyInPolyTime.bitsAppend
          else ``ComputableTidilyInPolyTime.listAppend'
      if body.isAppOf ``List.cons then
        return if plain then (if rawBits then ``plainBitsCons else ``plainListCons)
          else if rawBits then ``ComputableTidilyInPolyTime.bitsCons
          else ``ComputableTidilyInPolyTime.cons'
      if body.isAppOf ``Prod.mk then return predicate ++ `prod
      throwError "expected a constructor"
    guard <| liftMetaTactic fun goal => goal.applyConst rule

open Lean Meta Elab Tactic in
/-- Restate known local certificates in the goal's family. This introduces proof facts only;
it never changes the goal or searches the other calculus. -/
@[aesop safe -30 tactic (rule_sets := [PolyTime])]
private meta def polytimeKnownFacts : TacticM Unit := withMainContext do
  let mut goal ← getMainGoal
  let predicate ← polytimePredicate (← goal.getType)
  let (source, conversion) := if predicate == ``ComputableInPolyTime then
      (``ComputableTidilyInPolyTime, ``ComputableInPolyTime.of_tidy)
    else (``ComputableInPolyTime, ``ComputableInPolyTime.tidy)
  let mut added := false
  for h in ← getLCtx do
    unless h.isImplementationDetail do
      let type := (← instantiateMVars h.type).consumeMData
      if type.isAppOf source && !type.hasExprMVar then
        let proof ← mkAppM conversion #[h.toExpr]
        let type ← inferType proof
        let found ← (← getLCtx).anyM fun other => isDefEq other.type type
        unless found do
          let (_, next) ← goal.note (← mkFreshUserName `knownCertificate) proof
          goal := next
          added := true
  unless added do throwError "no new known certificate"
  replaceMainGoal [goal]

open Lean Meta Mathlib.Meta.FunProp in
/-- Retain ordinary transitions while excluding those that require raw construction predicates.
Both evaluated entries and lazy entries must be removed from this per-search tree. -/
private meta def plainTransitions (thms : GeneralTheorems) : MetaM GeneralTheorems := do
  let mut names : Std.HashSet Name := {}
  for node in thms.theorems.tries do
    for rule in node.values do names := names.insert rule.thmName
    for (_, rule) in node.pending do names := names.insert rule.thmName
  let mut blocked : Std.HashSet Name := {}
  for name in names do
    let raw ← forallTelescope (← getConstInfo name).type fun xs _ => xs.anyM fun x => do
      let type ← inferType x
      return (type.find? fun e => match e with
        | .const n _ => n.toString.startsWith "Turing.MultiTapeTM.ComputableTidily" ||
          n.toString.startsWith "Turing.MultiTapeTM.ComputesTidily"
        | _ => false).isSome
    if raw then blocked := blocked.insert name
  return { thms with theorems := { thms.theorems with
    tries := thms.theorems.tries.map fun node =>
      { node with
        values := node.values.filter fun rule => !blocked.contains rule.thmName
        pending := node.pending.filter fun entry => !blocked.contains entry.2.thmName } } }

open Lean Meta Elab Tactic Mathlib.Meta.FunProp in
/-- Use the standard `fun_prop` frontend's context and discharger with a local transition tree.
The normal transition depth remains available for ordinary plain-to-plain implications. -/
private meta def polytimePlainFunProp : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  let disch : Expr → MetaM (Option Expr) := fun e => do
    tacticToDischarge (← `(tactic| first | with_reducible assumption | infer_param)) e
  let ctx : Mathlib.Meta.FunProp.Context := { config := { maxSteps := 256 }, disch }
  let env ← getEnv
  let state : Mathlib.Meta.FunProp.State := {
    morTheorems := morTheoremsExt.getState env
    transitionTheorems := ← plainTransitions (transitionTheoremsExt.getState env) }
  let (result, state) ← (funProp target ctx).run state
  let some result := result | throwError "no compositional plain certificate: {state.msgLog}"
  goal.assign result.proof
  replaceMainGoal []

open Lean Meta Elab Tactic in
/-- An explicit raw construction goal may use a plain certificate and its existing PT normal
form. The nested search stays in the plain calculus; this rule never applies to a plain goal. -/
@[aesop unsafe 70% tactic (rule_sets := [PolyTime])]
private meta def polytimeRawFromPlain : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``ComputableTidilyInPolyTime do
    throwError "expected an internal raw polynomial-time goal"
  -- Do not launch a second search for every unresolved construction atom. A real plain
  -- certificate for this program head must be indexed before entering the plain backend.
  let key ← Cslib.Tactic.efficiencyKey target
  let plainKey := (``ComputableInPolyTime, key.2.1, key.2.2)
  let named := (Cslib.Tactic.certificateExt.getState (← getEnv)).getD plainKey #[]
  let functions ← Mathlib.Meta.FunProp.getTheoremsForFunction key.2.1 ``ComputableInPolyTime
  unless !named.isEmpty || !functions.isEmpty do
    throwError "no indexed plain certificate for this internal raw goal"
  let rawNamed := (Cslib.Tactic.certificateExt.getState (← getEnv)).getD key #[]
  let rawFunctions ← Mathlib.Meta.FunProp.getTheoremsForFunction key.2.1
    ``ComputableTidilyInPolyTime
  unless rawNamed.isEmpty && rawFunctions.isEmpty do
    throwError "an existing raw certificate family already handles this program"
  replaceMainGoal (← goal.applyConst ``ComputableInPolyTime.tidy)
  evalTactic (← `(tactic| solve |
    aesop (config := { terminal := true, assumptionTransparency := .reducible })
      (rule_sets := [PolyTime])))

open Lean Meta Elab Tactic in
/-- Let compositional certificates finish a goal before trying loop specifications. -/
private meta def polytimeFunProp : TacticM Unit :=
  withMainContext <| Term.withoutErrToSorry <| withoutRecover do
    let predicate ← polytimePredicate (← getMainTarget)
    -- Plain search uses plain lemmas, never a transition to a raw construction predicate.
    -- A failed compositional attempt must leave time for the specification rules.
    if predicate == ``ComputableInPolyTime then
      polytimePlainFunProp
    else
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

/-- Fix a raw bit list's encoding and expose the two growth cases before proof search. -/
private theorem plain_foldl_bits_rule {γ β : Type} {encIn : γ ↪ List Bool} {encB : β ↪ List Bool}
    {list : γ → List Bool} {init : γ → β} {step : β → Bool → β}
    (hlist : ComputableInPolyTime list encIn encBits)
    (hinit : ComputableInPolyTime init encIn encB)
    (hstep : ComputableInPolyTime (fun pair : β × Bool => step pair.1 pair.2)
      (encPair encB encBool) encB) {growth : ℕ}
    (hgrowth : ∀ state, (encB (step state false)).length ≤ (encB state).length + growth ∧
      (encB (step state true)).length ≤ (encB state).length + growth) :
    ComputableInPolyTime (fun x => (list x).foldl step (init x)) encIn encB :=
  .of_tidy (ComputableTidilyInPolyTime.foldl_of_bounded_growth hlist.tidy hinit.tidy hstep.tidy
    (fun state bit => by cases bit; exacts [(hgrowth state).1, (hgrowth state).2]))

/-- Fix a framed list's encoding before proof search infers the element encoding. -/
private theorem plain_foldl_list_rule {γ α β : Type} {encIn : γ ↪ List Bool}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {list : γ → List α} {init : γ → β} {step : β → α → β}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (hinit : ComputableInPolyTime init encIn encB)
    (hstep : ComputableInPolyTime (fun pair : β × α => step pair.1 pair.2)
      (encPair encB encA) encB) {growth : ℕ}
    (hgrowth : ∀ state value, (encB (step state value)).length ≤ (encB state).length + growth) :
    ComputableInPolyTime (fun x => (list x).foldl step (init x)) encIn encB :=
  .of_tidy (ComputableTidilyInPolyTime.foldl_of_bounded_growth
    hlist.tidy hinit.tidy hstep.tidy hgrowth)

open Lean Meta Elab Tactic in
/-- Resolve the traversed list's encoding before certifying the step. Try a nonincreasing state
bound first, committing to it only after its growth obligation has been proved. -/
private meta def polytimeFold (guard : TacticM Unit → TacticM Unit) : TacticM Unit :=
  withMainContext <| Term.withoutErrToSorry <| withoutRecover do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    let predicate ← polytimePredicate target
    let program ← Core.betaReduce (← etaExpand target.getAppArgs[2]!)
    let isFold ← lambdaTelescope program fun _ body => pure (body.isAppOf ``List.foldl)
    unless isFold do throwError "expected a list fold"
    guard do
      let rules := if predicate == ``ComputableInPolyTime then
        [``plain_foldl_bits_rule, ``plain_foldl_list_rule]
        else [``foldl_bits_rule, ``foldl_list_rule]
      for rule in rules do
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

/-- The plain iteration rule retains the same constant additive growth contract. -/
private theorem plainIterate {α β : Type} {encIn : α ↪ List Bool} {encState : β ↪ List Bool}
    {count : α → ℕ} {init : α → β} {step : β → β}
    (hcount : ComputableInPolyTime count encIn encUnary)
    (hinit : ComputableInPolyTime init encIn encState)
    (hstep : ComputableInPolyTime step encState encState)
    {growth : ℕ} (hgrowth : ∀ state, (encState (step state)).length ≤
      (encState state).length + growth) :
    ComputableInPolyTime (fun x => step^[count x] (init x)) encIn encState :=
  .of_tidy (ComputableTidilyInPolyTime.iterate_of_bounded_growth
    hcount.tidy hinit.tidy hstep.tidy hgrowth)

open Lean Meta Elab Tactic in
/-- Apply the bounded-growth iteration rule once the goal is seen to be an iteration. -/
private meta def polytimeIterate (guard : TacticM Unit → TacticM Unit) : TacticM Unit :=
  withMainContext do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    let predicate ← polytimePredicate target
    let program ← Core.betaReduce (← etaExpand target.getAppArgs[2]!)
    let isIter ← lambdaTelescope program fun _ body => pure (body.isAppOf ``Nat.iterate)
    unless isIter do throwError "expected an iteration"
    guard <| liftMetaTactic fun goal =>
      goal.applyConst (if predicate == ``ComputableInPolyTime then ``plainIterate
        else ``ComputableTidilyInPolyTime.iterate_of_bounded_growth)

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
