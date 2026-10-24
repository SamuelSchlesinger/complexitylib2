/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Tactic.PPT

/-!
# Source-only probabilistic automation

Named calls with literal parameters retain their callback obligations; branch rules apply to
actual conditionals. Nested plain callbacks use the same raw-transition boundary as `polytime`.
Only the normal tactic module is imported, without compiled program producers.
-/

public section

open Cslib Cslib.Probability Turing.MultiTapeTM

namespace ComplexityTests.PPTPlainSource

/-- Fixed parameters for the named client programs. -/
structure Parameters where
  useCallback : Bool

/-- A named deterministic probabilistic program with a fixed branch parameter. -/
@[expose] def run (parameters : Parameters) (callback : List Bool → List Bool)
    (word : List Bool) : ProbComp (List Bool) :=
  pure (if parameters.useCallback then callback word else word)

/-- The named certificate requires a plain callback, independently of its implementation. -/
@[program_certificate hcallback]
theorem run_ppt (parameters : Parameters) {callback : List Bool → List Bool}
    (hcallback : ComputableInPolyTime callback encBits encBits) :
    IsPPTOn encBits encBits (run parameters callback) := by
  have hcallback := hcallback.tidy
  fun_prop [run]

/-- The second named program captures one sampled fair bit. -/
@[expose] noncomputable def train (parameters : Parameters) (callback : List Bool → List Bool)
    (word : List Bool) : ProbComp (List Bool) := do
  let bit ← ProbComp.uniform Bool
  run parameters callback (bit :: word)

/-- Training has the same explicit plain callback obligation. -/
@[program_certificate hcallback]
theorem train_ppt (parameters : Parameters) {callback : List Bool → List Bool}
    (hcallback : ComputableInPolyTime callback encBits encBits) :
    IsPPTOn encBits encBits (train parameters callback) := by
  have hcallback := hcallback.tidy
  fun_prop [train, run]

example (callback : List Bool → List Bool)
    (hcallback : ComputableInPolyTime callback encBits encBits) :
    IsPPTOn encBits encBits (run ⟨true⟩ callback) := by
  fail_if_success (clear hcallback; ppt)
  ppt

example (callback : List Bool → List Bool)
    (hcallback : ComputableInPolyTime callback encBits encBits) :
    IsPPTOn encBits encBits (train ⟨true⟩ callback) := by
  fail_if_success (clear hcallback; ppt)
  ppt

example (condition : List Bool → Bool) (yes no : List Bool → ProbComp (List Bool))
    (hcondition : ComputableTidilyInPolyTime condition encBits encBool)
    (hyes : IsPPTOn encBits encBits yes) (hno : IsPPTOn encBits encBits no) :
    IsPPTOn encBits encBits (fun word => if condition word then yes word else no word) := by
  ppt

example (condition : List Bool → Prop) [∀ word, Decidable (condition word)]
    (yes no : List Bool → ProbComp (List Bool))
    (hcondition : ComputableTidilyInPolyTime (fun word => decide (condition word)) encBits encBool)
    (hyes : IsPPTOn encBits encBits yes) (hno : IsPPTOn encBits encBits no) :
    IsPPTOn encBits encBits (fun word => if condition word then yes word else no word) := by
  ppt

/-- Opacity makes the nested plain certificate, rather than the program body, decisive. -/
@[irreducible] def consume (callback : List Bool → List Bool) (word : List Bool) :
    ProbComp (List Bool) := pure (callback word)

/-- A plain-premise named certificate for testing nested deterministic search. -/
@[program_certificate hcallback]
theorem consume_ppt {callback : List Bool → List Bool}
    (hcallback : ComputableInPolyTime callback encBits encBits) :
    IsPPTOn encBits encBits (consume callback) := by
  unfold consume
  exact hcallback.tidy.isPPTOn

/-- The global raw certificate cannot satisfy a nested plain callback obligation. -/
@[irreducible] def rawOnlyReverse (word : List Bool) : List Bool := word.reverse

/-- Construction evidence exists, so the negative checks search policy rather than impossibility. -/
@[fun_prop] theorem rawOnlyReverse_tidy :
    ComputableTidilyInPolyTime rawOnlyReverse encBits encBits := by
  unfold rawOnlyReverse
  fun_prop

-- Literal pure programs must not recover a global raw certificate through either a function
-- rule or a composition rule. Ordinary proof use and unfiltered `fun_prop` remain available.
example : IsPPTOn encBits encBits (fun word => pure (rawOnlyReverse word)) := by
  fail_if_success ppt
  exact rawOnlyReverse_tidy.isPPTOn

example (callback : List Bool → List Bool)
    (hcallback : ComputableInPolyTime callback encBits encBits) :
    IsPPTOn encBits encBits (fun word => pure (callback word)) := by
  ppt

example (callback : List Bool → List Bool)
    (hcallback : ComputableTidilyInPolyTime callback encBits encBits) :
    IsPPTOn encBits encBits (fun word => pure (callback word)) := by
  ppt

example : IsPPTOn encBits encBits (fun word => pure (rawOnlyReverse word)) := by
  fun_prop

/-- A complete predicate alias exercises the same boundary inside probabilistic search. -/
abbrev RawAliasFull {α β : Type*} (f : α → β)
    (input : α ↪ List Bool) (output : β ↪ List Bool) : Prop :=
  ComputableTidilyInPolyTime f input output

/-- Registering this transition must not expose raw search to the nested plain obligation. -/
@[fun_prop] theorem rawAlias_toPlain {α β : Type*} {f : α → β}
    {input : α ↪ List Bool} {output : β ↪ List Bool}
    (h : RawAliasFull f input output) : ComputableInPolyTime f input output :=
  .of_tidy h

example : IsPPTOn encBits encBits (consume rawOnlyReverse) := by
  fail_if_success ppt
  exact consume_ppt (.of_tidy rawOnlyReverse_tidy)

example (callback : List Bool → List Bool) (h : RawAliasFull callback encBits encBits) :
    IsPPTOn encBits encBits (consume callback) := by
  ppt

/-- An opaque plain contract is a legitimate source of a nested deterministic certificate. -/
@[irreducible] def PlainContract (callback : List Bool → List Bool) : Prop :=
  ComputableInPolyTime callback encBits encBits

attribute [fun_prop] PlainContract

/-- This ordinary plain transition remains available to the shared backend. -/
@[fun_prop] theorem PlainContract.computable {callback : List Bool → List Bool}
    (h : PlainContract callback) : ComputableInPolyTime callback encBits encBits := by
  unfold PlainContract at h
  exact h

example (callback : List Bool → List Bool) (h : PlainContract callback) :
    IsPPTOn encBits encBits (consume callback) := by
  ppt

/-- A reducible client wrapper keeps the actual iteration operation visible to dispatch. -/
abbrev wrappedIterate {State : Type} (count : ℕ) (step : State → ProbComp State)
    (initial : State) : ProbComp State :=
  OracleComp.iterate count step initial

example (step : List Bool → ProbComp (List Bool))
    (hstep : IsPPTOn encBits encBits step)
    (hshrink : ∀ state next, next ∈ (ProbComp.eval (step state)).support →
      next.length ≤ state.length) :
    IsPPTOn encBits encBits (fun word => OracleComp.iterate word.length step word) := by
  fail_if_success (clear hstep; ppt)
  fail_if_success (clear hshrink; ppt)
  ppt

example (step : List Bool → ProbComp (List Bool))
    (hstep : IsPPTOn encBits encBits step)
    (hshrink : ∀ state next, next ∈ (ProbComp.eval (step state)).support →
      next.length ≤ state.length) :
    IsPPTOn encBits encBits (fun word => wrappedIterate word.length step word) := by
  ppt

example (step : List Bool → ProbComp (List Bool))
    (hstep : IsPPTOn encBits encBits step) (growth : ℕ)
    (hgrowth : ∀ state next, next ∈ (ProbComp.eval (step state)).support →
      next.length ≤ state.length + growth) :
    IsPPTOn encBits encBits (fun word => OracleComp.iterate word.length step word) := by
  fail_if_success (clear hgrowth; ppt)
  ppt

example (step : List Bool → List Bool → ProbComp (List Bool))
    (hstep : IsPPTOn (encPair encBits encBits) encBits (fun pair => step pair.1 pair.2))
    (growth : List Bool → ℕ) (hpoly : PolyBounded List.length growth)
    (hgrowth : ∀ word state next, next ∈ (ProbComp.eval (step word state)).support →
      next.length ≤ state.length + growth word) :
    IsPPTOn encBits encBits (fun word => wrappedIterate word.length (step word) word) := by
  fail_if_success (clear hstep; ppt)
  fail_if_success (clear hpoly; ppt)
  fail_if_success (clear hgrowth; ppt)
  ppt

end ComplexityTests.PPTPlainSource
