/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Fold

/-! Output-charged polynomial space, finite clients, and binary-counted loops. -/

namespace ComplexityTests.PlainPolySpaceProviderCutover

open Turing.MultiTapeTM

-- Unbounded output with zero raw work space still needs its polynomial encoded-output bound.
example : ComputableInPolySpace (fun w : List Bool => w) encBits encBits :=
  .of_polyTime .id'

example : ComputableInPolySpace (fun p : Bool × Bool => p.1 && p.2)
    (encPair encBool encBool) encBool := .of_polyTime ComputableInPolyTime.bool_and

private theorem seed : ComputableInPolySpace (fun _ : ℕ => false) encNat encBool :=
  .of_polyTime (.const false)

private theorem step : ComputableInPolySpace (fun p : ℕ × ℕ × Bool => !p.2.2)
    (encPair encNat (encPair encNat encBool)) encBool := .of_polyTime (by fun_prop)

-- The runtime count is binary: the count itself need not be polynomial in its word length.
example : ComputableInPolySpace (fun n : ℕ => Bool.not^[n] false) encNat encBool := by
  apply ComputableInPolySpace.iterate (.id') seed (.of_polyTime ComputableInPolyTime.bool_not)
    (B := fun _ => 1) (.const 1)
  intro n k hk
  simp

example : ComputableInPolySpace
    (fun n : ℕ => n.fold (fun _ _ state => !state) false) encNat encBool := by
  apply ComputableInPolySpace.natFold (.id') seed step (.const 1)
  intro n k hk
  simp

example : ComputableInPolySpace
    (fun n : ℕ => n.fold (fun _ _ state => !state) false) encNat encBool ∧
    ∀ n : ℕ, n.fold (fun _ _ state => !state) false = Bool.not^[n] false := by
  apply ComputableInPolySpace.natFold_spec (step := fun (_ : ℕ) (_ : ℕ) state => !state)
    (.id') seed step
    (invariant := fun _ k state => state = Bool.not^[k] false)
    (by simp) ?_ (bound := fun _ => 1) (.const 1) ?_
  · intro n k state hk hs
    rw [hs, Function.iterate_succ_apply']
  · intro n k state hk hs
    simp

example : Bool.not^[3] false = true := rfl

example {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} {f : β → γ} {g : α → β}
    (hf : ComputableInPolySpace f encB encC) (hg : ComputableInPolySpace g encA encB) :
    ComputableInPolySpace (fun a => f (g a)) encA encC := hf.comp hg

example {α β : Type} {input : α ↪ List Bool} {output : β ↪ List Bool} {f : α → β}
    (h : ComputableInPolySpace f input output) :
    PolyBounded (fun a => (input a).length) (fun a => (output (f a)).length) :=
  h.polyBounded_length

run_meta do
  let env ← Lean.getEnv
  -- This predicate is deliberately still staged; provider retirement is not S3 completion.
  unless env.contains `Turing.MultiTapeTM.ComputableTidilyInPolySpace do
    throwError "the staged raw predicate unexpectedly moved"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolySpace.of_polyTime then
    throwError "retired of_polyTime remains"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolySpace.of_polyTime do
    throwError "plain of_polyTime absent"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolySpace.polyBounded_length then
    throwError "retired polyBounded_length remains"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolySpace.polyBounded_length do
    throwError "plain polyBounded_length absent"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolySpace.comp then
    throwError "retired comp remains"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolySpace.comp do
    throwError "plain comp absent"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolySpace.id' then
    throwError "retired id' remains"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolySpace.id' do
    throwError "plain id' absent"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolySpace.prod then
    throwError "retired prod remains"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolySpace.prod do
    throwError "plain prod absent"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolySpace.ite then
    throwError "retired ite remains"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolySpace.ite do
    throwError "plain ite absent"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolySpace.congr then
    throwError "retired congr remains"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolySpace.congr do
    throwError "plain congr absent"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolySpace.iterate then
    throwError "retired iterate remains"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolySpace.iterate do
    throwError "plain iterate absent"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolySpace.comp' then
    throwError "retired comp' remains"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolySpace.comp' do
    throwError "plain comp' absent"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInDegree.increment then
    throwError "retired ComputableTidilyInDegree.increment remains"
  unless env.contains `Turing.MultiTapeTM.ComputableInDegree.increment do
    throwError "plain ComputableTidilyInDegree.increment absent"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.increment then
    throwError "retired ComputableTidilyInPolyTime.increment remains"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.increment do
    throwError "plain ComputableTidilyInPolyTime.increment absent"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolySpace.natFold then
    throwError "retired natFold remains"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolySpace.natFold do
    throwError "plain natFold absent"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolySpace.natFold_spec then
    throwError "retired natFold_spec remains"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolySpace.natFold_spec do
    throwError "plain natFold_spec absent"

end ComplexityTests.PlainPolySpaceProviderCutover
