/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain.Calculus
import Complexity.Tactic.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Plain.Calculus
import Complexity.Computability.Complexity.Parameterized.PlainCalculus

/-! Plain synthesis through generated rules, captured routines and preserved resource premises. -/

universe u

open Turing.MultiTapeTM

example : ComputableInPolyTime (fun xs : List ℕ => xs.map (fun x => x + x))
    (encList encUnary) (encList encUnary) := by fun_prop

example : ComputableInPolyTime (fun xs : List ℕ => xs.map (fun x => x + 1))
    (encList encNat) (encList encNat) := by fun_prop

example {α : Type} {enc : α ↪ List Bool} {f : α → ℕ} {xs : α → List ℕ}
    (hf : ComputableInPolyTime f enc encUnary)
    (hxs : ComputableInPolyTime xs enc (encList encUnary)) :
    ComputableInPolyTime (fun a => (xs a).map (fun x => f a + x))
      enc (encList encUnary) := by fun_prop

-- A whole telescope, including a bounded-growth hypothesis, is transported rather than only
-- replacing the conclusion. The ordinary implicit/explicit argument API remains usable.
example {α β γ : Type} {enc : γ ↪ List Bool} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {xs : γ → List α} {init : γ → β} {step : β → α → β}
    (hxs : ComputableInPolyTime xs enc (encList encA))
    (hinit : ComputableInPolyTime init enc encB)
    (hstep : ComputableInPolyTime (fun p : β × α => step p.1 p.2)
      (encPair encB encA) encB)
    {growth : ℕ}
    (hgrowth : ∀ state value, (encB (step state value)).length ≤
      (encB state).length + growth) :
    ComputableInPolyTime (fun a => (xs a).foldl step (init a)) enc encB :=
  ComputableInPolyTime.foldl_of_bounded_growth hxs hinit hstep hgrowth

-- Existing stronger universe-polymorphic projection rules are preserved, not replaced by the
-- Type-zero source rule. Named argument clients retain their old binder names.
example {α β γ : Type u} {enc : α ↪ List Bool} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} {f : α → β × γ}
    (hf : ComputableInPolyTime f enc (encPair encB encC)) :
    ComputableInPolyTime (fun a => (f a).1) enc encB :=
  ComputableInPolyTime.fst' (enc₁ := encB) (enc₂ := encC) hf

/-- error: Turing.MultiTapeTM.ComputableTidilyInPolyTime.of_linear retains an unsupported tidy notion after transformation -/
#guard_msgs in
attribute [plain_mirror rejectedLinearProbe] ComputableTidilyInPolyTime.of_linear

run_meta do
  let source := `Turing.MultiTapeTM.ComputableTidilyInPolyTime.foldl_of_bounded_growth
  let target := `Turing.MultiTapeTM.ComputableInPolyTime.foldl_of_bounded_growth
  unless (← Cslib.Tactic.PlainMirror.getMirror? source) == some target do
    throwError "bounded-growth mirror is absent from the registry"
  unless (← Cslib.Tactic.PlainMirror.getMirror?
      `Turing.MultiTapeTM.ComputableTidilyInPolyTime.of_linear).isNone do
    throwError "unsupported exact-resource conversion was recorded as covered"

/-- info: 'Turing.MultiTapeTM.ComputableInPolyTime.binary_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ComputableInPolyTime.binary_add

-- The tactic's named-program registry uses the plain predicate and retains the source rule's
-- eager list premise; the composed client needs no exposed tidy conversion.
run_meta do
  let rules := (Cslib.Tactic.certificateExt.getState (← Lean.getEnv)).getD
    (`Turing.MultiTapeTM.ComputableInPolyTime, `List.any, false) #[]
  unless rules.any (fun entry =>
      entry.1 == `Turing.MultiTapeTM.ComputableInPolyTime.anyWithInput &&
        entry.2 == #[`hlist]) do
    throwError "plain routine rule lost its program index or eager list premise"

example : ComputableInPolyTime (fun p : ℕ × List ℕ => p.2.any (fun x => decide (x = p.1)))
    (encPair encNat (encList encNat)) encBool := by polytime

-- Independent time and space functions remain independent under composition.
example {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} {f : β → γ} {g : α → β} {T₁ S₁ : α → ℕ} {T₂ S₂ : β → ℕ}
    (hf : ComputableInO f encB encC T₂ S₂) (hg : ComputableInO g encA encB T₁ S₁) :
    ComputableInO (f ∘ g) encA encC (fun a => T₁ a + T₂ (g a))
      (fun a => S₁ a + S₂ (g a)) := hf.comp hg

example : Cslib.Complexity.ComputableInFPTTime (fun n : ℕ => n + 1) encUnary encUnary id := by
  have hn : ComputableInPolyTime (fun n : ℕ => n + 1) encUnary encUnary := by fun_prop
  exact hn.computableInFPTTime id

example {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} {f : α → β} {g : β → γ} {κA : α → ℕ} {κB : β → ℕ}
    (hg : Cslib.Complexity.ComputableInFPTTime g encB encC κB)
    (hf : Cslib.Complexity.ComputableInFPTTime f encA encB κA) {h : ℕ → ℕ}
    (hκ : ∀ a, κB (f a) ≤ h (κA a)) :
    Cslib.Complexity.ComputableInFPTTime (g ∘ f) encA encC κA := hg.comp hf hκ
