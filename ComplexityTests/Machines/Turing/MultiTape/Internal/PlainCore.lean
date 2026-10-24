/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeComposition

/-! # Direct plain core contracts without the higher tidy calculus -/

open Turing.MultiTapeTM

run_elab do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInO, `Turing.MultiTapeTM.ComputableTidilyInDegree] do
    if (← Lean.getEnv).contains name then
      throwError "unexpected higher tidy calculus: {name}"

section Projections
universe u
variable {α β : Type u} (encA : α ↪ List Bool) (encB : β ↪ List Bool)
variable (enc : α × β ↪ List Bool) [PairEncoding encA encB enc]

-- Explicit generic certificates retain arbitrary encoding instances, including their other
-- component encoding, which is not inferable from an opaque input encoding alone.
example : ComputableInPolyTime (fun p : α × β => p.1) enc encA :=
  PairEncoding.computableInPolyTime_fst (enc₂ := encB)

example : ComputableInPolyTime (fun p : α × β => p.2) enc encB :=
  PairEncoding.computableInPolyTime_snd (enc₁ := encA)

example : ComputableInPolyTime (fun p : α × β => p.1) enc encA := by
  have hf : ComputableInPolyTime (fun p : α × β => p.1) enc encA :=
    PairEncoding.computableInPolyTime_fst (enc₂ := encB)
  fun_prop

example : ComputableInPolyTime (fun p : α × β => p.1) (encPair encA encB) encA :=
  ComputableInPolyTime.fst encA encB

example : ComputableInPolyTime (fun p : α × β => p.2) (encPair encA encB) encB := by fun_prop
end Projections

-- The constructor and projections compose on an actual finite encoding, without a raw bridge.
example : ComputableInPolyTime (fun b : Bool => (b, !b)) encBool
    (encPair encBool encBool) := by fun_prop

example : ComputableInPolyTime (fun b : Bool => if b then !b else b) encBool encBool := by
  fun_prop

section Resources
variable {α β γ : Type*} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
  {encC : γ ↪ List Bool} {f : β → γ} {g : α → β}

-- The output exponent is independent of the cost/workspace exponent; all may be zero.
example {d₁ e₁ d₂ e₂ : ℕ} (hf : ComputableInDegree f encB encC d₂ e₂)
    (hg : ComputableInDegree g encA encB d₁ e₁) :
    ComputableInDegree (fun a => f (g a)) encA encC (max d₁ (e₁ * d₂)) (e₁ * e₂) :=
  hf.comp hg

example (hf : ComputableInDegree f encB encC 0 0)
    (hg : ComputableInDegree g encA encB 0 0) :
    ComputableInDegree (fun a => f (g a)) encA encC 0 0 := hf.comp hg

example {T₁ S₁ : α → ℕ} {T₂ S₂ : β → ℕ}
    (hf : ComputableInO f encB encC T₂ S₂) (hg : ComputableInO g encA encB T₁ S₁) :
    ComputableInO (fun a => f (g a)) encA encC (fun a => T₁ a + T₂ (g a))
      (fun a => S₁ a + S₂ (g a)) := hf.comp hg
end Resources

/-- info: 'Turing.MultiTapeTM.ComputableInDegree.comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableInDegree.comp
/-- info: 'Turing.MultiTapeTM.ComputableInO.comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableInO.comp
/-- info: 'Turing.MultiTapeTM.ComputableInO.ite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableInO.ite
