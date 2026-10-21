/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Reduction

/-! Generic class contracts using only the reduction API, without Ladner's construction. -/

@[expose] public section

namespace ComplexityTests.ReductionClasses

open Cslib.Complexity Turing.MultiTapeTM

example {α : Type} {enc : α ↪ List Bool} : P enc ⊆ NP enc := P_subset_NP
example {α : Type} {enc : α ↪ List Bool} : P enc ⊆ coNP enc := P_subset_coNP

example {β : Type} {encB : β ↪ List Bool} {B : Set β}
    (hB : NPComplete encB B) (h : B ∈ P encB) {α : Type} (enc : α ↪ List Bool) :
    P enc = NP enc := hB.P_eq_NP_of_mem_P h enc

example {β : Type} {encB : β ↪ List Bool} {B : Set β}
    (hB : NPComplete encB B) : B ∈ P encB ↔ ∀ {α : Type} (enc : α ↪ List Bool), P enc = NP enc :=
  hB.mem_P_iff

example {β γ : Type} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {B : Set β} {C : Set γ} (hB : NPComplete encB B) (hC : NPComplete encC C) :
    B ∈ P encB ↔ C ∈ P encC := hB.mem_P_iff_mem_P hC

/-- The containment applies to the always-accepting decider with an empty certificate. -/
example : (Set.univ : Set (List Bool)) ∈ NP encBits :=
  P_subset_NP ⟨fun _ => true, ComputableTidilyInPolyTime.const true, fun _ => by simp⟩

end ComplexityTests.ReductionClasses
