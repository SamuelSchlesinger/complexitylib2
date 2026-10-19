/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.P
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# Boolean closure of P

## Main results

`P` is closed under union and intersection.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {A B : Set α}

/-- `P` is closed under intersection. -/
theorem inter_mem_P (hA : A ∈ P enc) (hB : B ∈ P enc) : A ∩ B ∈ P enc := by
  obtain ⟨f, hf, hA⟩ := hA
  obtain ⟨g, hg, hB⟩ := hB
  exact ⟨fun a => f a && g a, by fun_prop, fun a => by simp [hA a, hB a]⟩

/-- `P` is closed under union. -/
theorem union_mem_P (hA : A ∈ P enc) (hB : B ∈ P enc) : A ∪ B ∈ P enc := by
  obtain ⟨f, hf, hA⟩ := hA
  obtain ⟨g, hg, hB⟩ := hB
  exact ⟨fun a => f a || g a, by fun_prop, fun a => by simp [hA a, hB a]⟩


end Cslib.Complexity
