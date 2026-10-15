/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Logics.Propositional.CNF.ExactlyOne
import Complexity.Computability.Complexity.Problems.SAT

/-!
# Tests for formulas in conjunctive normal form and SAT
-/

namespace ComplexityTests.CNF

open Cslib.Logic.PL Cslib.Complexity

/-- `(x₀ ∨ ¬x₁) ∧ x₁`. -/
def φ : CNF ℕ := [[(0, true), (1, false)], [(1, true)]]

example : φ.eval (fun _ => true) = true := rfl
example : φ.eval (fun v => v == 0) = false := rfl
example : φ.vars = [0, 1, 1] := rfl

/-- The verifier reads values in order of first occurrence: `x₀ ↦ true`, `x₁ ↦ true`. -/
example : SAT.verifier (φ, [true, true]) = true := rfl
example : SAT.verifier (φ, [false, false]) = false := rfl

example : φ ∈ SAT := ⟨fun _ => true, rfl⟩

/-- Relabelling along an injective map preserves satisfiability. -/
example : (φ.relabel (· + 7)).Satisfiable ↔ φ.Satisfiable :=
  CNF.satisfiable_relabel (add_left_injective 7) φ

/-- Exactly one of three variables. -/
example : (CNF.exactlyOne [0, 1, 2]).eval (fun v => v == 1) = true := by decide
example : (CNF.exactlyOne [0, 1, 2]).eval (fun v => v != 0) = false := by decide
example : (CNF.exactlyOne [0, 1, 2]).eval (fun _ => false) = false := by decide

end ComplexityTests.CNF
