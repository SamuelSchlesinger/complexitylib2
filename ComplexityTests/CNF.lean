/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Logics.Propositional.CNF.ExactlyOne
import Complexity.Logics.Propositional.CNF.Parity
import Complexity.Logics.Propositional.ClauseSet.Basic
import Complexity.Logics.Propositional.DNF
import Complexity.Logics.Propositional.QBF
import Complexity.Computability.Complexity.Problems.SAT

/-!
# Tests for propositional normal forms, quantified Boolean formulas and SAT
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

/-! ### Clause sets -/

/-- `φ` and its clause set have the same solutions; its satisfying assignment is one. -/
example : φ.toClauseSet.Sat (fun _ => true) :=
  (CNF.sat_toClauseSet_iff φ _).2 rfl

example : ¬ φ.toClauseSet.Sat (fun v => v == 0) := by
  rw [CNF.sat_toClauseSet_iff]
  decide

/-- Listing the clauses of a clause set gives a formula with the same solutions. -/
example : φ.toClauseSet.toCNF.eval (fun _ => true) = true :=
  (ClauseSet.eval_toCNF_eq_true_iff _ _).2 ((CNF.sat_toClauseSet_iff φ _).2 rfl)

/-! ### Parity constraints -/

/-- The parity of `x₀, x₁` is odd under `x₀ ↦ true, x₁ ↦ false`, so the constraint for odd parity
holds and the one for even parity fails. -/
example : (CNF.parityOnEq ({0, 1} : Finset ℕ) true).eval (fun v => v == 0) = true :=
  (CNF.eval_parityOnEq_eq_true_iff _ _ _).2 (by decide)

example : (CNF.parityOnEq ({0, 1} : Finset ℕ) false).eval (fun v => v == 0) = false := by
  rw [Bool.eq_false_iff, ne_eq, CNF.eval_parityOnEq_eq_true_iff]
  decide

/-! ### Disjunctive normal form -/

/-- `(x₀ ∧ ¬x₁) ∨ x₁`. -/
def δ : DNF ℕ := [[(0, true), (1, false)], [(1, true)]]

example : δ.eval (fun v => v == 0) = true := rfl
example : δ.eval (fun _ => false) = false := rfl

/-- Negating every literal turns `δ` into a formula in conjunctive normal form for `¬δ`. -/
example : CNF.eval (fun _ => false) δ.negate = true := by
  rw [DNF.eval_negate]
  rfl

/-! ### Quantified Boolean formulas -/

/-- `∀ x₀, ∃ x₁, x₀ ↔ x₁` is closed and true. -/
def θ : QBF ℕ :=
  .all 0 (.ex 1 (.or (.and (.var 0) (.var 1)) (.and (.not (.var 0)) (.not (.var 1)))))

example : θ.Closed := by decide
example : θ.eval (fun _ => false) = true := by decide

/-- `∃ x₀, x₀ ∧ ¬x₀` is closed and false. -/
example : (QBF.ex 0 (.and (.var 0) (.not (.var 0)))).eval (fun _ => true) = false := by decide

/-- A closed formula has the same value under every assignment. -/
example (σ : ℕ → Bool) : θ.eval σ = true :=
  (QBF.eval_eq_of_closed (by decide) σ (fun _ => false)).trans (by decide)

end ComplexityTests.CNF
