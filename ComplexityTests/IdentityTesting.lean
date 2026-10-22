/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Arithmetic.IdentityTesting

/-!
# Tests for polynomial identity testing, Schwartz–Zippel and Kabanets–Impagliazzo

Concrete membership and non-membership in `PITInt`, Schwartz–Zippel root bounds and non-vanishing
witnesses on integer arithmetic circuits, Laplace permanent expansion and downward self-reducibility
via `laplacePermCircuit` and `IsLaplacePermChain`, the unconditional `NEXP` circuit lower bound, and
axiom guards for the headline results of
`Complexity.Computability.Circuit.Arithmetic.IdentityTesting`.
-/

namespace ComplexityTests.IdentityTesting

open Cslib Cslib.Circuits Cslib.Circuits.Arithmetic Cslib.Complexity MvPolynomial Finset

/-! ### Concrete membership and non-membership in `PITInt` -/

/-- `X₀ - X₀` is the zero polynomial, so `subCircuit (varCircuit 0) (varCircuit 0)` is in `PITInt`.
-/
example :
    (⟨1, subCircuit (varCircuit (R := ℤ) 0) (varCircuit 0)⟩ :
      Σ n, Circuit (arithSignature ℤ) n 1) ∈ PITInt := by
  rw [mem_PITInt_subCircuit_iff]

/-- `X₀` is nonzero, so `varCircuit 0` is not in `PITInt`. -/
private theorem varCircuit_zero_notMem_PITInt :
    (⟨1, varCircuit (R := ℤ) 0⟩ : Σ n, Circuit (arithSignature ℤ) n 1) ∉ PITInt := by
  rw [mem_PITInt_iff, polynomial_varCircuit]
  exact X_ne_zero 0

/-! ### Schwartz–Zippel on a concrete circuit -/

example :
    ∃ x : Fin 1 → ℤ, (∀ i, x i ∈ ({0, 1} : Finset ℤ)) ∧
      (varCircuit (R := ℤ) 0).eval (arithInterpretation ℤ) x 0 ≠ 0 := by
  refine exists_eval_ne_zero_of_notMem_PITInt varCircuit_zero_notMem_PITInt ?_
  rw [polynomial_varCircuit, totalDegree_X]
  decide

/-! ### Laplace expansion and `IsLaplacePermChain` non-vacuity -/

example (A : Matrix (Fin 2) (Fin 2) ℤ) :
    A.permanent = ∑ j : Fin 2, A 0 j * (A.submatrix Fin.succ j.succAbove).permanent :=
  Matrix.permanent_succ_row_zero A

/-- Unconditional instance of `IsLaplacePermChain` at every dimension `n`, witnessed by the
recursive Laplace permanent circuit family `laplacePermCircuit`. -/
example (n : ℕ) : IsLaplacePermChain (laplacePermCircuit (R := ℤ)) n :=
  isLaplacePermChain_laplacePermCircuit n

example :
    (⟨0, permBaseDiff (laplacePermCircuit (R := ℤ) 0)⟩ :
      Σ n, Circuit (arithSignature ℤ) n 1) ∈ PITInt :=
  (isLaplacePermChain_laplacePermCircuit 0).base_mem

example (m : ℕ) :
    (⟨(m + 1) * (m + 1),
        permStepDiff m (laplacePermCircuit (R := ℤ) m) (laplacePermCircuit (m + 1))⟩ :
      Σ n, Circuit (arithSignature ℤ) n 1) ∈ PITInt :=
  (isLaplacePermChain_laplacePermCircuit (m + 1)).step_mem m (Nat.lt_succ_self m)

/-- A circuit computing `0` instead of `1` at dimension `0` is rejected by `permBaseDiff`. -/
example :
    (⟨0, permBaseDiff (constCircuit (R := ℤ) 0)⟩ :
      Σ n, Circuit (arithSignature ℤ) n 1) ∉ PITInt := by
  rw [mem_PITInt_permBaseDiff_iff, polynomial_constCircuit, map_zero, permanent_genericMatrix_zero]
  exact zero_ne_one

/-! ### Unconditional `NEXP` circuit lower bound -/

example :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ NEXP Turing.MultiTapeTM.encBits ∧
      ∀ c, L ∉ Cslib.Circuits.Boolean.SIZE fun n => c * (n + 1) ^ 2 :=
  exists_mem_NEXP_notMem_SIZE 2

/-! ### Axiom guards -/

/--
info: 'MvPolynomial.card_roots_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPolynomial.card_roots_le

/--
info: 'MvPolynomial.exists_eval_ne_zero_of_totalDegree_lt_card' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPolynomial.exists_eval_ne_zero_of_totalDegree_lt_card

/--
info: 'Cslib.Circuits.Arithmetic.card_roots_eval_le_of_notMem_PITInt' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms card_roots_eval_le_of_notMem_PITInt

/--
info: 'Cslib.Circuits.Arithmetic.exists_eval_ne_zero_of_notMem_PITInt' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_eval_ne_zero_of_notMem_PITInt

/--
info: 'Matrix.permanent_succ_column_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.permanent_succ_column_zero

/--
info: 'Matrix.permanent_succ_row_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.permanent_succ_row_zero

/--
info: 'Cslib.Circuits.Arithmetic.permanent_genericMatrix_succ' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms permanent_genericMatrix_succ

/--
info: 'Cslib.Circuits.Arithmetic.forall_polynomial_eq_permanent_iff_mem_PITInt' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms forall_polynomial_eq_permanent_iff_mem_PITInt

/--
info: 'Cslib.Circuits.Arithmetic.isLaplacePermChain_laplacePermCircuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isLaplacePermChain_laplacePermCircuit

/--
info: 'Cslib.Circuits.Arithmetic.exists_certified_perm_family_of_PITInt_mem_P_of_mem_VP' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_certified_perm_family_of_PITInt_mem_P_of_mem_VP

/--
info: 'Cslib.Complexity.exists_mem_NEXP_notMem_SIZE' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_mem_NEXP_notMem_SIZE

/--
info: 'Cslib.Circuits.Arithmetic.kabanets_impagliazzo' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kabanets_impagliazzo

/--
info: 'Cslib.Circuits.Arithmetic.kabanets_impagliazzo_of_EXP_subset_P' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kabanets_impagliazzo_of_EXP_subset_P

end ComplexityTests.IdentityTesting
