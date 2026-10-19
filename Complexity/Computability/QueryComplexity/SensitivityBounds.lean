/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.QueryComplexity.NisanSzegedy

/-!
# Polynomial bounds in terms of sensitivity

Huang's theorem `deg(f) ≤ s(f)²` [Huang2019] and the Nisan–Szegedy bound `bs(f) ≤ 2 deg(f)²`
[NisanSzegedy1994] give `bs(f) ≤ 2 s(f)⁴`
(`QueryComplexity.blockSensitivity_le_two_mul_sensitivity_pow_four`). Combined with Nisan's
`C(f) ≤ s(f) bs(f)` [Nisan1991] and `D(f) ≤ C(f) bs(f)` [BealsBuhrmanCleveMoscaDeWolf2001], which
give `D(f) ≤ s(f) bs(f)²` (`DecisionTree.complexity_le_sensitivity_mul_blockSensitivity_sq`), this
bounds certificate and decision tree complexity polynomially in sensitivity:
`C(f) ≤ 2 s(f)⁵` and `D(f) ≤ 4 s(f)⁹`.

## Main results

* `Cslib.QueryComplexity.certificateComplexity_le_two_mul_sensitivity_pow_five`:
  `C(f) ≤ 2 s(f)⁵`.
* `Cslib.DecisionTree.complexity_le_four_mul_sensitivity_pow_nine`: `D(f) ≤ 4 s(f)⁹`.

## References

* [H. Huang, *Induced subgraphs of hypercubes and a proof of the Sensitivity
  Conjecture*][Huang2019]
* [N. Nisan, M. Szegedy, *On the degree of Boolean functions as real polynomials*][NisanSzegedy1994]
* [N. Nisan, *CREW PRAMs and decision trees*][Nisan1991]
* [R. Beals, H. Buhrman, R. Cleve, M. Mosca, R. de Wolf, *Quantum lower bounds by
  polynomials*][BealsBuhrmanCleveMoscaDeWolf2001]
-/

@[expose] public section

namespace Cslib

open BitString

variable {n : ℕ}

namespace QueryComplexity

/-- `C(f) ≤ 2 s(f)⁵`, from Nisan's `C(f) ≤ s(f) bs(f)` and `bs(f) ≤ 2 s(f)⁴`. -/
theorem certificateComplexity_le_two_mul_sensitivity_pow_five (f : BooleanFunction n) :
    certificateComplexity f ≤ 2 * sensitivity f ^ 5 :=
  (certificateComplexity_le_sensitivity_mul_blockSensitivity f).trans
    ((Nat.mul_le_mul_left _ (blockSensitivity_le_two_mul_sensitivity_pow_four f)).trans_eq
      (by ring))

end QueryComplexity

namespace DecisionTree

open QueryComplexity

/-- **Decision tree complexity is polynomial in sensitivity**: `D(f) ≤ 4 s(f)⁹`, from
`D(f) ≤ s(f) bs(f)²` and `bs(f) ≤ 2 s(f)⁴`. -/
theorem complexity_le_four_mul_sensitivity_pow_nine (f : BooleanFunction n) :
    complexity f ≤ 4 * sensitivity f ^ 9 :=
  (complexity_le_sensitivity_mul_blockSensitivity_sq f).trans
    ((Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left (blockSensitivity_le_two_mul_sensitivity_pow_four f) 2)).trans_eq
      (by ring))

end DecisionTree

end Cslib
