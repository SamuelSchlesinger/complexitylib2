/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.DecisionTree.Restrict
public import Complexity.Computability.QueryComplexity.Relations

/-!
# One-sided measures and negation

For a value `b`, the one-sided measures `s_b(f)`, `bs_b(f)` and `C_b(f)` are the largest
sensitivity, block sensitivity and certificate complexity of `f` at an input of value `b`.
Negation keeps sensitive coordinates, sensitive blocks and certificates, so it preserves `s`, `bs`
and `C` and exchanges the two values of the one-sided measures
(`BitString.sensitivityFor_not`, `QueryComplexity.blockSensitivityFor_not`,
`QueryComplexity.certificateComplexityFor_not`).

With `D(¬f) = D(f)` this turns the bound `D(f) ≤ bs₀(f) C₁(f)`, a one-sided form of the bound
`D(f) ≤ C₁(f) bs(f)` of [BealsBuhrmanCleveMoscaDeWolf2001], into its dual `D(f) ≤ bs₁(f) C₀(f)`
(`DecisionTree.complexity_le_blockSensitivityFor_not_mul_certificateComplexityFor`), hence
`D(f) ≤ min(C₀(f), C₁(f)) bs(f)`. With the one-sided form `C_b(f) ≤ s_{¬b}(f) bs_b(f)` of Nisan's
bound [Nisan1991]
(`QueryComplexity.certificateComplexityFor_le_sensitivityFor_mul_blockSensitivityFor`) it gives
`D(f) ≤ bs_{¬b}(f) s_{¬b}(f) bs_b(f)`, in particular `D(f) ≤ bs₀(f) bs₁(f) s(f)`.

## Main results

* `Cslib.BitString.sensitivity_not`, `Cslib.QueryComplexity.blockSensitivity_not`,
  `Cslib.QueryComplexity.certificateComplexity_not`: negation preserves `s`, `bs` and `C`.
* `Cslib.BitString.sensitivityFor_not`, `Cslib.QueryComplexity.blockSensitivityFor_not`,
  `Cslib.QueryComplexity.certificateComplexityFor_not`: negation exchanges the two values of the
  one-sided measures.
* `Cslib.DecisionTree.complexity_le_blockSensitivityFor_not_mul_certificateComplexityFor`:
  `D(f) ≤ bs_{¬b}(f) C_b(f)`.
* `Cslib.DecisionTree.complexity_le_min_certificateComplexityFor_mul_blockSensitivity`:
  `D(f) ≤ min(C₀(f), C₁(f)) bs(f)`.
* `Cslib.DecisionTree.complexity_le_blockSensitivityFor_mul_sensitivityFor_mul_blockSensitivityFor`:
  `D(f) ≤ bs_{¬b}(f) s_{¬b}(f) bs_b(f)`.
* `Cslib.DecisionTree.complexity_le_blockSensitivityFor_mul_blockSensitivityFor_mul_sensitivity`:
  `D(f) ≤ bs₀(f) bs₁(f) s(f)`.

## References

* [N. Nisan, *CREW PRAMs and decision trees*][Nisan1991]
* [R. Beals, H. Buhrman, R. Cleve, M. Mosca, R. de Wolf, *Quantum lower bounds by
  polynomials*][BealsBuhrmanCleveMoscaDeWolf2001]
* [H. Buhrman, R. de Wolf, *Complexity measures and decision tree complexity:
  a survey*][BuhrmanDeWolf2002]
-/

@[expose] public section

namespace Cslib

open Finset

variable {n : ℕ}

/-- Negation exchanges the inputs of value `b` and those of value `!b`. -/
private theorem filter_not_eq (f : BooleanFunction n) (b : Bool) :
    (univ.filter fun x => (!f x) = b) = univ.filter fun x => f x = !b := by
  ext x
  cases f x <;> cases b <;> simp

namespace BitString

/-- Negating a function keeps its sensitive coordinates. -/
@[simp]
theorem isSensitiveCoord_not {f : BooleanFunction n} {x : BitString n} {i : Fin n} :
    IsSensitiveCoord (fun y => !f y) x i ↔ IsSensitiveCoord f x i := by
  simp [IsSensitiveCoord]

/-- Negation preserves the sensitivity at an input. -/
theorem sensitivityAt_not (f : BooleanFunction n) (x : BitString n) :
    sensitivityAt (fun y => !f y) x = sensitivityAt f x := by
  unfold sensitivityAt sensitiveCoords
  congr 1
  ext i
  simp

/-- Negation preserves sensitivity. -/
theorem sensitivity_not (f : BooleanFunction n) :
    sensitivity (fun y => !f y) = sensitivity f := by
  rw [sensitivity, sensitivity, funext (sensitivityAt_not f)]

/-- Negation exchanges `s₀` and `s₁`. -/
theorem sensitivityFor_not (f : BooleanFunction n) (b : Bool) :
    sensitivityFor (fun y => !f y) b = sensitivityFor f (!b) := by
  rw [sensitivityFor, sensitivityFor, filter_not_eq, funext (sensitivityAt_not f)]

end BitString

open BitString

namespace QueryComplexity

variable {f : BooleanFunction n} {x : BitString n}

/-- Negating a function keeps its sensitive blocks. -/
@[simp]
theorem isSensitiveBlock_not {B : Block n} :
    IsSensitiveBlock (fun y => !f y) x B ↔ IsSensitiveBlock f x B := by
  simp [IsSensitiveBlock]

/-- Negating a function keeps its certificates. -/
@[simp]
theorem isCertificate_not {S : Finset (Fin n)} :
    IsCertificate (fun y => !f y) x S ↔ IsCertificate f x S := by
  simp [IsCertificate]

/-- Negation preserves the block sensitivity at an input. -/
theorem blockSensitivityAt_not (f : BooleanFunction n) (x : BitString n) :
    blockSensitivityAt (fun y => !f y) x = blockSensitivityAt f x := by
  have : sensitiveFamilies (fun y => !f y) x = sensitiveFamilies f x := by
    ext F
    simp [IsSensitiveFamily]
  rw [blockSensitivityAt, blockSensitivityAt, this]

/-- Negation preserves the certificate complexity at an input. -/
theorem certificateComplexityAt_not (f : BooleanFunction n) (x : BitString n) :
    certificateComplexityAt (fun y => !f y) x = certificateComplexityAt f x := by
  obtain ⟨S, hS, hSc⟩ := exists_isCertificate_card_eq f x
  obtain ⟨T, hT, hTc⟩ := exists_isCertificate_card_eq (fun y => !f y) x
  exact le_antisymm ((certificateComplexityAt_le (isCertificate_not.2 hS)).trans hSc.le)
    ((certificateComplexityAt_le (isCertificate_not.1 hT)).trans hTc.le)

/-- Negation preserves block sensitivity. -/
theorem blockSensitivity_not (f : BooleanFunction n) :
    blockSensitivity (fun y => !f y) = blockSensitivity f := by
  rw [blockSensitivity, blockSensitivity, funext (blockSensitivityAt_not f)]

/-- Negation preserves certificate complexity. -/
theorem certificateComplexity_not (f : BooleanFunction n) :
    certificateComplexity (fun y => !f y) = certificateComplexity f := by
  rw [certificateComplexity, certificateComplexity, funext (certificateComplexityAt_not f)]

/-- Negation exchanges `bs₀` and `bs₁`. -/
theorem blockSensitivityFor_not (f : BooleanFunction n) (b : Bool) :
    blockSensitivityFor (fun y => !f y) b = blockSensitivityFor f (!b) := by
  rw [blockSensitivityFor, blockSensitivityFor, filter_not_eq, funext (blockSensitivityAt_not f)]

/-- Negation exchanges `C₀` and `C₁`. -/
theorem certificateComplexityFor_not (f : BooleanFunction n) (b : Bool) :
    certificateComplexityFor (fun y => !f y) b = certificateComplexityFor f (!b) := by
  rw [certificateComplexityFor, certificateComplexityFor, filter_not_eq,
    funext (certificateComplexityAt_not f)]

end QueryComplexity

namespace DecisionTree

open QueryComplexity

/-- **Decision tree complexity from one-sided measures**: `D(f) ≤ bs_{¬b}(f) C_b(f)` for either
value `b`. For `b = 1` this is `D(f) ≤ bs₀(f) C₁(f)`, a one-sided form of the bound of Beals,
Buhrman, Cleve, Mosca and de Wolf [BealsBuhrmanCleveMoscaDeWolf2001]; negating the function gives
the dual `D(f) ≤ bs₁(f) C₀(f)`. -/
theorem complexity_le_blockSensitivityFor_not_mul_certificateComplexityFor
    (f : BooleanFunction n) (b : Bool) :
    complexity f ≤ blockSensitivityFor f (!b) * certificateComplexityFor f b := by
  cases b with
  | false =>
    have := complexity_le_blockSensitivityFor_mul_certificateComplexityFor (fun y => !f y)
    rwa [complexity_not, blockSensitivityFor_not, certificateComplexityFor_not] at this
  | true => exact complexity_le_blockSensitivityFor_mul_certificateComplexityFor f

/-- `D(f) ≤ C_b(f) bs(f)` for either value `b` [BealsBuhrmanCleveMoscaDeWolf2001]. -/
theorem complexity_le_certificateComplexityFor_mul_blockSensitivity (f : BooleanFunction n)
    (b : Bool) : complexity f ≤ certificateComplexityFor f b * blockSensitivity f :=
  (complexity_le_blockSensitivityFor_not_mul_certificateComplexityFor f b).trans (by
    rw [mul_comm]
    exact Nat.mul_le_mul_left _ (blockSensitivityFor_le_blockSensitivity f _))

/-- `D(f) ≤ min(C₀(f), C₁(f)) bs(f)`. -/
theorem complexity_le_min_certificateComplexityFor_mul_blockSensitivity (f : BooleanFunction n) :
    complexity f ≤
      min (certificateComplexityFor f false) (certificateComplexityFor f true) *
        blockSensitivity f := by
  rcases min_choice (certificateComplexityFor f false) (certificateComplexityFor f true) with h | h
  all_goals
    rw [h]
    exact complexity_le_certificateComplexityFor_mul_blockSensitivity f _

/-- `D(f) ≤ bs_{¬b}(f) s_{¬b}(f) bs_b(f)`, from `D(f) ≤ bs_{¬b}(f) C_b(f)` and the one-sided Nisan
bound. -/
theorem complexity_le_blockSensitivityFor_mul_sensitivityFor_mul_blockSensitivityFor
    (f : BooleanFunction n) (b : Bool) :
    complexity f ≤ blockSensitivityFor f (!b) * sensitivityFor f (!b) * blockSensitivityFor f b :=
  (complexity_le_blockSensitivityFor_not_mul_certificateComplexityFor f b).trans
    ((Nat.mul_le_mul_left _
      (certificateComplexityFor_le_sensitivityFor_mul_blockSensitivityFor f b)).trans_eq
      (Nat.mul_assoc _ _ _).symm)

/-- `D(f) ≤ bs₀(f) bs₁(f) s(f)`. -/
theorem complexity_le_blockSensitivityFor_mul_blockSensitivityFor_mul_sensitivity
    (f : BooleanFunction n) :
    complexity f ≤ blockSensitivityFor f false * blockSensitivityFor f true * sensitivity f :=
  (complexity_le_blockSensitivityFor_mul_sensitivityFor_mul_blockSensitivityFor f true).trans (by
    rw [Nat.mul_right_comm]
    exact Nat.mul_le_mul_left _ (sensitivityFor_le_sensitivity f _))

end DecisionTree

end Cslib
