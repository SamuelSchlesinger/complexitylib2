/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Computability.QueryComplexity.Measures
import Complexity.Computability.DecisionTree.Certificate
import Complexity.Computability.DecisionTree.Influence
import Complexity.Computability.DecisionTree.Parity
import Complexity.Computability.DecisionTree.Restrict
import Complexity.Computability.QueryComplexity.Restriction

/-! Joint upstream imports, native measures, and retained arbitrary-coordinate clients. -/

namespace ComplexityTests.QueryComplexity

open Cslib Cslib.BitString Cslib.QueryComplexity Finset
open scoped BigOperators

-- These are CSLib's measures, used directly by the local decision-tree bounds.
example {n : ℕ} (f : BooleanFunction n) :
    DecisionTree.complexity f ≤
      certificateComplexityFor f false * certificateComplexityFor f true :=
  DecisionTree.complexity_le_certificateComplexityFor_mul f

example {n : ℕ} (f : BooleanFunction n) :
    DecisionTree.complexity f ≤ Cslib.QueryComplexity.certificateComplexity f ^ 2 :=
  DecisionTree.complexity_le_certificateComplexity_sq f

example {n : ℕ} :
    sensitivity (parity n) = n ∧ blockSensitivity (parity n) = n ∧
      certificateComplexity (parity n) = n ∧ DecisionTree.complexity (parity n) = n :=
  ⟨sensitivity_parity, blockSensitivity_parity, certificateComplexity_parity,
    DecisionTree.complexity_parity⟩

-- The finite minimum is executable, including empty-coordinate and missing-output cases.
example : certificateComplexityAt (parity 2) (fun _ => false) = 2 := by decide

example (f : BooleanFunction 0) : certificateComplexity f = 0 :=
  Nat.eq_zero_of_le_zero (certificateComplexity_le_card f)

example (f : BooleanFunction 0) : sensitivity f = 0 :=
  Nat.eq_zero_of_le_zero (sensitivity_le_card f)

example (f : BooleanFunction 0) : blockSensitivity f = 0 :=
  Nat.eq_zero_of_le_zero (blockSensitivity_le_card f)

example (f : BooleanFunction 0) : DecisionTree.complexity f = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa using DecisionTree.complexity_le_card f

example {n : ℕ} : certificateComplexityFor (fun _ : BitString n => false) true = 0 := by
  simp [certificateComplexityFor]

example {n : ℕ} (b : Bool) : certificateComplexity (fun _ : BitString n => b) = 0 := by
  apply Nat.eq_zero_of_le_zero
  refine Finset.sup_le fun x _ => ?_
  exact (certificateComplexityAt_le (S := ∅) (fun _ _ => rfl)).trans_eq (by simp)

-- A non-Fin coordinate type and non-Boolean output still have the generic counting bound.
example : DecisionTree.complexity (fun x : Bool → Bool => x) = 2 := by
  apply (DecisionTree.complexity_eq_card_of_forall_update_ne
    (x := fun _ => false) ?_).trans (show Fintype.card Bool = 2 from rfl)
  intro i hi
  have h := congrFun hi i
  simp at h

-- For infinitely many possible coordinates, the explicit tree witness suffices.
private def natTree : DecisionTree ℕ ℕ := .node 0 (.leaf 3) (.leaf 5)

example : {0} ⊆ natTree.queries (fun _ => false) := by
  apply DecisionTree.subset_queries_of_forall_update_ne (f := natTree.eval) (fun _ => rfl)
  intro i hi
  have : i = 0 := Finset.mem_singleton.mp hi
  subst i
  decide

-- Upstream assignments and generic restrictions need no conversion or alternative encoding.
example {n : ℕ} (C : Cslib.QueryComplexity.PartialAssignment n) (x : BitString n) :
    Cslib.QueryComplexity.Agrees C x ↔ Cslib.BitString.PartialAssignment.fill C x = x :=
  Cslib.BitString.PartialAssignment.agrees_iff_fill_eq

example {n : ℕ} (C : Cslib.QueryComplexity.PartialAssignment n) :
    Cslib.QueryComplexity.support C = Cslib.BitString.PartialAssignment.support C := rfl

example {n : ℕ} (B : Finset (Fin n)) (x : BitString n) : flipOn B x = flipBlock B x := rfl

example {n : ℕ} (f : BooleanFunction n) (C : Cslib.QueryComplexity.PartialAssignment n)
    (b : Bool) (h : Forces f C b) :
    DecisionTree.complexity (f ∘ Cslib.BitString.PartialAssignment.fill C) = 0 :=
  DecisionTree.complexity_eq_zero_iff.mpr fun x y =>
    ((forces_iff_forall_fill f C b).mp h x).trans ((forces_iff_forall_fill f C b).mp h y).symm

example {n : ℕ} (x y : BitString n) (S : Finset (Fin n)) :
    Cslib.BitString.PartialAssignment.fill (Cslib.QueryComplexity.restrict x S) y =
      S.piecewise x y := by simp

example {ι β : Type*} [Finite ι] (C : Cslib.BitString.PartialAssignment ι)
    (f : (ι → Bool) → β) : DecisionTree.complexity (f ∘ C.fill) ≤ DecisionTree.complexity f :=
  DecisionTree.complexity_comp_fill_le C f

-- Generic Fourier theory and the native sensitivity corollary coexist.
example {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → Bool) :
    totalInfluence (fun x => signVal (f x)) =
      𝔼 x, (#{i | f (Function.update x i (!x i)) ≠ f x} : ℝ) :=
  totalInfluence_signVal f

example {n : ℕ} (f : BooleanFunction n) :
    totalInfluence (fun x => signVal (f x)) = 𝔼 x, (sensitivityAt f x : ℝ) :=
  totalInfluence_eq_expect_sensitivityAt f

example {n : ℕ} (f : BooleanFunction n) :
    totalInfluence (fun x => signVal (f x)) ≤ sensitivity f :=
  totalInfluence_le_sensitivity f

end ComplexityTests.QueryComplexity
