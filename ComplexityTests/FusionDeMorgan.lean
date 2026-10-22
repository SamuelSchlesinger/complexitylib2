/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Fusion.DeMorgan

/-!
# Fusion bounds for De Morgan circuits

A two-gate De Morgan circuit with an internal negation computes `x₀ ∧ ¬x₁`, so the lower bound
gives cover complexity at most four. A projection has an empty cover, so the upper bound gives a
De Morgan circuit within the stated budget. The headline bounds are instantiated for a function
with no assumptions on it, and the dual-rail selection is checked on all small inputs.
-/

namespace ComplexityTests.FusionDeMorgan

open Cslib Cslib.Circuits Cslib.Circuits.Fusion Cslib.Circuits.Boolean

private def andNot : BooleanFunction 2 := fun x => x 0 && !x 1

private def andNotCircuit : Circuit Boolean.signature 2 1 :=
  ⟨(((Program.empty : Program Boolean.signature 2 0).gate ⟨.not, ![.input 1]⟩).gate
    ⟨.and, ![.input 0, .gate 0]⟩), fun _ => .gate 1⟩

private theorem andNotCircuit_computes :
    andNotCircuit.Computes Boolean.interpretation (single andNot) := by
  unfold Circuit.Computes
  decide

example : andNotCircuit.size = 2 := rfl

/-- The internal negation is allowed by the De Morgan lower bound. -/
example : pairCoverComplexity {x | andNot x = true}
    (fun i => {x | AltFormula.literals x i = true}) ≤ 4 :=
  pairCoverComplexity_le_two_mul_size andNotCircuit andNotCircuit_computes

/-- The lower bound also holds for semi-ultrafilters. -/
example : pairCoverComplexity {x | andNot x = true}
    (fun i => {x | AltFormula.literals x i = true}) Semifilter.IsUltra ≤ 4 :=
  pairCoverComplexity_le_two_mul_size andNotCircuit andNotCircuit_computes _

private def proj : BooleanFunction 1 := fun x => x 0

/-- The positive literal is exactly the target, so no witness exists and the empty list covers. -/
private def projCover : PairCover {x | proj x = true}
    (fun i => {x | AltFormula.literals x i = true}) where
  pairs := []
  isCover w _ := w.filter.not_apply_empty (by
    have h := w.above 0 w.point.property
    have hempty : Subtype.val ⁻¹' {x : BitString 1 | AltFormula.literals x 0 = true} =
        (∅ : Set ↥({x | proj x = true}ᶜ)) := by
      ext ⟨x, hx⟩
      have hx' : x 0 = false := by simpa [proj] using hx
      have hlit : AltFormula.literals x 0 = x 0 := rfl
      simp [hlit, hx']
    rwa [hempty] at h)

example : ∃ d : Circuit Boolean.signature 1 1, d.Computes Boolean.interpretation (single proj) ∧
    d.size ≤ 13 :=
  projCover.exists_computes_size_le

example (n : ℕ) (f : BooleanFunction n) :
    ∃ t : ℕ, pairCoverComplexity {x | f x = true}
        (fun i => {x | AltFormula.literals x i = true}) = t ∧
      t ≤ 2 * complexity Boolean.interpretation (single f) ∧
      complexity Boolean.interpretation (single f) ≤ 4 * (t + 1) ^ 2 * (2 * n + t + 1) + n :=
  pairCoverComplexity_complexity_bounds f

/-- Monotone AND complexity from literals is at most the square of the cover bound. -/
example : ecomplexityFrom Monotone.interpretation Monotone.andCost
    (fun x (_ : Fin 1) => andNot x) AltFormula.literals ≤ 16 := by
  have h : pairCoverComplexity {x | andNot x = true}
      (fun i => {x | AltFormula.literals x i = true}) ≤ 4 :=
    pairCoverComplexity_le_two_mul_size andNotCircuit andNotCircuit_computes
  calc _ ≤ _ := (andComplexity_bounds andNot).2
    _ ≤ 4 ^ 2 := pow_le_pow_left₀ zero_le h 2
    _ = 16 := by norm_num

/-- The dual-rail inputs are selected correctly from the literals on all inputs of length two. -/
example : ∀ x : BitString 2, (railCircuit 2).eval Monotone.interpretation
    (AltFormula.literals x) = Monotone.railBitString x :=
  eval_railCircuit

example : (railCircuit 3).program.cost Monotone.andCost = 0 := cost_railCircuit

/--
info: 'Cslib.Circuits.Fusion.andComplexity_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Fusion.andComplexity_bounds

/--
info: 'Cslib.Circuits.Fusion.pairCoverComplexity_le_two_mul_size' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Fusion.pairCoverComplexity_le_two_mul_size

/--
info: 'Cslib.Circuits.Fusion.PairCover.exists_computes_size_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Fusion.PairCover.exists_computes_size_le

/--
info: 'Cslib.Circuits.Fusion.pairCoverComplexity_complexity_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Fusion.pairCoverComplexity_complexity_bounds

end ComplexityTests.FusionDeMorgan
