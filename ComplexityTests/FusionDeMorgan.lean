/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Fusion.DeMorgan

/-!
# Fusion bounds for De Morgan circuits

A two-gate De Morgan circuit computes NAND by negating an internal AND gate, so the lower bound
gives cover complexity at most four. A projection has an empty cover, so the upper bound gives a
De Morgan circuit within the stated budget. The headline bounds are instantiated for an arbitrary
function, and the dual-rail selection theorem is instantiated at `n = 2`.
-/

namespace ComplexityTests.FusionDeMorgan

open Cslib Cslib.Circuits Cslib.Circuits.Fusion Cslib.Circuits.Boolean

private def nand : BooleanFunction 2 := fun x => !(x 0 && x 1)

private def nandCircuit : Circuit Boolean.signature 2 1 :=
  ⟨(((Program.empty : Program Boolean.signature 2 0).gate ⟨.and, ![.input 0, .input 1]⟩).gate
    ⟨.not, ![.gate 0]⟩), fun _ => .gate 1⟩

private theorem nandCircuit_computes :
    nandCircuit.Computes Boolean.interpretation (single nand) := by
  unfold Circuit.Computes
  decide

example : nandCircuit.size = 2 := rfl

/-- A negation of an internal gate is allowed by the De Morgan lower bound. -/
example : pairCoverComplexity {x | nand x = true}
    (fun i => {x | AltFormula.literals x i = true}) ≤ 4 :=
  pairCoverComplexity_le_two_mul_size nandCircuit nandCircuit_computes

/-- The lower bound also holds for semi-ultrafilters. -/
example : pairCoverComplexity {x | nand x = true}
    (fun i => {x | AltFormula.literals x i = true}) Semifilter.IsUltra ≤ 4 :=
  pairCoverComplexity_le_two_mul_size nandCircuit nandCircuit_computes _

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
    (fun x (_ : Fin 1) => nand x) AltFormula.literals ≤ 16 := by
  have h : pairCoverComplexity {x | nand x = true}
      (fun i => {x | AltFormula.literals x i = true}) ≤ 4 :=
    pairCoverComplexity_le_two_mul_size nandCircuit nandCircuit_computes
  calc _ ≤ _ := (ecomplexityFrom_literals_bounds nand).2
    _ ≤ 4 ^ 2 := pow_le_pow_left₀ zero_le h 2
    _ = 16 := by norm_num

/-- The dual-rail selection theorem, instantiated at `n = 2`. -/
example : ∀ x : BitString 2, (Monotone.literalsRailCircuit 2).eval Monotone.interpretation
    (AltFormula.literals x) = Monotone.railBitString x :=
  Monotone.eval_literalsRailCircuit

example : (Monotone.literalsRailCircuit 3).program.cost Monotone.andCost = 0 := Monotone.cost_literalsRailCircuit

/--
info: 'Cslib.Circuits.Fusion.ecomplexityFrom_literals_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Fusion.ecomplexityFrom_literals_bounds

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
