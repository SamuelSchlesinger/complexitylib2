/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Advice

/-!
# Polynomial advice clients

Prefix substitution preserves live suffix inputs, including empty prefixes and suffixes.
The empty and full languages inhabit the advice class using actual constant-time deciders.
-/

namespace ComplexityTests.Advice

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Turing.MultiTapeTM

example (x : BitString 2) :
    substitute (prependInputs (fun _ : Fin 1 => true)) x = Fin.append (fun _ => true) x :=
  substitute_prependInputs _ _

example (x : BitString 2) : substitute (prependInputs (n := 2) Fin.elim0) x = x := by
  rw [substitute_prependInputs]
  ext i
  fin_cases i <;> rfl

example (r : BitString 2) : substitute (prependInputs (n := 0) r) Fin.elim0 = r := by
  rw [substitute_prependInputs]
  ext i
  fin_cases i <;> rfl

example : (substituteCircuit (prependInputs (n := 0) (p := 0) Fin.elim0)).size = 2 :=
  size_substituteCircuit _

example (r : BitString 1) (x : BitString 2) :
    (substituteCircuit (prependInputs r)).eval interpretation x = Fin.append r x := by
  rw [eval_substituteCircuit, substitute_prependInputs]

private theorem top_mem_advice : (⊤ : Language Bool) ∈ PAdvice := by
  refine ⟨fun _ => [], (by change PolynomiallyBounded fun _ : ℕ => 0; fun_prop),
    Set.univ, ?_, fun _ => Iff.rfl⟩
  exact ⟨fun _ => true, ComputableTidilyInPolyTime.const _, fun _ => by simp⟩

private theorem zero_mem_advice : (0 : Language Bool) ∈ PAdvice := by
  refine ⟨fun _ => [true], (by change PolynomiallyBounded fun _ : ℕ => 1; fun_prop),
    ∅, ?_, fun _ => Iff.rfl⟩
  exact ⟨fun _ => false, ComputableTidilyInPolyTime.const _, fun _ => by simp⟩

example : (⊤ : Language Bool) ∈ PPoly := PAdvice_subset_PPoly top_mem_advice
example : (0 : Language Bool) ∈ PPoly := PAdvice_subset_PPoly zero_mem_advice

example : (⊤ : Language Bool) ∈ PPoly :=
  PPoly.of_advice PPoly.top_mem (fun _ => [])
    (by change PolynomiallyBounded fun _ : ℕ => 0; fun_prop) (fun _ => Iff.rfl)

/--
info: 'Cslib.Circuits.Boolean.PPoly.of_advice' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Boolean.PPoly.of_advice
/--
info: 'Cslib.Circuits.Boolean.PAdvice_subset_PPoly' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Boolean.PAdvice_subset_PPoly

end ComplexityTests.Advice
