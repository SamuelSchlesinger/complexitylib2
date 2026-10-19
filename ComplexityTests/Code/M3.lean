/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Data.Code.BerlekampWelch
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.ComputeDegree

/-!
# Tests: decoding algebraic codes

The Berlekamp–Welch decoder over `ZMod 7` reports failure on a received word of length three that
no constant is within distance one of, although `2 * 1 + 1 ≤ 3`; without its checks the decoder
returned a quotient here. The axioms of the headline theorems.
-/

namespace ComplexityTests.Code.M3

open Cslib Cslib.Code Finset Polynomial

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-! ### Failure detection of the Berlekamp–Welch decoder -/

/-- Three points of `ZMod 7`. -/
private def points3 : Fin 3 → ZMod 7 := fun i => (i : ℕ)

private theorem points3_injective : Function.Injective points3 := by decide

/-- A received word with three distinct values: every constant differs from it twice. -/
private def received3 : Fin 3 → ZMod 7 := ![1, 2, 4]

private theorem lt_hammingDist_received3 (p : (ZMod 7)[X]) (hp : p.degree < 1) :
    1 < hammingDist (fun i => p.eval (points3 i)) received3 := by
  rw [eq_C_of_degree_le_zero (Order.le_of_lt_succ hp)]
  simp only [eval_C]
  generalize p.coeff 0 = a
  revert a
  decide

/-- No constant is within distance one of the received word, so the decoder fails. -/
example : berlekampWelch points3 1 1 received3 = none :=
  berlekampWelch_eq_none_of_forall_lt_hammingDist lt_hammingDist_received3

/-- The decoder for one error and dimension one returns nothing on the received word, since
`2 * 1 + 1 ≤ 3`: it fails exactly when no constant is within distance one. -/
example : ¬∃ p, berlekampWelch points3 1 1 received3 = some p := by
  rintro ⟨p, hp⟩
  have := (berlekampWelch_eq_some_iff points3_injective (by simp)).1 hp
  exact absurd this.2 (not_le.2 (lt_hammingDist_received3 p this.1))

/-! ### Axioms of the headline theorems -/

/--
info: 'Cslib.Code.exists_isSolution_mul_of_berlekampWelch_eq_some' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Code.exists_isSolution_mul_of_berlekampWelch_eq_some

/--
info: 'Cslib.Code.hammingDist_le_of_berlekampWelch_eq_some' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Code.hammingDist_le_of_berlekampWelch_eq_some

/--
info: 'Cslib.Code.berlekampWelch_eq_some_iff' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Code.berlekampWelch_eq_some_iff

/--
info: 'Cslib.Code.berlekampWelch_eq_none_iff' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Code.berlekampWelch_eq_none_iff

end ComplexityTests.Code.M3
