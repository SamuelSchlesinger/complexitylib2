/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Continuity
import Complexity.Computability.Circuit.Complexity

/-! The modulus of continuity of De Morgan circuit complexity: a single changed input moves the
complexity of a projection, the modulus vanishes at zero and is subadditive, the square-root upper
bounds instantiated, and the lower bound `2 ^ 4 ≤ 16 ω_{8,1}(2 ^ 4)`. -/

namespace ComplexityTests.CircuitHamming.Continuity

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

/-! ### A single changed input -/

/-- The projection on one input and the constant `false` differ on one input. -/
theorem hammingDist_proj_false :
    hammingDist (single fun x : BitString 1 => x 0) (single fun _ => false) = 1 := by
  decide

/-- The same distance through the single values. -/
example : hammingDist (single fun x : BitString 1 => x 0) (single fun _ => false) =
    hammingDist (fun x : BitString 1 => x 0) fun _ => false := by
  rw [hammingDist_single]

/-- **A single changed input moves the complexity**: the projection costs nothing and the
constant `false`, which is not a projection, costs a gate, so `ω_{1,1}(1) ≥ 1`. -/
example : 1 ≤ complexityModulus interpretation 1 1 1 := by
  have hfalse : 1 ≤ complexity interpretation (single fun _ : BitString 1 => false) :=
    one_le_complexity_single fun i h => by
      have := congrFun h fun _ => true
      simp at this
  refine le_trans ?_ (dist_complexity_le_complexityModulus hammingDist_proj_false.le)
  rw [complexity_single_proj, Nat.dist_zero_left]
  exact hfalse

/-- So, by subadditivity, `ω_{1,1}(2) ≤ 2 ω_{1,1}(1)`. -/
example : complexityModulus interpretation 1 1 2 ≤ 2 * complexityModulus interpretation 1 1 1 :=
  complexityModulus_le_mul

/-- Changing no input changes nothing. -/
example : complexityModulus interpretation 3 2 0 = 0 :=
  complexityModulus_zero

/-- The modulus is attained. -/
example : ∃ f g : BitString 2 → Fin 1 → Bool, hammingDist f g ≤ 1 ∧
    Nat.dist (complexity interpretation f) (complexity interpretation g) =
      complexityModulus interpretation 2 1 1 :=
  exists_dist_complexity_eq_complexityModulus

/-! ### Square-root continuity -/

/-- The single-output upper bound at `ε = 1`. -/
example : ∃ p₀ : ℕ, ∀ p ≥ p₀,
    (complexityModulus interpretation (2 * p) 1 (2 ^ p) : ℝ) ≤ (1 + 1) * 2 ^ p :=
  complexityModulus_two_pow_single_output_le 1 one_pos

/-- The multi-output upper bound at `ε = 1`. -/
example : ∃ p₀ : ℕ, ∀ p ≥ p₀, ∀ m ≤ 2 * p,
    (complexityModulus interpretation (2 * p) m (2 ^ p) : ℝ) ≤ (3 + 1) * 2 ^ p :=
  complexityModulus_two_pow_le 1 one_pos

/-- **The lower bound at `p = 4`**: some change on `16` of the `256` inputs on eight bits moves
the complexity, so `ω_{8,1}(16) ≥ 1`. -/
example : 1 ≤ complexityModulus interpretation (2 * 4) 1 (2 ^ 4) := by
  have h := two_pow_le_sixteen_mul_complexityModulus (p := 4) le_rfl
  exact Nat.one_le_iff_ne_zero.2 fun h0 => by rw [h0] at h; exact absurd h (by norm_num)

/-! ### Axioms -/

/--
info: 'Cslib.Circuits.dist_complexity_le_complexityModulus' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms dist_complexity_le_complexityModulus

/--
info: 'Cslib.Circuits.complexityModulus_add_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms complexityModulus_add_le

/--
info: 'Cslib.Circuits.exists_dist_complexity_eq_complexityModulus' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_dist_complexity_eq_complexityModulus

/--
info: 'Cslib.Circuits.Boolean.complexityModulus_two_pow_single_output_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms complexityModulus_two_pow_single_output_le

/--
info: 'Cslib.Circuits.Boolean.complexityModulus_two_pow_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms complexityModulus_two_pow_le

/--
info: 'Cslib.Circuits.Boolean.two_pow_le_sixteen_mul_complexityModulus' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms two_pow_le_sixteen_mul_complexityModulus

/--
info: 'exists_hammingDist_le_and_hammingDist_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_hammingDist_le_and_hammingDist_le

end ComplexityTests.CircuitHamming.Continuity
