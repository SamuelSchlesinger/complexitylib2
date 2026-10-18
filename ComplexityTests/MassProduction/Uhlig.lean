/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.MassProduction.Uhlig

/-!
# Uhlig mass-production clients

These clients exercise the recovery code at equal and reversed requests, the vanishing boundary
position, a concrete instance of the layer recursion, families of different circuits on disjoint
blocks, and copy depths on both sides of the `d(n) log₂ n = o(n)` boundary. The theorem then
applies to a superpolynomial number of copies. Axiom checks record the headline dependencies.
-/

namespace ComplexityTests.MassProduction.Uhlig

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.MassProduction
open Cslib.Circuits.Boolean.MassProduction.Uhlig Filter

/-! ### The recovery code -/

/-- The sequence `true, false, true` followed by zeros. -/
private def bits (i : ℕ) : Bool := i == 0 || i == 2

-- Adjacent sums, including the final position that repeats the last bit.
example : (List.range 4).map (code bits) = [true, true, true, true] := by decide

-- Equal requests use complementary position sets: an initial and a final segment.
example : (List.range 4).map (first 1 1) = [true, true, false, false] := by decide
example : (List.range 4).map (second 1 1) = [false, false, true, true] := by decide

-- Reversed requests swap the roles: the first request now uses the final segment.
example : (List.range 4).map (first 2 0) = [false, false, false, true] := by decide
example : (List.range 4).map (second 2 0) = [true, false, false, false] := by decide

-- Both requests recover their bits from the code.
example : ∑ j ∈ Finset.range 4, (first 2 0 j && code bits j) = bits 2 :=
  sum_first_code (by decide) (by decide) 0
example : ∑ j ∈ Finset.range 4, (second 2 0 j && code bits j) = bits 0 :=
  sum_second_code (by decide) (by decide) 2

-- No position serves both requests, for every pair of requests.
example (a b j : ℕ) (h : first a b j = true) : second a b j = false :=
  second_eq_false_of_first h

-- A sequence that does not vanish at `M` breaks final-segment recovery.
example : ∑ j ∈ Finset.Ico 1 3, code (fun _ => true) j ≠ true := by decide

-- Restrictions vanish beyond the last prefix, the boundary used by final segments.
example (f : BooleanFunction (2 + 3)) (z : BitString 3) : restriction f z 4 = false :=
  restriction_two_pow f z

/-! ### Circuit families -/

private def notGate : Circuit signature 1 1 := Circuit.oneGate .not (fun _ => 0)
private def andGate : Circuit signature 1 1 := ⟨.gate (.gate .empty
  ⟨.const true, Fin.elim0⟩) ⟨.and, fun i => if i = 0 then .input 0 else .gate 0⟩, fun _ => .gate 1⟩

-- Different members keep their own costs; the constant is charged by size but not by
-- nonconstant cost.
example : (Circuit.parallelFamily ![notGate, andGate]).size = 3 := by
  simp [notGate, andGate, Fin.sum_univ_two]

example : (Circuit.parallelFamily ![notGate, andGate]).program.cost nonconstantCost = 2 := by
  rw [Circuit.cost_program_parallelFamily]
  rfl

example : (Circuit.parallelFamily ![notGate, andGate]).eval interpretation ![false, true] =
    ![true, true] := by decide

-- The empty family has no gates.
example (cs : Fin 0 → Circuit signature 3 2) : (Circuit.parallelFamily cs).size = 0 := by simp

/-! ### One layer -/

/-- A function of no inputs is a constant, which has one copy of size one. -/
private theorem complexity_directProduct_zero_inputs (g : BooleanFunction 0) :
    complexity interpretation (directProduct g 1) ≤ 1 :=
  complexity_directProduct_one_le.trans
    (Synthesis.of_forall_eq_const (s := inputs 0) (g ![])
      fun _ => congrArg g (Subsingleton.elim _ _)).complexity_le

-- The layer hypothesis is satisfiable: two copies of any one-input function.
example (f : BooleanFunction (1 + 0)) :
    complexity interpretation (directProduct f (2 * 1)) ≤
      (2 ^ 1 + 1) * 1 + 1 * layerOverhead 1 0 :=
  complexity_directProduct_two_mul_le complexity_directProduct_zero_inputs f

-- Two layers from single copies on no inputs: four copies of every function on two inputs.
example (f : BooleanFunction (2 * 1 + 0)) :
    complexity interpretation (directProduct f (2 ^ 2)) ≤
      (2 ^ 1 + 1) ^ 2 * (1 + 2 * 2 ^ 2 * layerOverhead 1 1) :=
  complexity_directProduct_two_pow_le complexity_directProduct_zero_inputs 2 _ rfl
    (fun e he => layerOverhead_mono (by omega)) f

/-! ### Copy depths -/

-- Single copies: Lupanov's coefficient one.
example : IsUhligDepth fun _ => 0 := fun _ => Eventually.of_forall fun _ => by simp

/-- `n / log₂² n` layers satisfy the depth condition, so `2 ^ (n / log₂² n)` copies of any
function, a superpolynomial number, fit within the asymptotic single-copy ceiling `2 ^ n / n`. -/
theorem isUhligDepth_div_log_sq : IsUhligDepth fun n => n / Nat.log 2 n ^ 2 := by
  intro c
  filter_upwards [eventually_ge_atTop (2 ^ (c + 1))] with n hn
  have hlog : c + 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hn
  set L := Nat.log 2 n
  calc c * (n / L ^ 2) * L ≤ L * (n / L ^ 2) * L := by gcongr; omega
    _ = n / L ^ 2 * L ^ 2 := by ring
    _ ≤ n := Nat.div_mul_le_self n _

/-- With `n / log₂ n` layers the depth condition fails: the multiplier two is never met. -/
theorem not_isUhligDepth_div_log : ¬ IsUhligDepth fun n => n / Nat.log 2 n := by
  intro h
  obtain ⟨n, hn, h4⟩ := ((h 2).and (eventually_ge_atTop 4)).exists
  simp only at hn
  have hL : 0 < Nat.log 2 n := Nat.log_pos (by norm_num) (by omega)
  have hlt : n < n / Nat.log 2 n * Nat.log 2 n + Nat.log 2 n := Nat.lt_div_mul_add hL
  have hsmall : 2 * Nat.log 2 n ≤ n :=
    (Nat.mul_le_pow (by decide : 2 ≠ 1) _).trans (Nat.pow_log_le_self 2 (by omega))
  have e : 2 * (n / Nat.log 2 n) * Nat.log 2 n = 2 * (n / Nat.log 2 n * Nat.log 2 n) := by ring
  omega

-- The theorem applies to the superpolynomial copy budget.
example (P : ℕ) : ∀ᶠ n in atTop, ∀ (f : BooleanFunction n) (k : ℕ),
    k ≤ 2 ^ (n / Nat.log 2 n ^ 2) →
      (P * n : ℕ∞) * massComplexity f k ≤ ((P + 1) * 2 ^ n : ℕ) :=
  eventually_mul_massComplexity_le isUhligDepth_div_log_sq P

-- Zero copies are included and cost nothing.
example (f : BooleanFunction 5) : massComplexity f 0 = 0 := massComplexity_zero

/-! ### Axioms -/

/--
info: 'Cslib.Circuits.Boolean.MassProduction.eventually_mul_massComplexity_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eventually_mul_massComplexity_le

/--
info: 'Cslib.Circuits.Boolean.MassProduction.eventually_mul_complexity_directProduct_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eventually_mul_complexity_directProduct_le

/--
info: 'Cslib.Circuits.Boolean.MassProduction.mul_complexity_directProduct_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms mul_complexity_directProduct_le

/--
info: 'Cslib.Circuits.Boolean.MassProduction.complexity_directProduct_two_pow_le' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms complexity_directProduct_two_pow_le

/--
info: 'Cslib.Circuits.Boolean.MassProduction.Uhlig.complexity_directProduct_two_mul_le' depends
on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms complexity_directProduct_two_mul_le

/--
info: 'Cslib.Circuits.Circuit.eval_parallelFamily_apply' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Circuit.eval_parallelFamily_apply

end ComplexityTests.MassProduction.Uhlig
