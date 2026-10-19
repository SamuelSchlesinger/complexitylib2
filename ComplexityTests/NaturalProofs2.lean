/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.GGM.Circuit
import Cslib.Crypto.Primitives.PRG.Basic

/-! The GGM family on fixed-width labels for a concrete toy generator, its agreement with the list
construction, the bounds on its circuits, non-vacuity of the security hypotheses, the identity and
constant families as witnesses that exponential security is consistent and has content, and the
axioms of the headline theorems. -/

namespace ComplexityTests.NaturalProofs2

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Crypto Cslib.MCSP Filter Finset
open scoped NNReal

/-! ### A toy generator

The generator `s ↦ s ++ !s` on one bit, which is not pseudorandom: its children are the seed and
its complement, so the GGM function with key `s` is `s` plus the parity of the input. -/

/-- The one-bit generator `s ↦ (s, !s)`. -/
def toy : PRG.Generator (BitString 1) (BitString (2 * 1)) :=
  ⟨fun s i => if (i : ℕ) = 0 then s 0 else !s 0⟩

example : GGM.booleanFamily toy 3 (fun _ => false) (fun i => decide ((i : ℕ) ≠ 1)) = false := by
  decide

example : GGM.booleanFamily toy 3 (fun _ => true) (fun i => decide ((i : ℕ) = 1)) = false := by
  decide

example : GGM.booleanFamily toy 2 (fun _ => true) (fun _ => false) = true := by
  decide

/-- The fixed-width evaluation is the list construction with the generator read on lists. -/
example : List.ofFn (GGM.evalBits toy (fun _ => true) (fun i : Fin 2 => decide ((i : ℕ) = 0))) =
    GGM.eval (GGM.listGenerator toy) [true] [true, false] :=
  GGM.ofFn_evalBits toy _ _

example : GGM.eval (GGM.listGenerator toy) [true] [true, false] = [false] := by
  decide

/-- The members of the toy family on `n` inputs have circuits with `n (C + 4) + 2` gates. -/
example (n : ℕ) (seed : BitString 1) :
    complexity interpretation (single (GGM.booleanFamily toy n seed)) ≤
      n * (complexity interpretation ⇑toy + 4) + 2 := by
  simpa using GGM.complexity_booleanFamily_le toy n seed

/-! ### The security theorem

Every generator is secure with error `1`, so the hypothesis of the security theorem can be met; the
conclusion then bounds the advantage by `2 ^ n - 1`. -/

example (n t : ℕ) :
    (truthTableGenerator (GGM.booleanFamily toy n)).Secure (IsCircuitTest t) ((2 ^ n - 1) * 1) :=
  GGM.secure_truthTableGenerator_booleanFamily (toy.secure_one _)

/-- Subexponential security constrains only `m ≥ 1`: at `m = 0` it asks for error `1`. -/
example (G : ∀ k, PRG.Generator (BitString k) (BitString (2 * k))) (k : ℕ) :
    (G k).Secure (IsCircuitTest (2 ^ 0)) (2 ^ 0)⁻¹ := by
  simpa using (G k).secure_one _

/-- Security against circuits of size `2 ^ (k ^ ε)` with `ε = 1 / 2` gives subexponential security
with `d = 2`. -/
example (G : ∀ k, PRG.Generator (BitString k) (BitString (2 * k)))
    (hG : ∀ k, (G k).Secure (IsCircuitTest ⌊(2 : ℝ) ^ ((k : ℝ) ^ (1 / 2 : ℝ))⌋₊)
      ((2 : ℝ≥0) ^ ((k : ℝ) ^ (1 / 2 : ℝ)))⁻¹) :
    PRG.IsSubexponentiallySecure G 2 :=
  PRG.IsSubexponentiallySecure.of_rpow (by norm_num) hG

/-! ### Exponential security is consistent and has content

The identity family, keyed by the functions themselves, has uniformly random truth tables and so
is exponentially secure; its members are not of polynomial size, so it does not contradict
`not_isUseful_PPoly_of_isNatural`. A constant family is not exponentially secure: a test reading
one bit of the truth table has advantage `1 / 2`. -/

/-- The identity family is exponentially secure. -/
example : IsExponentiallySecure fun n (f : BooleanFunction n) => f := by
  refine fun c => Eventually.of_forall fun n => ?_
  refine ((truthTableGenerator fun f : BooleanFunction n => f).secure_zero_of_outputDist_eq ?_
    _).mono bot_le
  exact Probability.PMF.uniformOfFintype_map_equiv (truthTable n)

/-- A test reading one bit accepts half of all truth tables. -/
theorem toReal_idealExperiment_apply_zero (n : ℕ) :
    (PRG.Generator.idealExperiment (fun T : BitString (2 ^ n) => PMF.pure (T 0)) true).toReal =
      1 / 2 := by
  obtain ⟨N, hN⟩ : ∃ N, 2 ^ n = N + 1 := ⟨2 ^ n - 1, (Nat.succ_pred_eq_of_pos (by positivity)).symm⟩
  rw [PRG.Generator.toReal_idealExperiment_pure, dens, ← Fintype.piFinset_univ,
    Fintype.card_filter_piFinset_const_eq_of_mem _ _ (mem_univ true)]
  simp only [card_univ, Fintype.card_bool, Fintype.card_fin, Fintype.card_pi, prod_const]
  rw [hN, Nat.add_sub_cancel, pow_succ]
  push_cast
  field_simp

/-- A constant family is not exponentially secure. -/
example : ¬ IsExponentiallySecure fun n (_ : Unit) => fun _ : BitString n => false := by
  intro h
  obtain ⟨n, hsec, hn⟩ := ((h 1).and (eventually_ge_atTop 2)).exists
  have htest : IsCircuitTest (2 ^ (1 * n)) fun T : BitString (2 ^ n) => PMF.pure (T 0) := by
    refine ⟨fun T => T 0, ?_, rfl⟩
    have h0 : (single fun T : BitString (2 ^ n) => T 0) = fun T => T ∘ fun _ : Fin 1 => 0 := rfl
    rw [h0, complexity_wiring]
    exact Nat.zero_le _
  have hadv := hsec _ htest
  rw [PRG.Generator.advantage, toReal_idealExperiment_apply_zero,
    PRG.Generator.toReal_realExperiment_pure] at hadv
  have hfalse : ({u : Unit | (truthTableGenerator fun _ (x : BitString n) => false) u 0 = true} :
      Finset Unit) = ∅ := by
    ext u
    simp
  rw [hfalse, dens_empty, NNRat.cast_zero, zero_sub, abs_neg, abs_of_pos (by norm_num)] at hadv
  have hsmall : (((2 ^ (1 * n))⁻¹ : ℝ≥0) : ℝ) ≤ 1 / 4 := by
    rw [one_mul, NNReal.coe_inv, NNReal.coe_pow, NNReal.coe_ofNat, one_div]
    exact inv_anti₀ (by norm_num) (by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right₀ one_le_two (by omega))
  linarith

/-! ### The barrier corollaries -/

/-- Under subexponentially secure generators of polynomial circuit complexity, the property of
needing more than `2 ^ n / (5 n)` gates is not `P/poly`-natural. -/
example {G : ∀ k, PRG.Generator (BitString k) (BitString (2 * k))} {d : ℕ}
    (hsize : PolynomiallyBounded fun k => complexity interpretation ⇑(G k))
    (hG : PRG.IsSubexponentiallySecure G d) :
    ¬ IsNatural PPoly fun n => {f : BooleanFunction n |
      2 ^ n / (5 * n) < complexity interpretation (single f)} := fun hC =>
  not_isUseful_PPoly_of_isNatural_of_generator hsize hG hC isUseful_PPoly_setOf_lt_complexity

/-! ### Axioms -/

/--
info: 'Cslib.Crypto.GGM.secure_truthTableGenerator_booleanFamily' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GGM.secure_truthTableGenerator_booleanFamily

/--
info: 'Cslib.Crypto.GGM.complexity_booleanFamily_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GGM.complexity_booleanFamily_le

/--
info: 'Cslib.Crypto.GGM.ofFn_evalBits' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GGM.ofFn_evalBits

/--
info: 'Cslib.Crypto.GGM.isExponentiallySecure_booleanFamily' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GGM.isExponentiallySecure_booleanFamily

/--
info: 'Cslib.Crypto.PRG.IsSubexponentiallySecure.of_rpow' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.IsSubexponentiallySecure.of_rpow

/--
info: 'Cslib.Circuits.Boolean.not_isUseful_PPoly_of_isNatural_of_generator' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.not_isUseful_PPoly_of_isNatural_of_generator

/--
info: 'Cslib.Circuits.Boolean.not_isNatural_PPoly_setOf_lt_complexity' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.not_isNatural_PPoly_setOf_lt_complexity

end ComplexityTests.NaturalProofs2
