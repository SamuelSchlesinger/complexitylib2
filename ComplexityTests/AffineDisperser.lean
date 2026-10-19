/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Combinatorics.AffineDisperser
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Affine dispersers from subspace polynomials: clients

These clients instantiate the cube-sum identities, the Moore finite-difference formula and the
covering lemma at small sizes, and apply the independent-sources theorem and the disperser theorem
to concrete Galois fields. The disperser instance takes `F = GF(2 ^ 400)`, whose proper subfields
have at most `2 ^ 200` elements, `r = 100` blocks and `t = 10`; the dimension bound is then
`38100 < 40000 = dim F ^ 100`, so the whole space is a non-vacuous instance. Axiom checks record
the headline dependencies.
-/

namespace ComplexityTests.AffineDisperser

open Cslib Cslib.FiniteField Cslib.AffineDisperser Module

/-! ### Small identities -/

-- One affine form in one Boolean variable: the cube sum is its linear coefficient.
example (a b : ZMod 2) :
    ∑ c : Fin 1 → ZMod 2, ∏ _p : Fin 1, (a + ∑ v, c v • b) = b := by
  rw [sum_cube_prod_affine_eq_permanent (κ := Fin 1) (fun _ => a) (fun _ _ => b)]
  simp [Matrix.permanent_unique]

-- The first Moore determinant is the vector itself: `∑_{c ∈ 𝔽₂} (a + c u) = u`.
example (a u : GaloisField 2 3) :
    ∑ c : Fin 1 → ZMod 2, (a + ∑ l, c l • (fun _ => u) l) ^ (2 ^ 1 - 1) = u := by
  rw [sum_cube_pow_eq_det_mooreMatrix]
  simp [mooreMatrix, Matrix.det_unique]

-- In characteristic two the determinant is the permanent.
example (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) : M.det = M.permanent := det_eq_permanent M

-- Covering assignments between equal block sets: `J = I` is forced.
example (I : Finset (Fin 3)) (ℓ : (Σ j : I, Fin (3 - j)) → Option (Σ i : I, Fin (3 - i)))
    (hcov : ∀ v, ∃ p, ℓ p = some v) (hmono : ∀ p v, ℓ p = some v → (v.1 : Fin 3) ≤ p.1) :
    I = I :=
  eq_of_covering (fun i => 3 - i)
    (fun i j hij => show 3 - (j : ℕ) < 3 - (i : ℕ) by have := j.2; have : (i : ℕ) < j := hij; omega)
    (fun i => show 0 < 3 - (i : ℕ) by have := i.2; omega) I I rfl ℓ hcov hmono

-- Pivot spaces of the whole space `(ZMod 2) ^ 2` add up to its dimension.
example : ∑ i, finrank (ZMod 2) (pivotSpace (⊤ : Submodule (ZMod 2) (Fin 2 → ZMod 2)) i) = 2 := by
  rw [sum_finrank_pivotSpace, finrank_top, Module.finrank_fin_fun]

/-! ### Subfields of `GF(2 ^ n)` -/

theorem finrank_galoisField (n : ℕ) (hn : n ≠ 0) : finrank (ZMod 2) (GaloisField 2 n) = n :=
  GaloisField.finrank 2 hn

-- Proper subfields of `GF(2 ^ 400)` have at most `2 ^ 200` elements.
theorem card_subfield_galoisField_le (K : Subfield (GaloisField 2 400)) (hK : K ≠ ⊤) :
    Nat.card K ≤ 2 ^ 200 :=
  card_subfield_le (finrank_galoisField 400 (by norm_num)) K hK

/-! ### The independent-sources theorem on `GF(2 ^ 5)` -/

-- The whole field (dimension `5`), Moore pairs (`k = 2`): `5 < 5 + (5 - 2)`.
example : ∃ u : Fin 1 → Fin 2 → GaloisField 2 5, (∀ i l, u i l ∈ (⊤ : Submodule (ZMod 2) _)) ∧
    Algebra.trace (ZMod 2) (GaloisField 2 5) (1 * ∏ i, (mooreMatrix (u i)).det) ≠ 0 := by
  have hn := finrank_galoisField 5 (by norm_num)
  refine exists_trace_mul_prod_det_mooreMatrix_ne_zero hn
    (fun K hK => card_subfield_le hn K hK) (fun _ => ⊤) (fun _ => 2) (fun _ => le_rfl)
    (fun _ => ?_) (fun _ => ?_) 0 ?_ one_ne_zero <;>
    simp [finrank_top, hn]

/-! ### The disperser theorem on `GF(2 ^ 400) ^ 100` -/

/-- With `n = 400`, `s = 200`, `r = 100` and `t = 10` the dimension bound is
`100 * 200 + 100 * 101 + 400 * 10 + 400 * 100 / 10 = 38100`, below the dimension `40000` of the
whole space. -/
theorem exists_traceSym_ne_top :
    ∃ x ∈ (⊤ : AffineSubspace (ZMod 2) (Fin 100 → GaloisField 2 400)),
      ∃ y ∈ (⊤ : AffineSubspace (ZMod 2) (Fin 100 → GaloisField 2 400)),
        traceSym (1 : GaloisField 2 400) 100 10 x ≠ traceSym 1 100 10 y := by
  have hn := finrank_galoisField 400 (by norm_num)
  refine exists_traceSym_ne (s := 200) hn card_subfield_galoisField_le one_ne_zero
    (by norm_num) ⊤ ?_
  rw [AffineSubspace.direction_top, finrank_top, Module.finrank_pi_fintype]
  simp [hn]

/-! ### Axioms -/

/--
info: 'Cslib.AffineDisperser.exists_traceSym_ne' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_traceSym_ne

/--
info: 'Cslib.AffineDisperser.exists_trace_mul_prod_det_mooreMatrix_ne_zero' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_trace_mul_prod_det_mooreMatrix_ne_zero

/--
info: 'Cslib.AffineDisperser.eq_of_covering' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eq_of_covering

/--
info: 'Cslib.FiniteField.exists_coeffPattern' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_coeffPattern

/--
info: 'Cslib.FiniteField.exists_isLinearized_range_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_isLinearized_range_eq

/--
info: 'Cslib.FiniteField.sum_cube_pow_eq_det_mooreMatrix' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sum_cube_pow_eq_det_mooreMatrix

/--
info: 'Cslib.sum_cube_prod_affine' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sum_cube_prod_affine

/--
info: 'ComplexityTests.AffineDisperser.exists_traceSym_ne_top' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_traceSym_ne_top

end ComplexityTests.AffineDisperser
