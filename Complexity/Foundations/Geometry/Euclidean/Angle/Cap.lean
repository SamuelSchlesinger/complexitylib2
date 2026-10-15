/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Geometry/Euclidean/Angle/Unoriented/` and
-- `Mathlib/Analysis/InnerProductSpace/Basic.lean`)

public import Complexity.Init
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.Data.Finset.Prod
import Complexity.Foundations.Analysis.SpecialFunctions.Arccos
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

/-!
# Angles within a spherical cap

Fix a unit vector `x` of a real inner product space and `κ ≥ 0`. The unit vectors `y` with
`κ ≤ ⟪y, x⟫` form the spherical cap of angular radius `arccos κ` around `x`. Vectors in such a
cap are close to each other:

* `InnerProductGeometry.two_mul_sq_sub_one_le_inner`: two of them have inner product at least
  `2 κ ^ 2 - 1 = cos (2 arccos κ)`, by the triangle inequality for angles.
* `InnerProductGeometry.le_sum_offDiag_inner`: `n` of them have inner products summing, over the
  ordered pairs of distinct indices, to at least `n ^ 2 κ ^ 2 - n`. Indeed their sum `S` has
  `‖S‖ ≥ ⟪S, x⟫ ≥ n κ`, and `‖S‖ ^ 2` is `n` plus that sum (`norm_sum_sq_real`).
* `InnerProductGeometry.sum_offDiag_angle_le`: if moreover `κ ≥ √2 / 2`, these inner products lie
  in `[0, 1]`, where `arccos` is concave, so by Jensen's inequality the angles over the
  `n (n - 1)` ordered pairs sum to at most `n (n - 1) arccos ((n κ ^ 2 - 1) / (n - 1))`.

The last bound beats the pairwise bound `2 arccos κ` on every angle: for `n = 3` the average
inner product is at least `(3 κ ^ 2 - 1) / 2`, which exceeds `2 κ ^ 2 - 1` by `(1 - κ ^ 2) / 2`.

## Main results

* `norm_sum_sq_real`: the squared norm of a finite sum, expanded over the diagonal and the
  ordered pairs of distinct indices.
* `InnerProductGeometry.two_mul_sq_sub_one_le_inner`: the pairwise bound in a cap.
* `InnerProductGeometry.le_sum_offDiag_inner`: the bound on the sum of the pairwise inner
  products in a cap.
* `InnerProductGeometry.sum_offDiag_angle_le`: the bound on the sum of the pairwise angles in a
  cap.
-/

@[expose] public section

open Real Finset
open scoped RealInnerProductSpace

variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The squared norm of a finite sum is the sum of the squared norms plus the inner products
over the ordered pairs of distinct indices. -/
theorem norm_sum_sq_real (s : Finset ι) (f : ι → V) :
    ‖∑ i ∈ s, f i‖ ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2 + ∑ p ∈ s.offDiag, ⟪f p.1, f p.2⟫ := by
  classical
  rw [← real_inner_self_eq_norm_sq, sum_inner,
    ← sum_congr rfl fun i _ => (inner_sum s f (f i)).symm,
    ← sum_product' (f := fun i j => ⟪f i, f j⟫), ← diag_union_offDiag,
    sum_union (disjoint_diag_offDiag s), sum_diag]
  simp only [real_inner_self_eq_norm_sq]

namespace InnerProductGeometry

/-- The angle between unit vectors is the `arccos` of their inner product. -/
theorem angle_eq_arccos_inner_of_norm_eq_one {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    angle x y = arccos ⟪x, y⟫ := by
  simp [angle, hx, hy]

/-- **Two vectors in a cap.** Two unit vectors whose inner products with a unit vector `x` are at
least `κ ≥ 0` have inner product at least `2 κ ^ 2 - 1`: each makes an angle at most `arccos κ`
with `x`, so they make an angle at most `2 arccos κ ≤ π` with each other. -/
theorem two_mul_sq_sub_one_le_inner {x y z : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1)
    {κ : ℝ} (hκ : 0 ≤ κ) (hyx : κ ≤ ⟪y, x⟫) (hzx : κ ≤ ⟪z, x⟫) :
    2 * κ ^ 2 - 1 ≤ ⟪y, z⟫ := by
  have hκ1 : κ ≤ 1 := hyx.trans ((real_inner_le_norm y x).trans_eq (by rw [hy, hx, one_mul]))
  have hyx' : angle y x ≤ arccos κ := by
    rw [angle_eq_arccos_inner_of_norm_eq_one hy hx]
    exact arccos_le_arccos hyx
  have hxz' : angle x z ≤ arccos κ := by
    rw [angle_comm, angle_eq_arccos_inner_of_norm_eq_one hz hx]
    exact arccos_le_arccos hzx
  have hπ : 2 * arccos κ ≤ π := by linarith [arccos_le_pi_div_two.2 hκ]
  rw [inner_eq_cos_angle_of_norm_eq_one hy hz]
  calc 2 * κ ^ 2 - 1 = cos (2 * arccos κ) := by
        rw [cos_two_mul, cos_arccos (by linarith) hκ1]
    _ ≤ cos (angle y z) := cos_le_cos_of_nonneg_of_le_pi (angle_nonneg y z) hπ
        ((angle_le_angle_add_angle y x z).trans (by linarith))

/-- **Many vectors in a cap.** If `n` unit vectors have inner products at least `κ ≥ 0` with a
unit vector, their inner products over the ordered pairs of distinct indices sum to at least
`n ^ 2 κ ^ 2 - n`. -/
theorem le_sum_offDiag_inner {x : V} (hx : ‖x‖ = 1) {s : Finset ι} {y : ι → V}
    (hy : ∀ i ∈ s, ‖y i‖ = 1) {κ : ℝ} (hκ : 0 ≤ κ) (hyx : ∀ i ∈ s, κ ≤ ⟪y i, x⟫) :
    (#s : ℝ) ^ 2 * κ ^ 2 - #s ≤ ∑ p ∈ s.offDiag, ⟪y p.1, y p.2⟫ := by
  have hlin : #s * κ ≤ ‖∑ i ∈ s, y i‖ :=
    calc #s * κ ≤ ∑ i ∈ s, ⟪y i, x⟫ := by simpa using card_nsmul_le_sum s _ κ hyx
      _ = ⟪∑ i ∈ s, y i, x⟫ := (sum_inner s y x).symm
      _ ≤ ‖∑ i ∈ s, y i‖ := (real_inner_le_norm _ x).trans_eq (by rw [hx, mul_one])
  have hn : ∑ i ∈ s, ‖y i‖ ^ 2 = #s := by
    rw [sum_congr rfl fun i hi => by rw [hy i hi, one_pow], sum_const, nsmul_one]
  have hsq := norm_sum_sq_real s y
  rw [hn] at hsq
  have h0 : 0 ≤ (#s : ℝ) * κ := by positivity
  nlinarith [mul_le_mul hlin hlin h0 (h0.trans hlin)]

/-- **Angles in a cap.** If `n` unit vectors have inner products at least `κ ≥ √2 / 2` with a
unit vector, the angles between them over the `n (n - 1)` ordered pairs of distinct indices sum
to at most `n (n - 1) arccos ((n κ ^ 2 - 1) / (n - 1))`. -/
theorem sum_offDiag_angle_le {x : V} (hx : ‖x‖ = 1) {s : Finset ι} {y : ι → V}
    (hy : ∀ i ∈ s, ‖y i‖ = 1) {κ : ℝ} (hκ : √2 / 2 ≤ κ) (hyx : ∀ i ∈ s, κ ≤ ⟪y i, x⟫) :
    ∑ p ∈ s.offDiag, angle (y p.1) (y p.2) ≤
      #s * (#s - 1) * arccos ((#s * κ ^ 2 - 1) / (#s - 1)) := by
  have hκ0 : 0 ≤ κ := (by positivity : (0 : ℝ) ≤ √2 / 2).trans hκ
  have hκ2 : 1 ≤ 2 * κ ^ 2 := by
    have h := mul_le_mul hκ hκ (by positivity) hκ0
    rw [div_mul_div_comm, mul_self_sqrt zero_le_two] at h
    nlinarith
  have hoff : ∀ p ∈ s.offDiag, ‖y p.1‖ = 1 ∧ ‖y p.2‖ = 1 ∧ κ ≤ ⟪y p.1, x⟫ ∧ κ ≤ ⟪y p.2, x⟫ :=
    fun p hp => by
      obtain ⟨h1, h2, -⟩ := mem_offDiag.1 hp
      exact ⟨hy _ h1, hy _ h2, hyx _ h1, hyx _ h2⟩
  rw [sum_congr rfl fun p hp => angle_eq_arccos_inner_of_norm_eq_one (hoff p hp).1
    (hoff p hp).2.1]
  rcases lt_or_ge #s 2 with hs | hs
  · -- At most one vector: there are no pairs.
    have : s.offDiag = ∅ := by
      rw [← card_eq_zero, offDiag_card]
      interval_cases #s <;> rfl
    have hs' : (#s : ℝ) * (#s - 1) = 0 := by
      interval_cases #s <;> simp
    rw [this, sum_empty, hs', zero_mul]
  have hs1 : (0 : ℝ) < #s - 1 := by
    have : (2 : ℝ) ≤ #s := by exact_mod_cast hs
    linarith
  have hcard : (#s.offDiag : ℝ) = #s * (#s - 1) := by
    rw [offDiag_card, Nat.cast_sub (Nat.le_mul_self _), Nat.cast_mul]
    ring
  rw [← hcard]
  refine sum_arccos_le_card_mul_arccos _ (fun p hp => ⟨?_, ?_⟩) ?_
  · obtain ⟨h1, h2, h3, h4⟩ := hoff p hp
    linarith [two_mul_sq_sub_one_le_inner hx h1 h2 hκ0 h3 h4]
  · obtain ⟨h1, h2, -⟩ := hoff p hp
    exact (real_inner_le_norm _ _).trans_eq (by rw [h1, h2, one_mul])
  · rw [hcard, mul_assoc, mul_div_cancel₀ _ hs1.ne']
    linarith [le_sum_offDiag_inner hx hy hκ0 hyx]

end InnerProductGeometry
