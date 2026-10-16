/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Probability/StatisticalDistance.lean`)

public import Cslib.Probability.StatisticalDistance
public import Complexity.Probability.PMF

/-!
# Statistical distance with public side information

Revealing a shared sample makes the joint distance exactly the average conditional distance.
Its square is bounded by the corresponding average squared distance.
These statements reuse the upstream finite-PMF metric and its enumeration instances.

## Main results

* `Cslib.Probability.PMF.abs_sum_mul_sub_le`: bounded-score changes under statistical distance.
* `Cslib.Probability.PMF.dist_bind_pair`: exact average distance with a shared public sample.
* `Cslib.Probability.PMF.dist_bind_pair_sq_le`: the squared-distance bound used in leftover hashing.

## References

Adapted from `Probability/StatisticalDistance.lean` on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`. The metric itself remains the upstream one.
-/

@[expose] public section

namespace Cslib.Probability.PMF

variable {α β : Type*}

/-- With a shared revealed input, distance is the average distance of the conditional outputs. -/
theorem dist_bind_pair [Fintype α] [Fintype β] (p : PMF α) (f g : α → PMF β) :
    dist (p.bind (fun a => (f a).map (a, ·)))
        (p.bind (fun a => (g a).map (a, ·))) =
      ∑ a, (p a).toReal * dist (f a) (g a) := by
  simp only [dist_eq, Fintype.sum_prod_type, PMF.map, Function.comp_def, bind_pair_apply,
    ENNReal.toReal_mul, ← mul_sub, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg,
    ← Finset.mul_sum, Finset.sum_div, mul_div_assoc]

/-- Squared distance with a shared revealed input is at most the average squared distance. -/
theorem dist_bind_pair_sq_le [Fintype α] [Fintype β] (p : PMF α) (f g : α → PMF β) :
    dist (p.bind (fun a => (f a).map (a, ·)))
        (p.bind (fun a => (g a).map (a, ·))) ^ 2 ≤
      ∑ a, (p a).toReal * dist (f a) (g a) ^ 2 := by
  rw [dist_bind_pair]
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun a => (p a).toReal * dist (f a) (g a))
    (f := fun a => (p a).toReal) (g := fun a => (p a).toReal * dist (f a) (g a) ^ 2)
    (fun _ _ => ENNReal.toReal_nonneg)
    (fun _ _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))
    (fun _ _ => by ring_nf; rfl)
  simpa only [sum_toReal, one_mul] using h

/-- Changing the distribution changes a bounded real-valued score by at most twice its
absolute bound times statistical distance. Signed prediction scores may use `bound = 1`. -/
theorem abs_sum_mul_sub_le [Fintype α] (p q : PMF α) (score : α → ℝ)
    {bound : ℝ} (hscore : ∀ a, |score a| ≤ bound) :
    |(∑ a, (p a).toReal * score a) - ∑ a, (q a).toReal * score a| ≤
      2 * bound * dist p q := by
  rw [← Finset.sum_sub_distrib]
  simp only [← sub_mul]
  calc
    _ ≤ ∑ a, |((p a).toReal - (q a).toReal) * score a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, |(p a).toReal - (q a).toReal| * bound := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hscore a) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, dist_eq]; ring

end Cslib.Probability.PMF
