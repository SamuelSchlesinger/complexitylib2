/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.BooleanAnalysis.Bernoulli
import Mathlib.Tactic.Linarith

/-!
# Conditional sampling inside a union of masks

Let `P` and `Q` be independent random masks of rates `p` and `q`. Their union `S` has rate
`p + q - p q`, and conditionally on `S`, the difference `P \ Q` selects each coordinate of `S`
independently with rate `r = p (1 - q) / (p + q - p q)` (`bernoulliAverage_union_difference`).
The law is stated as an equality of finite expectations, with `(p + q - p q) r = p (1 - q)`, so it
avoids conditioning on events of probability zero and covers degenerate rates. This is the
coordinate-sampling step of Korten's mirror-set argument [Korten2026].

## Main results

* `Cslib.BooleanAnalysis.bernoulliAverage_union_difference`: the joint law of `P ∪ Q` and
  `P \ Q`.
* `Cslib.BooleanAnalysis.bernoulliAverage_union_difference_subtype`: the same, with the difference
  as a mask on the coordinates of the union.
* `Cslib.BooleanAnalysis.conditionalSamplingRate_bounds`: the conditional rate is a probability,
  at most `p / q`.

## References

* [O. Korten, *Top-Down Lower Bounds for All Depths*][Korten2026]
-/

@[expose] public section

namespace Cslib.BooleanAnalysis

private theorem bernoulliAverage_union_difference_fin {n : ℕ} (p q r : ℝ)
    (hr : (p + q - p * q) * r = p * (1 - q))
    (f : (Fin n → Bool) → (Fin n → Bool) → ℝ) :
    bernoulliAverage p (fun P => bernoulliAverage q (fun Q =>
      f (fun i => P i || Q i) (fun i => P i && !Q i))) =
      bernoulliAverage (p + q - p * q) (fun S => bernoulliAverage r (fun T =>
        f S (fun i => S i && T i))) := by
  induction n with
  | zero =>
    have he : f = fun _ _ => f (fun _ => false) (fun _ => false) := by
      funext x y
      congr 1 <;> exact Subsingleton.elim _ _
    rw [he]
    simp only [bernoulliAverage_const]
  | succ n ih =>
    have hc (op : Bool → Bool → Bool) (a b : Bool) (x y : Fin n → Bool) :
        (fun i => op ((Fin.cons a x : Fin (n + 1) → Bool) i)
          ((Fin.cons b y : Fin (n + 1) → Bool) i)) =
          Fin.cons (op a b) (fun i => op (x i) (y i)) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    rw [bernoulliAverage_cons p, bernoulliAverage_cons (p + q - p * q)]
    simp_rw [bernoulliAverage_cons (n := n) q,
      bernoulliAverage_cons (n := n) r, hc Bool.or,
      hc (fun a b => a && !b), hc Bool.and]
    simp only [Bool.or_false, Bool.or_true, Bool.not_false, Bool.not_true,
      Bool.and_false, Bool.and_true]
    simp_rw [bernoulliAverage_linear]
    rw [ih (fun S R => f (Fin.cons false S) (Fin.cons false R)),
      ih (fun S R => f (Fin.cons true S) (Fin.cons false R)),
      ih (fun S R => f (Fin.cons true S) (Fin.cons true R))]
    linear_combination
      -(bernoulliAverage (p + q - p * q) (fun S => bernoulliAverage r (fun T =>
        f (Fin.cons true S) (Fin.cons true (fun i => S i && T i)))) -
      bernoulliAverage (p + q - p * q) (fun S => bernoulliAverage r (fun T =>
        f (Fin.cons true S) (Fin.cons false (fun i => S i && T i))))) * hr

/-- **The joint law of `P ∪ Q` and `P \ Q`**: for independent masks `P` and `Q` of rates `p` and
`q`, the union and the difference are distributed as a mask `S` of rate `p + q - p q` and the
part inside `S` of an independent mask of rate `r`, when `(p + q - p q) r = p (1 - q)`. -/
theorem bernoulliAverage_union_difference {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q r : ℝ)
    (hr : (p + q - p * q) * r = p * (1 - q))
    (f : (ι → Bool) → (ι → Bool) → ℝ) :
    bernoulliAverage p (fun P => bernoulliAverage q (fun Q =>
      f (fun i => P i || Q i) (fun i => P i && !Q i))) =
      bernoulliAverage (p + q - p * q) (fun S => bernoulliAverage r (fun T =>
        f S (fun i => S i && T i))) := by
  let e := (Fintype.equivFin ι).symm
  rw [← bernoulliAverage_reindex e p,
    ← bernoulliAverage_reindex e (p + q - p * q)]
  simp_rw [← bernoulliAverage_reindex e q, ← bernoulliAverage_reindex e r]
  exact bernoulliAverage_union_difference_fin p q r hr (fun S R =>
    f (fun i => S (e.symm i)) (fun i => R (e.symm i)))

/-- For `p ≥ 0` and `0 < q ≤ 1`, the conditional rate of the difference is a probability, at most
`p / q`. -/
theorem conditionalSamplingRate_bounds {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) (hq' : q ≤ 1) :
    0 ≤ p * (1 - q) / (p + q - p * q) ∧
      p * (1 - q) / (p + q - p * q) ≤ p / q ∧
      p * (1 - q) / (p + q - p * q) ≤ 1 := by
  have htheta : 0 < p + q - p * q := by
    nlinarith [mul_nonneg hp (sub_nonneg.mpr hq')]
  refine ⟨div_nonneg (mul_nonneg hp (sub_nonneg.mpr hq')) htheta.le, ?_, ?_⟩
  · apply (div_le_div_iff₀ htheta hq).mpr
    nlinarith [mul_nonneg (sq_nonneg p) (sub_nonneg.mpr hq'), mul_nonneg hp (sq_nonneg q)]
  · apply (div_le_one htheta).mpr
    linarith

/-- The joint law of `P ∪ Q` and `P \ Q`, with the difference as a mask on the coordinates of the
union. -/
theorem bernoulliAverage_union_difference_subtype {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q r : ℝ)
    (hr : (p + q - p * q) * r = p * (1 - q))
    (f : (S : ι → Bool) → ({i // S i = true} → Bool) → ℝ) :
    bernoulliAverage p (fun P => bernoulliAverage q (fun Q =>
      f (fun i => P i || Q i) (fun i => P i && !Q i))) =
      bernoulliAverage (p + q - p * q) (fun S => bernoulliAverage r (f S)) := by
  change bernoulliAverage p (fun P => bernoulliAverage q (fun Q =>
    (fun S R => f S (fun i => R i)) (fun i => P i || Q i)
      (fun i => P i && !Q i))) = _
  rw [bernoulliAverage_union_difference p q r hr (fun S R => f S (fun i => R i))]
  congr 1
  funext S
  have he (T : ι → Bool) : (fun i : {i // S i = true} => S i && T i) =
      (fun i : {i // S i = true} => T i) := by
    funext i
    simp only [i.property, Bool.true_and]
  simp_rw [he]
  exact bernoulliAverage_restrict r S (f S)

end Cslib.BooleanAnalysis
