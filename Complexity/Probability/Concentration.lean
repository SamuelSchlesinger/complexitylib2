/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.Product
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Analysis.SpecialFunctions.Exp
import Complexity.Probability.PMF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Concentration for independent finite samples

The finite-PMF form of Hoeffding's inequality exposes ordinary sums and event probabilities.
Its proof uses Mathlib's product measures, independence, and sub-Gaussian concentration theorem.
No measurable-space choices appear in the client-facing statements.

## Main results

* `Cslib.Probability.PMF.pi_sum_le_mean_sub`: lower-tail concentration of bounded scores.
* `Cslib.Probability.PMF.pi_sum_ge_mean_add`: the corresponding upper-tail bound.
* `Cslib.Probability.PMF.pi_sum_abs_sub_mean_ge`: the two-sided bound.
* `Cslib.Probability.PMF.uniform_abs_sum_div_sub_expect_ge_le`: the two-sided bound for the
  empirical average of a `[-1, 1]`-valued function at independent uniform points.

## References

* [W. Hoeffding, *Probability inequalities for sums of bounded random variables*][Hoeffding1963].
* [T. Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*][Holenstein2006], Section 3.3 and Proposition 1.
  These bounded-score estimates support repetition in entropy extraction; they do not assert
  the full smoothed conditional-entropy statement of that proposition.

Adapted from Probability/Concentration.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, reusing Mathlib's sub-Gaussian estimates.

-/

@[expose] public section

namespace Cslib.Probability.PMF

open MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, Fintype (α i)]

/-- The sum of independent bounded scores falls below its mean only with exponentially small
probability. The scores and their means are finite sums; all probabilities are ordinary PMFs. -/
theorem pi_sum_le_mean_sub (p : ∀ i, PMF (α i)) (score : ∀ i, α i → ℝ)
    {bound ε : ℝ} (hbound : 0 ≤ bound)
    (hscore : ∀ i a, a ∈ (p i).support → score i a ∈ Set.Icc 0 bound) (hε : 0 ≤ ε) :
    ((pi p).toOuterMeasure {outcome |
      ∑ i, score i (outcome i) ≤ (∑ i, ∑ a, (p i a).toReal * score i a) - ε}).toReal ≤
        Real.exp (-2 * ε ^ 2 / (Fintype.card ι * bound ^ 2)) := by
  classical
  let (i : ι) : MeasurableSpace (α i) := ⊤
  let μ := (pi p).toMeasure
  let mean (i : ι) := ∑ a, (p i a).toReal * score i a
  have hmean (i : ι) : ∫ outcome, score i (outcome i) ∂μ = mean i := by
    rw [← integral_map (measurable_pi_apply i).aemeasurable
      (measurable_of_countable _).aestronglyMeasurable]
    simp only [μ, PMF.toMeasure_map _ _ (measurable_pi_apply i), pi_map_eval,
      PMF.integral_eq_sum, smul_eq_mul, mean]
  have hindep : iIndepFun (fun i outcome => mean i - score i (outcome i)) μ :=
    (iIndepFun_pi p).comp (fun i a => mean i - score i a)
      (fun _ => measurable_of_countable _)
  have hsub (i : ι) : HasSubgaussianMGF (fun outcome => mean i - score i (outcome i))
      ((‖bound‖₊ / 2) ^ 2) μ := by
    have hb : ∀ᵐ outcome ∂μ, score i (outcome i) ∈ Set.Icc 0 bound := by
      apply ae_iff_of_countable.mpr
      intro outcome houtcome
      rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)] at houtcome
      exact hscore i (outcome i) ((mem_support_pi_iff p outcome).mp houtcome i)
    have h := (hasSubgaussianMGF_of_mem_Icc
      (measurable_of_countable (fun outcome : ∀ i, α i => score i (outcome i))).aemeasurable
      hb).neg
    simpa only [sub_zero, hmean, Pi.neg_def, neg_sub] using h
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hindep
    (s := Finset.univ) (fun i _ => hsub i) hε
  have hevent : {outcome : ∀ i, α i | ε ≤ ∑ i, (mean i - score i (outcome i))} =
      {outcome | ∑ i, score i (outcome i) ≤ (∑ i, mean i) - ε} := by
    ext outcome
    simp only [Set.mem_ofPred_eq, Finset.sum_sub_distrib]
    constructor <;> intro h <;> linarith
  rw [hevent] at h
  simp only [measureReal_def, μ, PMF.toMeasure_apply_eq_toOuterMeasure_apply _
    ((Set.to_countable _).measurableSet), mean] at h
  convert h using 1
  congr 1
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, NNReal.coe_mul,
    NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm,
    Real.norm_of_nonneg hbound]
  ring

/-- The upper-tail counterpart of `pi_sum_le_mean_sub`, obtained by reflecting each score
within its bounded interval. -/
theorem pi_sum_ge_mean_add (p : ∀ i, PMF (α i)) (score : ∀ i, α i → ℝ)
    {bound ε : ℝ} (hbound : 0 ≤ bound)
    (hscore : ∀ i a, a ∈ (p i).support → score i a ∈ Set.Icc 0 bound) (hε : 0 ≤ ε) :
    ((pi p).toOuterMeasure {outcome |
      (∑ i, ∑ a, (p i a).toReal * score i a) + ε ≤ ∑ i, score i (outcome i)}).toReal ≤
        Real.exp (-2 * ε ^ 2 / (Fintype.card ι * bound ^ 2)) := by
  have hmean (i : ι) : ∑ a, (p i a).toReal * (bound - score i a) =
      bound - ∑ a, (p i a).toReal * score i a := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_toReal, one_mul]
  have h := pi_sum_le_mean_sub p (fun i a => bound - score i a) hbound
    (fun i a ha => ⟨sub_nonneg.mpr (hscore i a ha).2, sub_le_self _ (hscore i a ha).1⟩) hε
  simp only [hmean, Finset.sum_sub_distrib] at h
  convert h using 1
  congr 2
  ext outcome
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro h <;> linarith

/-- The two-sided finite Hoeffding bound, with an explicit factor of two for the two tails. -/
theorem pi_sum_abs_sub_mean_ge (p : ∀ i, PMF (α i)) (score : ∀ i, α i → ℝ)
    {bound ε : ℝ} (hbound : 0 ≤ bound)
    (hscore : ∀ i a, a ∈ (p i).support → score i a ∈ Set.Icc 0 bound) (hε : 0 ≤ ε) :
    ((pi p).toOuterMeasure {outcome |
      ε ≤ |(∑ i, score i (outcome i)) - ∑ i, ∑ a, (p i a).toReal * score i a|}).toReal ≤
        2 * Real.exp (-2 * ε ^ 2 / (Fintype.card ι * bound ^ 2)) := by
  let lower : Set (∀ i, α i) := {outcome | ∑ i, score i (outcome i) ≤
    (∑ i, ∑ a, (p i a).toReal * score i a) - ε}
  let upper : Set (∀ i, α i) := {outcome | (∑ i, ∑ a, (p i a).toReal * score i a) + ε ≤
    ∑ i, score i (outcome i)}
  have hevent : {outcome | ε ≤
      |(∑ i, score i (outcome i)) - ∑ i, ∑ a, (p i a).toReal * score i a|} =
      lower ∪ upper := by
    ext outcome
    simp only [Set.mem_ofPred_eq, Set.mem_union, le_abs, lower, upper]
    constructor <;> rintro (h | h)
    · right; linarith
    · left; linarith
    · right; linarith
    · left; linarith
  rw [hevent]
  have hunion := ENNReal.toReal_le_add
    (measure_union_le (μ := (pi p).toOuterMeasure) lower upper)
    (toOuterMeasure_ne_top _ _) (toOuterMeasure_ne_top _ _)
  have hlower := pi_sum_le_mean_sub p score hbound hscore hε
  have hupper := pi_sum_ge_mean_add p score hbound hscore hε
  dsimp only [lower, upper] at hunion
  linarith

section Average

open Finset
open scoped BigOperators

/-- **Hoeffding's inequality for an empirical average**: the average of a function with values in
`[-1, 1]` at `m > 0` independent uniform points is off from its mean by at least `γ` with
probability at most `2 exp (-m γ² / 2)`. -/
theorem uniform_abs_sum_div_sub_expect_ge_le {m : ℕ} {α : Type*} [Fintype α] [Nonempty α]
    (s : α → ℝ) (hs : ∀ a, |s a| ≤ 1) (hm : 0 < m) {γ : ℝ} (hγ : 0 ≤ γ) :
    (PMF.uniformOfFintype (Fin m → α)).toOuterMeasure
      {ω | γ ≤ |(∑ j, s (ω j)) / m - 𝔼 a, s a|} ≤
        ENNReal.ofReal (2 * Real.exp (-(m * γ ^ 2) / 2)) := by
  rw [ENNReal.le_ofReal_iff_toReal_le (toOuterMeasure_ne_top _ _) (by positivity)]
  have h := pi_sum_abs_sub_mean_ge (fun _ : Fin m => PMF.uniformOfFintype α)
    (fun _ a => 1 + s a) (bound := 2) (ε := m * γ) (by norm_num)
    (fun _ a _ => ⟨by linarith [(abs_le.1 (hs a)).1], by linarith [(abs_le.1 (hs a)).2]⟩)
    (by positivity)
  rw [pi_uniformOfFintype] at h
  have hmean : ∑ a, ((PMF.uniformOfFintype α) a).toReal * (1 + s a) = 1 + 𝔼 a, s a := by
    have hc : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, ← mul_sum,
      sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one, expect_eq_sum_div_card]
    field_simp
  simp only [hmean, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have hmR : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hevent : {ω : Fin m → α | γ ≤ |(∑ j, s (ω j)) / m - 𝔼 a, s a|} =
      {ω | m * γ ≤ |∑ j, (1 + s (ω j)) - m * (1 + 𝔼 a, s a)|} := by
    ext ω
    have hsum : ∑ j, (1 + s (ω j)) - m * (1 + 𝔼 a, s a) =
        m * ((∑ j, s (ω j)) / m - 𝔼 a, s a) := by
      simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      field_simp
      ring
    simp only [Set.mem_ofPred_eq, hsum, abs_mul, abs_of_pos hmR]
    exact (mul_le_mul_iff_right₀ hmR).symm
  rw [hevent]
  refine h.trans_eq ?_
  congr 2
  field_simp

end Average

end Cslib.Probability.PMF
