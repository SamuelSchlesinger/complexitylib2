/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Learning.Basic
public import Complexity.Foundations.BooleanAnalysis.SignApproximation
import Complexity.Probability.Concentration
import Complexity.Probability.PMF
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The low-degree algorithm

The **low-degree algorithm** of Linial, Mansour and Nisan [LinialMansourNisan1993]
[O'Donnell, Section 3.4][ODonnell2014] learns from uniform random examples every Boolean function
whose Fourier spectrum is concentrated on the sets of at most `t` coordinates. From `m` examples
`(x_j, y_j)` it estimates each Fourier coefficient `f̂(S)` with `#S ≤ t` by the empirical average
`c̃(S) = (1 / m) ∑_j y_j χ_S(x_j)`, reading the labels as signs (`Learning.empiricalCoeff`), and
outputs the sign of the truncated expansion `∑_{#S ≤ t} c̃(S) χ_S`
(`Learning.lowDegreeHypothesis`, `Learning.lowDegreeLearner`).

Each `c̃(S)` is an average of `m` independent values in `[-1, 1]` with mean `f̂(S)`, so by
Hoeffding's inequality it is off by at least `γ` with probability at most `2 exp (-m γ² / 2)`
(`Learning.uniform_abs_empiricalCoeff_sub_ge_le`). Let `N` be the number of sets of at most `t`
coordinates, at most `(n + 1) ^ t` for `n` coordinates (`Learning.card_filter_card_le_le`). By the
union bound, all `N` estimates are within `γ = √(ε / (2 N))` of their coefficients except with
probability at most `2 N exp (-m ε / (4 N))`, and then rounding the truncated expansion
misclassifies at most a fraction `N γ² + W = ε / 2 + W` of the points, where `W` is the Fourier
weight of `f` above degree `t` (`BitString.hammingDist_signRound_sum_mul_chi_div_le`). So if
`W ≤ ε / 2`, the hypothesis has error above `ε` with probability at most
`2 N exp (-m ε / (4 N))` (`Learning.uniform_error_lowDegreeHypothesis_gt_le`), which is at most
`δ` once `m ≥ (4 N / ε) log (2 N / δ)` (`Learning.lowDegreeLearner_learns`).

**Cost.** The algorithm uses `m` examples, computes `N` empirical coefficients, each an average of
`m` characters `χ_S(x_j)` of sets of at most `t` coordinates, so `O (N m t)` arithmetic operations
on the examples, and evaluates its hypothesis at a point with `O (N t)` operations. This count is
informal: the running time is not certified by a machine model here, and the theorems below bound
only the number of examples.

## Main definitions

* `Cslib.Learning.empiricalCoeff`: the empirical Fourier coefficient of a sample of examples.
* `Cslib.Learning.lowDegreeHypothesis`, `Cslib.Learning.lowDegreeLearner`: the low-degree
  algorithm.

## Main results

* `Cslib.Learning.card_filter_card_le_le`: there are at most `(n + 1) ^ t` sets of at most `t`
  of `n` coordinates.
* `Cslib.Learning.uniform_abs_empiricalCoeff_sub_ge_le`: estimating one Fourier coefficient.
* `Cslib.Learning.uniform_error_lowDegreeHypothesis_gt_le`: the failure probability of the
  low-degree algorithm.
* `Cslib.Learning.lowDegreeLearner_learns`: the low-degree algorithm learns the functions with
  Fourier weight at most `ε / 2` above degree `t` from `(4 N / ε) log (2 N / δ)` examples.

## References

* [N. Linial, Y. Mansour, N. Nisan, *Constant depth circuits, Fourier transform, and
  learnability*][LinialMansourNisan1993]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
* [W. Hoeffding, *Probability inequalities for sums of bounded random
  variables*][Hoeffding1963]
-/

@[expose] public section

namespace Cslib.Learning

open BitString Finset Cslib.Probability
open scoped BigOperators ENNReal

variable {ι : Type*} {m : ℕ}

/-! ### Counting the sets of low degree -/

/-- `∑_{i ≤ t} n ^ i ≤ (n + 1) ^ t`. -/
private theorem sum_range_pow_le (n t : ℕ) : ∑ i ∈ range (t + 1), n ^ i ≤ (n + 1) ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [sum_range_succ, pow_succ (n + 1) t]
    have h : n ^ (t + 1) ≤ (n + 1) ^ t * n := by
      rw [pow_succ]
      exact Nat.mul_le_mul_right n (Nat.pow_le_pow_left (Nat.le_succ n) t)
    linarith [mul_add ((n + 1) ^ t) n 1]

section Fintype

variable [Fintype ι]

/-- There are at most `(n + 1) ^ t` sets of at most `t` of `n` coordinates. -/
theorem card_filter_card_le_le (t : ℕ) :
    #{S : Finset ι | #S ≤ t} ≤ (Fintype.card ι + 1) ^ t := by
  classical
  have hfib : #{S : Finset ι | #S ≤ t} =
      ∑ i ∈ range (t + 1), #{S ∈ ({S : Finset ι | #S ≤ t} : Finset _) | #S = i} :=
    card_eq_sum_card_fiberwise fun S hS =>
      mem_coe.2 (mem_range.2 (Nat.lt_succ_of_le (mem_filter.1 (mem_coe.1 hS)).2))
  have hchoose (i : ℕ) (hi : i ∈ range (t + 1)) :
      #{S ∈ ({S : Finset ι | #S ≤ t} : Finset _) | #S = i} = (Fintype.card ι).choose i := by
    rw [← card_univ, ← card_powersetCard]
    congr 1
    ext S
    simp only [mem_filter, mem_univ, true_and, mem_powersetCard, subset_univ]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨h ▸ Nat.le_of_lt_succ (mem_range.1 hi), h⟩
  rw [hfib, sum_congr rfl hchoose]
  exact (sum_le_sum fun i _ => Nat.choose_le_pow _ i).trans (sum_range_pow_le _ t)

/-- The empty set has degree at most `t`, so there is at least one set of low degree. -/
theorem one_le_card_filter_card_le (t : ℕ) : 1 ≤ #{S : Finset ι | #S ≤ t} :=
  card_pos.2 ⟨∅, by simp⟩

end Fintype

/-! ### The algorithm -/

/-- A character times the sign of a label is `±1`, so adding one gives a value in `[0, 2]`. -/
private theorem one_add_signVal_mul_chi_mem (b : Bool) (S : Finset ι) (x : ι → Bool) :
    1 + signVal b * chi ℝ S x ∈ Set.Icc (0 : ℝ) 2 := by
  rw [chi_eq_signVal_parityOn, signVal_mul_signVal]
  split_ifs <;> norm_num

variable [Fintype ι] [DecidableEq ι]

/-- The empirical Fourier coefficient on `S` of a sample of labelled examples `(x_j, y_j)`: the
average of `y_j χ_S(x_j)` over the examples, reading the labels as signs. -/
noncomputable def empiricalCoeff (e : Fin m → (ι → Bool) × Bool) (S : Finset ι) : ℝ :=
  (∑ j, signVal (e j).2 * chi ℝ S (e j).1) / m

/-- The hypothesis of the low-degree algorithm of degree `t`: the sign of the empirical Fourier
expansion `∑_{#S ≤ t} c̃(S) χ_S` truncated at degree `t`. -/
noncomputable def lowDegreeHypothesis (t : ℕ) (e : Fin m → (ι → Bool) × Bool) :
    (ι → Bool) → Bool :=
  signRound fun x => ∑ S with #S ≤ t, empiricalCoeff e S * chi ℝ S x

variable (ι) in
/-- **The low-degree algorithm** of degree `t` from `m` examples: estimate the Fourier
coefficients on the sets of at most `t` coordinates empirically, and output the sign of the
truncated expansion. It is deterministic. -/
noncomputable def lowDegreeLearner (t m : ℕ) : Learner ι m :=
  Learner.ofHypothesis (lowDegreeHypothesis t)

/-! ### Estimating one coefficient -/

/-- The mean of `1 + f(x) χ_S(x)` over a uniform point is `1 + f̂(S)`. -/
private theorem sum_uniform_mul_one_add (f : (ι → Bool) → Bool) (S : Finset ι) :
    ∑ a, ((PMF.uniformOfFintype (ι → Bool)) a).toReal * (1 + signVal (f a) * chi ℝ S a) =
      1 + fourierCoeff (fun x => signVal (f x)) S := by
  have hc : (Fintype.card (ι → Bool) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, ← mul_sum,
    sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one, fourierCoeff,
    expect_eq_sum_div_card]
  field_simp

/-- **Estimating a Fourier coefficient**: from `m > 0` uniform random examples of `f`, the
empirical coefficient on `S` is off from `f̂(S)` by at least `γ` with probability at most
`2 exp (-m γ² / 2)`, by Hoeffding's inequality. -/
theorem uniform_abs_empiricalCoeff_sub_ge_le (f : (ι → Bool) → Bool) (S : Finset ι)
    (hm : 0 < m) {γ : ℝ} (hγ : 0 ≤ γ) :
    ((PMF.uniformOfFintype (Fin m → ι → Bool)).toOuterMeasure
      {x | γ ≤ |empiricalCoeff (examples f x) S - fourierCoeff (fun x => signVal (f x)) S|}).toReal
        ≤ 2 * Real.exp (-(m * γ ^ 2) / 2) := by
  have h := PMF.pi_sum_abs_sub_mean_ge
    (fun _ : Fin m => PMF.uniformOfFintype (ι → Bool))
    (fun _ a => 1 + signVal (f a) * chi ℝ S a) (bound := 2) (ε := m * γ) (by norm_num)
    (fun _ a _ => one_add_signVal_mul_chi_mem (f a) S a) (by positivity)
  rw [PMF.pi_uniformOfFintype] at h
  simp only [sum_uniform_mul_one_add, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have hmR : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hevent : {x : Fin m → ι → Bool |
      γ ≤ |empiricalCoeff (examples f x) S - fourierCoeff (fun x => signVal (f x)) S|} =
      {x | m * γ ≤ |∑ j, (1 + signVal (f (x j)) * chi ℝ S (x j)) -
        m * (1 + fourierCoeff (fun x => signVal (f x)) S)|} := by
    ext x
    have hsum : ∑ j, (1 + signVal (f (x j)) * chi ℝ S (x j)) -
        m * (1 + fourierCoeff (fun x => signVal (f x)) S) =
        m * (empiricalCoeff (examples f x) S - fourierCoeff (fun x => signVal (f x)) S) := by
      simp only [empiricalCoeff, examples_apply, sum_add_distrib, sum_const, card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one]
      field_simp
      ring
    simp only [Set.mem_ofPred_eq, hsum, abs_mul, abs_of_pos hmR]
    exact (mul_le_mul_iff_right₀ hmR).symm
  rw [hevent]
  refine h.trans_eq ?_
  congr 2
  field_simp

/-! ### The low-degree algorithm -/

/-- **The failure probability of the low-degree algorithm.** If the Fourier weight of `f`, read as
signs, on the sets of more than `t` coordinates is at most `ε / 2`, then from `m` uniform random
examples the low-degree hypothesis of degree `t` has error above `ε` with probability at most
`2 N exp (-m ε / (4 N))`, where `N` is the number of sets of at most `t` coordinates. -/
theorem uniform_error_lowDegreeHypothesis_gt_le (f : (ι → Bool) → Bool) (t m : ℕ) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hf : ∑ S with t < #S, fourierCoeff (fun x => signVal (f x)) S ^ 2 ≤ ε / 2) :
    (PMF.uniformOfFintype (Fin m → ι → Bool)).toOuterMeasure
      {x | ε < error f (lowDegreeHypothesis t (examples f x))} ≤
        ENNReal.ofReal (2 * #{S : Finset ι | #S ≤ t} *
          Real.exp (-(m * ε) / (4 * #{S : Finset ι | #S ≤ t}))) := by
  set T : Finset (Finset ι) := {S : Finset ι | #S ≤ t} with hT
  set N : ℝ := (#T : ℝ)
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.2 (one_le_card_filter_card_le t)
  have hN : 0 < N := one_pos.trans_le hN1
  set μ := (PMF.uniformOfFintype (Fin m → ι → Bool)).toOuterMeasure
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- without examples, the bound is at least one
    refine (PMF.toOuterMeasure_le_one _ _).trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [Nat.cast_zero, zero_mul, neg_zero, zero_div, Real.exp_zero, mul_one]
    linarith
  set γ := Real.sqrt (ε / (2 * N))
  have hγ : 0 ≤ γ := Real.sqrt_nonneg _
  have hγsq : γ ^ 2 = ε / (2 * N) := Real.sq_sqrt (by positivity)
  -- the samples on which the estimate of the coefficient on `S` is off by at least `γ`
  set bad : Finset ι → Set (Fin m → ι → Bool) := fun S =>
    {x | γ ≤ |empiricalCoeff (examples f x) S - fourierCoeff F S|}
  -- if every estimate is within `γ`, the hypothesis has error at most `ε`
  have hsub : {x : Fin m → ι → Bool | ε < error f (lowDegreeHypothesis t (examples f x))} ⊆
      ⋃ S ∈ T, bad S := by
    intro x hx
    by_contra hgood
    simp only [bad, Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_le] at hgood
    have herr := hammingDist_signRound_sum_mul_chi_div_le f T (empiricalCoeff (examples f x))
    have hcompl : Tᶜ = ({S : Finset ι | t < #S} : Finset (Finset ι)) := by
      rw [hT, compl_filter]
      simp only [not_le]
    rw [hcompl] at herr
    have hest : ∑ S ∈ T, (fourierCoeff F S - empiricalCoeff (examples f x) S) ^ 2 ≤ ε / 2 := by
      calc ∑ S ∈ T, (fourierCoeff F S - empiricalCoeff (examples f x) S) ^ 2
          ≤ ∑ _S ∈ T, γ ^ 2 := sum_le_sum fun S hS => by
            rw [← sq_abs, abs_sub_comm]
            exact pow_le_pow_left₀ (abs_nonneg _) (hgood S hS).le 2
        _ = ε / 2 := by
            rw [sum_const, nsmul_eq_mul, hγsq]
            change N * (ε / (2 * N)) = ε / 2
            field_simp
    have : error f (lowDegreeHypothesis t (examples f x)) ≤ ε := by
      refine herr.trans ?_
      linarith
    exact absurd hx (not_lt.2 this)
  -- the union bound over the `N` estimates
  have hone (S : Finset ι) : μ (bad S) ≤ ENNReal.ofReal (2 * Real.exp (-(m * ε) / (4 * N))) := by
    rw [ENNReal.le_ofReal_iff_toReal_le (PMF.toOuterMeasure_ne_top _ _)
      (by positivity)]
    refine (uniform_abs_empiricalCoeff_sub_ge_le f S hm hγ).trans_eq ?_
    rw [hγsq]
    congr 2
    field_simp
    ring
  calc μ {x : Fin m → ι → Bool | ε < error f (lowDegreeHypothesis t (examples f x))}
      ≤ μ (⋃ S ∈ T, bad S) := μ.mono hsub
    _ ≤ ∑ S ∈ T, μ (bad S) := MeasureTheory.measure_biUnion_finset_le T _
    _ ≤ ∑ _S ∈ T, ENNReal.ofReal (2 * Real.exp (-(m * ε) / (4 * N))) :=
        sum_le_sum fun S _ => hone S
    _ = ENNReal.ofReal (2 * N * Real.exp (-(m * ε) / (4 * N))) := by
        rw [sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-- **The low-degree algorithm** [LinialMansourNisan1993], [O'Donnell, Section 3.4][ODonnell2014]:
let `N` be the number of sets of at most `t` coordinates (at most `(n + 1) ^ t`,
`card_filter_card_le_le`). The low-degree algorithm of degree `t` from
`m ≥ (4 N / ε) log (2 N / δ)` uniform random examples learns, with error `ε` and confidence
`1 - δ`, every class of Boolean functions whose Fourier weight, read as signs, on the sets of more
than `t` coordinates is at most `ε / 2`. -/
theorem lowDegreeLearner_learns {t m : ℕ} {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hm : 4 * #{S : Finset ι | #S ≤ t} / ε * Real.log (2 * #{S : Finset ι | #S ≤ t} / δ) ≤ m)
    {C : Set ((ι → Bool) → Bool)}
    (hC : ∀ f ∈ C, ∑ S with t < #S, fourierCoeff (fun x => signVal (f x)) S ^ 2 ≤ ε / 2) :
    (lowDegreeLearner ι t m).Learns C ε δ := by
  rw [lowDegreeLearner, Learner.learns_ofHypothesis_iff]
  intro f hf
  refine (uniform_error_lowDegreeHypothesis_gt_le f t m hε.le (hC f hf)).trans
    (ENNReal.ofReal_le_ofReal ?_)
  set N : ℝ := (#{S : Finset ι | #S ≤ t} : ℝ)
  have hN : 0 < N := Nat.cast_pos.2 (one_le_card_filter_card_le t)
  have hlog : Real.log (2 * N / δ) ≤ m * ε / (4 * N) := by
    rw [le_div_iff₀ (by positivity)]
    have := (div_mul_eq_mul_div (4 * N) ε (Real.log (2 * N / δ))).symm.trans_le hm
    rw [div_le_iff₀ hε] at this
    linarith
  have hexp : Real.exp (-(m * ε) / (4 * N)) ≤ δ / (2 * N) := by
    calc Real.exp (-(m * ε) / (4 * N)) = Real.exp (-(m * ε / (4 * N))) := by ring_nf
      _ ≤ Real.exp (-Real.log (2 * N / δ)) := Real.exp_le_exp.2 (neg_le_neg hlog)
      _ = δ / (2 * N) := by
          rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  calc 2 * N * Real.exp (-(m * ε) / (4 * N)) ≤ 2 * N * (δ / (2 * N)) := by gcongr
    _ = δ := by field_simp

end Cslib.Learning
