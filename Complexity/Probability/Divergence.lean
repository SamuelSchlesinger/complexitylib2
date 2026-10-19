/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.Entropy
public import Complexity.Probability.StatisticalDistance
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs
import Complexity.Probability.PairwiseIndependent
import Complexity.Probability.PMF.Expect
import Complexity.Probability.PMF.Map
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.MeasureTheory.Measure.TotalVariation.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Kullback–Leibler divergence of finite distributions

The library has one divergence notion, Mathlib's `InformationTheory.klDiv`, and one entropy
notion, `Cslib.Probability.PMF.entropy`. This file bridges them. For PMFs on a finite type with
a discrete measurable structure, `klDiv p.toMeasure q.toMeasure` is finite exactly when the
support of `p` is contained in that of `q`, and is then the finite sum
`∑ a, p a * log (p a / q a)` in nats. Consequences:

* Gibbs' inequality: the sum is nonnegative and vanishes only at `p = q`. Equivalently, the
  entropy of `p` is at most its cross-entropy `∑ a, p a * surprisal q a`.
* Entropy is the logarithm of the alphabet size minus the divergence from uniform.
* Mutual information, `H(X) + H(Y) - H(X, Y)`, is the divergence of the joint law from the
  product of its marginals. Entropy is subadditive and conditioning cannot increase it; by the
  equality case of Gibbs' inequality, subadditivity is an equality exactly for independent
  pairs.
* Pinsker's inequality `2 δ(p, q)² ≤ D(p ‖ q)` for the statistical distance `δ`. It is proved
  for arbitrary probability measures and events, following the variational proof: Gibbs'
  inequality for an exponentially tilted measure (Mathlib's `integral_llr_tilted_right`) and
  Hoeffding's lemma for the indicator of the event. A Hahn decomposition gives the form with
  Mathlib's total variation distance `tvDist`, which is twice the statistical distance.

Divergences are in nats and entropies in bits, so the bridges divide by `log 2`.

## Main results

* `Cslib.Probability.PMF.toReal_klDiv_toMeasure`: the finite-sum formula.
* `Cslib.Probability.PMF.klDiv_toMeasure_ne_top_iff`: finiteness is support inclusion.
* `Cslib.Probability.PMF.klDiv_toMeasure_map_le`: data processing for deterministic maps.
* `Cslib.Probability.PMF.sum_mul_log_div_nonneg`, `.sum_mul_log_div_eq_zero_iff`: Gibbs.
* `Cslib.Probability.PMF.entropy_le_sum_mul_surprisal`: entropy is at most cross-entropy.
* `Cslib.Probability.PMF.entropy_le_logb_card_of_support_subset`: entropy is at most the
  logarithm of the support size.
* `Cslib.Probability.PMF.entropy_eq_logb_card_sub_klDiv`: entropy and divergence from uniform.
* `Cslib.Probability.PMF.entropy_map_fst_add_entropy_map_snd_sub_entropy`: mutual information.
* `Cslib.Probability.PMF.entropy_le_entropy_map_fst_add_entropy_map_snd`: subadditivity, with
  equality exactly for independent pairs
  (`Cslib.Probability.PMF.entropy_eq_entropy_map_fst_add_entropy_map_snd_iff`).
* `Cslib.Probability.PMF.conditionalEntropy_le_entropy_map_snd`: conditioning reduces entropy.
* `Cslib.Probability.ofReal_two_mul_sq_measureReal_sub_le_klDiv`: Pinsker for an event.
* `Cslib.Probability.ofReal_tvDist_sq_div_two_le_klDiv`: Pinsker with Mathlib's `tvDist`.
* `Cslib.Probability.PMF.dist_eq_tvDist_toMeasure_div_two`: statistical distance is half of
  `tvDist`.
* `Cslib.Probability.PMF.ofReal_two_mul_dist_sq_le_klDiv`,
  `Cslib.Probability.PMF.dist_le_sqrt_toReal_klDiv_div_two`: Pinsker's inequality.

## References

* [T. M. Cover, J. A. Thomas, *Elements of Information Theory*][CoverThomas2006],
  Theorems 2.6.3 (Gibbs), 2.6.4 (uniform maximizes entropy), 2.6.5 (conditioning reduces
  entropy), 2.6.6 (independence bound on entropy, here for two variables), Section 2.3 and
  Theorem 2.4.1 (mutual information) and Lemma 11.6.1 (Pinsker).
-/

@[expose] public section

namespace Cslib.Probability

open MeasureTheory ProbabilityTheory InformationTheory

variable {α β : Type*}

/-! ### Pinsker's inequality for an event -/

/-- **Pinsker's inequality** for a single event: `2 (μ s - ν s)² ≤ klDiv μ ν`, the divergence in
nats, for probability measures and a measurable event `s`. The statement holds unconditionally
since `klDiv μ ν = ∞` when `μ` is not absolutely continuous with respect to `ν` or the
log-likelihood ratio is not integrable. -/
theorem ofReal_two_mul_sq_measureReal_sub_le_klDiv {mα : MeasurableSpace α}
    {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {s : Set α} (hs : MeasurableSet s) :
    ENNReal.ofReal (2 * (μ.real s - ν.real s) ^ 2) ≤ klDiv μ ν := by
  by_cases hac : μ ≪ ν
  swap; · simp [klDiv_of_not_ac hac]
  by_cases hint : Integrable (llr μ ν) μ
  swap; · simp [klDiv_of_not_integrable hint]
  rw [klDiv_of_ac_of_integrable hac hint]
  apply ENNReal.ofReal_le_ofReal
  simp only [probReal_univ, add_sub_cancel_right]
  set δ := μ.real s - ν.real s
  set t := 4 * δ
  let X : α → ℝ := s.indicator fun _ => 1
  have hX : Measurable X := measurable_const.indicator hs
  have hXmem (x : α) : X x ∈ Set.Icc (0 : ℝ) 1 := by
    by_cases hx : x ∈ s <;> simp [X, hx]
  have hexp : Integrable (fun x => Real.exp (t * X x)) ν :=
    Integrable.of_bound (by fun_prop) (Real.exp |t|) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
      calc t * X x ≤ |t * X x| := le_abs_self _
        _ = |t| * X x := by rw [abs_mul, abs_of_nonneg (hXmem x).1]
        _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left (hXmem x).2 (abs_nonneg t)
        _ = |t| := mul_one _)
  have hfμ : Integrable (fun x => t * X x) μ := ((integrable_const 1).indicator hs).const_mul t
  -- Gibbs' inequality for the tilted measure `ν.tilted (t * X)`.
  have hgibbs : 0 ≤ ∫ x, llr μ (ν.tilted fun x => t * X x) x ∂μ := by
    have := isProbabilityMeasure_tilted hexp
    have h := integral_llr_add_sub_measure_univ_nonneg
      (hac.trans (absolutelyContinuous_tilted hexp))
      (integrable_llr_tilted_right hac hfμ hint hexp)
    simpa only [probReal_univ, add_sub_cancel_right] using h
  rw [integral_llr_tilted_right hac hfμ hexp hint] at hgibbs
  -- Hoeffding's lemma for the indicator of `s` under `ν`.
  have hmean : ∫ x, X x ∂ν = ν.real s := by
    rw [integral_indicator_const (1 : ℝ) hs, smul_eq_mul, mul_one]
  have hhoeffding : ∫ x, Real.exp (t * X x) ∂ν ≤ Real.exp (t * ν.real s + t ^ 2 / 8) := by
    have h := (hasSubgaussianMGF_of_mem_Icc (μ := ν) hX.aemeasurable (ae_of_all _ hXmem)).mgf_le t
    rw [hmean, show (fun x => X x - ν.real s) = fun x => X x + -ν.real s from
      funext fun _ => sub_eq_add_neg _ _, mgf_add_const] at h
    rw [mgf] at h
    calc ∫ x, Real.exp (t * X x) ∂ν
        = ((∫ x, Real.exp (t * X x) ∂ν) * Real.exp (t * -ν.real s)) *
            Real.exp (t * ν.real s) := by
          rw [mul_assoc, ← Real.exp_add]; simp
      _ ≤ Real.exp ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 * t ^ 2 / 2) * Real.exp (t * ν.real s) :=
          mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      _ = Real.exp (t * ν.real s + t ^ 2 / 8) := by
          rw [← Real.exp_add, sub_zero, nnnorm_one]
          congr 1
          push_cast
          ring
  have hlog : Real.log (∫ x, Real.exp (t * X x) ∂ν) ≤ t * ν.real s + t ^ 2 / 8 :=
    (Real.log_le_iff_le_exp (integral_exp_pos hexp)).mpr hhoeffding
  have hint_f : ∫ x, t * X x ∂μ = t * μ.real s := by
    rw [integral_const_mul, integral_indicator_const (1 : ℝ) hs, smul_eq_mul, mul_one]
  rw [hint_f] at hgibbs
  nlinarith [sq_nonneg δ]

/-- **Pinsker's inequality** with Mathlib's total variation distance `tvDist`, which takes values
in `[0, 2]` for probability measures: `tvDist μ ν ^ 2 / 2 ≤ klDiv μ ν`, the divergence in nats. It
follows from the event form applied to a Hahn decomposition. -/
theorem ofReal_tvDist_sq_div_two_le_klDiv {mα : MeasurableSpace α}
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ENNReal.ofReal (tvDist μ ν ^ 2 / 2) ≤ klDiv μ ν := by
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  have h := ofReal_two_mul_sq_measureReal_sub_le_klDiv (μ := μ) (ν := ν) hs.measurableSet.compl
  rw [hs.tvDist_eq, probReal_compl_eq_one_sub hs.measurableSet,
    probReal_compl_eq_one_sub (μ := ν) hs.measurableSet]
  rw [probReal_compl_eq_one_sub hs.measurableSet,
    probReal_compl_eq_one_sub (μ := ν) hs.measurableSet] at h
  convert h using 2
  ring

namespace PMF

/-! ### The finite-sum formula -/

section Bridge

variable [MeasurableSpace α] [MeasurableSingletonClass α]

/-- A PMF measure on a countable type is absolutely continuous with respect to another exactly
when its support is contained in the other's support. -/
theorem toMeasure_absolutelyContinuous_iff [Countable α] {p q : PMF α} :
    p.toMeasure ≪ q.toMeasure ↔ p.support ⊆ q.support := by
  constructor
  · intro h a ha
    by_contra hq
    have hq0 : q.toMeasure {a} = 0 := by
      rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a)]
      exact (PMF.apply_eq_zero_iff q a).mpr hq
    have := h hq0
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a)] at this
    exact ha this
  · intro h s hs
    have hsm : MeasurableSet s := (Set.to_countable s).measurableSet
    rw [PMF.toMeasure_apply_eq_zero_iff _ hsm] at hs ⊢
    exact hs.mono_left h

/-- The finite-sum formula for the Kullback–Leibler divergence of finite distributions, in
nats. Null outcomes of `p` contribute zero. -/
theorem toReal_klDiv_toMeasure [Fintype α] {p q : PMF α} (h : p.support ⊆ q.support) :
    (klDiv p.toMeasure q.toMeasure).toReal =
      ∑ a, (p a).toReal * Real.log ((p a).toReal / (q a).toReal) := by
  have hac := toMeasure_absolutelyContinuous_iff.mpr h
  rw [toReal_klDiv_of_measure_eq hac (by simp)]
  have hdensity : p.toMeasure = q.toMeasure.withDensity (fun a => p a / q a) := by
    apply Measure.ext_of_singleton
    intro a
    rw [withDensity_apply _ (measurableSet_singleton a), lintegral_singleton,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a),
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a)]
    by_cases hq : q a = 0
    · have hp : p a = 0 := by
        by_contra hp
        exact (PMF.mem_support_iff q a).mp (h ((PMF.mem_support_iff p a).mpr hp)) hq
      simp [hp, hq]
    · exact (ENNReal.div_mul_cancel hq (PMF.apply_ne_top q a)).symm
  have hrn : p.toMeasure.rnDeriv q.toMeasure =ᵐ[p.toMeasure] fun a => p a / q a := by
    have h := Measure.rnDeriv_withDensity q.toMeasure
      (f := fun a => p a / q a) (measurable_of_countable _)
    rw [← hdensity] at h
    exact hac.ae_le h
  rw [integral_congr_ae (hrn.mono fun a ha => by rw [llr, ha]), PMF.integral_eq_sum]
  simp [ENNReal.toReal_div]

/-- The divergence of finite distributions is finite exactly when the support of the first is
contained in the support of the second. -/
theorem klDiv_toMeasure_ne_top_iff [Finite α] {p q : PMF α} :
    klDiv p.toMeasure q.toMeasure ≠ ⊤ ↔ p.support ⊆ q.support := by
  constructor
  · intro h
    exact toMeasure_absolutelyContinuous_iff.mp (klDiv_ne_top_iff.mp h).1
  · intro h
    exact klDiv_ne_top (toMeasure_absolutelyContinuous_iff.mpr h) Integrable.of_finite

/-- The divergence of finite distributions with nested supports, as an extended real. -/
theorem klDiv_toMeasure_eq_ofReal [Fintype α] {p q : PMF α} (h : p.support ⊆ q.support) :
    klDiv p.toMeasure q.toMeasure =
      ENNReal.ofReal (∑ a, (p a).toReal * Real.log ((p a).toReal / (q a).toReal)) := by
  rw [← toReal_klDiv_toMeasure h, ENNReal.ofReal_toReal (klDiv_toMeasure_ne_top_iff.mpr h)]

/-- **Data processing**: a deterministic map cannot increase the divergence of distributions on
a countable type. -/
theorem klDiv_toMeasure_map_le [Countable α] [MeasurableSpace β] (p q : PMF α) (f : α → β) :
    klDiv (p.map f).toMeasure (q.map f).toMeasure ≤ klDiv p.toMeasure q.toMeasure := by
  have hf : Measurable f := measurable_of_countable f
  rw [← _root_.PMF.toMeasure_map f p hf, ← _root_.PMF.toMeasure_map f q hf]
  exact klDiv_map_le _ _ hf

end Bridge

/-! ### Gibbs' inequality -/

section Gibbs

variable [Fintype α]

/-- **Gibbs' inequality**: the divergence sum of finite distributions is nonnegative. -/
theorem sum_mul_log_div_nonneg {p q : PMF α} (h : p.support ⊆ q.support) :
    0 ≤ ∑ a, (p a).toReal * Real.log ((p a).toReal / (q a).toReal) := by
  let : MeasurableSpace α := ⊤
  rw [← toReal_klDiv_toMeasure h]
  exact ENNReal.toReal_nonneg

/-- The equality case of Gibbs' inequality: the divergence sum vanishes only for equal
distributions. -/
theorem sum_mul_log_div_eq_zero_iff {p q : PMF α} (h : p.support ⊆ q.support) :
    ∑ a, (p a).toReal * Real.log ((p a).toReal / (q a).toReal) = 0 ↔ p = q := by
  let : MeasurableSpace α := ⊤
  rw [← toReal_klDiv_toMeasure h, ENNReal.toReal_eq_zero_iff,
    or_iff_left (klDiv_toMeasure_ne_top_iff.mpr h), klDiv_eq_zero_iff]
  exact PMF.toMeasure_injective.eq_iff

omit [Fintype α] in
/-- Where `p` has positive mass, the information-content gap of `p` and `q` is the logarithm
of their mass ratio, in bits. -/
private theorem mul_surprisal_sub_eq {p q : PMF α} (h : p.support ⊆ q.support) (a : α) :
    (p a).toReal * (surprisal q a - surprisal p a) =
      (p a).toReal * Real.log ((p a).toReal / (q a).toReal) / Real.log 2 := by
  by_cases hp : p a = 0
  · simp [hp]
  have hq : q a ≠ 0 := (PMF.mem_support_iff q a).mp (h ((PMF.mem_support_iff p a).mpr hp))
  have hp' : (p a).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hp, PMF.apply_ne_top p a⟩
  have hq' : (q a).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hq, PMF.apply_ne_top q a⟩
  rw [surprisal, surprisal, Real.logb, Real.logb, Real.log_div hp' hq']
  ring

/-- **Gibbs' inequality** in entropy form: the entropy of `p` is at most its cross-entropy
relative to any `q` whose support contains that of `p`. -/
theorem entropy_le_sum_mul_surprisal {p q : PMF α} (h : p.support ⊆ q.support) :
    entropy p ≤ ∑ a, (p a).toReal * surprisal q a := by
  rw [entropy_eq_sum_surprisal, ← sub_nonneg, ← Finset.sum_sub_distrib]
  simp only [← mul_sub, mul_surprisal_sub_eq h, ← Finset.sum_div]
  exact div_nonneg (sum_mul_log_div_nonneg h) (Real.log_nonneg (by norm_num))

omit [Fintype α] in
/-- The uniform distribution on a nonempty finite set has the logarithm of its size as
entropy. -/
theorem entropy_uniformOfFinset [Finite α] (s : Finset α) (hs : s.Nonempty) :
    entropy (uniformOfFinset s hs) = Real.logb 2 s.card := by
  classical
  let := Fintype.ofFinite α
  have hcard : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  have hterm (a : α) : Real.negMulLog ((uniformOfFinset s hs) a).toReal =
      if a ∈ s then (s.card : ℝ)⁻¹ * Real.log s.card else 0 := by
    by_cases ha : a ∈ s <;> simp [ha, Real.negMulLog, Real.log_inv]
  rw [entropy_eq_sum]
  simp only [hterm, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
    Real.logb]
  field_simp

omit [Fintype α] in
/-- A distribution supported on a finite set `s` has entropy at most `log₂ |s|`. This is Gibbs'
inequality against the uniform distribution on `s`. -/
theorem entropy_le_logb_card_of_support_subset [Finite α] (p : PMF α) {s : Finset α}
    (h : p.support ⊆ s) : entropy p ≤ Real.logb 2 s.card := by
  classical
  let := Fintype.ofFinite α
  obtain ⟨a, ha⟩ := p.support_nonempty
  have hs : s.Nonempty := ⟨a, h ha⟩
  have hsupport : p.support ⊆ (uniformOfFinset s hs).support := by
    intro b hb
    rw [mem_support_uniformOfFinset_iff]
    exact h hb
  refine (entropy_le_sum_mul_surprisal hsupport).trans_eq ?_
  have hterm (b : α) : (p b).toReal * surprisal (uniformOfFinset s hs) b =
      (p b).toReal * Real.logb 2 s.card := by
    by_cases hb : p b = 0
    · simp [hb]
    have hbs : b ∈ s := h ((PMF.mem_support_iff p b).mpr hb)
    simp [surprisal, hbs, Real.logb_inv]
  simp only [hterm, ← Finset.sum_mul, sum_toReal, one_mul]

/-- Entropy is the logarithm of the alphabet size minus the divergence from the uniform
distribution, converted to bits. -/
theorem entropy_eq_logb_card_sub_klDiv [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) :
    entropy p = Real.logb 2 (Fintype.card α) -
      (klDiv p.toMeasure (PMF.uniformOfFintype α).toMeasure).toReal / Real.log 2 := by
  have hsupport : p.support ⊆ (PMF.uniformOfFintype α).support := by
    intro a _
    simp [PMF.mem_support_iff]
  rw [toReal_klDiv_toMeasure hsupport, entropy_eq_sum_surprisal]
  have hcard : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hterm (a : α) : (p a).toReal * Real.log ((p a).toReal /
      ((PMF.uniformOfFintype α) a).toReal) / Real.log 2 =
        (p a).toReal * Real.logb 2 (Fintype.card α) - (p a).toReal * surprisal p a := by
    by_cases hp : p a = 0
    · simp [hp]
    have hp' : (p a).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hp, PMF.apply_ne_top p a⟩
    simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      div_inv_eq_mul, surprisal, Real.logb, Real.log_mul hp' hcard.ne']
    ring
  simp only [Finset.sum_div, hterm, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_toReal,
    one_mul]
  ring

end Gibbs

/-! ### Mutual information and subadditivity -/

section MutualInformation

/-- The mass of an independent pair is the product of the masses of its components. -/
private theorem bind_map_prodMk_apply (p : PMF α) (q : PMF β) (pair : α × β) :
    (p.bind fun a => q.map (a, ·)) pair = p pair.1 * q pair.2 := by
  simp only [PMF.map, Function.comp_def]
  exact bind_pair_apply p (fun _ => q) pair.1 pair.2

/-- A joint law is supported where the product of its marginals is. -/
private theorem support_subset_bind_map_prodMk (joint : PMF (α × β)) :
    joint.support ⊆
      ((joint.map Prod.fst).bind fun a => (joint.map Prod.snd).map (a, ·)).support := by
  intro pair hpair
  rw [PMF.mem_support_iff, bind_map_prodMk_apply]
  exact mul_ne_zero
    (ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hpair) (le_map_apply joint _ pair)))
    (ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hpair) (le_map_apply joint _ pair)))

/-- **Mutual information** `I(X; Y) = H(X) + H(Y) - H(X, Y)`, in bits, is the divergence of
the joint law from the product of its marginals. -/
theorem entropy_map_fst_add_entropy_map_snd_sub_entropy [Finite α] [Finite β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β] (joint : PMF (α × β)) :
    entropy (joint.map Prod.fst) + entropy (joint.map Prod.snd) - entropy joint =
      (klDiv joint.toMeasure
        ((joint.map Prod.fst).toMeasure.prod (joint.map Prod.snd).toMeasure)).toReal /
          Real.log 2 := by
  let := Fintype.ofFinite α
  let := Fintype.ofFinite β
  rw [← toMeasure_bind_pair, toReal_klDiv_toMeasure (support_subset_bind_map_prodMk joint)]
  have hterm (pair : α × β) : (joint pair).toReal * Real.log ((joint pair).toReal /
      (((joint.map Prod.fst).bind fun a => (joint.map Prod.snd).map (a, ·)) pair).toReal) =
        -Real.negMulLog (joint pair).toReal -
          (joint pair).toReal * Real.log ((joint.map Prod.fst) pair.1).toReal -
            (joint pair).toReal * Real.log ((joint.map Prod.snd) pair.2).toReal := by
    by_cases hp : joint pair = 0
    · simp [hp]
    have hp' : (joint pair).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hp, PMF.apply_ne_top _ _⟩
    have h1 : ((joint.map Prod.fst) pair.1).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr ⟨ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hp)
        (le_map_apply joint Prod.fst pair)), PMF.apply_ne_top _ _⟩
    have h2 : ((joint.map Prod.snd) pair.2).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr ⟨ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hp)
        (le_map_apply joint Prod.snd pair)), PMF.apply_ne_top _ _⟩
    rw [bind_map_prodMk_apply, ENNReal.toReal_mul, Real.log_div hp' (mul_ne_zero h1 h2),
      Real.log_mul h1 h2, Real.negMulLog]
    ring
  simp only [hterm, Finset.sum_sub_distrib]
  rw [← sum_map_mul joint Prod.fst (fun a => Real.log ((joint.map Prod.fst) a).toReal),
    ← sum_map_mul joint Prod.snd (fun b => Real.log ((joint.map Prod.snd) b).toReal)]
  simp only [entropy_eq_sum, Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
  ring

variable [Finite α] [Finite β]

/-- **Conditioning reduces entropy**: the entropy of the second component given the first is
at most its unconditional entropy. -/
theorem conditionalEntropy_le_entropy_map_snd (joint : PMF (α × β)) :
    conditionalEntropy joint ≤ entropy (joint.map Prod.snd) := by
  have h := conditionalEntropy_map_fst_ge joint (fun _ => ())
  rwa [show joint.map (fun pair => ((), pair.2)) = (joint.map Prod.snd).map ((), ·) by
    rw [PMF.map_comp]; rfl, conditionalEntropy_map_const] at h

/-- **Subadditivity of entropy**: the joint entropy is at most the sum of the marginal
entropies ([CoverThomas2006], Theorem 2.6.6 for two variables). -/
theorem entropy_le_entropy_map_fst_add_entropy_map_snd (joint : PMF (α × β)) :
    entropy joint ≤ entropy (joint.map Prod.fst) + entropy (joint.map Prod.snd) := by
  have h := conditionalEntropy_le_entropy_map_snd joint
  rw [conditionalEntropy] at h
  linarith

/-- Subadditivity of entropy is an equality exactly for independent pairs, whose joint law is
the product of its marginals. -/
theorem entropy_eq_entropy_map_fst_add_entropy_map_snd_iff (joint : PMF (α × β)) :
    entropy joint = entropy (joint.map Prod.fst) + entropy (joint.map Prod.snd) ↔
      joint = (joint.map Prod.fst).bind fun a => (joint.map Prod.snd).map (a, ·) := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  have h := entropy_map_fst_add_entropy_map_snd_sub_entropy joint
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [← toMeasure_bind_pair] at h
  have hne := klDiv_toMeasure_ne_top_iff (p := joint)
    (q := (joint.map Prod.fst).bind fun a => (joint.map Prod.snd).map (a, ·))
  constructor
  · intro heq
    have h0 : (klDiv joint.toMeasure ((joint.map Prod.fst).bind
        fun a => (joint.map Prod.snd).map (a, ·)).toMeasure).toReal = 0 := by
      rw [show entropy (joint.map Prod.fst) + entropy (joint.map Prod.snd) - entropy joint = 0
        by linarith, eq_comm, div_eq_zero_iff] at h
      exact h.resolve_right hlog.ne'
    rcases ENNReal.toReal_eq_zero_iff _ |>.mp h0 with h0 | htop
    · exact PMF.toMeasure_injective (klDiv_eq_zero_iff.mp h0)
    · exact absurd htop (hne.mpr (support_subset_bind_map_prodMk joint))
  · intro heq
    rw [← heq, klDiv_self, ENNReal.toReal_zero, zero_div] at h
    linarith

end MutualInformation

/-! ### Pinsker's inequality -/

section Pinsker

variable [Fintype α]

/-- Statistical distance is the probability gap on the event where `p` exceeds `q`. -/
theorem dist_eq_sum_filter_lt (p q : PMF α) :
    dist p q = ∑ a ∈ Finset.univ.filter (fun a => (q a).toReal < (p a).toReal),
      ((p a).toReal - (q a).toReal) := by
  rw [dist_eq, Finset.sum_filter]
  have hsum : ∑ a, ((p a).toReal - (q a).toReal) = 0 := by
    rw [Finset.sum_sub_distrib, sum_toReal, sum_toReal, sub_self]
  have habs (a : α) : |(p a).toReal - (q a).toReal| =
      2 * (if (q a).toReal < (p a).toReal then (p a).toReal - (q a).toReal else 0) -
        ((p a).toReal - (q a).toReal) := by
    split_ifs with h
    · rw [abs_of_pos (sub_pos.mpr h)]; ring
    · rw [abs_of_nonpos (sub_nonpos.mpr (not_lt.mp h))]; ring
  simp only [habs, Finset.sum_sub_distrib, hsum, ← Finset.mul_sum]
  ring

omit [Fintype α] in
/-- The probability of an event under a PMF measure is the sum of its masses. -/
private theorem measureReal_toMeasure_eq_sum [MeasurableSpace α] [MeasurableSingletonClass α]
    (r : PMF α) (event : Finset α) :
    r.toMeasure.real (event : Set α) = ∑ a ∈ event, (r a).toReal := by
  rw [measureReal_def, PMF.toMeasure_apply_finset,
    ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top r a)]

/-- Statistical distance is half of Mathlib's total variation distance `tvDist` of the PMF
measures. -/
theorem dist_eq_tvDist_toMeasure_div_two [MeasurableSpace α] [MeasurableSingletonClass α]
    (p q : PMF α) : dist p q = tvDist p.toMeasure q.toMeasure / 2 := by
  classical
  let below : Finset α := Finset.univ.filter fun a => (p a).toReal ≤ (q a).toReal
  have hbelow : (↑below : Set α)ᶜ = ↑(Finset.univ.filter
      fun a => (q a).toReal < (p a).toReal) := by
    ext a; simp [below]
  have hhahn : IsHahnDecomposition p.toMeasure q.toMeasure below := by
    have hle (μ ν : PMF α) (t : Set α) (ht : ∀ a ∈ t, (μ a).toReal ≤ (ν a).toReal) :
        μ.toMeasure t ≤ ν.toMeasure t := by
      rw [PMF.toMeasure_apply_fintype, PMF.toMeasure_apply_fintype]
      refine Finset.sum_le_sum fun a _ => ?_
      by_cases ha : a ∈ t
      · simpa [ha] using (ENNReal.toReal_le_toReal (PMF.apply_ne_top _ _)
          (PMF.apply_ne_top _ _)).mp (ht a ha)
      · simp [ha]
    refine ⟨(Set.to_countable _).measurableSet, Measure.le_iff'.mpr fun t => ?_,
      Measure.le_iff'.mpr fun t => ?_⟩
    · rw [Measure.restrict_apply' (Set.to_countable _).measurableSet,
        Measure.restrict_apply' (Set.to_countable _).measurableSet]
      exact hle p q _ fun a ha => by simpa [below] using ha.2
    · rw [Measure.restrict_apply' (Set.to_countable _).measurableSet,
        Measure.restrict_apply' (Set.to_countable _).measurableSet, hbelow]
      exact hle q p _ fun a ha => (Finset.mem_filter.mp (Finset.mem_coe.mp ha.2)).2.le
  rw [hhahn.tvDist_eq, probReal_compl_eq_one_sub (μ := p.toMeasure) hhahn.measurableSet,
    probReal_compl_eq_one_sub (μ := q.toMeasure) hhahn.measurableSet,
    dist_eq_sum_filter_lt, Finset.sum_sub_distrib, ← measureReal_toMeasure_eq_sum p,
    ← measureReal_toMeasure_eq_sum q, ← hbelow,
    probReal_compl_eq_one_sub (μ := p.toMeasure) hhahn.measurableSet,
    probReal_compl_eq_one_sub (μ := q.toMeasure) hhahn.measurableSet]
  ring

/-- **Pinsker's inequality** for finite distributions: twice the squared statistical distance
is at most the Kullback–Leibler divergence, in nats. -/
theorem ofReal_two_mul_dist_sq_le_klDiv [MeasurableSpace α] [MeasurableSingletonClass α]
    (p q : PMF α) : ENNReal.ofReal (2 * dist p q ^ 2) ≤ klDiv p.toMeasure q.toMeasure := by
  have h := ofReal_two_mul_sq_measureReal_sub_le_klDiv (μ := p.toMeasure) (ν := q.toMeasure)
    (s := ↑(Finset.univ.filter fun a => (q a).toReal < (p a).toReal))
    ((Set.to_countable _).measurableSet)
  rwa [measureReal_toMeasure_eq_sum, measureReal_toMeasure_eq_sum, ← Finset.sum_sub_distrib,
    ← dist_eq_sum_filter_lt] at h

/-- **Pinsker's inequality** with a finite-sum divergence. -/
theorem two_mul_dist_sq_le_sum_mul_log_div {p q : PMF α} (h : p.support ⊆ q.support) :
    2 * dist p q ^ 2 ≤ ∑ a, (p a).toReal * Real.log ((p a).toReal / (q a).toReal) := by
  let : MeasurableSpace α := ⊤
  have hpinsker := ofReal_two_mul_dist_sq_le_klDiv p q
  rw [klDiv_toMeasure_eq_ofReal h] at hpinsker
  exact (ENNReal.ofReal_le_ofReal_iff (sum_mul_log_div_nonneg h)).mp hpinsker

/-- **Pinsker's inequality** in its usual form: statistical distance is at most
`sqrt (D(p ‖ q) / 2)`, the divergence in nats. -/
theorem dist_le_sqrt_toReal_klDiv_div_two [MeasurableSpace α] [MeasurableSingletonClass α]
    {p q : PMF α} (h : p.support ⊆ q.support) :
    dist p q ≤ Real.sqrt ((klDiv p.toMeasure q.toMeasure).toReal / 2) := by
  rw [toReal_klDiv_toMeasure h]
  apply Real.le_sqrt_of_sq_le
  linarith [two_mul_dist_sq_le_sum_mul_log_div h]

end Pinsker

end PMF

end Cslib.Probability
