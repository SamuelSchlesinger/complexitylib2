/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker, Devon Tuma, Kexing Ying, Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Probability/PMF.lean`)

public import Complexity.Init
public import Cslib.Probability.PMF

/-!
# Resampling and two-stage experiments

Draw `a` uniformly from `α` and, independently, `b` uniformly from `β`. For any equivalence
`e : α × β ≃ γ × δ`, the pair `e (a, b)` is uniform on `γ × δ`, so its first component is uniform
on `γ` (`uniformOfFintype_bind_map_fst_equiv`). This is the resampling step of hybrid arguments:
overwriting part of a uniform string `a` by independent uniform values `b` leaves it uniform, since
the overwritten string and the old part together determine `(a, b)`.

A two-stage experiment `μ.bind f` gives an outcome the probability `c` when every second stage
does (`bind_apply_of_forall`), and some possible first stage gives it at least the probability
of the whole experiment (`exists_bind_apply_le`).

## Main results

* `Cslib.Probability.PMF.uniformOfFintype_prod_map_fst`: the first component of a uniform pair is
  uniform.
* `Cslib.Probability.PMF.uniformOfFintype_bind_map_fst_equiv`,
  `Cslib.Probability.PMF.uniformOfFintype_bind_bind_fst_equiv`: resampling along an equivalence.
* `Cslib.Probability.PMF.bind_apply_of_forall`, `Cslib.Probability.PMF.exists_bind_apply_le`:
  two-stage experiments.
* `Cslib.Probability.PMF.bind_congr_on_support`: continuations need agree only on possible inputs,
  adapted from the cslib `crypto` branch at `5ff69ca`.
* `Cslib.Probability.PMF.bind_apply_mono_on_support`: compare two continuations at one outcome.
* `Cslib.Probability.PMF.toOuterMeasure_bind_failure_le`,
  `toOuterMeasure_bind_failure_toReal_le`: compose failure bounds without independence,
  adapted from the cslib `crypto` branch at `5ff69ca`.
* `Cslib.Probability.PMF.toOuterMeasure_rate_ge`: turn average bias into candidate probability.
* `Cslib.Probability.PMF.filter_apply_toReal`: conditioned masses, with event/complement rules.
* `Cslib.Probability.PMF.map_injective`: injective encodings preserve equality of distributions,
  adapted from the same branch.
* `Cslib.Probability.PMF.bind_apply_toReal`, `sum_toReal`: real-valued finite averages,
  copied from cslib PR #1062.
-/

@[expose] public section

namespace Cslib.Probability.PMF

open scoped ENNReal

universe u

variable {α β γ δ ε : Type*}

/-- Every event has finite probability, including on an infinite ambient type.
Adapted from the cslib `crypto` branch at `5ff69ca`. -/
theorem toOuterMeasure_ne_top (p : PMF α) (event : Set α) : p.toOuterMeasure event ≠ ⊤ := by
  simpa only [PMF.toOuterMeasure_apply] using p.tsum_coe_indicator_ne_top event

/-- An event has probability at most one. -/
theorem toOuterMeasure_le_one (p : PMF α) (event : Set α) : p.toOuterMeasure event ≤ 1 := by
  rw [PMF.toOuterMeasure_apply, ← p.tsum_coe]
  exact ENNReal.tsum_le_tsum (fun a => Set.indicator_apply_le (fun _ => le_rfl))

open Classical in
/-- Event probabilities on finite spaces are sums of the masses of their members. -/
theorem toOuterMeasure_apply_toReal [Fintype α] (p : PMF α) (event : Set α) :
    (p.toOuterMeasure event).toReal = ∑ a, if a ∈ event then (p a).toReal else 0 := by
  classical
  rw [PMF.toOuterMeasure_apply_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a ∈ event <;> simp [ha]
  · intro a _
    by_cases ha : a ∈ event <;> simp [ha, PMF.apply_ne_top]

/-- An event and its complement have total probability one, in real-valued probability units. -/
theorem toOuterMeasure_toReal_add_compl (p : PMF α) (event : Set α) :
    (p.toOuterMeasure event).toReal + (p.toOuterMeasure eventᶜ).toReal = 1 := by
  have h : p.toOuterMeasure event + p.toOuterMeasure eventᶜ = 1 := by
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
    convert p.tsum_coe using 1
    congr 1
    funext a
    by_cases ha : a ∈ event <;> simp [ha]
  simpa only [ENNReal.toReal_add (toOuterMeasure_ne_top p _) (toOuterMeasure_ne_top p _),
    ENNReal.toReal_one] using congrArg ENNReal.toReal h

/-- An event has positive real probability exactly when it contains a possible outcome. -/
theorem toOuterMeasure_toReal_pos_iff (p : PMF α) (event : Set α) :
    0 < (p.toOuterMeasure event).toReal ↔ ∃ a ∈ event, a ∈ p.support := by
  classical
  simp [ENNReal.toReal_pos_iff, lt_top_iff_ne_top, toOuterMeasure_ne_top, pos_iff_ne_zero,
    PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left, and_comm]

open Classical in
/-- Conditioning keeps the event's masses and divides them by its probability. -/
theorem filter_apply_toReal (p : PMF α) (event : Set α)
    (hevent : ∃ a ∈ event, a ∈ p.support) (a : α) :
    ((p.filter event hevent) a).toReal =
      if a ∈ event then (p a).toReal / (p.toOuterMeasure event).toReal else 0 := by
  rw [PMF.filter_apply, ← PMF.toOuterMeasure_apply]
  by_cases ha : a ∈ event <;> simp [ha, ENNReal.toReal_mul, div_eq_mul_inv]

/-- Event probability after a finite random choice is the average conditional probability. -/
theorem toOuterMeasure_bind_toReal [Fintype α] (p : PMF α) (kernel : α → PMF β)
    (event : Set β) :
    ((p.bind kernel).toOuterMeasure event).toReal =
      ∑ a, (p a).toReal * ((kernel a).toOuterMeasure event).toReal := by
  rw [PMF.toOuterMeasure_bind_apply, tsum_fintype, ENNReal.toReal_sum
    (fun a _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (toOuterMeasure_ne_top _ _))]
  simp only [ENNReal.toReal_mul]

/-- A randomized continuation can fail because its precondition was already false or because
it fails from a valid input. No independence or finite-state assumption is needed. -/
theorem toOuterMeasure_bind_failure_le (p : PMF α) (kernel : α → PMF β)
    (pre : Set α) (failure : Set β) (error : ENNReal)
    (hstep : ∀ a ∈ p.support, a ∈ pre → (kernel a).toOuterMeasure failure ≤ error) :
    (p.bind kernel).toOuterMeasure failure ≤ p.toOuterMeasure preᶜ + error := by
  classical
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply]
  calc
    _ ≤ ∑' a, ((preᶜ).indicator p a + p a * error) := by
      apply ENNReal.tsum_le_tsum
      intro a
      by_cases ha : a ∈ pre
      · simp only [Set.indicator_of_notMem (show a ∉ preᶜ by simpa), zero_add]
        by_cases hs : a ∈ p.support
        · exact mul_le_mul_of_nonneg_left (hstep a hs ha) zero_le
        · have hz : p a = 0 := by simpa only [PMF.mem_support_iff, not_not] using hs
          simp [hz]
      · simp only [Set.indicator_of_mem (show a ∈ preᶜ from ha)]
        exact (mul_le_mul_of_nonneg_left (toOuterMeasure_le_one (kernel a) failure)
          zero_le).trans (by simp)
    _ = _ := by rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, p.tsum_coe, one_mul]

/-- The real-valued error rule for a randomized continuation. -/
theorem toOuterMeasure_bind_failure_toReal_le (p : PMF α) (kernel : α → PMF β)
    (pre : Set α) (failure : Set β) {error : ℝ} (herror : 0 ≤ error)
    (hstep : ∀ a ∈ p.support, a ∈ pre →
      ((kernel a).toOuterMeasure failure).toReal ≤ error) :
    ((p.bind kernel).toOuterMeasure failure).toReal ≤
      (p.toOuterMeasure preᶜ).toReal + error := by
  have h := toOuterMeasure_bind_failure_le p kernel pre failure (ENNReal.ofReal error)
    (fun a ha hpre => (ENNReal.le_ofReal_iff_toReal_le (toOuterMeasure_ne_top _ _) herror).mpr
      (hstep a ha hpre))
  have hfinite : p.toOuterMeasure preᶜ + ENNReal.ofReal error ≠ ⊤ := ENNReal.add_ne_top.mpr
    ⟨toOuterMeasure_ne_top p preᶜ, ENNReal.ofReal_ne_top⟩
  simpa only [ENNReal.toReal_add (toOuterMeasure_ne_top p preᶜ) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal herror] using ENNReal.toReal_mono hfinite h

/-- If a randomized test beats a threshold on average, at least its excess probability mass
consists of inputs whose conditional acceptance probability reaches that threshold. -/
theorem toOuterMeasure_rate_ge (p : PMF α) (kernel : α → PMF β) (event : Set β)
    {threshold : ℝ} (hthreshold : 0 ≤ threshold) :
    ((p.bind kernel).toOuterMeasure event).toReal - threshold ≤
      (p.toOuterMeasure {a | threshold ≤ ((kernel a).toOuterMeasure event).toReal}).toReal := by
  have h := toOuterMeasure_bind_failure_toReal_le p kernel
    {a | ((kernel a).toOuterMeasure event).toReal < threshold} event hthreshold
    (fun a _ ha => le_of_lt ha)
  simpa only [Set.compl_ofPred, not_lt] using (sub_le_iff_le_add.mpr h)

/-- The pairing law also holds when the second sample's type depends on the first.
Adapted from the cslib `crypto` branch at `5ff69ca`. -/
theorem bind_sigma_apply {β : α → Type*} (p : PMF α) (f : (a : α) → PMF (β a))
    (a : α) (b : β a) :
    (p.bind (fun a => (f a).map (Sigma.mk a))) ⟨a, b⟩ = p a * f a b := by
  classical
  simp only [PMF.bind_apply, PMF.map_apply, ← ENNReal.tsum_mul_left, mul_ite, mul_zero]
  rw [← ENNReal.tsum_sigma]
  simp

/-! ### Monad notation

Copied from cslib PR #1129 at `4e626b5449d9c93b4ac7028e596e91324ed2f4f1`.
Remove this block when that PR is in the base pin; the resampling lemmas below remain candidates.
-/

-- upstream: submitted #1129 @4e626b5449d9c93b4ac7028e596e91324ed2f4f1

@[simp] theorem monad_pure_eq_pure (a : α) : (pure a : PMF α) = PMF.pure a := rfl

@[simp] theorem monad_bind_eq_bind {α β : Type u} (p : PMF α) (f : α → PMF β) :
    p >>= f = p.bind f := rfl

attribute [simp] _root_.PMF.monad_map_eq_map _root_.PMF.pure_map

/-! ### Real-valued probability masses

Copied from cslib PR #1062 at `807f066de941490e437833e91f099927a984eb87`.
Remove this block when that PR is in the base pin; the candidate lemmas below remain.
-/

-- upstream: submitted #1062 @807f066de941490e437833e91f099927a984eb87

/-- Real-valued probability masses are summable, even on an infinite ambient type. -/
theorem summable_toReal (p : PMF α) : Summable (fun a => (p a).toReal) :=
  ENNReal.summable_toReal p.tsum_coe_ne_top

/-- The real-valued masses of any discrete distribution sum to one. -/
@[simp] theorem tsum_toReal (p : PMF α) : ∑' a, (p a).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq p.apply_ne_top, p.tsum_coe, ENNReal.toReal_one]

/-- The real-valued probabilities of a finite distribution sum to one. -/
theorem sum_toReal [Fintype α] (p : PMF α) :
    ∑ a, (p a).toReal = 1 := by simpa using tsum_toReal p

/-- Randomized postprocessing averages the outcome probabilities over any discrete input. -/
theorem bind_apply_toReal_tsum (p : PMF α) (kernel : α → PMF β) (b : β) :
    (p.bind kernel b).toReal = ∑' a, (p a).toReal * (kernel a b).toReal := by
  rw [PMF.bind_apply, ENNReal.tsum_toReal_eq (fun a =>
    ENNReal.mul_ne_top (p.apply_ne_top a) ((kernel a).apply_ne_top b))]
  simp

/-- The probability of an outcome after a finite random choice is its weighted average. -/
theorem bind_apply_toReal [Fintype α] (p : PMF α)
    (kernel : α → PMF β) (b : β) :
    (p.bind kernel b).toReal =
      ∑ a, (p a).toReal * (kernel a b).toReal := by
  simpa using bind_apply_toReal_tsum p kernel b

/-! ### Injective representations -/

/-- An injective representation of outcomes also embeds their complete probability laws. -/
theorem map_injective {f : α → β} (hf : Function.Injective f) :
    Function.Injective (PMF.map f) := by
  classical
  intro p q h
  ext a
  simpa only [PMF.map_apply, hf.eq_iff, tsum_ite_eq'] using congrArg (fun law => law (f a)) h

section Uniform

variable [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]

/-- The first component of a uniform pair is uniform. -/
theorem uniformOfFintype_prod_map_fst :
    (uniformOfFintype (α × β)).map Prod.fst = uniformOfFintype α := by
  rw [← uniformOfFintype_prod, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  calc _ = (uniformOfFintype α).bind PMF.pure := by
        congr 1
        funext a
        exact PMF.map_const _ _
    _ = _ := PMF.bind_pure _

variable [Fintype γ] [Nonempty γ] [Finite δ]

/-- **Resampling**: for independent uniform `a` and `b` and an equivalence `e : α × β ≃ γ × δ`,
the first component of `e (a, b)` is uniform. -/
theorem uniformOfFintype_bind_map_fst_equiv (e : α × β ≃ γ × δ) :
    ((uniformOfFintype α).bind fun a => (uniformOfFintype β).map fun b => (e (a, b)).1) =
      uniformOfFintype γ := by
  have : Fintype δ := Fintype.ofFinite δ
  have : Nonempty δ := ⟨(e (Classical.arbitrary _)).2⟩
  calc _ = (uniformOfFintype (α × β)).map (Prod.fst ∘ e) := by
        rw [← uniformOfFintype_prod, PMF.map_bind]
        simp only [PMF.map_comp]
        rfl
    _ = (uniformOfFintype (γ × δ)).map Prod.fst := by
        rw [← PMF.map_comp, uniformOfFintype_map_equiv]
    _ = _ := uniformOfFintype_prod_map_fst

/-- **Resampling** inside an experiment: running `f` on the first component of `e (a, b)`, for
independent uniform `a` and `b`, is running `f` on a uniform input. -/
theorem uniformOfFintype_bind_bind_fst_equiv (e : α × β ≃ γ × δ) (f : γ → PMF ε) :
    ((uniformOfFintype α).bind fun a => (uniformOfFintype β).bind fun b => f (e (a, b)).1) =
      (uniformOfFintype γ).bind f := by
  rw [← uniformOfFintype_bind_map_fst_equiv e]
  simp only [PMF.bind_bind, PMF.bind_map]
  rfl

end Uniform

/-- A continuation only needs to agree on outcomes the preceding distribution can produce. -/
theorem bind_congr_on_support (p : PMF α) (f g : α → PMF β)
    (h : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  rw [← PMF.bindOnSupport_eq_bind p f, ← PMF.bindOnSupport_eq_bind p g]
  congr 1
  funext a ha
  exact h a ha

/-- If every second stage of a two-stage experiment gives the outcome `b` probability `c`, so
does the experiment. -/
theorem bind_apply_of_forall (μ : PMF α) {f : α → PMF β} {b : β} {c : ℝ≥0∞}
    (h : ∀ a, f a b = c) : μ.bind f b = c := by
  simp only [PMF.bind_apply, h, ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]

/-- Increasing an outcome's probability on every possible first-stage result increases its
probability in the whole experiment. The sample spaces may be infinite. -/
theorem bind_apply_mono_on_support (μ : PMF α) {f g : α → PMF β} (b : β)
    (h : ∀ a ∈ μ.support, f a b ≤ g a b) : μ.bind f b ≤ μ.bind g b := by
  simp only [PMF.bind_apply]
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases ha : a ∈ μ.support
  · exact mul_le_mul_right (h a ha) _
  · simp [(μ.apply_eq_zero_iff a).mpr ha]

/-- Some possible outcome of the first stage of a two-stage experiment does at least as well as
the experiment. -/
theorem exists_bind_apply_le [Finite α] (μ : PMF α) (f : α → PMF β) (b : β) :
    ∃ a ∈ μ.support, μ.bind f b ≤ f a b := by
  obtain ⟨a, ha, hmax⟩ :=
    μ.support.exists_max_image (fun a => f a b) μ.support.toFinite μ.support_nonempty
  refine ⟨a, ha, ?_⟩
  exact (bind_apply_mono_on_support μ b hmax).trans_eq
    (bind_apply_of_forall μ fun _ => rfl)

end Cslib.Probability.PMF
