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
