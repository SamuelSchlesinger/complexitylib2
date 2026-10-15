/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
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
-/

@[expose] public section

namespace Cslib.Probability.PMF

open scoped ENNReal

variable {α β γ δ ε : Type*}

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

/-- If every second stage of a two-stage experiment gives the outcome `b` probability `c`, so
does the experiment. -/
theorem bind_apply_of_forall (μ : PMF α) {f : α → PMF β} {b : β} {c : ℝ≥0∞}
    (h : ∀ a, f a b = c) : μ.bind f b = c := by
  simp only [PMF.bind_apply, h, ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]

/-- Some possible outcome of the first stage of a two-stage experiment does at least as well as
the experiment. -/
theorem exists_bind_apply_le [Finite α] (μ : PMF α) (f : α → PMF β) (b : β) :
    ∃ a ∈ μ.support, μ.bind f b ≤ f a b := by
  obtain ⟨a, ha, hmax⟩ :=
    μ.support.exists_max_image (fun a => f a b) μ.support.toFinite μ.support_nonempty
  refine ⟨a, ha, ?_⟩
  rw [PMF.bind_apply]
  calc ∑' a', μ a' * f a' b ≤ ∑' a', μ a' * f a b := ENNReal.tsum_le_tsum fun a' => by
        by_cases h : a' ∈ μ.support
        · exact mul_le_mul_right (hmax a' h) _
        · simp [(μ.apply_eq_zero_iff a').mpr h]
    _ = f a b := by rw [ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]

end Cslib.Probability.PMF
