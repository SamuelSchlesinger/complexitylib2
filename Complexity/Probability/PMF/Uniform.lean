/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker, Devon Tuma, Kexing Ying, Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Probability/PMF.lean`)

public import Complexity.Probability.PMF

/-!
# Uniform distributions and resampling

Every value of a nonempty finite type has positive uniform mass (`mem_support_uniformOfFintype`),
and the uniform probability of an event is the fraction of its members
(`toOuterMeasure_uniformOfFintype`, `toOuterMeasure_uniformOfFintype_toReal`).

Draw `a` uniformly from `α` and, independently, `b` uniformly from `β`. For any equivalence
`e : α × β ≃ γ × δ`, the pair `e (a, b)` is uniform on `γ × δ`, so its first component is uniform
on `γ` (`uniformOfFintype_bind_map_fst_equiv`). This is the resampling step of hybrid arguments:
overwriting part of a uniform string `a` by independent uniform values `b` leaves it uniform, since
the overwritten string and the old part together determine `(a, b)`.

## Main results

* `Cslib.Probability.PMF.mem_support_uniformOfFintype`: every value has positive uniform mass.
* `Cslib.Probability.PMF.uniformOfFintype_prod_map_fst`: the first component of a uniform pair is
  uniform.
* `Cslib.Probability.PMF.uniformOfFintype_bind_map_fst_equiv`,
  `Cslib.Probability.PMF.uniformOfFintype_bind_bind_fst_equiv`: resampling along an equivalence.
* `Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype`,
  `Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_toReal`: the uniform probability of an
  event is the fraction of its members.
-/

@[expose] public section

namespace Cslib.Probability.PMF

open scoped ENNReal

variable {α β γ δ ε : Type*}

section Uniform

/-- Every value of a nonempty finite type is in the uniform distribution's support. -/
theorem mem_support_uniformOfFintype [Fintype α] [Nonempty α] (a : α) :
    a ∈ (uniformOfFintype α).support := by
  simp [uniformOfFintype]

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

omit [Fintype β] [Nonempty β] [Fintype γ] [Nonempty γ] [Finite δ] in
/-- The uniform distribution on a finite type gives an event the fraction of its members, as an
extended nonnegative real. -/
theorem toOuterMeasure_uniformOfFintype (event : Set α) [DecidablePred (· ∈ event)] :
    (uniformOfFintype α).toOuterMeasure event =
      (Finset.univ.filter (· ∈ event)).card * (Fintype.card α : ℝ≥0∞)⁻¹ := by
  rw [PMF.toOuterMeasure_apply, tsum_fintype]
  simp only [Set.indicator_apply, uniformOfFintype_apply]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

end Uniform

/-- The probability of an event under the uniform distribution on a finite type is the fraction
of its members. -/
theorem toOuterMeasure_uniformOfFintype_toReal [Fintype α] [Nonempty α] (event : Set α)
    [DecidablePred (· ∈ event)] :
    ((uniformOfFintype α).toOuterMeasure event).toReal =
      (Finset.univ.filter (· ∈ event)).card / Fintype.card α := by
  rw [toOuterMeasure_uniformOfFintype, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast, div_eq_mul_inv]

end Cslib.Probability.PMF
