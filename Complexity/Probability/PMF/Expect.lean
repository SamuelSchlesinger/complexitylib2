/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Probability/PMF.lean`)

public import Complexity.Init
public import Cslib.Probability.PMF
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Data.Finset.Density
public import Mathlib.Basic.Real.Basic
import Complexity.Foundations.Data.Finset.Expect

/-!
# Uniform experiments as averages

An experiment that starts by drawing `a` uniformly from a finite type and then runs `f a` outputs
`b` with probability the average over `a` of the probability that `f a` outputs `b`
(`toReal_uniformOfFintype_bind_apply`). In particular, a Boolean function `g` of a uniform sample
is `true` with probability the density of the set where `g` is `true`
(`toReal_uniformOfFintype_map_apply_true`). These translate experiments written with `PMF.bind`
into the vocabulary of `Finset.expect` (`𝔼`) and `Finset.dens`.

## Main results

* `Cslib.Probability.PMF.toReal_uniformOfFintype_bind_apply`: a uniform first stage averages the
  second stages.
* `Cslib.Probability.PMF.toReal_uniformOfFintype_map_apply_true`: the probability that a Boolean
  function of a uniform sample is `true` is a density.
-/

@[expose] public section

namespace Cslib.Probability.PMF

open Finset
open scoped BigOperators ENNReal

variable {α β : Type*} [Fintype α] [Nonempty α]

/-- An experiment whose first stage draws `a` uniformly outputs `b` with probability the average
over `a` of the probability that the second stage `f a` outputs `b`. -/
theorem toReal_uniformOfFintype_bind_apply (f : α → PMF β) (b : β) :
    ((uniformOfFintype α).bind f b).toReal = 𝔼 a, (f a b).toReal := by
  rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum fun a _ =>
    ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _),
    Fintype.expect_eq_sum_div_card, sum_div]
  refine sum_congr rfl fun a _ => ?_
  rw [ENNReal.toReal_mul, uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    inv_mul_eq_div]

/-- A Boolean function `g` of a uniform sample is `true` with probability the density of the set
where `g` is `true`. -/
theorem toReal_uniformOfFintype_map_apply_true (g : α → Bool) :
    ((uniformOfFintype α).map g true).toReal = dens {a | g a = true} := by
  rw [← PMF.bind_pure_comp, toReal_uniformOfFintype_bind_apply]
  have h (a : α) : ((Function.comp PMF.pure g a) true).toReal =
      if g a = true then 1 else 0 := by
    simp only [Function.comp_apply, PMF.pure_apply, eq_comm (a := true)]
    split_ifs <;> rfl
  simp only [h]
  exact Fintype.expect_boole _

end Cslib.Probability.PMF
