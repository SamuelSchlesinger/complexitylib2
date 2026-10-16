/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.PMF

/-!
# Relabeling discrete distributions

## Main results

* `Cslib.Probability.PMF.map_equiv_apply`: point masses after an equivalence.
* `Cslib.Probability.PMF.map_congr_on_support`: only supported inputs need equal outputs.

## References

Adapted from `Probability/PMF.lean` on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, reusing Mathlib's support-sensitive bind congruence.
-/

@[expose] public section

namespace Cslib.Probability.PMF

variable {α β : Type*}

/-- Relabeling a distribution by an equivalence preserves each corresponding point mass. -/
theorem map_equiv_apply (p : PMF α) (e : α ≃ β) (b : β) :
    p.map e b = p (e.symm b) := by
  classical
  simp only [PMF.map_apply, ← e.symm_apply_eq, tsum_ite_eq']

/-- Re-encoding only needs to agree on outcomes which the distribution can produce. -/
theorem map_congr_on_support (p : PMF α) (f g : α → β)
    (h : ∀ a ∈ p.support, f a = g a) : p.map f = p.map g :=
  PMF.bind_congr_on_support p _ _ (fun a ha => congrArg PMF.pure (h a ha))

end Cslib.Probability.PMF
