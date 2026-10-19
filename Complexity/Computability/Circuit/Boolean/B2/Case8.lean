/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.B2.Eliminate

/-!
# Case 8 of gate elimination

Case 8 of [Mishra and Santhanam, Section 4.3][MishraSanthanam2026]: fix `x` so that the minimal
AND `G` becomes constant, and delete all children of `x` and of `G`. Only unpaired isolated
parameters whose child is a child of `G` can gain weight, and when `deg x = 2` the parameter `y`
loses a child, so `ΔW ≤ 14 Δa` outside the bottleneck configuration.

## Main results

* `Cslib.Circuits.Boolean.B2.State.Valid.step_case8`: Case 8 of gate elimination.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.B2

open Finset Cslib.BitString

namespace State

variable {n : ℕ} {f : BooleanFunction n}

/-- **Case 8** of [Mishra and Santhanam][MishraSanthanam2026]. -/
theorem Valid.step_case8 {S : State n} (hS : S.Valid f) (hexcl : S.Exclusive)
    (hdel : ¬ S.DeletionAvailable) {G x y : ℕ} (h : S.MinAnd G x y) (h7 : ¬ S.Case7 G x y)
    (hbot : ¬ S.Bottleneck G x) : ∃ S', Step f S S' := by
  sorry


end State

end Cslib.Circuits.Boolean.B2
