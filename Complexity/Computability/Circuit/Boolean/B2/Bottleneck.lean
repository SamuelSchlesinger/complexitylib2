/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.B2.Eliminate

/-!
# Cases 9 and 10 of gate elimination

Cases 9 and 10 of [Mishra and Santhanam, Section 4.3][MishraSanthanam2026]: in the bottleneck
configuration the minimal AND `G` has a unique child `D` reading an unpaired isolated parameter
`z`. If `D` is AND-type (Case 9), fix `x` and `y` so that `G` and then `D` become constant and
delete `G`, `D` and the second children of `x` and `y`: `Δa = -2`, `ΔW ≤ -28`. If `D` is XOR-type
(Case 10), the quadratic reparameterisation deletes `G` and `D`: `Δa = -1`, `ΔW ≤ -14`.

## Main results

* `Cslib.Circuits.Boolean.B2.State.Valid.step_bottleneck`: Cases 9 and 10 of gate elimination.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.B2

open Finset Cslib.BitString

namespace State

variable {n : ℕ} {f : BooleanFunction n}

/-- **Cases 9 and 10** of [Mishra and Santhanam][MishraSanthanam2026]. -/
theorem Valid.step_bottleneck {S : State n} {d : ℕ} (hS : S.Valid f)
    (hf : IsAffineDisperser f d) (ha : d < S.a) (hexcl : S.Exclusive)
    (hdel : ¬ S.DeletionAvailable) {G x y : ℕ} (h : S.MinAnd G x y) (h7 : ¬ S.Case7 G x y)
    (hbot : S.Bottleneck G x) : ∃ S', Step f S S' := by
  sorry


end State

end Cslib.Circuits.Boolean.B2
