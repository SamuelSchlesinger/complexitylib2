/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.B2.Eliminate

/-!
# Case 7 of gate elimination

Case 7 of [Mishra and Santhanam, Section 4.3][MishraSanthanam2026]: if `deg x = deg y = 2` and
`x`, `y` share their second child `B`, restrict to a line of `𝔽₂²` on which both the minimal
AND `G` and `B` are constant (fixing `x`, fixing `y`, or imposing `x = y + γ`), and delete `G`
and `B`: `Δa = -1` and `ΔW ≤ -18`.

## Main results

* `Cslib.Circuits.Boolean.B2.State.Valid.step_case7`: Case 7 of gate elimination.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.B2

open Finset Cslib.BitString

namespace State

variable {n : ℕ} {f : BooleanFunction n}

/-- **Case 7** of [Mishra and Santhanam][MishraSanthanam2026]. -/
theorem Valid.step_case7 {S : State n} (hS : S.Valid f) (hdel : ¬ S.DeletionAvailable)
    {G x y : ℕ} (h : S.MinAnd G x y) (h7 : S.Case7 G x y) : ∃ S', Step f S S' := by
  sorry


end State

end Cslib.Circuits.Boolean.B2
