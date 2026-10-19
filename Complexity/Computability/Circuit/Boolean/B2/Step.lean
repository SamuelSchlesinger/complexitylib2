/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.B2.Potential

/-!
# Lemma 4.2: one step of gate elimination

WIP: the case analysis of [Mishra and Santhanam, Section 4][MishraSanthanam2026].

## Main results

* `Cslib.Circuits.Boolean.B2.State.Valid.exists_step`: Lemma 4.2.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.B2

open Cslib.BitString

namespace State

variable {n : ℕ} {f : BooleanFunction n}

/-- **Lemma 4.2** of [Mishra and Santhanam][MishraSanthanam2026]. -/
theorem Valid.exists_step {d : ℕ} {S : State n} (hS : S.Valid f) (hf : IsAffineDisperser f d)
    (ha : d < S.a) : ∃ S' : State n, S'.Valid f ∧ S'.m + S'.s < S.m + S.s ∧
      S'.W + 14 * S.a ≤ S.W + 14 * S'.a := by
  sorry

end State

end Cslib.Circuits.Boolean.B2
