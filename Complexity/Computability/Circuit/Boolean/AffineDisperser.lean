/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.AffineDisperser.LowerBound

/-!
# A `3.5 n - 7 d` lower bound for affine dispersers

**Theorem 4.1** of [Mishra and Santhanam][MishraSanthanam2026]: every circuit over the full
binary basis `B₂` computing an affine disperser for dimension `d` on `n` bits has at least
`3.5 n - 7 d` gates (`Cslib.Circuits.Boolean.AffineDisperser.seven_mul_le_two_mul_size_add`).

The proof is a gate elimination on fair semi-circuits (`Cslib.Circuits.Boolean.SemiCircuit`),
organised as follows.

* `AffineDisperser.State`: the states of gate elimination, their potential, Proposition 2.2 and
  Lemma 2.3 of the source.
* `AffineDisperser.Operations`: restrictions, deletions and reparameterisations, with validity.
* `AffineDisperser.Reduction`: reductions, which restrict parameters and delete constraints, and
  their accounting, done once for all reductions.
* `AffineDisperser.Normal`: the preliminary reductions of Section 4.1.
* `AffineDisperser.MinimalAnd`: restructuring and eliminating the minimal AND, Sections 4.2
  and 4.3.
* `AffineDisperser.Step`: Lemma 4.2, one step of gate elimination.
* `AffineDisperser.LowerBound`: Theorem 4.1, by summing the steps.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
-/
