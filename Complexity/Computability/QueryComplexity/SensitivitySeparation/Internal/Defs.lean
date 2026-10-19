/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Flip
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Superquadratic sensitivity separation: model

This file fixes the model of Boolean functions `f : (I → Bool) → Bool` used throughout the
separation: flipping a finite set of input coordinates, the sensitivity of `f` at an input and
overall, and the block sensitivity of `f` at an input and overall. All maxima are `Finset.sup`s
over the actual finite input space or the finite space of block families, so the definitions
agree literally with the standard ones. These measures are internal to the construction, which
needs arbitrary finite coordinate types; `Bridge` identifies them on `Fin n` with CSLib's
`BitString.sensitivity` and `QueryComplexity.blockSensitivity`.

## Main definitions

* `flip`: negate the coordinates of an input lying in a given finite set; this is
  `BitString.flipOn` with the arguments swapped and classical decidable equality.
* `sensitivityAt`: the number of coordinates whose flip changes `f x`.
* `sensitivity`: the maximum of `sensitivityAt f x` over all inputs `x`.
* `blockSensitivityAt`: the maximum number of disjoint nonempty blocks whose flips change `f x`.
* `blockSensitivity`: the maximum of `blockSensitivityAt f x` over all inputs `x`.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/Model.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.QueryComplexity.SensitivitySeparation.Internal

noncomputable section

open scoped Classical in
/-- Flip exactly the coordinates belonging to the specified block. -/
def flip {I : Type} (x : I → Bool) (B : Finset I) : I → Bool :=
  BitString.flipOn B x

open scoped Classical in
/-- Coordinatewise, `flip x B` negates exactly the coordinates in `B`. -/
theorem flip_apply {I : Type} (x : I → Bool) (B : Finset I) (i : I) :
    flip x B i = if i ∈ B then !(x i) else x i :=
  rfl

/-- The ordinary number of sensitive individual input coordinates. -/
def sensitivityAt {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) (x : I → Bool) : ℕ :=
  (Finset.univ.filter fun i => f (flip x {i}) ≠ f x).card

open scoped Classical in
/-- Maximum ordinary sensitivity over all Boolean inputs. -/
def sensitivity {I : Type} [Fintype I] (f : (I → Bool) → Bool) : ℕ :=
  Finset.univ.sup (sensitivityAt f)

open scoped Classical in
/-- Maximum size of a family of disjoint nonempty sensitive blocks at an input.
The empty family is allowed and contributes zero. Invalid families contribute zero. -/
def blockSensitivityAt {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) (x : I → Bool) : ℕ :=
  Finset.univ.sup fun blocks : Finset (Finset I) =>
    if (∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) ∧
        (∀ B ∈ blocks, B.Nonempty ∧ f (flip x B) ≠ f x)
    then blocks.card else 0

open scoped Classical in
/-- Maximum block sensitivity over all Boolean inputs. -/
def blockSensitivity {I : Type} [Fintype I] (f : (I → Bool) → Bool) : ℕ :=
  Finset.univ.sup (blockSensitivityAt f)

end

end Cslib.QueryComplexity.SensitivitySeparation.Internal
