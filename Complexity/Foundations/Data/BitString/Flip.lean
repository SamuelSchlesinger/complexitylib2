/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Foundations/Data/BitString.lean`)

public import Cslib.Foundations.Data.BitString
public import Mathlib.Data.Finset.Piecewise
public import Mathlib.Data.Fintype.Pi

/-!
# Flipping bits

`BitString.flipOn T x` flips the bits of the Boolean vector `x` at the positions in `T`. Flipping
one bit is `Function.update x i (!x i)` (`BitString.flipOn_singleton`), and flipping twice at the
same positions changes nothing (`BitString.flipOn_flipOn`). Flips are the moves of sensitivity and
block sensitivity, and they span the subcubes of the Boolean cube.

Sensitivity and certificate measures use CSLib's `Computability.QueryComplexity.Measures`.

An input `x` of a Boolean function `g` is *isolated* when flipping any one of its bits changes the
value of `g` (`BitString.isolatedInputs`). A formula in disjunctive normal form needs a term for
each isolated true input, and parity has only isolated inputs.

## Main definitions

* `Cslib.BitString.flipOn`: flip the bits at a set of positions.
* `Cslib.BitString.isolatedInputs`: the isolated inputs of a Boolean function with a given value.

## Main results

* `Cslib.BitString.flipOn_apply`: coordinatewise evaluation of `flipOn`.
* `Cslib.BitString.flipOn_singleton`: flipping one bit.
* `Cslib.BitString.flipOn_flipOn`, `Cslib.BitString.flipOn_involutive`: flipping is an involution.

## References

* [N. Nisan, *CREW PRAMs and decision trees*][Nisan1991]
-/

@[expose] public section

namespace Cslib.BitString

open Finset

variable {ι : Type*} [DecidableEq ι] {T U : Finset ι} {x : ι → Bool} {i : ι}

/-- Flip the bits of `x` at the positions in `T`. -/
def flipOn (T : Finset ι) (x : ι → Bool) : ι → Bool :=
  fun i => if i ∈ T then !x i else x i

/-- Coordinatewise, `flipOn T x` negates the bits in `T` and keeps the others. -/
theorem flipOn_apply (T : Finset ι) (x : ι → Bool) (i : ι) :
    flipOn T x i = if i ∈ T then !x i else x i :=
  rfl

/-- `flipOn T x` is `x` with its bits at the positions in `T` replaced by their negations. -/
theorem flipOn_eq_piecewise (T : Finset ι) (x : ι → Bool) :
    flipOn T x = T.piecewise (fun i => !x i) x :=
  rfl

/-- At a position in `T`, `flipOn T x` has the negated bit of `x`. -/
theorem flipOn_apply_of_mem (h : i ∈ T) : flipOn T x i = !x i := by
  simp [flipOn, h]

/-- At a position outside `T`, `flipOn T x` has the bit of `x`. -/
theorem flipOn_apply_of_notMem (h : i ∉ T) : flipOn T x i = x i := by
  simp [flipOn, h]

/-- Flipping at no positions changes nothing. -/
@[simp] theorem flipOn_empty (x : ι → Bool) : flipOn ∅ x = x := by
  funext i
  simp [flipOn]

/-- Flipping one bit. -/
@[simp] theorem flipOn_singleton (i : ι) (x : ι → Bool) :
    flipOn {i} x = Function.update x i (!x i) := by
  funext j
  by_cases h : j = i
  · subst h
    simp [flipOn]
  · simp [flipOn, h]

/-- Flipping at `T` and at `U` gives the same bit at any position `i` that lies in `T` exactly
when it lies in `U`. -/
theorem flipOn_apply_eq_of_iff (h : i ∈ T ↔ i ∈ U) : flipOn T x i = flipOn U x i := by
  by_cases hi : i ∈ T
  · rw [flipOn_apply_of_mem hi, flipOn_apply_of_mem (h.mp hi)]
  · rw [flipOn_apply_of_notMem hi, flipOn_apply_of_notMem fun hU => hi (h.mpr hU)]

/-- Flipping twice at the same positions changes nothing. -/
@[simp] theorem flipOn_flipOn (T : Finset ι) (x : ι → Bool) : flipOn T (flipOn T x) = x := by
  funext i
  by_cases h : i ∈ T <;> simp [flipOn, h]

/-- Flipping at a fixed set of positions is an involution. -/
theorem flipOn_involutive (T : Finset ι) : Function.Involutive (flipOn T) :=
  flipOn_flipOn T

section Isolated

variable [Fintype ι] {g : (ι → Bool) → Bool} {b : Bool}

/-- The *isolated inputs* of `g` with value `b`: the inputs `x` with `g x = b` at which flipping
any one bit changes the value of `g`. -/
def isolatedInputs (g : (ι → Bool) → Bool) (b : Bool) : Finset (ι → Bool) :=
  {x | g x = b ∧ ∀ i, g (Function.update x i !x i) = !b}

/-- `x` is an isolated input of `g` with value `b` exactly when `g x = b` and flipping any one bit
of `x` gives the value `!b`. -/
@[simp] theorem mem_isolatedInputs :
    x ∈ isolatedInputs g b ↔ g x = b ∧ ∀ i, g (Function.update x i !x i) = !b := by
  simp [isolatedInputs]

/-- The isolated inputs of the negation of `g` with value `b` are those of `g` with value `!b`. -/
theorem isolatedInputs_not (g : (ι → Bool) → Bool) (b : Bool) :
    isolatedInputs (fun x => !g x) b = isolatedInputs g (!b) := by
  ext x
  cases b <;> simp

end Isolated

end Cslib.BitString
