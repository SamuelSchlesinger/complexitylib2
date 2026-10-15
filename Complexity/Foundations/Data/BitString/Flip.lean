/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Foundations/Data/BitString.lean`)

public import Cslib.Foundations.Data.BitString
public import Mathlib.Data.Finset.Piecewise

/-!
# Flipping bits

`BitString.flipOn T x` flips the bits of the Boolean vector `x` at the positions in `T`. Flipping
one bit is `Function.update x i (!x i)` (`BitString.flipOn_singleton`), and flipping twice at the
same positions changes nothing (`BitString.flipOn_flipOn`). Flips are the moves of sensitivity and
block sensitivity, and they span the subcubes of the Boolean cube.

## Main definitions

* `Cslib.BitString.flipOn`: flip the bits at a set of positions.

## Main results

* `Cslib.BitString.flipOn_singleton`: flipping one bit.
* `Cslib.BitString.flipOn_flipOn`, `Cslib.BitString.flipOn_involutive`: flipping is an involution.
-/

@[expose] public section

namespace Cslib.BitString

variable {ι : Type*} [DecidableEq ι] {T U : Finset ι} {x : ι → Bool} {i : ι}

/-- Flip the bits of `x` at the positions in `T`. -/
def flipOn (T : Finset ι) (x : ι → Bool) : ι → Bool :=
  fun i => if i ∈ T then !x i else x i

theorem flipOn_eq_piecewise (T : Finset ι) (x : ι → Bool) :
    flipOn T x = T.piecewise (fun i => !x i) x :=
  rfl

theorem flipOn_apply_of_mem (h : i ∈ T) : flipOn T x i = !x i := by
  simp [flipOn, h]

theorem flipOn_apply_of_notMem (h : i ∉ T) : flipOn T x i = x i := by
  simp [flipOn, h]

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

theorem flipOn_apply_eq_of_iff (h : i ∈ T ↔ i ∈ U) : flipOn T x i = flipOn U x i := by
  by_cases hi : i ∈ T
  · rw [flipOn_apply_of_mem hi, flipOn_apply_of_mem (h.mp hi)]
  · rw [flipOn_apply_of_notMem hi, flipOn_apply_of_notMem fun hU => hi (h.mpr hU)]

/-- Flipping twice at the same positions changes nothing. -/
@[simp] theorem flipOn_flipOn (T : Finset ι) (x : ι → Bool) : flipOn T (flipOn T x) = x := by
  funext i
  by_cases h : i ∈ T <;> simp [flipOn, h]

theorem flipOn_involutive (T : Finset ι) : Function.Involutive (flipOn T) :=
  flipOn_flipOn T

end Cslib.BitString
