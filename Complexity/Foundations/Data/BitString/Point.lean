/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Foundations.Data.BitString
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Bit encodings of points and lines

Field elements are read through an additive bijection `bits : K ≃+ BitString b`, so adding a
fixed point is a coordinatewise exclusive or. A point of `K ^ ℓ` is `ℓ` consecutive blocks of `b`
bits, and a batch of `t` points is `t` consecutive point blocks. A batch of lines `u + c • v` is
listed point by point in a fixed order of `s` scalars.

## Main definitions

* `Cslib.BitString.pointBits`: the bits of one point.
* `Cslib.BitString.pointEquiv`: the equivalence between points and their bits.
* `Cslib.BitString.targetBits`: the bits of a batch of points.
* `Cslib.BitString.lineBits`: the listed points of a batch of lines.

## Main results

* `Cslib.BitString.pointBits_add`: point encodings preserve addition.
* `Cslib.BitString.pointBits_injective`: distinct points have distinct encodings.

## References

* Adapted from the vector encodings in MassProduction/BinaryEncoding.lean of
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.BitString

variable {K : Type*} {ℓ b s t : ℕ}

/-- The bits of a point: block `i` holds the bits of coordinate `i`. -/
def pointBits [Add K] (bits : K ≃+ BitString b) (u : Fin ℓ → K) : BitString (ℓ * b) :=
  fun x => bits (u (finProdFinEquiv.symm x).1) (finProdFinEquiv.symm x).2

/-- Point bits add coordinatewise. -/
theorem pointBits_add [Add K] (bits : K ≃+ BitString b) (u v : Fin ℓ → K) :
    pointBits bits (u + v) = pointBits bits u + pointBits bits v := by
  funext x
  simp only [pointBits, Pi.add_apply, map_add]

/-- Distinct points have distinct bits. -/
theorem pointBits_injective [Add K] (bits : K ≃+ BitString b) :
    Function.Injective (pointBits (ℓ := ℓ) bits) := by
  intro u v h
  funext i
  apply bits.injective
  funext β
  simpa only [pointBits, Equiv.symm_apply_apply] using congrFun h (finProdFinEquiv (i, β))

/-- Points of `K ^ ℓ` are their bits. -/
def pointEquiv [Add K] (bits : K ≃+ BitString b) : (Fin ℓ → K) ≃ BitString (ℓ * b) where
  toFun := pointBits bits
  invFun y i := bits.symm fun r => y (finProdFinEquiv (i, r))
  left_inv u := by
    funext i
    simp only [pointBits, Equiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  right_inv y := by
    funext x
    simp only [pointBits, AddEquiv.apply_symm_apply, Prod.mk.eta, Equiv.apply_symm_apply]

/-- `pointEquiv bits` sends a point to its bits `pointBits bits`. -/
@[simp] theorem pointEquiv_apply [Add K] (bits : K ≃+ BitString b) (u : Fin ℓ → K) :
    pointEquiv bits u = pointBits bits u :=
  rfl

/-- The bits of a batch of points: block `i` holds the bits of point `i`. -/
def targetBits [Add K] (bits : K ≃+ BitString b) (targets : Fin t → Fin ℓ → K) :
    BitString (t * (ℓ * b)) :=
  fun x => pointBits bits (targets (finProdFinEquiv.symm x).1) (finProdFinEquiv.symm x).2

/-- The listed points of a batch of lines: block `i` lists, for each scalar index `j`, the bits of
`targets i + scalar j • directions i`. -/
def lineBits [Semiring K] (bits : K ≃+ BitString b) (scalar : Fin s → K)
    (targets directions : Fin t → Fin ℓ → K) : BitString (t * (s * (ℓ * b))) :=
  fun x =>
    let ix := finProdFinEquiv.symm x
    let jy := finProdFinEquiv.symm ix.2
    pointBits bits (targets ix.1 + scalar jy.1 • directions ix.1) jy.2

end Cslib.BitString
