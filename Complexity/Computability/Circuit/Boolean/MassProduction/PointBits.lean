/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.MassProduction.Line
public import Cslib.Computability.Circuit.Boolean.Basic
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Bit encodings of points and recovery lines

Circuits read field elements through an additive bijection `bits : K ≃+ BitString b`, so adding a
fixed point is a coordinatewise exclusive or. A point of `K ^ ℓ` is `ℓ` consecutive blocks of `b`
bits; a batch of `t` points is `t` consecutive point blocks. A punctured line is listed point by
point in a fixed order of the nonzero scalars.

A scheduler circuit reads `t` target points and writes, for every request in its original
position, the points of a punctured line through that request's target, such that the lines of
distinct requests are disjoint (`IsScheduler`). Targets may repeat. The directions are existential;
only the listed points are outputs.

## Main definitions

* `Cslib.Circuits.Boolean.MassProduction.pointBits`: the bits of one point.
* `Cslib.Circuits.Boolean.MassProduction.targetBits`: the bits of a batch of points.
* `Cslib.Circuits.Boolean.MassProduction.lineBits`: the listed points of a batch of lines.
* `Cslib.Circuits.Boolean.MassProduction.IsScheduler`: the scheduler specification.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.MassProduction

open Finset

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {ℓ b s t : ℕ}

/-- The bits of a point: block `i` holds the bits of coordinate `i`. -/
def pointBits (bits : K ≃+ BitString b) (u : Fin ℓ → K) : BitString (ℓ * b) :=
  fun x => bits (u (finProdFinEquiv.symm x).1) (finProdFinEquiv.symm x).2

/-- The bits of a batch of points: block `i` holds the bits of point `i`. -/
def targetBits (bits : K ≃+ BitString b) (targets : Fin t → Fin ℓ → K) :
    BitString (t * (ℓ * b)) :=
  fun x => pointBits bits (targets (finProdFinEquiv.symm x).1) (finProdFinEquiv.symm x).2

/-- The listed points of a batch of lines: block `i` lists, for each scalar index `j`, the bits of
`targets i + scalar j • directions i`. -/
def lineBits (bits : K ≃+ BitString b) (scalar : Fin s ≃ {c : K // c ≠ 0})
    (targets directions : Fin t → Fin ℓ → K) : BitString (t * (s * (ℓ * b))) :=
  fun x =>
    let ix := finProdFinEquiv.symm x
    let jy := finProdFinEquiv.symm ix.2
    pointBits bits (targets ix.1 + (scalar jy.1 : K) • directions ix.1) jy.2

/-- A scheduler maps every batch of `t` targets to listed punctured lines through them, with
nonzero directions and pairwise disjoint lines, keeping every request in its original
position. -/
def IsScheduler (bits : K ≃+ BitString b) (scalar : Fin s ≃ {c : K // c ≠ 0})
    (c : Circuit Boolean.signature (t * (ℓ * b)) (t * (s * (ℓ * b)))) : Prop :=
  ∀ targets : Fin t → Fin ℓ → K, ∃ directions : Fin t → Fin ℓ → K,
    (∀ i, directions i ≠ 0) ∧
      (∀ i j, i ≠ j →
        Disjoint (puncturedLine (targets i) (directions i))
          (puncturedLine (targets j) (directions j))) ∧
      c.eval Boolean.interpretation (targetBits bits targets) =
        lineBits bits scalar targets directions

end Cslib.Circuits.Boolean.MassProduction
