/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Data.Fintype.Pi

/-!
# Line-parity codes and recovery menus

The sharp mass-production construction stores the restrictions of a Boolean function in a code
on the points of `K ^ ℓ`, for a finite field `K` of characteristic two. Each value of a codeword
is the sum of its values on every punctured affine line through that point
(`LineCode.sum_extend`), so a requested value can be recovered from any one of many disjoint
sets of other points. A scheduler chooses, for every request, a line avoiding the points already
used and the lines of the other requests (`IsClean`). It tests a fixed menu of direction tuples
that leaves at least half of the pending requests clean in every possible state
(`IsUniversalMenu`).

This module fixes these shared definitions; constructions are in later modules.

## Main definitions

* `Cslib.Circuits.Boolean.MassProduction.puncturedLine`: the points `u + c • v` for `c ≠ 0`.
* `Cslib.Circuits.Boolean.MassProduction.LineCode`: a systematic line-parity code.
* `Cslib.Circuits.Boolean.MassProduction.occupiedPoints`: the points of a list of lines.
* `Cslib.Circuits.Boolean.MassProduction.IsClean`: a request whose line avoids the others.
* `Cslib.Circuits.Boolean.MassProduction.IsUniversalMenu`: a menu serving every state.

## References

* Adapted from `MassProduction/Scheduler.lean`, `MassProduction/HighRate/Code.lean` and
  `MassProduction/Nonuniform/PhaseMenu.lean` in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.MassProduction

open Finset

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {ℓ : ℕ}

/-- The punctured affine line through `u` with direction `v`: the points `u + c • v` for nonzero
scalars `c`. The point `u` itself is omitted. -/
def puncturedLine (u v : Fin ℓ → K) : Finset (Fin ℓ → K) :=
  ((univ : Finset K).erase 0).image fun c => u + c • v

variable (K ℓ) in
/-- A code on the points of `K ^ ℓ`. Data given on the information set `info` extends to a
codeword whose value at every point is the sum of its values on every punctured line through
that point. -/
structure LineCode where
  /-- The information set, on which the code is systematic. -/
  info : Finset (Fin ℓ → K)
  /-- The codeword extending the given data on `info`; values of `data` elsewhere are ignored
  by the specification. -/
  extend : ((Fin ℓ → K) → K) → (Fin ℓ → K) → K
  /-- Codewords agree with their data on the information set. -/
  extend_eq : ∀ data u, u ∈ info → extend data u = data u
  /-- Line parity: every value is the sum over every punctured line through its point. -/
  sum_extend : ∀ data u v, v ≠ 0 →
    ∑ c ∈ (univ : Finset K).erase 0, extend data (u + c • v) = extend data u

/-- The points covered by a list of at most `g` lines, each given by an anchor and a direction;
`none` marks an unused slot. -/
def occupiedPoints {g : ℕ} (lines : Fin g → Option ((Fin ℓ → K) × (Fin ℓ → K))) :
    Finset (Fin ℓ → K) :=
  univ.biUnion fun i => (lines i).elim ∅ fun line => puncturedLine line.1 line.2

/-- Request `i` is clean when its line avoids the occupied points and the lines of all other
requests. -/
def IsClean {k : ℕ} (occupied : Finset (Fin ℓ → K)) (targets directions : Fin k → Fin ℓ → K)
    (i : Fin k) : Prop :=
  Disjoint (puncturedLine (targets i) (directions i)) occupied ∧
    ∀ j, j ≠ i →
      Disjoint (puncturedLine (targets i) (directions i)) (puncturedLine (targets j) (directions j))

/-- A menu of nonzero direction tuples for `k` pending requests is universal for `g` occupied
lines when, for every occupied list of at most `g` lines and every tuple of `k` targets, some
entry leaves at least half of the requests clean. Targets may repeat and may be occupied. -/
def IsUniversalMenu {k r : ℕ} (g : ℕ) (menu : Fin r → Fin k → Fin ℓ → K) : Prop :=
  (∀ e i, menu e i ≠ 0) ∧
    ∀ (lines : Fin g → Option ((Fin ℓ → K) × (Fin ℓ → K))) (targets : Fin k → Fin ℓ → K),
      ∃ e, ∃ clean : Finset (Fin k), k ≤ 2 * clean.card ∧
        ∀ i ∈ clean, IsClean (occupiedPoints lines) targets (menu e) i

end Cslib.Circuits.Boolean.MassProduction
