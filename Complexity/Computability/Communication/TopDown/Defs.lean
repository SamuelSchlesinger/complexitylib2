/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Communication.RoundProtocol
public import Complexity.Foundations.BooleanAnalysis.MirrorSets

/-!
# Density rectangles for the top-down adversary

The invariant from Sections 3--4 of [Korten2026].

The actual sampling rate may be smaller than the parameter bound. This is
needed because density-limit conditions need not be monotone in the rate.
-/

@[expose] public section

namespace Cslib.Communication

open Cslib.BooleanAnalysis

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A nonempty rectangle with both deficits at most `k`, and a positive
sampling rate at most `p` for which one side consists of density limits of
the other side. -/
def DensityRectangle (X Y : Finset (ι → Bool)) (p k : ℝ) : Prop :=
  X.Nonempty ∧ Y.Nonempty ∧ uniformDeficit X ≤ k ∧ uniformDeficit Y ≤ k ∧
    ∃ r : ℝ, 0 < r ∧ r ≤ p ∧
      ((∀ x ∈ X, IsDensityLimit Y r k x) ∨ (∀ y ∈ Y, IsDensityLimit X r k y))


end Cslib.Communication
