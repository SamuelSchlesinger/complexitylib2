/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import Complexity.Crypto.Game

/-! Clients of pointwise and common-mixture game advantage bounds. -/

namespace ComplexityTests.GameBounds

open Cslib Cslib.Crypto
open scoped NNReal ENNReal

-- Mutual probability bounds compose through an arbitrary common first-stage sampler.
example {α : Type*} (d : PMF α) (game1 game2 : α → Game) (ε : ℝ≥0)
    (h1 : ∀ a, game1 a true ≤ game2 a true + (ε : ℝ≥0∞))
    (h2 : ∀ a, game2 a true ≤ game1 a true + (ε : ℝ≥0∞)) :
    (Game.advantage (d.bind game1) (d.bind game2) : ℝ) ≤ ε := by
  apply Game.advantage_bind_le
  intro a
  simpa using Game.advantage_le_of_apply_le (B := (ε : ℝ≥0∞)) (by simp) (h1 a) (h2 a)

-- Zero advantage is preserved without requiring a finite first-stage type.
example (d : PMF ℕ) (game : ℕ → Game) :
    (Game.advantage (d.bind game) (d.bind game) : ℝ) ≤ 0 := by
  apply Game.advantage_bind_le
  intro n
  simp

-- The finite-error premise matters: top has real value zero, but these games differ maximally.
example : ¬ ((Game.advantage (PMF.pure true) (PMF.pure false) : ℝ) ≤ (⊤ : ℝ≥0∞).toReal) := by
  simp [Game.succProbability]

end ComplexityTests.GameBounds
