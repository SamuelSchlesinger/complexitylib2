/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Plumbing/TransformsTapes.lean`; bridges the `runFrom` form of
-- `TransformsTapes` in crei:crei/tidy-universal @7f7c0696 to the run paths of cslib #1117)

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes
public import Complexity.Computability.Machines.Turing.MultiTape.TapeLemmas

/-!
# Tape transformations as runs

`Turing.MultiTapeTM.TransformsTapes` asks for a run path to the halted normal form within the time
and space bounds. Since a deterministic machine stays where it halted, this is the same as asking
that the run of exactly `t` steps ends in the normal form, using at most `s` cells: the form in
which Christian Reitwiessner's branch `crei/tidy-universal` states and proves its specifications.

## Main results

* `Turing.MultiTapeTM.transformsTapes_iff_runFrom`: a tape transformation, read on runs.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {tm : MultiTapeTM k Symbol State}

/-- **A tape transformation, read on runs.** `TransformsTapes tm P Q t s` holds exactly when, on
words `ws` satisfying `P`, the run of `t` steps ends in the halted normal form, holding words `ws'`
and having emitted `emitted` with `Q input ws ws' emitted`, and uses at most `s` cells. -/
theorem transformsTapes_iff_runFrom
    {P : (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {Q : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) →
      List Symbol → Prop} {t s : ℕ} :
    TransformsTapes tm P Q t s ↔ ∀ (input : List Symbol) (ws : Fin k → List Symbol)
      (out : List Symbol), P input ws → ∃ ws' emitted,
        tm.runFrom (wordsCfg input (some tm.q₀) ws out) t =
          wordsCfg input none ws' (out ++ emitted) ∧
        Q input ws ws' emitted ∧ tm.space (wordsCfg input (some tm.q₀) ws out) t ≤ s := by
  refine forall₄_congr fun input ws out _ => exists₂_congr fun ws' emitted => ?_
  rw [exists_runPath_iff_runFrom rfl]
  tauto

end Turing.MultiTapeTM
