/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape

/-!
# Writing a word on selected tapes

A tidy computation can write its output onto a selected work tape, using selected blank scratch
tapes and preserving every other tape. The output head and scratch heads finish at cell zero.
This is a specification of the existing output redirection and tape embedding combinators.

## Main results

* `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.outputToWord_extendTapes`: write a word without
  disturbing the unselected tapes or the ambient output.

## References

This combines Christian Reitwiessner's `outputToWord` and `TransformsTapes.extendTapes`
specifications from cslib PR #1111.
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- A tidy computation writes its output on the selected last tape, leaves its selected scratch
tapes blank, and preserves all unselected words. All selected tapes must initially be blank. -/
theorem ComputesTidilyInTimeAndSpace.outputToWord_extendTapes
    {k n : ℕ} {Symbol State : Type*} {machine : MultiTapeTM k Symbol State}
    {input output : List Symbol} {t s : ℕ}
    (h : machine.ComputesTidilyInTimeAndSpace input output t s) (e : Fin (k + 1) ↪ Fin n) :
    TransformsTapes (machine.outputToWord.extendTapes e)
      (fun inp ws => inp = input ∧ ∀ j, ws (e j) = [])
      (fun _ ws ws' emitted => ws' = Function.update ws (e (Fin.last k)) output ∧ emitted = [])
      (t + output.length + 2) (s + 2 * output.length + k + 4 + (n - (k + 1))) := by
  refine (h.outputToWord.extendTapes e).imp (fun _ _ h => ⟨h.1, funext h.2⟩) ?_ le_rfl le_rfl
  rintro inp ws ws' emitted hP ⟨⟨hv, rfl⟩, hx⟩
  refine ⟨funext fun i => ?_, rfl⟩
  by_cases hi : i ∈ Set.range e
  · obtain ⟨j, rfl⟩ := hi
    simpa [Function.update_apply, e.injective.eq_iff, hP.2] using congrFun hv j
  · rw [hx i hi, Function.update_of_ne]
    exact fun h => hi ⟨Fin.last k, h.symm⟩

end Turing.MultiTapeTM
