/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration

/-!
# Fixed division of unary counters

A quotient/remainder loop scans the unary input. One invariant proves its arithmetic
specification and the linear bound on encoded intermediate states.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_div_const`: division by a fixed natural.

## References

The machine realization uses the invariant-based loop calculus in `PolyTime.Iteration`.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- Division by any fixed natural is polynomial time on unary counters, including division by
zero with Lean's convention. The loop maintains a quotient and a remainder. -/
@[fun_prop]
theorem unary_div_const (divisor : ℕ) :
    ComputableTidilyInPolyTime (fun n : ℕ => n / divisor) encUnary encUnary := by
  rcases Nat.eq_zero_or_pos divisor with rfl | hpos
  · simpa using (const (encIn := encUnary) (encMid := encUnary) 0)
  let step (state : ℕ × ℕ) :=
    if state.2 + 1 == divisor then (state.1 + 1, 0) else (state.1, state.2 + 1)
  have hstep : ComputableTidilyInPolyTime step (encPair encUnary encUnary)
      (encPair encUnary encUnary) := by unfold step; fun_prop
  obtain ⟨hefficient, hspec⟩ := iterate_spec (count := id) (init := fun _ => (0, 0))
    (encIn := encUnary) id' (const (0, 0)) hstep
    (fun _ i state => i = divisor * state.1 + state.2 ∧ state.2 < divisor)
    (fun _ => by simp [hpos]) (fun _ i state _ h => by
      dsimp only [step]
      split <;> rename_i htest
      · dsimp only
        have heq : state.2 + 1 = divisor := by simpa using htest
        exact ⟨by nlinarith [h.1], hpos⟩
      · dsimp only
        have hne : state.2 + 1 ≠ divisor := by simpa using htest
        exact ⟨by nlinarith [h.1], by lia⟩)
    (size := fun n => 2 * n + 1) (by fun_prop) (fun _ i state hi h => by
      simp only [length_encPair, encUnary_apply, List.length_replicate]
      simp only [id_eq] at hi
      nlinarith [h.1, h.2])
  simp only [id_eq] at hspec hefficient
  have hquot (n : ℕ) : (step^[n] (0, 0)).1 = n / divisor := by
    symm
    apply Nat.div_eq_of_lt_le <;> nlinarith [(hspec n).1, (hspec n).2]
  simpa only [Function.comp_def, id_eq, hquot] using hefficient.fst'

end Turing.MultiTapeTM.ComputableTidilyInPolyTime
