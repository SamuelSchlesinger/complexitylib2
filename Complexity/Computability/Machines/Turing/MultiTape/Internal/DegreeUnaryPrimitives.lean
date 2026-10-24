/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Unary

/-!
# Direct unary degree primitives

Streaming machines implement successor and saturating predecessor with linear cost and output
growth. No higher tidy computability calculus is used.
-/

@[expose] public section
namespace Turing.MultiTapeTM
namespace Internal.Unary

/-- Copy the input and append one unary symbol. -/
private def succT : Transducer Bool Unit where
  q₀ := ()
  step _ b := ((), [b])
  final _ := [true]
  length_step_le _ _ := by simp
  length_final_le _ := by simp

private lemma succT_run (w : List Bool) : succT.run () w = w ++ [true] := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    change [b] ++ succT.run () w = (b :: w) ++ [true]
    simp [ih]

/-- Drop the first unary symbol and copy the remaining input. -/
private def predT : Transducer Bool Bool where
  q₀ := false
  step seen b := (true, if seen then [b] else [])
  final _ := []
  length_step_le seen _ := by cases seen <;> simp
  length_final_le _ := by simp

private lemma predT_run_true (w : List Bool) : predT.run true w = w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    change [b] ++ predT.run true w = b :: w
    simp [ih]

private lemma predT_run (w : List Bool) : predT.run false w = w.tail := by
  cases w with
  | nil => rfl
  | cons b w =>
    change [] ++ predT.run true w = w
    simp [predT_run_true]

end Internal.Unary
namespace ComputableInDegree
open Internal.Unary

/-- Successor on unary natural numbers, including the empty encoding of zero. -/
theorem unary_succ : ComputableInDegree (· + 1) encUnary encUnary 1 1 := by
  refine ⟨⟨fun n => 2 * (encUnary n).length + 3, fun _ => 0,
    ⟨3, fun _ => by simp only [pow_one]; omega⟩, DegreeBounded.const 0,
    0, _, inferInstance, succT.toTM, fun n => ?_⟩,
    ⟨1, fun n => by simp⟩⟩
  have heq : encUnary (n + 1) = succT.run succT.q₀ (encUnary n) := by
    rw [show succT.q₀ = () from rfl, succT_run]
    simp [List.replicate_add]
  simpa only [heq] using succT.computesInTimeAndSpace_toTM (encUnary n)

/-- Saturating predecessor on unary natural numbers. -/
theorem unary_pred : ComputableInDegree (· - 1) encUnary encUnary 1 1 := by
  refine ⟨⟨fun n => 2 * (encUnary n).length + 3, fun _ => 0,
    ⟨3, fun _ => by simp only [pow_one]; omega⟩, DegreeBounded.const 0,
    0, _, inferInstance, predT.toTM, fun n => ?_⟩,
    ⟨1, fun n => by simp; omega⟩⟩
  have heq : encUnary (n - 1) = predT.run predT.q₀ (encUnary n) := by
    rw [show predT.q₀ = false from rfl, predT_run]
    cases n <;> simp [List.replicate_succ]
  simpa only [heq] using predT.computesInTimeAndSpace_toTM (encUnary n)

end ComputableInDegree
end Turing.MultiTapeTM
