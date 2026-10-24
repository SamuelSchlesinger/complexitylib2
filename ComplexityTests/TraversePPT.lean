/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Probabilistic.Traverse
import Complexity.Tactic.PPT

/-! Ordinary traversal automation charges every element, result and captured input. -/

namespace ComplexityTests.TraversePPT

open Cslib Cslib.Probability Turing.MultiTapeTM

example (program : List Bool → ProbComp Bool) (h : IsPPTOn encBits encBool program) :
    IsPPTOn (encList encBits) (encList encBool) (fun words => words.mapM program) := by ppt

-- Both the number and lengths of the words vary at runtime, with a fresh draw for each word.
example : IsPPTOn (encList encBits) (encList encBits) (fun words : List (List Bool) =>
    words.mapM fun word => do
      let bit ← ProbComp.uniform Bool
      pure (bit :: word)) := by ppt

-- Every call captures the complete prefix; the input list and prefix both grow independently.
example : IsPPTOn (encPair encBits (encList encBits)) (encList encBits)
    (fun input : List Bool × List (List Bool) =>
      input.2.mapM fun word => pure (input.1 ++ word)) := by ppt

example {α : Type} {input : α ↪ List Bool} {words : α → List (List Bool)}
    {program : α → List Bool → ProbComp Bool}
    (hwords : ComputableInPolyTime words input (encList encBits))
    (hprogram : IsPPTOn (encPair input encBits) encBool (fun p => program p.1 p.2)) :
    IsPPTOn input (encList encBool) (fun a => (words a).mapM (program a)) := by ppt

example (program : Bool → ProbComp Bool) :
    ProbComp.eval (([] : List Bool).mapM program) = PMF.pure [] := rfl

-- With two independent fair draws, every ordered result has mass one quarter.
example : ProbComp.eval ([false, true].mapM (fun _ => ProbComp.uniform Bool)) [true, false] =
    1 / 4 := by
  norm_num [List.mapM_cons, List.mapM_nil, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbComp.eval_uniform, PMF.bind_apply, PMF.pure_apply, tsum_fintype]
  rw [← ENNReal.mul_inv] <;> norm_num

-- An arbitrary per-element program is not automatically certified.
example (_program : List Bool → ProbComp Bool) : True := by
  fail_if_success
    have : IsPPTOn (encList encBits) (encList encBool)
        (fun words => words.mapM _program) := by ppt
  trivial

end ComplexityTests.TraversePPT
