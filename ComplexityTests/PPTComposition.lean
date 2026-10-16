/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Probabilistic.PPT.Composition
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Crypto.Computational.GGM.Evaluation

/-! Functional pipelines use the ordinary monadic interface and existing deterministic proofs. -/

namespace ComplexityTests.PPTComposition

open Cslib Cslib.Probability Turing.MultiTapeTM

-- The result length can depend on randomness, and can be zero.
example : IsPPTOn encBits encBits (fun _ => do
    let bit ← ProbComp.uniform Bool
    pure (if bit then [true, false, true] else [])) := by
  fun_prop

example : IsPPTOn encBits encBool (fun _ => do
    let bit ← ProbComp.uniform Bool
    pure (!bit)) := by
  fun_prop

example {α β γ : Type} {input : α ↪ List Bool} {middle : β ↪ List Bool}
    {output : γ ↪ List Bool} {sample : α → ProbComp β} {finish : β → ProbComp γ}
    (hsample : IsPPTOn input middle sample) (hfinish : IsPPTOn middle output finish) :
    IsPPTOn input output (fun a => do
      let b ← sample a
      finish b) := by
  fun_prop

-- GGM's existing evaluator proof works after any certified seed/path sampler.
example {α : Type} {input : α ↪ List Bool}
    {sample : α → ProbComp (List Bool × List Bool)} {generator : List Bool → List Bool}
    (hsample : IsPPTOn input (encPair encBits encBits) sample)
    (hgenerator : ComputableTidilyInPolyTime generator encBits encBits) :
    IsPPTOn input encBits (fun a => do
      let pair ← sample a
      pure (Crypto.GGM.eval generator pair.1 pair.2)) := by
  fun_prop

-- Preprocessing can traverse unbounded encoded inputs before invoking a certified sampler.
example {sample : List Bool → ProbComp Bool} (hsample : IsPPTOn encBits encBool sample) :
    IsPPTOn encBits encBool (fun word => sample word.reverse) := by
  fun_prop

-- Composition does not turn arbitrary finite-uniform sampling into strict fair-coin PPT.
example : True := by
  let encFin3 : Fin 3 ↪ List Bool := Fin.valEmbedding.trans encNat
  fail_if_success have : IsPPTOn encBits encFin3 (fun _ => ProbComp.uniform (Fin 3)) := by fun_prop
  trivial

end ComplexityTests.PPTComposition
