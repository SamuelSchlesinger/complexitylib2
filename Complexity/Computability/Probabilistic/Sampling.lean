/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.PPT

/-!
# Certified fair-bit sampling

The finite-uniform Boolean program has a one-instruction machine realization. This primitive is
independent of the input and is registered with `fun_prop`. Larger samplers need their own
resource-certified constructions; finite uniformity alone does not imply strict fair-coin PPT.

## Main results

* `Cslib.Probability.isPPTOn_uniform_bool`: one fair bit is uniformly PPT.
-/

@[expose] public section

namespace Cslib.Probability

private def coinMachine : Turing.MultiTapePTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ bit := .step
    { inputTape := 0, workTapes := Fin.elim0, output := some bit, state := none }
    Empty.elim Empty.elim

/-- Sampling one fair bit is strict PPT for every fixed input encoding. -/
@[fun_prop]
theorem isPPTOn_uniform_bool {α : Type} (input : α ↪ List Bool) :
    IsPPTOn input Turing.MultiTapeTM.encBool (fun _ => ProbComp.uniform Bool) := by
  refine ⟨0, Unit, inferInstance, coinMachine, 1, 0, fun a => ?_⟩
  change (ProbComp.eval (ProbComp.uniform Bool)).map (fun bit => [bit]) = _
  simp [Turing.MultiTapePTM.runClosed, Turing.MultiTapePTM.run, Turing.MultiTapePTM.runFrom,
    Turing.MultiTapePTM.runConfigFrom, Turing.MultiTapeMachine.runConfigFrom, coinMachine,
    Turing.MultiTapeMachine.initialConfig, Turing.Cfg.init, Turing.MultiTapeMachine.Config.step,
    Turing.Action.apply]

end Cslib.Probability
