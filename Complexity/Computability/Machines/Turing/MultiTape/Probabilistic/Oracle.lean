/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Deterministic
public import Complexity.Languages.Probabilistic.Oracle

/-!
# Fair-coin machines with external oracle calls

`runOracle` fixes the coin program of the common machine interpreter and exposes its word-based
external channels. The two effects use disjoint query types: external handlers cannot choose
the machine's private coins. Every live instruction draws one fresh fair bit; query writing and
reply reading still use ordinary machine instructions.

## Main definitions

* `Turing.MultiTapePTM.runOracle`: the clocked run as a `ProbOracleComp` program.

## Main results

* `Turing.MultiTapePTM.length_output_runOracle_le`: the clock bounds supported output lengths.
* `Turing.MultiTapePTM.run_interpret_runOracle_ofDeterministic`: deterministic embedding preserves
  the output and external oracle state.

## References

Adapts the oracle run from the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8` to the common machine and typed sum interface.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib Cslib.Probability MultiTapeMachine

variable {k : ℕ} {Symbol State Operation OracleState : Type} [DecidableEq Operation]

/-- Use private fair coins and submit each channel's accumulated word to the external oracle. -/
noncomputable def runOracle (machine : MultiTapePTM k Symbol State Operation)
    (fuel : ℕ) (input : List Symbol) :
    ProbOracleComp (fun _ : Operation × List Symbol => List Symbol) (List Symbol) :=
  machine.run (ProbOracleComp.sample (ProbComp.uniform Bool))
    (fun op word => ProbOracleComp.query (op, word)) fuel input

/-- Arbitrarily long oracle replies cannot bypass the cost of writing the output. -/
theorem length_output_runOracle_le (machine : MultiTapePTM k Symbol State Operation)
    (oracle : Operation × List Symbol → StateT OracleState PMF (List Symbol))
    (fuel : ℕ) (input output : List Symbol) (s s' : OracleState)
    (h : (output, s') ∈ ((OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (machine.runOracle fuel input)).run s).support) : output.length ≤ fuel := by
  have hbound := MultiTapeMachine.length_output_runFrom_le machine
    (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
    (fun op word => ProbOracleComp.query
      (spec := fun _ : Operation × List Symbol => List Symbol) (op, word))
    (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle) fuel
    (machine.initialConfig input) s s' output h
  simpa only [initialConfig, Cfg.init, List.length_nil, Nat.zero_add] using hbound

/-- A deterministic run ignores the external oracle and preserves its full private state. -/
theorem run_interpret_runOracle_ofDeterministic (machine : MultiTapeTM k Symbol State)
    (oracle : Operation × List Symbol → StateT OracleState PMF (List Symbol))
    (fuel : ℕ) (input : List Symbol) (s : OracleState) :
    (OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        ((ofDeterministic machine).runOracle fuel input)).run s =
      PMF.pure ((machine.runFrom (machine.initCfg input) fuel).output, s) := by
  apply run_interpret_ofDeterministic machine (ProbOracleComp.sample (ProbComp.uniform Bool))
    (fun op word => ProbOracleComp.query
      (spec := fun _ : Operation × List Symbol => List Symbol) (op, word))
    (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
    (PMF.uniformOfFintype Bool)
  intro state
  simp only [ProbOracleComp.run_interpret_sample, ProbComp.eval_uniform]

end Turing.MultiTapePTM
