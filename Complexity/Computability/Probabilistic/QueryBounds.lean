/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.Oracle
public import Complexity.Languages.Probabilistic.Oracle.Transcript
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.QueryBounds

/-!
# Polynomial external query budgets

An oracle PPT certificate implies polynomial bounds on the number and encoded length of external
requests. The derivation instruments the shared oracle state with a transcript and uses the
certificate's equality of the full final-state distribution. It does not assume a separate query
bound or restrict oracle reply sizes. Private randomness is independent and is not logged.

## Main results

* `Cslib.Probability.IsOraclePPTOn.query_bounds`: one polynomial bounds calls and request lengths
  uniformly over all inputs and shared stateful oracles.

## References

Adapted from Computability/Probabilistic/QueryBounds.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the current word-oracle realization contract.
-/

@[expose] public section

namespace Cslib.Probability

/-- Instrumenting the private state transfers the machine clock's query bounds to the program.
The same machine polynomial controls call count and request length. -/
theorem IsOraclePPTOn.query_bounds {Operation α β : Type} [DecidableEq Operation]
    {input : α ↪ List Bool} {output : β ↪ List Bool}
    {program : α → WordOracleComp Operation β} (h : IsOraclePPTOn input output program) :
    ∃ c d : ℕ, ∀ a, ProbOracleComp.HasQueryBounds (program a) (fun request => request.2.length)
      (c * ((input a).length + 1) ^ d) (c * ((input a).length + 1) ^ d) := by
  obtain ⟨_, k, Control, _, machine, c, d, h⟩ := h
  refine ⟨c, d, fun a => ?_⟩
  rw [← ProbOracleComp.hasQueryBounds_map_iff output]
  intro State oracle s s' result transcript hresult
  rw [h a (State × OracleComp.Transcript (fun _ : Operation × List Bool => List Bool))
    (OracleComp.withTranscript oracle) (s, [])] at hresult
  exact machine.query_bounds_runOracle _ (input a) State oracle s s' result transcript hresult

end Cslib.Probability
