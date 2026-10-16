/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.Oracle
public import Complexity.Computability.Probabilistic.PPT
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite
import Complexity.Computability.Probabilistic.Realization.OracleSimulation
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Efficient stateful oracle substitution

A certified oracle program can be interpreted against a closed stateful PPT handler. A local
invariant bounds reply length and the amount of encoded private storage added per call. The
result is a closed PPT program returning both the original result and the final handler state.
The proof charges the native interpreter, captured inputs, requests, replies and all stored data.

The machine, clock, finite configurations and query bounds remain internal. Individually efficient
calls alone do not suffice: repeatedly doubling the state does not satisfy a resource allowance
that depends only on the caller and request.

## Main results

* `Cslib.Probability.IsOraclePPTOn.run_interpret_preprocess`: efficient substitution with captured
  caller data, a local state invariant and an efficiently computed resource allowance.

## References

Adapts `Computability/Probabilistic/OracleSimulation.lean` on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the shared `OracleComp.interpret` interface.
-/

@[expose] public section

namespace Cslib.Probability

open Turing.MultiTapeTM

/-- Substitute a stateful handler into an oracle program, preserving the joint output/state law.
The efficiently computed allowance bounds each reply and the added encoded state. One invariant
must hold on every supported transition; clocks and storage bounds are derived internally. -/
theorem IsOraclePPTOn.run_interpret_preprocess {Operation α β Caller State : Type}
    [DecidableEq Operation] [Finite Operation]
    {source : α ↪ List Bool} {input : Caller ↪ List Bool} {output : β ↪ List Bool}
    {stateEncoding : State ↪ List Bool} {program : α → WordOracleComp Operation β}
    {handler : Caller → Operation × List Bool → State → ProbComp (List Bool × State)}
    {prepare : Caller → α} {initial : Caller → State} {resources : Caller → List Bool → ℕ}
    (hprogram : IsOraclePPTOn source output program)
    (hprepare : ComputableTidilyInPolyTime prepare input source)
    (hhandler : IsPPTOn
      (encPair input (encPair (encPair (encFinite Operation) encBits) stateEncoding))
      (encPair encBits stateEncoding) (fun pair => handler pair.1 pair.2.1 pair.2.2))
    (hinitial : ComputableTidilyInPolyTime initial input stateEncoding)
    (invariant : Caller → State → Prop) (hinit : ∀ a, invariant a (initial a))
    (hresources : ComputableTidilyInPolyTime (fun pair => resources pair.1 pair.2)
      (encPair input encBits) encUnary)
    (hpreserve : ∀ a request state, invariant a state →
      ∀ result ∈ (ProbComp.eval (handler a request state)).support,
        invariant a result.2 ∧ result.1.length ≤ resources a request.2 ∧
        (stateEncoding result.2).length ≤ (stateEncoding state).length + resources a request.2) :
    IsPPTOn input (encPair output stateEncoding) (fun a =>
      (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifFin n)) (handler a))
          (program (prepare a))).run (initial a)) := by
  obtain ⟨resourceCoeff, resourceDegree, hbound⟩ := hresources.polyBounded_length
  let allowance := fun size => resourceCoeff * (2 * size + 2) ^ resourceDegree
  have hallowance : PolynomiallyBounded allowance := by unfold allowance; fun_prop
  have hbound' (a : Caller) (query : List Bool) :
      resources a query ≤ allowance ((input a).length + query.length) := by
    have h := hbound (a, query)
    simp only [encUnary_apply, List.length_replicate, length_encPair, encBits_apply] at h
    exact h.trans (Nat.mul_le_mul_left resourceCoeff
      (Nat.pow_le_pow_left (by lia) resourceDegree))
  obtain ⟨_, k, Control, hfinite, machine, c, d, hrealize⟩ := hprogram
  let _ := hfinite
  have hword : ComputableTidilyInPolyTime (fun a => source (prepare a)) input encBits :=
    hprepare.of_enc_eq (fun _ => rfl)
  have hcount : ComputableTidilyInPolyTime
      (fun a => c * ((source (prepare a)).length + 1) ^ d) input encUnary := by
    have hclock : ComputableTidilyInPolyTime (fun n => c * (n + 1) ^ d) encUnary encUnary := by
      fun_prop
    exact hclock.comp (ComputableTidilyInPolyTime.length_bits.comp hword)
  have hrun := OracleSimulation.isPPTOn_run machine hword hcount hhandler hinitial
    invariant hinit hallowance (fun a request state hstate result hresult => by
      obtain ⟨hstate', hreply, hgrowth⟩ := hpreserve a request state hstate result hresult
      exact ⟨hstate', hreply.trans (hbound' a request.2),
        hgrowth.trans (Nat.add_le_add_left (hbound' a request.2) _)⟩)
  apply isPPTOn_iff_encoded.mpr
  refine (isPPTOn_iff_encoded.mp hrun).congr ?_
  intro a
  have h := hrealize (prepare a) State
    (fun request state => ProbComp.eval (handler a request state)) (initial a)
  rw [OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map] at h
  simp only [ProbComp.eval_map, ProbOracleComp.eval_run_interpret]
  rw [← h, PMF.map_comp]
  rfl

end Cslib.Probability
