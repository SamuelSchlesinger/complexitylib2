/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Oracle
public import Complexity.Languages.Probabilistic.Oracle.Transcript

/-!
# External query bounds from the machine clock

Each instruction makes at most one external request and writes at most one symbol per query
buffer. Starting from empty channels, a run of `fuel` instructions therefore makes at most
`fuel` external calls, each with a request length at most `fuel`. Private coins are sampled
independently and do not count as external requests. The bound permits arbitrarily long replies
and arbitrary state shared by the external handlers.

## Main results

* `Turing.MultiTapePTM.query_bounds_runFrom`: bounds from a partial run and its initial buffers.
* `Turing.MultiTapePTM.query_bounds_runOracle`: the clock bounds calls and request lengths.

## References

Adapted from `Computability/Machines/Turing/MultiTape/Oracle/QueryBounds.lean` on the cslib
`crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the common machine.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib MultiTapeMachine

variable {k : ℕ} {Symbol Control Operation Query State : Type} [DecidableEq Operation]
  {input : List Symbol}

/-- A partial run adds at most one external call per instruction. Requests fit within the
initial buffer bound plus elapsed time, regardless of the oracle's reply sizes. -/
theorem query_bounds_runFrom (machine : MultiTapePTM k Symbol Control Operation)
    (request : Operation → List Symbol → Query) (size : Query → ℕ)
    (hrequest : ∀ op word, size (request op word) ≤ word.length)
    (oracle : Query → StateT State PMF (List Symbol)) (fuel : ℕ)
    (cfg : Config k Symbol Control Operation input) (bound : ℕ)
    (hbuffers : ∀ op, (cfg.channels op).queryBuffer.length ≤ bound)
    (s s' : State) (transcript transcript' : OracleComp.Transcript
      (fun _ : Query => List Symbol)) (output : List Symbol)
    (htranscript : ∀ entry ∈ transcript, size entry.1 ≤ bound)
    (h : (output, s', transcript') ∈ ((OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n))
        (OracleComp.withTranscript oracle))
      (machine.runFrom (ProbOracleComp.sample (ProbComp.uniform Bool))
        (fun op word => ProbOracleComp.query (request op word)) fuel cfg)).run
          (s, transcript)).support) :
    transcript'.length ≤ transcript.length + fuel ∧
      ∀ entry ∈ transcript', size entry.1 ≤ bound + fuel := by
  induction fuel generalizing cfg bound s transcript with
  | zero =>
    simp only [runFrom_zero, OracleComp.interpret_pure, StateT.run_pure,
      Probability.PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at h
    rw [h.2.2]
    exact ⟨by simp, by simpa using htranscript⟩
  | succ fuel ih =>
    cases hs : cfg.tapes.state with
    | none =>
      simp only [runFrom_succ, hs, OracleComp.interpret_pure, StateT.run_pure,
        Probability.PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at h
      rw [h.2.2]
      exact ⟨by simp, fun entry hentry => (htranscript entry hentry).trans (Nat.le_add_right ..)⟩
    | some control =>
      simp only [runFrom_succ, hs, OracleComp.interpret_bind, StateT.run_bind,
        ProbOracleComp.run_interpret_sample, ProbComp.eval_uniform,
        Probability.PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def,
        PMF.mem_support_bind_iff] at h
      obtain ⟨coin, _, h⟩ := h
      cases ha : machine.tr control cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbols coin with
      | step action symbol move =>
        rw [ha] at h
        have hnext : ∀ op, ((cfg.step action symbol move).channels op).queryBuffer.length ≤
            bound + 1 := by
          intro op
          simp only [Config.step, List.length_append]
          exact Nat.add_le_add (hbuffers op) (symbol op).length_toList_le
        obtain ⟨hcount, hsize⟩ := ih _ (bound + 1) hnext _ _
          (fun entry hentry => (htranscript entry hentry).trans (Nat.le_add_right ..)) h
        exact ⟨by lia, fun entry hentry => by have := hsize entry hentry; lia⟩
      | query op next =>
        simp only [ha, OracleComp.interpret_bind, StateT.run_bind,
          Probability.PMF.monad_bind_eq_bind, ProbOracleComp.interpret_query] at h
        simp only [StateT.run, OracleComp.withTranscript, PMF.bind_map, Function.comp_def,
          PMF.mem_support_bind_iff] at h
        obtain ⟨⟨answer, nextState⟩, _, h⟩ := h
        have hnext : ∀ operation,
            ((cfg.receive op next answer).channels operation).queryBuffer.length ≤ bound := by
          intro operation
          by_cases heq : operation = op
          · subst operation
            simp [Config.receive]
          · simpa [Config.receive, heq] using hbuffers operation
        obtain ⟨hcount, hsize⟩ := ih _ bound hnext _ _ (by
          intro entry hentry
          rcases List.mem_cons.mp hentry with rfl | hentry
          · exact (hrequest op _).trans (hbuffers op)
          · exact htranscript entry hentry) h
        exact ⟨by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcount,
          fun entry hentry => (hsize entry hentry).trans (by lia)⟩

/-- From blank channels, the same clock bounds external calls and every request length. -/
theorem query_bounds_runOracle (machine : MultiTapePTM k Symbol Control Operation)
    (fuel : ℕ) (input : List Symbol) :
    ProbOracleComp.HasQueryBounds (machine.runOracle fuel input)
      (fun request => request.2.length) fuel fuel := by
  intro State oracle s s' output transcript h
  simpa using query_bounds_runFrom machine (fun op word => (op, word))
    (fun request => request.2.length) (by intros; exact le_rfl) oracle fuel
    (machine.initialConfig input) 0 (by simp [initialConfig])
    s s' [] transcript output (by simp) h

end Turing.MultiTapePTM
