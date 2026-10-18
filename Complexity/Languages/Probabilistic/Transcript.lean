/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Simulation

/-!
# Observing oracle transcripts

`withTranscript` records each query and its answer while preserving the oracle's private state.
Entries are stored newest first. Forgetting the transcript recovers the original execution,
including its final private state.

`HasQueryBounds` expresses uniform bounds on the number and size of queries, independently of
the machine model. Deriving these bounds from an oracle PPT certificate remains separate work.

This is semantic instrumentation, not a claim that recording arbitrary replies is efficient.
In particular, a machine's clock bounds its requests but need not bound the oracle's replies.

## Main definitions

* `Cslib.OracleComp.Transcript`, `.withTranscript`: typed query logging with private state.
* `Cslib.OracleComp.HasQueryBounds`: uniform supported bounds on request count and size.

## Main results

* `Cslib.OracleComp.run_interpret_withTranscript`: forgetting the log preserves full execution.
* `Cslib.OracleComp.run_interpret_withTranscript_append`: retain an existing transcript suffix.

## References

Adapted from `Languages/Probabilistic/Transcript.lean` on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the single `OracleComp.interpret` interface.
-/

@[expose] public section

namespace Cslib.OracleComp

universe u

variable {Query : Type u} {Response : Query → Type u} {State α : Type u}

/-- Queries and their typed replies, stored in reverse chronological order. -/
abbrev Transcript (Response : Query → Type u) := List ((q : Query) × Response q)

/-- Observe calls without changing the underlying oracle's replies or private state. -/
noncomputable def withTranscript (oracle : (q : Query) → StateT State PMF (Response q))
    (q : Query) : StateT (State × Transcript Response) PMF (Response q) :=
  fun (s, transcript) => (oracle q s).map
    (fun (answer, s') => (answer, (s', ⟨q, answer⟩ :: transcript)))

/-- Forgetting the transcript preserves the result and the oracle's complete final state. -/
theorem run_interpret_withTranscript (oracle : (q : Query) → StateT State PMF (Response q))
    (program : OracleComp Response α) (s : State) (transcript : Transcript Response) :
    ((interpret (withTranscript oracle) program).run (s, transcript)).map
        (fun (result, state) => (result, state.1)) = (interpret oracle program).run s := by
  apply run_interpret_map_state (withTranscript oracle) oracle Prod.fst
  intro q state
  simp only [withTranscript, PMF.map_comp, Function.comp_def, Prod.mk.eta]
  exact PMF.map_id _

/-- An existing transcript is an untouched suffix of the newly recorded interaction. -/
theorem run_interpret_withTranscript_append (oracle : (q : Query) → StateT State PMF (Response q))
    (program : OracleComp Response α) (s : State) (transcript : Transcript Response) :
    (interpret (withTranscript oracle) program).run (s, transcript) =
      ((interpret (withTranscript oracle) program).run (s, [])).map
        (fun (result, state, fresh) => (result, state, fresh ++ transcript)) := by
  symm
  apply run_interpret_map_state (withTranscript oracle) (withTranscript oracle)
    (fun state => (state.1, state.2 ++ transcript))
  intro q state
  simp [withTranscript, PMF.map_comp, Function.comp_def]

/-- Every possible interaction makes at most `calls` queries, each of size at most `maxSize`.
The bound is uniform in the oracle and its initial private state; it asserts no runtime bound. -/
def HasQueryBounds (program : OracleComp Response α) (size : Query → ℕ)
    (calls maxSize : ℕ) : Prop :=
  ∀ (State : Type u) (oracle : (q : Query) → StateT State PMF (Response q))
    (s s' : State) (result : α) (transcript : Transcript Response),
    (result, s', transcript) ∈ ((interpret (withTranscript oracle) program).run (s, [])).support →
      transcript.length ≤ calls ∧ ∀ entry ∈ transcript, size entry.1 ≤ maxSize

/-- Returning a value makes no oracle call. -/
theorem HasQueryBounds.pure (a : α) (size : Query → ℕ) (maxSize : ℕ) :
    (pure a : OracleComp Response α).HasQueryBounds size 0 maxSize := by
  simp +contextual [HasQueryBounds]

/-- One typed query uses one call, independently of its answer or the oracle's private state. -/
theorem HasQueryBounds.query (q : Query) (size : Query → ℕ) {maxSize : ℕ}
    (hsize : size q ≤ maxSize) :
    (query (spec := Response) q).HasQueryBounds size 1 maxSize := by
  intro State oracle s s' result transcript h
  simp only [interpret_query, StateT.run, withTranscript, PMF.mem_support_map_iff] at h
  obtain ⟨⟨answer, next⟩, _, heq⟩ := h
  cases heq
  simpa using hsize

/-- Adaptive sequencing adds call budgets when all continuations share a request-size bound. -/
theorem HasQueryBounds.bind {β : Type u} {program : OracleComp Response α}
    {next : α → OracleComp Response β} {size : Query → ℕ} {firstCalls nextCalls maxSize : ℕ}
    (hfirst : program.HasQueryBounds size firstCalls maxSize)
    (hnext : ∀ a, (next a).HasQueryBounds size nextCalls maxSize) :
    (program >>= next).HasQueryBounds size (firstCalls + nextCalls) maxSize := by
  intro State oracle s s' result transcript h
  simp only [interpret_bind, StateT.run_bind, Probability.PMF.monad_bind_eq_bind,
    PMF.mem_support_bind_iff] at h
  obtain ⟨⟨a, middle, seen⟩, hbefore, hafter⟩ := h
  obtain ⟨hcount, hsize⟩ := hfirst State oracle s middle a seen hbefore
  rw [run_interpret_withTranscript_append oracle (next a) middle seen,
    PMF.mem_support_map_iff] at hafter
  obtain ⟨⟨result', finish, fresh⟩, hfresh, heq⟩ := hafter
  cases heq
  obtain ⟨hcount', hsize'⟩ := hnext a State oracle middle _ _ fresh hfresh
  refine ⟨by simp only [List.length_append]; lia, ?_⟩
  intro entry hentry
  exact (List.mem_append.mp hentry).elim (hsize' entry) (hsize entry)

/-- Increasing either query bound preserves its validity. -/
theorem HasQueryBounds.mono {program : OracleComp Response α} {size : Query → ℕ}
    {calls maxSize calls' maxSize' : ℕ} (h : program.HasQueryBounds size calls maxSize)
    (hcalls : calls ≤ calls') (hsize : maxSize ≤ maxSize') :
    program.HasQueryBounds size calls' maxSize' := by
  intro State oracle s s' result transcript hresult
  obtain ⟨hcount, hlength⟩ := h State oracle s s' result transcript hresult
  exact ⟨hcount.trans hcalls, fun entry hentry => (hlength entry hentry).trans hsize⟩

/-- Postprocessing the returned value leaves the oracle transcript unchanged. -/
@[simp] theorem hasQueryBounds_map_iff {β : Type u} (f : α → β)
    (program : OracleComp Response α) (size : Query → ℕ) (calls maxSize : ℕ) :
    (f <$> program).HasQueryBounds size calls maxSize ↔
      program.HasQueryBounds size calls maxSize := by
  simp only [HasQueryBounds, interpret_map, StateT.run_map, PMF.monad_map_eq_map,
    PMF.mem_support_map_iff]
  constructor
  · exact fun h S oracle s s' a transcript ha =>
      h S oracle s s' (f a) transcript ⟨(a, s', transcript), ha, rfl⟩
  · rintro h S oracle s s' b transcript ⟨⟨a, t, seen⟩, ha, heq⟩
    cases heq
    exact h S oracle s _ a _ ha

end Cslib.OracleComp
