/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Oracle
public import Complexity.Languages.Probabilistic.Transcript

import Complexity.Languages.Probabilistic.Oracle.Simulation

/-!
# External query budgets for randomized programs

The existing typed transcript records only external requests; private samples use the other
component of `ProbOracleComp.handler` and do not enter the log. This distinction lets an oracle
machine certificate supply call and request-size budgets while leaving private sampling unchanged.
The budgets are semantic bounds, not runtime bounds or restrictions on oracle reply sizes.

## Main definitions

* `Cslib.ProbOracleComp.HasQueryBounds`: external call and request-size bounds with private coins.

## Main results

* `Cslib.ProbOracleComp.run_interpret_withTranscript`: forgetting the log preserves full state.
* `Cslib.ProbOracleComp.HasQueryBounds.bind`: adaptive sequencing adds external call budgets.
* `Cslib.ProbOracleComp.HasQueryBounds.sample`: private samples make no external call.

## References

Adapts `Languages/Probabilistic/Transcript.lean` from the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, reusing its typed log and the general simulation API.
-/

@[expose] public section

namespace Cslib.ProbOracleComp

open OracleComp

variable {Query α State : Type} {Response : Query → Type}

/-- Forgetting the external log preserves the joint result and complete oracle state. -/
theorem run_interpret_withTranscript (oracle : (q : Query) → StateT State PMF (Response q))
    (program : ProbOracleComp Response α) (s : State) (transcript : Transcript Response) :
    ((interpret (handler (fun n => StateT.lift (ProbComp.unifOracle n)) (withTranscript oracle))
      program).run (s, transcript)).map (fun (result, state) => (result, state.1)) =
        (interpret (handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          program).run s := by
  apply ProbOracleComp.run_interpret_map_state (withTranscript oracle) oracle Prod.fst
  intro q state
  simp only [withTranscript, PMF.map_comp, Function.comp_def, Prod.mk.eta]
  exact PMF.map_id _

/-- Fresh external observations are prepended to an existing transcript. Private draws do not
change either part of the log. -/
theorem run_interpret_withTranscript_append
    (oracle : (q : Query) → StateT State PMF (Response q)) (program : ProbOracleComp Response α)
    (s : State) (transcript : Transcript Response) :
    (interpret (handler (fun n => StateT.lift (ProbComp.unifOracle n)) (withTranscript oracle))
      program).run (s, transcript) =
        ((interpret
          (handler (fun n => StateT.lift (ProbComp.unifOracle n)) (withTranscript oracle))
            program).run (s, [])).map (fun (result, state, fresh) =>
              (result, state, fresh ++ transcript)) := by
  symm
  apply ProbOracleComp.run_interpret_map_state (withTranscript oracle) (withTranscript oracle)
    (fun state => (state.1, state.2 ++ transcript))
  intro q state
  simp [withTranscript, PMF.map_comp, Function.comp_def]

/-- Uniform external call and request-size bounds, with fresh private samples. No bound on
ordinary computation or the oracle's reply sizes is asserted. -/
def HasQueryBounds (program : ProbOracleComp Response α) (size : Query → ℕ)
    (calls maxSize : ℕ) : Prop :=
  ∀ (State : Type) (oracle : (q : Query) → StateT State PMF (Response q))
    (s s' : State) (result : α) (transcript : Transcript Response),
    (result, s', transcript) ∈ ((interpret
      (handler (fun n => StateT.lift (ProbComp.unifOracle n)) (withTranscript oracle))
        program).run (s, [])).support →
      transcript.length ≤ calls ∧ ∀ entry ∈ transcript, size entry.1 ≤ maxSize

/-- Returning a value makes no external call. -/
theorem HasQueryBounds.pure (a : α) (size : Query → ℕ) (maxSize : ℕ) :
    HasQueryBounds (pure a : ProbOracleComp Response α) size 0 maxSize := by
  simp +contextual [HasQueryBounds]

/-- A closed sampler does not call the external oracle, independently of its own runtime. -/
theorem HasQueryBounds.sample (program : ProbComp α) (size : Query → ℕ) (maxSize : ℕ) :
    HasQueryBounds (ProbOracleComp.sample (spec := Response) program) size 0 maxSize := by
  intro State oracle s s' result transcript h
  rw [run_interpret_sample, PMF.mem_support_map_iff] at h
  obtain ⟨_, _, heq⟩ := h
  cases heq
  simp

/-- A single external request uses one call, regardless of the size or content of its reply. -/
theorem HasQueryBounds.query (q : Query) (size : Query → ℕ) {maxSize : ℕ}
    (hsize : size q ≤ maxSize) :
    HasQueryBounds (ProbOracleComp.query (spec := Response) q) size 1 maxSize := by
  intro State oracle s s' result transcript h
  simp only [ProbOracleComp.interpret_query, StateT.run, withTranscript,
    PMF.mem_support_map_iff] at h
  obtain ⟨⟨answer, next⟩, _, heq⟩ := h
  cases heq
  simpa using hsize

/-- Adaptive sequencing adds external call budgets under a common request-size bound. -/
theorem HasQueryBounds.bind {β : Type} {program : ProbOracleComp Response α}
    {next : α → ProbOracleComp Response β} {size : Query → ℕ} {firstCalls nextCalls maxSize : ℕ}
    (hfirst : HasQueryBounds program size firstCalls maxSize)
    (hnext : ∀ a, HasQueryBounds (next a) size nextCalls maxSize) :
    HasQueryBounds (program >>= next) size (firstCalls + nextCalls) maxSize := by
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

/-- Increasing either external query bound preserves the contract. -/
theorem HasQueryBounds.mono {program : ProbOracleComp Response α} {size : Query → ℕ}
    {calls maxSize calls' maxSize' : ℕ} (h : HasQueryBounds program size calls maxSize)
    (hcalls : calls ≤ calls') (hsize : maxSize ≤ maxSize') :
    HasQueryBounds program size calls' maxSize' := by
  intro State oracle s s' result transcript hresult
  obtain ⟨hcount, hlength⟩ := h State oracle s s' result transcript hresult
  exact ⟨hcount.trans hcalls, fun entry hentry => (hlength entry hentry).trans hsize⟩

/-- Deterministic result postprocessing leaves the external transcript unchanged. -/
@[simp] theorem hasQueryBounds_map_iff {β : Type} (f : α → β)
    (program : ProbOracleComp Response α) (size : Query → ℕ) (calls maxSize : ℕ) :
    HasQueryBounds (f <$> program) size calls maxSize ↔
      HasQueryBounds program size calls maxSize := by
  simp only [HasQueryBounds, interpret_map, StateT.run_map, PMF.monad_map_eq_map,
    PMF.mem_support_map_iff]
  constructor
  · exact fun h S oracle s s' a transcript ha =>
      h S oracle s s' (f a) transcript ⟨(a, s', transcript), ha, rfl⟩
  · rintro h S oracle s s' b transcript ⟨⟨a, t, seen⟩, ha, heq⟩
    cases heq
    exact h S oracle s _ a _ ha

end Cslib.ProbOracleComp
