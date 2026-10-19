/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Oracle
public import Complexity.Languages.Probabilistic.Iteration

/-!
# Possible results of randomized oracle programs

A result is possible when some stateful external handler, initial oracle state and private coin
sequence produce it. Invariants of adaptive loops quantify over these results, so they remain
valid for every shared oracle and every reply length.

## Main definitions

* `Cslib.ProbOracleComp.support`: results produced under some stateful external handler.

## Main results

* `Cslib.ProbOracleComp.mem_support_bind`: a possible result of a sequence factors through a
  possible intermediate result.
* `Cslib.ProbOracleComp.support_sample_subset`: private samples stay in their closed support.
* `Cslib.ProbOracleComp.iterate_invariant`: an invariant preserved by every possible step holds
  for every possible result of a bounded loop.
-/

@[expose] public section

namespace Cslib.ProbOracleComp

variable {Query α β : Type} {spec : Query → Type}

/-- The results returned by `program` with positive probability for some stateful external
handler and initial oracle state. -/
def support (program : ProbOracleComp spec α) : Set α :=
  {result | ∃ (State : Type) (oracle : (q : Query) → StateT State PMF (spec q)) (s s' : State),
    (result, s') ∈ ((OracleComp.interpret
      (handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle) program).run s).support}

/-- A result supported by one stateful execution is possible. -/
theorem mem_support_of_mem {program : ProbOracleComp spec α} {State : Type}
    (oracle : (q : Query) → StateT State PMF (spec q)) {s s' : State} {result : α}
    (h : (result, s') ∈ ((OracleComp.interpret
      (handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle) program).run s).support) :
    result ∈ support program :=
  ⟨State, oracle, s, s', h⟩

/-- A returned value is the only possible result. -/
theorem eq_of_mem_support_pure {a result : α}
    (h : result ∈ support (pure a : ProbOracleComp spec α)) : result = a := by
  obtain ⟨State, oracle, s, s', h⟩ := h
  simp only [OracleComp.interpret_pure, StateT.run_pure, Probability.PMF.monad_pure_eq_pure,
    PMF.mem_support_pure_iff] at h
  exact (Prod.mk.inj h).1

/-- A possible result of a sequence comes from a possible first result. -/
theorem mem_support_bind {program : ProbOracleComp spec α} {next : α → ProbOracleComp spec β}
    {result : β} (h : result ∈ support (program >>= next)) :
    ∃ a ∈ support program, result ∈ support (next a) := by
  obtain ⟨State, oracle, s, s', h⟩ := h
  simp only [OracleComp.interpret_bind, StateT.run_bind, Probability.PMF.monad_bind_eq_bind,
    PMF.mem_support_bind_iff] at h
  obtain ⟨⟨a, s₁⟩, ha, h⟩ := h
  exact ⟨a, ⟨State, oracle, s, s₁, ha⟩, ⟨State, oracle, s₁, s', h⟩⟩

/-- A possible mapped result is the image of a possible result. -/
theorem mem_support_map {program : ProbOracleComp spec α} {f : α → β} {result : β}
    (h : result ∈ support (f <$> program)) : ∃ a ∈ support program, f a = result := by
  rw [← bind_pure_comp] at h
  obtain ⟨a, ha, h⟩ := mem_support_bind h
  exact ⟨a, ha, (eq_of_mem_support_pure h).symm⟩

/-- Private samples can only return results in the support of the closed program. -/
theorem support_sample_subset (program : ProbComp α) :
    support (sample (spec := spec) program) ⊆ (ProbComp.eval program).support := by
  rintro result ⟨State, oracle, s, s', h⟩
  rw [run_interpret_sample, PMF.mem_support_map_iff] at h
  obtain ⟨a, ha, heq⟩ := h
  exact (Prod.mk.inj heq).1 ▸ ha

/-- An invariant indexed by the number of completed steps holds for every possible result of a
bounded loop when every possible step preserves it. -/
theorem iterate_invariant {σ : Type} {step : σ → ProbOracleComp spec σ} {count : ℕ}
    {initial : σ} (invariant : ℕ → σ → Prop) (hbase : invariant 0 initial)
    (hpreserve : ∀ i state, i < count → invariant i state →
      ∀ next ∈ support (step state), invariant (i + 1) next) :
    ∀ state ∈ support (OracleComp.iterate count step initial), invariant count state := by
  induction count with
  | zero =>
    intro state hstate
    exact (eq_of_mem_support_pure hstate) ▸ hbase
  | succ count ih =>
    intro state hstate
    rw [OracleComp.iterate_succ] at hstate
    obtain ⟨middle, hmiddle, hstate⟩ := mem_support_bind hstate
    exact hpreserve count middle (Nat.lt_succ_self count)
      (ih (fun i state hi => hpreserve i state (Nat.lt_succ_of_lt hi)) middle hmiddle)
      state hstate

end Cslib.ProbOracleComp
