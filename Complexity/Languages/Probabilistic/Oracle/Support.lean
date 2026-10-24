/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Oracle
public import Complexity.Languages.Probabilistic.Iteration

import Complexity.Languages.Probabilistic.Oracle.Simulation

/-!
# Possible results of randomized oracle programs

A result of a program with private coins is possible when some private samples and some replies
to its external queries lead to it: `ProbOracleComp.support` is the set of results at the leaves
of the program's tree of calls. Every stateful execution returns only possible results
(`mem_support_of_mem`). When every reply type is nonempty, every possible result is returned by
some stateful execution (`mem_support_iff_exists`): an oracle that answers its first call with a
chosen reply realizes each path. Invariants of adaptive loops quantify over possible results, so
they remain valid for every shared oracle and every reply length.

## Main definitions

* `Cslib.ProbOracleComp.support`: the results at the leaves of the program's tree of calls.

## Main results

* `Cslib.ProbOracleComp.mem_support_bind_iff`: a possible result of a sequence is a possible result
  of a continuation at a possible intermediate result.
* `Cslib.ProbOracleComp.support_sample`: private samples range over the closed program's support.
* `Cslib.ProbOracleComp.mem_support_iff_exists`: with nonempty reply types, the possible results
  are the results of stateful executions.
* `Cslib.ProbOracleComp.iterate_invariant`: an invariant preserved by every possible step holds
  for every possible result of a bounded loop.

## References

Generalizes the supported loop invariants of Computability/Probabilistic/Adaptive.lean on the
cslib `crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8` to programs with external
calls, for the loop rules adapted from Christian Reitwiessner's `Combinators/IterateWhile`
(crei:crei/tidy-universal @7f7c0696).
-/

@[expose] public section

namespace Cslib.ProbOracleComp

open OracleComp

variable {Query α β : Type} {spec : Query → Type}

/-- The results of `program` for some private samples and some replies to its external queries:
the results at the leaves of its tree of calls. -/
def support : ProbOracleComp spec α → Set α
  | .pure a => {a}
  | .liftBind _ cont => ⋃ a, support (cont a)

/-- A returned value is the only possible result. -/
@[simp] theorem support_pure (a : α) : support (pure a : ProbOracleComp spec α) = {a} := rfl

/-- A returned value is the only possible result. -/
theorem eq_of_mem_support_pure {a result : α}
    (h : result ∈ support (pure a : ProbOracleComp spec α)) : result = a := h

/-- A possible result of a sequence is a possible result of a continuation at a possible
intermediate result. -/
@[simp] theorem mem_support_bind_iff {program : ProbOracleComp spec α}
    {next : α → ProbOracleComp spec β} {result : β} :
    result ∈ support (program >>= next) ↔ ∃ a ∈ support program, result ∈ support (next a) := by
  induction program with
  | pure a => simp [support]
  | liftBind q cont ih =>
    change result ∈ ⋃ b, support (cont b >>= next) ↔ ∃ a ∈ ⋃ b, support (cont b), _
    simp only [Set.mem_iUnion, ih]
    constructor
    · rintro ⟨b, a, ha, h⟩
      exact ⟨a, ⟨b, ha⟩, h⟩
    · rintro ⟨a, ⟨b, ha⟩, h⟩
      exact ⟨b, a, ha, h⟩

/-- A possible result of a sequence comes from a possible first result. -/
theorem mem_support_bind {program : ProbOracleComp spec α} {next : α → ProbOracleComp spec β}
    {result : β} (h : result ∈ support (program >>= next)) :
    ∃ a ∈ support program, result ∈ support (next a) :=
  mem_support_bind_iff.mp h

/-- A possible mapped result is the image of a possible result. -/
@[simp] theorem mem_support_map_iff {program : ProbOracleComp spec α} {f : α → β} {result : β} :
    result ∈ support (f <$> program) ↔ ∃ a ∈ support program, f a = result := by
  rw [← bind_pure_comp, mem_support_bind_iff]
  simp [eq_comm]

/-- A possible mapped result is the image of a possible result. -/
theorem mem_support_map {program : ProbOracleComp spec α} {f : α → β} {result : β}
    (h : result ∈ support (f <$> program)) : ∃ a ∈ support program, f a = result :=
  mem_support_map_iff.mp h

/-- An external query may return any reply. -/
@[simp] theorem support_query (q : Query) : support (query (spec := spec) q) = Set.univ :=
  Set.eq_univ_of_forall fun a => Set.mem_iUnion.mpr ⟨a, rfl⟩

/-- Private samples range over the support of the closed program. -/
@[simp] theorem support_sample (program : ProbComp α) :
    support (sample (spec := spec) program) = (ProbComp.eval program).support := by
  induction program with
  | pure a => simp [ProbComp.eval]
  | liftBind n cont ih =>
    change support (sample (spec := spec) (OracleComp.query n >>= cont)) =
      (ProbComp.eval (OracleComp.query n >>= cont)).support
    have hquery : sample (spec := spec) (OracleComp.query n) = OracleComp.query (Sum.inl n) :=
      OracleComp.interpret_query _ _
    have hsample : support (OracleComp.query (spec := probOracleSpec spec) (Sum.inl n)) =
        Set.univ :=
      Set.eq_univ_of_forall fun a => Set.mem_iUnion.mpr ⟨a, rfl⟩
    have heval : (ProbComp.eval (OracleComp.query (spec := unifSpec) n)).support = Set.univ := by
      rw [show OracleComp.query (spec := unifSpec) n = ProbComp.unifFin n from rfl,
        ProbComp.eval_unifFin]
      exact Set.eq_univ_of_forall fun a => by simp
    ext result
    rw [sample_bind, hquery, ProbComp.eval_bind, PMF.mem_support_bind_iff, mem_support_bind_iff,
      hsample, heval]
    simp only [Set.mem_univ, true_and, ih]

/-- Private samples can only return results in the support of the closed program. -/
theorem support_sample_subset (program : ProbComp α) :
    support (sample (spec := spec) program) ⊆ (ProbComp.eval program).support :=
  (support_sample program).subset

/-- A result supported by one stateful execution is possible. -/
theorem mem_support_of_mem {program : ProbOracleComp spec α} {State : Type}
    (oracle : (q : Query) → StateT State PMF (spec q)) {s s' : State} {result : α}
    (h : (result, s') ∈ ((OracleComp.interpret
      (handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle) program).run s).support) :
    result ∈ support program := by
  induction program generalizing s s' with
  | pure a =>
    change (result, s') ∈ (PMF.pure (a, s)).support at h
    exact (Prod.mk.inj ((PMF.mem_support_pure_iff _ _).mp h)).1
  | liftBind q cont ih =>
    change (result, s') ∈ ((OracleComp.interpret
      (handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (OracleComp.query q >>= cont)).run s).support at h
    simp only [interpret_bind, OracleComp.interpret_query, StateT.run_bind,
      Probability.PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at h
    obtain ⟨⟨a, middle⟩, -, h⟩ := h
    exact Set.mem_iUnion.mpr ⟨a, ih a h⟩

/-- When every reply type is nonempty, the possible results of a program are exactly the results
of its stateful executions. -/
theorem mem_support_iff_exists [hne : ∀ q, Nonempty (spec q)] {program : ProbOracleComp spec α}
    {result : α} :
    result ∈ support program ↔
      ∃ (State : Type) (oracle : (q : Query) → StateT State PMF (spec q)) (s s' : State),
        (result, s') ∈ ((OracleComp.interpret
          (handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle) program).run s).support
    := by
  classical
  refine ⟨fun h => ?_, fun ⟨State, oracle, s, s', h⟩ => mem_support_of_mem oracle h⟩
  induction program with
  | pure a =>
    refine ⟨Unit, fun q _ => PMF.pure (Classical.choice (hne q), ()), (), (), ?_⟩
    rw [eq_of_mem_support_pure h]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  | liftBind q cont ih =>
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp h
    obtain ⟨State, oracle, s, s', hrun⟩ := ih a ha
    have hrun' {S : Type} (oracle : (q : Query) → StateT S PMF (spec q)) (state : S) :
        (OracleComp.interpret (handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (PFunctor.FreeM.liftBind q cont)).run state =
        ((handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle q).run state).bind
          fun first => (OracleComp.interpret
            (handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle) (cont first.1)).run
              first.2 := rfl
    cases q with
    | inl n =>
      refine ⟨State, oracle, s, s', ?_⟩
      rw [hrun', PMF.mem_support_bind_iff]
      refine ⟨(a, s), ?_, hrun⟩
      simp [handler, ProbComp.unifOracle]
    | inr q =>
      let first (q' : Query) : spec q' :=
        if hq : q' = q then hq ▸ a else Classical.choice (hne q')
      let oracle' (q' : Query) : StateT (Option State) PMF (spec q') := fun
        | none => PMF.pure (first q', some s)
        | some state => (oracle q' state).map fun (b, state') => (b, some state')
      have hlift := run_interpret_map_state oracle oracle' some (fun q' state => by
        simp [oracle']) (cont a) s
      refine ⟨Option State, oracle', none, some s', ?_⟩
      rw [hrun' oracle', PMF.mem_support_bind_iff]
      refine ⟨(a, some s), ?_, ?_⟩
      · change (a, some s) ∈ (PMF.pure (first q, some s)).support
        simp [first]
      · rw [← hlift, PMF.mem_support_map_iff]
        exact ⟨(result, s'), hrun, rfl⟩

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
