/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Repeat
public import Complexity.Languages.Probabilistic.Oracle.Transcript

/-!
# Saved samples in adaptive oracle interactions

An external handler can consume one saved sample per call while the client continues drawing
independent private randomness. A sufficient list of independent samples gives exactly the
online joint output and ordinary private state. Unused samples are discarded in this equality;
they need not be independent of the final state or the client's stopping time.

## Main definitions

* `Cslib.OracleComp.withSampleList`: supply a list's head to a handler and retain its tail.

## Main results

* `Cslib.ProbOracleComp.run_interpret_presample`: pre-sampling preserves the joint output/state
  law under a call bound on the online interaction alone.
* `Cslib.ProbOracleComp.HasQueryBounds.eval_presample`: semantic external budgets suffice.

## References

Adapted from Languages/Probabilistic/Presample.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the typed sum of private and external calls.
-/

@[expose] public section

namespace Cslib

namespace OracleComp

universe u v w

/-- Supply the next saved sample to a stateful handler. The fallback makes short lists total;
the ordinary state and unused suffix are retained. -/
def withSampleList {Query : Type u} {spec : Query → Type v} {State Value : Type v}
    {m : Type v → Type w} [Functor m] (fallback : Value)
    (oracle : Value → (q : Query) → StateT State m (spec q))
    (q : Query) : StateT (State × List Value) m (spec q) := fun (state, values) =>
  (fun (answer, next) => (answer, next, values.tail)) <$> oracle (values.headD fallback) q state

end OracleComp

namespace ProbOracleComp

open OracleComp Probability

variable {Query α State Value : Type} {spec : Query → Type}

private theorem query_bound_cont (oracle : (q : Query) → StateT State PMF (spec q))
    (q : Query) (cont : spec q → ProbOracleComp spec α) (s : State) (count : ℕ)
    (hbound : ∀ result next transcript,
      (result, next, transcript) ∈ ((interpret
        (handler (fun n => StateT.lift (ProbComp.unifOracle n)) (withTranscript oracle))
          (query q >>= cont)).run (s, [])).support → transcript.length ≤ count)
    (answer : spec q) (next : State) (hanswer : (answer, next) ∈ (oracle q s).support)
    (result : α) (final : State) (transcript : Transcript spec)
    (hresult : (result, final, transcript) ∈ ((interpret
      (handler (fun n => StateT.lift (ProbComp.unifOracle n)) (withTranscript oracle))
        (cont answer)).run (next, [])).support) : transcript.length + 1 ≤ count := by
  have htrace : (result, final, transcript ++ [⟨q, answer⟩]) ∈ ((interpret
      (handler (fun n => StateT.lift (ProbComp.unifOracle n)) (withTranscript oracle))
        (cont answer)).run (next, [⟨q, answer⟩])).support := by
    rw [run_interpret_withTranscript_append]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨(result, final, transcript), hresult, rfl⟩
  have hwhole : (result, final, transcript ++ [⟨q, answer⟩]) ∈ ((interpret
      (handler (fun n => StateT.lift (ProbComp.unifOracle n)) (withTranscript oracle))
        (query q >>= cont)).run (s, [])).support := by
    simp only [interpret_bind, interpret_query, StateT.run_bind,
      PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff]
    refine ⟨(answer, next, [⟨q, answer⟩]), ?_, htrace⟩
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨(answer, next), hanswer, rfl⟩
  have hlength : (transcript ++ ([⟨q, answer⟩] : Transcript spec)).length =
      transcript.length + 1 := List.length_append
  exact hlength ▸ hbound result final (transcript ++ [⟨q, answer⟩]) hwhole

/-- Drawing enough independent samples in advance preserves an adaptive interaction's output
and ordinary private state. Only the original online interaction needs a supported call bound.
Private client samples do not consume the saved list. -/
theorem run_interpret_presample (source : ProbComp Value) (fallback : Value)
    (oracle : Value → (q : Query) → StateT State PMF (spec q))
    (program : ProbOracleComp spec α) (s : State) (count : ℕ)
    (hbound : ∀ result next transcript,
      (result, next, transcript) ∈ ((interpret
        (handler (fun n => StateT.lift (ProbComp.unifOracle n)) (withTranscript
          (fun q s => (ProbComp.eval source).bind (fun value => oracle value q s))))
            program).run (s, [])).support → transcript.length ≤ count) :
    (ProbComp.eval (replicate count source)).bind (fun values => ((interpret
      (handler (fun n => StateT.lift (ProbComp.unifOracle n))
        (withSampleList fallback oracle)) program).run (s, values)).map
          (fun (result, next, _) => (result, next))) =
      (interpret (handler (fun n => StateT.lift (ProbComp.unifOracle n))
        (fun q s => (ProbComp.eval source).bind (fun value => oracle value q s)))
          program).run s := by
  induction program using PFunctor.FreeM.induction generalizing s count with
  | pure a => simp [PMF.pure_map]
  | lift_bind op cont ih =>
    change (ProbComp.eval (replicate count source)).bind (fun values => ((interpret
      (m := StateT (State × List Value) PMF) _
      (OracleComp.query op >>= cont)).run (s, values)).map _) =
        (interpret (m := StateT State PMF) _ (OracleComp.query op >>= cont)).run s
    change ∀ result next transcript, (result, next, transcript) ∈ ((interpret
      (m := StateT (State × Transcript spec) PMF) _
      (OracleComp.query op >>= cont)).run (s, [])).support → transcript.length ≤ count at hbound
    cases op with
    | inl n =>
      have hnext value (hvalue : value ∈ (ProbComp.unifOracle n).support) :
          ∀ result next transcript, (result, next, transcript) ∈ ((interpret
            (handler (fun n => StateT.lift (ProbComp.unifOracle n)) (withTranscript
              (fun q s => (ProbComp.eval source).bind (fun value => oracle value q s))))
                (cont value)).run (s, [])).support → transcript.length ≤ count := by
        intro result next transcript hresult
        apply hbound result next transcript
        simp only [interpret_bind, OracleComp.interpret_query, handler, StateT.run_bind_lift,
          PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff]
        exact ⟨value, hvalue, hresult⟩
      simp only [interpret_bind, OracleComp.interpret_query, handler, StateT.run_bind_lift,
        PMF.monad_bind_eq_bind, PMF.map_bind]
      rw [PMF.bind_comm]
      apply PMF.bind_congr_on_support
      intro value hvalue
      exact ih value s count (hnext value hvalue)
    | inr q =>
      have hnext := query_bound_cont
        (fun q s => (ProbComp.eval source).bind (fun value => oracle value q s))
          q cont s count hbound
      obtain ⟨⟨answer, next⟩, hanswer⟩ :=
        ((ProbComp.eval source).bind (fun value => oracle value q s)).support_nonempty
      obtain ⟨⟨result, final, transcript⟩, hresult⟩ := ((interpret
        (handler (fun n => StateT.lift (ProbComp.unifOracle n)) (withTranscript
          (fun q s => (ProbComp.eval source).bind (fun value => oracle value q s))))
            (cont answer)).run (next, [])).support_nonempty
      have hpositive : 0 < count := by
        have := hnext answer next hanswer result final transcript hresult
        lia
      cases count with
      | zero => lia
      | succ count =>
        simp only [replicate_succ, ProbComp.eval_bind, ProbComp.eval_map, PMF.bind_bind,
          PMF.bind_map, Function.comp_def, interpret_bind, OracleComp.interpret_query,
          handler, StateT.run_bind, PMF.monad_bind_eq_bind, PMF.map_bind]
        simp only [StateT.run, withSampleList, List.headD_cons, List.tail_cons,
          PMF.monad_map_eq_map, PMF.bind_map, PMF.bind_bind, Function.comp_def]
        apply PMF.bind_congr_on_support
        intro value hvalue
        rw [PMF.bind_comm]
        apply PMF.bind_congr_on_support
        rintro ⟨answer, next⟩ hanswer
        apply ih answer next count
        intro result final transcript hresult
        have h := hnext answer next
          ((PMF.mem_support_bind_iff _ _ _).mpr ⟨value, hvalue, hanswer⟩)
          result final transcript hresult
        lia

/-- A uniform external query budget suffices for every online handler. This is an exact joint
distribution law, independent of the efficiency of the client or the sample source. -/
theorem HasQueryBounds.eval_presample {program : ProbOracleComp spec α}
    {size : Query → ℕ} {count maxSize : ℕ} (h : program.HasQueryBounds size count maxSize)
    (source : ProbComp Value) (fallback : Value)
    (oracle : Value → (q : Query) → StateT State ProbComp (spec q)) (s : State) :
    ProbComp.eval (do
      let values ← replicate count source
      (fun (result, next, _) => (result, next)) <$> (interpret
        (handler (fun n => StateT.lift (ProbComp.unifFin n))
          (withSampleList fallback oracle)) program).run (s, values)) =
      ProbComp.eval ((interpret (handler (fun n => StateT.lift (ProbComp.unifFin n))
        (fun q s => do
          let value ← source
          oracle value q s)) program).run s) := by
  have hrun := run_interpret_presample source fallback
    (fun value q s => ProbComp.eval (oracle value q s)) program s count
    (fun result next transcript hresult => (h _ _ s next result transcript hresult).1)
  have hstep (q : Query) (state : State × List Value) :
      ProbComp.eval (withSampleList fallback oracle q state) =
        withSampleList fallback (fun value q s => ProbComp.eval (oracle value q s)) q state := by
    simp [withSampleList, PMF.monad_map_eq_map]
  simpa only [ProbComp.eval_bind, ProbComp.eval_map, eval_run_interpret, hstep] using hrun

end ProbOracleComp

end Cslib
