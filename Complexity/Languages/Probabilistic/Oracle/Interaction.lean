/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Oracle

/-!
# Running a program against a stateful oracle

A program with private samples and typed external calls (`Cslib.ProbOracleComp`) interacts with a
stateful probabilistic oracle answering each call `q` with an element of `spec q`, possibly at
random and updating a private state. `Cslib.ProbOracleComp.runWith` is the joint law of the result
and the final oracle state, with fresh fair samples for the private coins, and
`Cslib.ProbOracleComp.acceptProbWith` the probability that a Boolean program returns `true`.
A prover of an interactive proof is such an oracle; `Cslib.Complexity.Prover.run` is the case of
word queries and replies (`Cslib.Complexity.Prover.run_eq_runWith`).

## Main definitions

* `Cslib.ProbOracleComp.runWith`: the joint law of the result and the final oracle state.
* `Cslib.ProbOracleComp.acceptProbWith`: the acceptance probability.

## Main results

* `Cslib.ProbOracleComp.runWith_bind`, `Cslib.ProbOracleComp.acceptProbWith_bind`: sequencing.
* `Cslib.ProbOracleComp.acceptProbWith_query_bind`,
  `Cslib.ProbOracleComp.acceptProbWith_sample_bind`: averages over replies and samples.
* `Cslib.ProbOracleComp.acceptProbWith_bind_ite_le`: a check run only after another one accepted
  accepts at most as often.
-/

@[expose] public section

namespace Cslib.ProbOracleComp

open scoped ENNReal

variable {Query : Type} {spec : Query → Type} {State α β : Type}
  (oracle : (q : Query) → StateT State PMF (spec q))

/-- The joint law of the result of `program` and the final state of the oracle answering its
external calls, starting from the state `s`. Private samples are fresh. -/
noncomputable def runWith (program : ProbOracleComp spec α) (s : State) : PMF (α × State) :=
  (OracleComp.interpret
    (handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle) program).run s

/-- The probability that `program` returns `true` against the oracle from the state `s`. -/
noncomputable def acceptProbWith (program : ProbOracleComp spec Bool) (s : State) : ℝ≥0∞ :=
  (runWith oracle program s).map Prod.fst true

theorem runWith_pure (a : α) (s : State) : runWith oracle (pure a) s = PMF.pure (a, s) := rfl

theorem runWith_bind (program : ProbOracleComp spec α) (next : α → ProbOracleComp spec β)
    (s : State) :
    runWith oracle (program >>= next) s =
      (runWith oracle program s).bind fun x => runWith oracle (next x.1) x.2 := by
  simp only [runWith, OracleComp.interpret_bind, StateT.run_bind]
  rfl

theorem runWith_query (q : Query) (s : State) :
    runWith oracle (query (spec := spec) q) s = oracle q s := by
  simp only [runWith, interpret_query]
  rfl

theorem runWith_sample (program : ProbComp α) (s : State) :
    runWith oracle (sample (spec := spec) program) s = (ProbComp.eval program).map (·, s) :=
  run_interpret_sample _ _ _

theorem acceptProbWith_pure (b : Bool) (s : State) :
    acceptProbWith oracle (pure b) s = if b then 1 else 0 := by
  rw [acceptProbWith, runWith_pure, PMF.pure_map, PMF.pure_apply]
  cases b <;> simp

theorem acceptProbWith_le_one (program : ProbOracleComp spec Bool) (s : State) :
    acceptProbWith oracle program s ≤ 1 :=
  PMF.coe_le_one _ _

theorem acceptProbWith_bind (program : ProbOracleComp spec α)
    (next : α → ProbOracleComp spec Bool) (s : State) :
    acceptProbWith oracle (program >>= next) s =
      ∑' x, runWith oracle program s x * acceptProbWith oracle (next x.1) x.2 := by
  rw [acceptProbWith, runWith_bind, PMF.map_bind, PMF.bind_apply]
  rfl

theorem acceptProbWith_query_bind (q : Query) (next : spec q → ProbOracleComp spec Bool)
    (s : State) :
    acceptProbWith oracle (query (spec := spec) q >>= next) s =
      ∑' x, oracle q s x * acceptProbWith oracle (next x.1) x.2 := by
  rw [acceptProbWith_bind, runWith_query]

theorem acceptProbWith_sample_bind (program : ProbComp α) (next : α → ProbOracleComp spec Bool)
    (s : State) :
    acceptProbWith oracle (sample program >>= next) s =
      ∑' a, ProbComp.eval program a * acceptProbWith oracle (next a) s := by
  rw [acceptProbWith, runWith_bind, runWith_sample, PMF.bind_map, PMF.map_bind, PMF.bind_apply]
  rfl

/-- Running a second check only after a first one accepted accepts at most as often as the first
check. -/
theorem acceptProbWith_bind_ite_le (program : ProbOracleComp spec Bool)
    (next : ProbOracleComp spec Bool) (s : State) :
    acceptProbWith oracle (program >>= fun b => if b then next else pure false) s ≤
      acceptProbWith oracle program s := by
  conv_rhs => rw [← bind_pure program, acceptProbWith_bind]
  rw [acceptProbWith_bind]
  refine ENNReal.tsum_le_tsum fun x => mul_le_mul_right ?_ _
  cases x.1
  · simp only [Bool.false_eq_true, ↓reduceIte, le_refl]
  · simp only [↓reduceIte, acceptProbWith_pure]
    exact acceptProbWith_le_one _ _ _

end Cslib.ProbOracleComp
