/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.RandomOracle
public import Complexity.Languages.Probabilistic.Oracle

/-!
# Lazy random functions with independent private randomness

The eager/lazy completion law also holds for clients interleaving external queries with fresh
private finite-uniform samples. Only external replies are cached. The joint law retains the
client's result and the completed table, including when a private sample or an earlier reply
determines a later query.

## Main results

* `Cslib.RandomOracle.run_interpret_answer_complete_prob`: the full joint completion law.
* `Cslib.RandomOracle.interpret_prob_eq_lazy`: the marginal eager/lazy equivalence.
* `Cslib.RandomOracle.uniform_interpret_prob_eq_lazy`: specialization to a uniform random function.

## References

* [O. Goldreich, S. Goldwasser, S. Micali, *How to Construct Random Functions*][GGM1986],
  Section 3.3.

Extends the crypto-branch lazy-sampling proof at `5ff69ca93402e7c947208dc56396d6d86203ccd8`
to the disjoint-sum interface of `ProbOracleComp`, reusing the general state simulation rule.
-/

@[expose] public section

namespace Cslib.RandomOracle

open Probability ProbOracleComp

variable {Query α : Type} {Response : Query → Type} [Fintype Query]
  [∀ q, Finite (Response q)]

/-- Complete the cache before or after a client with fresh private randomness: the joint result
and complete-table distributions agree, even for arbitrary preassigned cache entries. -/
theorem run_interpret_answer_complete_prob [DecidableEq Query]
    (distribution : (q : Query) → PMF (Response q))
    (program : ProbOracleComp Response α) (cache : Cache Response) :
    ((OracleComp.interpret
      (handler (fun n => StateT.lift (ProbComp.unifOracle n)) (answer distribution))
        program).run cache).bind (fun (result, cache') =>
          (complete distribution cache').map (result, ·)) =
      (complete distribution cache).bind (fun table =>
        (OracleComp.interpret
          (handler ProbComp.unifOracle (fun q => PMF.pure (table q))) program).map (·, table)) := by
  have h := OracleComp.run_interpret_simulation
    (handler (fun n => StateT.lift (ProbComp.unifOracle n)) (answer distribution))
    (fun q table => (handler ProbComp.unifOracle (fun q => PMF.pure (table q)) q).map
      (·, table)) (complete distribution)
    (fun q cache => by
      cases q with
      | inl n =>
        change ((ProbComp.unifOracle n).map (·, cache)).bind
          (fun (value, cache') => (complete distribution cache').map (value, ·)) =
            (complete distribution cache).bind
              (fun table => (ProbComp.unifOracle n).map (·, table))
        simp only [PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind]
        exact PMF.bind_comm _ _ _
      | inr q =>
        simpa only [handler, PMF.map, Function.comp_def, PMF.pure_bind] using
          answer_complete distribution cache q) program cache
  refine h.trans (congrArg ((complete distribution cache).bind) (funext fun table => ?_))
  simpa only [PMF.monad_map_eq_map] using OracleComp.run_interpret_readOnly
    (fun q (table : (q : Query) → Response q) =>
      handler ProbComp.unifOracle (fun q => PMF.pure (table q)) q) program table

/-- Lazy sampling from an empty cache implements the eager table experiment for randomized,
adaptive clients, with private randomness independent of the table. -/
theorem interpret_prob_eq_lazy [DecidableEq Query]
    (distribution : (q : Query) → PMF (Response q)) (program : ProbOracleComp Response α) :
    (PMF.pi distribution).bind (fun table =>
      OracleComp.interpret
        (handler ProbComp.unifOracle (fun q => PMF.pure (table q))) program) =
      ((OracleComp.interpret
        (handler (fun n => StateT.lift (ProbComp.unifOracle n)) (answer distribution))
          program).run (fun _ => none)).map Prod.fst := by
  have h := congrArg (PMF.map Prod.fst)
    (run_interpret_answer_complete_prob distribution program (fun _ => none))
  simpa only [complete_empty, PMF.map_bind, PMF.map_comp, PMF.map, Function.comp_def,
    PMF.bind_const, PMF.bind_pure, PMF.bind_bind, PMF.pure_bind] using h.symm

/-- A uniform random function can be implemented by consistent lazy uniform replies even when
the client uses private randomness between its adaptive queries. -/
theorem uniform_interpret_prob_eq_lazy [DecidableEq Query] [∀ q, Fintype (Response q)]
    [∀ q, Nonempty (Response q)] (program : ProbOracleComp Response α) :
    (PMF.uniformOfFintype ((q : Query) → Response q)).bind (fun table =>
      OracleComp.interpret
        (handler ProbComp.unifOracle (fun q => PMF.pure (table q))) program) =
      ((OracleComp.interpret
        (handler (fun n => StateT.lift (ProbComp.unifOracle n))
          (answer (fun q => PMF.uniformOfFintype (Response q))))
            program).run (fun _ => none)).map Prod.fst := by
  simpa only [PMF.pi_uniformOfFintype] using
    interpret_prob_eq_lazy (fun q => PMF.uniformOfFintype (Response q)) program

end Cslib.RandomOracle
