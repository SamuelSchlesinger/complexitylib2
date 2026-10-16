/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Probabilistic.QueryBounds
import Complexity.Languages.Probabilistic.RandomOracle.Probabilistic
import Complexity.Tactic.PPT

/-! Private coins, adaptive queries, and non-vacuous strict oracle-PPT certificates. -/

namespace ComplexityTests.OraclePPT

open Cslib Cslib.Probability Turing Turing.MultiTapeTM

private noncomputable def randomized :
    ProbOracleComp (fun _ : Bool => Bool) (Bool × Bool × Bool) := do
  let first ← ProbOracleComp.sample (ProbComp.uniform Bool)
  let answer ← ProbOracleComp.query first
  let second ← ProbOracleComp.sample (ProbComp.uniform Bool)
  let repeated ← ProbOracleComp.query first
  return (answer, second, repeated)

-- Private samples do not count as external calls; the adaptive client makes two requests.
private theorem randomized_queryBounds :
    ProbOracleComp.HasQueryBounds randomized (fun _ => 1) 2 1 := by
  apply ProbOracleComp.HasQueryBounds.bind (nextCalls := 2) (.sample _ _ _)
  intro first
  apply ProbOracleComp.HasQueryBounds.bind (nextCalls := 1) (.query first _ le_rfl)
  intro answer
  apply ProbOracleComp.HasQueryBounds.bind (nextCalls := 1) (.sample _ _ _)
  intro second
  apply ProbOracleComp.HasQueryBounds.bind (nextCalls := 0) (.query first _ le_rfl)
  intro repeated
  exact .pure (answer, second, repeated) _ _

-- Private sampling remains fresh while an external query is answered consistently.
example :
    (PMF.uniformOfFintype (Bool → Bool)).bind (fun table =>
      OracleComp.interpret
        (ProbOracleComp.handler ProbComp.unifOracle (fun q => PMF.pure (table q))) randomized) =
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n))
          (Cslib.RandomOracle.answer (fun _ => PMF.uniformOfFintype Bool))) randomized).run
            (fun _ => none)).map Prod.fst :=
  Cslib.RandomOracle.uniform_interpret_prob_eq_lazy randomized

-- Executable list memoization implements this same randomized adaptive table experiment.
example :
    ProbComp.eval (Prod.fst <$> (OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifFin n))
        (memoize (fun _ : Bool => ProbComp.uniform Bool))) randomized).run []) =
      (PMF.pi (fun _ : Bool => PMF.uniformOfFintype Bool)).bind (fun table =>
        OracleComp.interpret
          (ProbOracleComp.handler ProbComp.unifOracle (fun q => PMF.pure (table q)))
            randomized) := by
  simpa only [ProbComp.eval_uniform] using
    Cslib.RandomOracle.eval_run_interpret_memoize_prob_eq_eager
      (fun _ : Bool => ProbComp.uniform Bool) randomized

-- Two external calls give at most 18 encoded bits, including pair/list framing; draws are free
-- only with respect to this storage bound, not the separate machine time certificate.
example (result : Bool × Bool × Bool) (cache : List (Bool × Bool))
    (h : (result, cache) ∈ ((OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n))
        (memoize (fun _ : Bool => PMF.uniformOfFintype Bool))) randomized).run []).support) :
    (encList (encPair encBool encBool) cache).length ≤ 18 := by
  exact memoize_cache_size_le encBool encBool _ randomized 2 1 1
    (by simpa only [encBool_apply, List.length_singleton] using randomized_queryBounds)
    (by simp only [encBool_apply, List.length_singleton, le_refl, implies_true]) [] cache
    (by simp) result h

-- A duplicate preassigned answer may lie outside the sampler's support and still be returned.
example : (true, [(false, true), (false, false)]) ∈
    (memoize (fun _ : Bool => PMF.pure false) false [(false, true), (false, false)]).support := by
  rw [Cslib.RandomOracle.mem_support_memoize_iff]
  exact Or.inl ⟨by decide, rfl⟩

-- Two equal sampling requests draw independently, even in the presence of an external oracle.
example (State : Type) (oracle : Bool → StateT State PMF Bool) (s : State) :
    (OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        ((do
          let first ← ProbOracleComp.sample (ProbComp.uniform Bool)
          let second ← ProbOracleComp.sample (ProbComp.uniform Bool)
          return (first, second)) : ProbOracleComp (fun _ : Bool => Bool) (Bool × Bool))).run s =
      (PMF.uniformOfFintype (Bool × Bool)).map (·, s) := by
  simp only [OracleComp.interpret_bind, StateT.run_bind, ProbOracleComp.run_interpret_sample,
    OracleComp.interpret_pure, StateT.run_pure, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, ProbComp.eval_uniform, PMF.bind_map, Function.comp_def,
    PMF.map_comp, ← PMF.uniformOfFintype_prod, PMF.map_bind]
  rfl

-- Functional deterministic code reuses the existing tactic certificates with external channels.
example : IsOraclePPTOn (Operation := Bool) encBits encBits
    (fun word => pure (word ++ word)) := by fun_prop

private def readHead : MultiTapePTM 0 Bool Bool Unit where
  initial := false
  tr state _ _ answer _ := if state then
    .step ⟨0, Fin.elim0, answer (), none⟩ (fun _ => none) (fun _ => 0)
    else .query () true

-- Two instructions suffice to submit an empty request and copy at most one reply symbol.
example : IsOraclePPTOn encBits encBits
    (fun input => readHead.runOracle 2 input) := by
  simpa using IsOraclePPTOn.of_machine (input := encBits) readHead 2 0

private theorem readHead_law (State : Type)
    (oracle : Unit × List Bool → StateT State PMF (List Bool)) (s : State) (input : List Bool) :
    (OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (readHead.runOracle 2 input)).run s =
      ((oracle ((), [])).run s).map (fun (reply, state) => (reply.take 1, state)) := by
  simp only [MultiTapePTM.runOracle, MultiTapePTM.run, MultiTapePTM.runFrom,
    MultiTapePTM.runConfigFrom, MultiTapeMachine.runConfigFrom, readHead,
    MultiTapeMachine.initialConfig, Cfg.init]
  simp [OracleComp.interpret_bind, StateT.run_bind, StateT.run_map,
    ProbOracleComp.run_interpret_sample, -ProbOracleComp.interpret_sample,
    MultiTapeMachine.Config.receive, MultiTapeMachine.Config.step,
    MultiTapeMachine.Config.answerSymbols, MultiTapeMachine.Channel.answerSymbol,
    Turing.Action.apply, Function.comp_def, PMF.map, List.take_one, List.head?_eq_getElem?]

private def requestHead (_ : List Bool) : WordOracleComp Unit (List Bool) := do
  let reply ← ProbOracleComp.query ((), [])
  return reply.take 1

-- The same certificate describes the functional program while retaining every oracle effect.
private theorem requestHead_isOraclePPTOn : IsOraclePPTOn encBits encBits requestHead := by
  apply (IsOraclePPTOn.of_machine (input := encBits) readHead 2 0).congr
  intro input State oracle state
  simpa only [requestHead, encBits, Function.Embedding.coe_refl, id_eq, pow_zero, Nat.mul_one,
    bind_pure_comp, OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map,
    ProbOracleComp.interpret_query] using readHead_law State oracle state input

-- The resource contract derives a uniform budget for this concrete functional oracle client.
example : ∃ c d : ℕ, ∀ input, ProbOracleComp.HasQueryBounds (requestHead input)
    (fun request => request.2.length) (c * (input.length + 1) ^ d)
      (c * (input.length + 1) ^ d) := requestHead_isOraclePPTOn.query_bounds

-- The trace contains one external request despite two private draws and an unbounded reply.
example (n : ℕ) :
    (OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n))
        (OracleComp.withTranscript (fun _ : Unit × List Bool =>
          fun state : ℕ => PMF.pure (List.replicate n true, state + 1))))
            (readHead.runOracle 2 [])).run (7, []) =
      PMF.pure ((List.replicate n true).take 1, 8, [⟨((), []), List.replicate n true⟩]) := by
  rw [readHead_law]
  simp [OracleComp.withTranscript, StateT.run]

-- Returning an unrestricted oracle reply cannot satisfy a uniform strict polynomial clock.
example : ¬ IsOraclePPTOn encBits encBits
    (fun _ : List Bool => ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
      ((), [])) := by
  intro h
  obtain ⟨c, d, hbound⟩ := h.length_le
  let reply := List.replicate (c + 1) false
  have hlength := hbound [] Unit (fun _ s => PMF.pure (reply, s)) () () reply (by
    simp [StateT.run])
  simp only [encBits, Function.Embedding.coe_refl, id_eq, List.length_nil, Nat.zero_add, one_pow,
    Nat.mul_one, reply, List.length_replicate] at hlength
  lia

end ComplexityTests.OraclePPT
