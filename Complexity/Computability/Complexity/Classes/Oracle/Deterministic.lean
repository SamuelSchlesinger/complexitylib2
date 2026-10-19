/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Oracle
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Fintype.Option

/-!
# Deterministic machines behind polynomial time relative to an oracle

A certificate of `Cslib.Complexity.ComputableInPolyTimeWithOracle` is a fair-coin machine that
reproduces a deterministic program against every stateful oracle. Fixing all of its coins to
`false` gives a deterministic run of the same machine, itself a word-query program
(`Turing.MultiTapeMachine.run` with the coin program `pure false`). Its result against every
answer function is the program's (`Cslib.Probability.IsOraclePPTOn.exists_run_pure_false`): the
coin-fixed run is one of the supported runs of the certificate, whose result is determined. The
run makes at most one request per instruction
(`Turing.MultiTapeMachine.length_queriesWith_runConfigFrom_le`).

Relabelling the control states along an equivalence preserves the run program
(`Turing.MultiTapePTM.runFrom_relabel`), and tables with finitely many symbols, states and channels
form a finite type (`Turing.MultiTapePTM.finite`). Together, the deterministic runs behind all
certificates come from countably many machines with control `Fin m`
(`Cslib.Probability.IsOraclePPTOn.exists_fin_run_pure_false`), as oracle diagonalizations need.

## Main definitions

* `Turing.MultiTapeMachine.Action.mapState`, `Turing.MultiTapeMachine.Config.mapState`: rename
  control states in instructions and configurations.
* `Turing.MultiTapePTM.relabel`: rename the control states of a fair-coin table.

## Main results

* `Turing.MultiTapeMachine.length_queriesWith_runConfigFrom_le`: a deterministic run makes at most
  one request per instruction.
* `Turing.MultiTapePTM.mem_support_runConfigFrom_pure`: a coin-fixed run is supported by the
  fair-coin run.
* `Turing.MultiTapePTM.runFrom_relabel`, `Turing.MultiTapePTM.finite`.
* `Cslib.Probability.IsOraclePPTOn.exists_run_pure_false`,
  `Cslib.Probability.IsOraclePPTOn.exists_fin_run_pure_false`: certificates of deterministic
  programs are deterministic runs of finite machines with a polynomial clock.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 3.4
  (oracle Turing machines).
-/

@[expose] public section

namespace Turing

open Cslib

namespace MultiTapeMachine

variable {k : ℕ} {Symbol State State' Oracle : Type} {input : List Symbol}

/-- Rename the successor state of an instruction. -/
def Action.mapState (e : State → State') :
    Action k Symbol State Oracle → Action k Symbol State' Oracle
  | .step action symbol move => .step { action with state := action.state.map e } symbol move
  | .query oracle next => .query oracle (e next)

/-- Rename the control state of a configuration, keeping its tapes and channels. -/
def Config.mapState (e : State → State') (cfg : Config k Symbol State Oracle input) :
    Config k Symbol State' Oracle input where
  tapes := cfg.tapes.mapState (Option.map e)
  channels := cfg.channels

@[simp] theorem Config.mapState_tapes_state (e : State → State')
    (cfg : Config k Symbol State Oracle input) :
    (cfg.mapState e).tapes.state = cfg.tapes.state.map e := rfl

@[simp] theorem Config.mapState_tapes_output (e : State → State')
    (cfg : Config k Symbol State Oracle input) :
    (cfg.mapState e).tapes.output = cfg.tapes.output := rfl

theorem Config.mapState_step (e : State → State') (cfg : Config k Symbol State Oracle input)
    (action : Turing.Action k Symbol State) (symbol : Oracle → Option Symbol)
    (move : Oracle → SignType) :
    (cfg.mapState e).step { action with state := action.state.map e } symbol move =
      (cfg.step action symbol move).mapState e := rfl

theorem Config.mapState_receive [DecidableEq Oracle] (e : State → State')
    (cfg : Config k Symbol State Oracle input) (oracle : Oracle) (next : State)
    (answer : List Symbol) :
    (cfg.mapState e).receive oracle (e next) answer = (cfg.receive oracle next answer).mapState e :=
  rfl

/-- **A deterministic run makes at most one request per instruction**, under every answer
function. -/
theorem length_queriesWith_runConfigFrom_le {Choose : Type → Type} [DecidableEq Oracle]
    (machine : MultiTapeMachine k Symbol State Oracle Choose)
    (pick : Choose (Action k Symbol State Oracle) → Action k Symbol State Oracle)
    (answer : Oracle × List Symbol → List Symbol) (fuel : ℕ)
    (cfg : Config k Symbol State Oracle input) :
    (OracleComp.queriesWith answer (machine.runConfigFrom (fun choices => pure (pick choices))
      (fun oracle word => OracleComp.query (oracle, word)) fuel cfg)).length ≤ fuel := by
  induction fuel generalizing cfg with
  | zero => simp
  | succ fuel ih =>
    cases hs : cfg.tapes.state with
    | none => simp [runConfigFrom, hs]
    | some state =>
      simp only [runConfigFrom, hs, pure_bind]
      cases pick (machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
        cfg.answerSymbols) with
      | step action symbol move => exact (ih _).trans (Nat.le_succ _)
      | query oracle next =>
        rw [OracleComp.queriesWith_query_bind, List.length_cons]
        exact Nat.succ_le_succ (ih _)

end MultiTapeMachine

namespace MultiTapePTM

open MultiTapeMachine

variable {k : ℕ} {Symbol State State' Oracle : Type} {input : List Symbol}

/-- Rename the control states of a fair-coin table along an equivalence. -/
def relabel (e : State ≃ State') (machine : MultiTapePTM k Symbol State Oracle) :
    MultiTapePTM k Symbol State' Oracle where
  initial := e machine.initial
  tr state symbol work answer bit :=
    (machine.tr (e.symm state) symbol work answer bit).mapState e

@[simp] theorem initialConfig_relabel (e : State ≃ State')
    (machine : MultiTapePTM k Symbol State Oracle) (input : List Symbol) :
    (machine.relabel e).initialConfig input = (machine.initialConfig input).mapState e := rfl

variable [DecidableEq Oracle]

/-- Relabelling commutes with the run program, for every coin and request program. -/
theorem runConfigFrom_relabel {Query : Type} {spec : OracleSpec.{0, 0} Query} (e : State ≃ State')
    (machine : MultiTapePTM k Symbol State Oracle) (coin : OracleComp spec Bool)
    (query : Oracle → List Symbol → OracleComp spec (List Symbol)) (fuel : ℕ)
    (cfg : Config k Symbol State Oracle input) :
    (machine.relabel e).runConfigFrom coin query fuel (cfg.mapState e) =
      Config.mapState e <$> machine.runConfigFrom coin query fuel cfg := by
  induction fuel generalizing cfg with
  | zero => rfl
  | succ fuel ih =>
    cases hs : cfg.tapes.state with
    | none =>
      simp [runConfigFrom, MultiTapeMachine.runConfigFrom, hs]
    | some state =>
      simp only [runConfigFrom] at ih ⊢
      simp only [MultiTapeMachine.runConfigFrom, Config.mapState_tapes_state, hs, Option.map_some,
        map_bind, bind_map_left]
      congr 1
      funext bit
      change (match (machine.tr (e.symm (e state)) cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbols bit).mapState e with
        | .step action symbol move =>
          MultiTapeMachine.runConfigFrom (machine.relabel e) (fun choices => choices <$> coin) query
            fuel ((cfg.mapState e).step action symbol move)
        | .query oracle next => do
          let answer ← query oracle (cfg.channels oracle).queryBuffer
          MultiTapeMachine.runConfigFrom (machine.relabel e) (fun choices => choices <$> coin) query
            fuel ((cfg.mapState e).receive oracle next answer)) = _
      rw [Equiv.symm_apply_apply]
      cases machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols bit
        with
      | step action symbol move =>
        simp only [Action.mapState]
        rw [Config.mapState_step, ih]
      | query oracle next =>
        simp only [Action.mapState, map_bind]
        congr 1
        funext answer
        rw [Config.mapState_receive, ih]

/-- Relabelling preserves the output program of every run. -/
theorem runFrom_relabel {Query : Type} {spec : OracleSpec.{0, 0} Query} (e : State ≃ State')
    (machine : MultiTapePTM k Symbol State Oracle) (coin : OracleComp spec Bool)
    (query : Oracle → List Symbol → OracleComp spec (List Symbol)) (fuel : ℕ)
    (cfg : Config k Symbol State Oracle input) :
    (machine.relabel e).runFrom coin query fuel (cfg.mapState e) =
      machine.runFrom coin query fuel cfg := by
  simp only [runFrom, runConfigFrom_relabel, Functor.map_map, Config.mapState_tapes_output]

/-- Relabelling preserves the output program of every run from the initial configuration. -/
theorem run_relabel {Query : Type} {spec : OracleSpec.{0, 0} Query} (e : State ≃ State')
    (machine : MultiTapePTM k Symbol State Oracle) (coin : OracleComp spec Bool)
    (query : Oracle → List Symbol → OracleComp spec (List Symbol)) (fuel : ℕ)
    (input : List Symbol) :
    (machine.relabel e).run coin query fuel input = machine.run coin query fuel input := by
  rw [run, initialConfig_relabel, runFrom_relabel, run]

omit [DecidableEq Oracle] in
/-- Finitely many symbols, states and channels give finitely many fair-coin tables. -/
theorem finite [Finite Symbol] [Finite State] [Finite Oracle] :
    Finite (MultiTapePTM k Symbol State Oracle) := by
  have hTuring : Finite (Turing.Action k Symbol State) :=
    Finite.of_injective (fun a : Turing.Action k Symbol State =>
      (a.inputTape, a.workTapes, a.output, a.state)) fun a b h => by
        cases a; cases b; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; rfl
  have hAction : Finite (MultiTapeMachine.Action k Symbol State Oracle) :=
    Finite.of_injective (fun a : MultiTapeMachine.Action k Symbol State Oracle => match a with
      | .step action symbol move => (Sum.inl (action, symbol, move) :
          (Turing.Action k Symbol State × (Oracle → Option Symbol) × (Oracle → SignType)) ⊕
            (Oracle × State))
      | .query oracle next => Sum.inr (oracle, next)) fun a b h => by
        cases a <;> cases b <;> simp_all
  have : Finite ((Oracle → Option Symbol) → Bool →
      MultiTapeMachine.Action k Symbol State Oracle) := inferInstance
  have : Finite ((Fin k → Option Symbol) → (Oracle → Option Symbol) → Bool →
      MultiTapeMachine.Action k Symbol State Oracle) := inferInstance
  exact Finite.of_injective (β := State × (State → Option Symbol → (Fin k → Option Symbol) →
      (Oracle → Option Symbol) → Bool → MultiTapeMachine.Action k Symbol State Oracle))
    (fun machine => (machine.initial, fun state symbol work answer bit =>
      machine.tr state symbol work answer bit))
    fun a b h => by
      simp only [Prod.mk.injEq] at h
      refine MultiTapeMachine.ext h.1 ?_
      funext state symbol work answer bit
      exact congrFun (congrFun (congrFun (congrFun (congrFun h.2 state) symbol) work) answer) bit

/-- **A coin-fixed run is supported.** Against a deterministic oracle, the result of the run with
every coin fixed to `bit` is a supported result of the fair-coin run, with the unchanged state. -/
theorem mem_support_runConfigFrom_pure {σ : Type} (machine : MultiTapePTM k Symbol State Oracle)
    (bit : Bool) (answer : Oracle × List Symbol → List Symbol) (s : σ) (fuel : ℕ)
    (cfg : Config k Symbol State Oracle input) :
    (OracleComp.interpret (m := Id) answer (machine.runConfigFrom (pure bit)
        (fun oracle word => OracleComp.query (oracle, word)) fuel cfg), s) ∈
      ((OracleComp.interpret (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n))
          (fun q s => PMF.pure (answer q, s)))
        (machine.runConfigFrom (ProbOracleComp.sample (ProbComp.uniform Bool))
          (fun oracle word => ProbOracleComp.query (oracle, word)) fuel cfg)).run s).support := by
  have hbit : bit ∈ (Probability.PMF.uniformOfFintype Bool).support := by
    rw [PMF.mem_support_iff, Probability.PMF.uniformOfFintype_apply]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  simp only [runConfigFrom]
  induction fuel generalizing cfg with
  | zero => exact (PMF.mem_support_pure_iff _ _).mpr rfl
  | succ fuel ih =>
    cases hs : cfg.tapes.state with
    | none =>
      simp only [MultiTapeMachine.runConfigFrom, hs]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl
    | some state =>
      simp only [map_pure] at ih
      simp only [MultiTapeMachine.runConfigFrom, hs, map_pure, pure_bind, bind_map_left,
        OracleComp.interpret_bind, StateT.run_bind, ProbOracleComp.run_interpret_sample,
        ProbComp.eval_uniform, Probability.PMF.monad_bind_eq_bind, PMF.bind_map,
        PMF.mem_support_bind_iff, Function.comp_apply]
      refine ⟨bit, hbit, ?_⟩
      cases machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols bit
        with
      | step action symbol move => exact ih _
      | query oracle next =>
        simp only [OracleComp.interpret_bind, ProbOracleComp.interpret_query, StateT.run_bind,
          Probability.PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff]
        exact ⟨(answer (oracle, (cfg.channels oracle).queryBuffer), s),
          (PMF.mem_support_pure_iff _ _).mpr rfl, ih _⟩

end MultiTapePTM

end Turing

namespace Cslib.Probability.IsOraclePPTOn

open Turing Complexity

variable {Operation α β : Type} [DecidableEq Operation] {input : α ↪ List Bool}
  {output : β ↪ List Bool}

omit [DecidableEq Operation] in
/-- A deterministic program against a deterministic oracle returns a point mass and keeps the
oracle's state. -/
theorem run_interpret_interpret_query {σ : Type} (answer : Operation × List Bool → List Bool)
    (program : WordQueryComp Operation β) (s : σ) :
    (OracleComp.interpret (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n))
        (fun q s => PMF.pure (answer q, s)))
      (OracleComp.interpret ProbOracleComp.query program)).run s =
      PMF.pure (OracleComp.interpret (m := Id) answer program, s) := by
  rw [OracleComp.interpret_interpret]
  simp only [ProbOracleComp.interpret_query]
  induction program using PFunctor.FreeM.induction generalizing s with
  | pure b => rfl
  | lift_bind q cont ih =>
    rw [show (PFunctor.FreeM.lift q).bind cont = OracleComp.query q >>= cont from rfl,
      OracleComp.interpret_bind, OracleComp.interpret_query, StateT.run_bind,
      Probability.PMF.monad_bind_eq_bind]
    exact (PMF.pure_bind _ _).trans (ih _ s)

/-- **Certificates are deterministic runs.** A certificate for a deterministic program yields a
finite machine and a polynomial clock whose run with every coin fixed to `false` returns, against
every answer function, the encoded result of the program. -/
theorem exists_run_pure_false {program : α → WordQueryComp Operation β}
    (h : IsOraclePPTOn input output
      (fun a => OracleComp.interpret ProbOracleComp.query (program a))) :
    ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
      (machine : MultiTapePTM k Bool Control Operation) (c d : ℕ),
      ∀ a (answer : Operation × List Bool → List Bool),
        OracleComp.interpret (m := Id) answer (machine.run (pure false)
            (fun op word => OracleComp.query (op, word)) (c * ((input a).length + 1) ^ d)
            (input a)) =
          output (OracleComp.interpret (m := Id) answer (program a)) := by
  obtain ⟨-, k, Control, hfinite, machine, c, d, h⟩ := h
  refine ⟨k, Control, hfinite, machine, c, d, fun a answer => ?_⟩
  have hcert := h a Unit (fun q s => PMF.pure (answer q, s)) ()
  rw [OracleComp.interpret_map, StateT.run_map, run_interpret_interpret_query,
    PMF.monad_map_eq_map, PMF.pure_map] at hcert
  have hmem := MultiTapePTM.mem_support_runConfigFrom_pure machine false answer ()
    (c * ((input a).length + 1) ^ d) (machine.initialConfig (input a))
  have hmem' : (OracleComp.interpret (m := Id) answer (machine.run (pure false)
      (fun op word => OracleComp.query (op, word)) (c * ((input a).length + 1) ^ d) (input a)),
      ()) ∈ ((OracleComp.interpret (ProbOracleComp.handler
        (fun n => StateT.lift (ProbComp.unifOracle n)) (fun q s => PMF.pure (answer q, s)))
        (machine.runOracle (c * ((input a).length + 1) ^ d) (input a))).run ()).support := by
    simp only [MultiTapePTM.runOracle, MultiTapePTM.run, MultiTapePTM.runFrom,
      OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map, PMF.mem_support_map_iff]
    exact ⟨_, hmem, rfl⟩
  rw [← hcert, PMF.mem_support_pure_iff] at hmem'
  exact (Prod.mk.inj hmem').1

/-- **Certificates are deterministic runs of countably many machines.** As
`exists_run_pure_false`, with control states `Fin m`. -/
theorem exists_fin_run_pure_false {program : α → WordQueryComp Operation β}
    (h : IsOraclePPTOn input output
      (fun a => OracleComp.interpret ProbOracleComp.query (program a))) :
    ∃ (k m : ℕ) (machine : MultiTapePTM k Bool (Fin m) Operation) (c d : ℕ),
      ∀ a (answer : Operation × List Bool → List Bool),
        OracleComp.interpret (m := Id) answer (machine.run (pure false)
            (fun op word => OracleComp.query (op, word)) (c * ((input a).length + 1) ^ d)
            (input a)) =
          output (OracleComp.interpret (m := Id) answer (program a)) := by
  obtain ⟨k, Control, hfinite, machine, c, d, h⟩ := exists_run_pure_false h
  have := Fintype.ofFinite Control
  refine ⟨k, Fintype.card Control, machine.relabel (Fintype.equivFin Control), c, d,
    fun a answer => ?_⟩
  rw [MultiTapePTM.run_relabel]
  exact h a answer

end Cslib.Probability.IsOraclePPTOn
