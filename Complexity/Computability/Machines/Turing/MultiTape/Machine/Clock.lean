/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Machine.Simulation
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# An internal clock on a work tape

`withClock` reserves a last work tape for a unary budget. Each true cell permits one source
instruction, implemented by two target instructions. The first other cell stops the controller.
After the source halts, the controller consumes the remaining budget without changing source
tapes or communication channels. Preparing this tape is a separate computation: a machine does
not receive a polynomial-sized budget for free.

The choice interpreter must commute with mapping and interpret a constant choice as a pure
result with unchanged private state. For probabilistic machines, stateless coin draws satisfy
these conditions even when controller instructions discard their result. Query programs may
modify shared private state.

## Main definitions

* `Turing.MultiTapeMachine.withClock`: consume a budget stored on a fresh work tape.
* `Turing.MultiTapeMachine.Clock.config`: embed source data alongside the clock tape and head.

## Main results

* `Turing.MultiTapeMachine.run_interpret_runConfigFrom_withClock_add`: a budget of `t` cells
  reproduces the externally clocked source in `2 * t + 1` instructions, with arbitrary padding.
* `Turing.MultiTapeMachine.withClock_halted`: every supported final configuration has halted.

## References

Adapted from `MultiTape/Oracle/Clock.lean` on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8` to the common machine and typed program interface.
-/

@[expose] public section

namespace Turing.MultiTapeMachine

open Cslib

universe u v

variable {k : ℕ} {State Oracle : Type} {Choose : Type → Type v} {input : List Bool}

namespace Clock

/-- A phase bit and the source's optional control state. -/
abbrev Control (State : Type) := Bool × Option State

/-- Add a budget tape; a true phase bit means the next instruction advances its head. -/
def config (cfg : Config k Bool State Oracle input) (tape : ℤ → Option Bool) (position : ℤ)
    (ticking : Bool) : Config (k + 1) Bool (Control State) Oracle input where
  tapes :=
    { state := some (ticking, cfg.tapes.state)
      inputPos := cfg.tapes.inputPos
      workTapes := Fin.lastCases tape cfg.tapes.workTapes
      workTapePos := Fin.lastCases position cfg.tapes.workTapePos
      output := cfg.tapes.output }
  channels := cfg.channels

/-- Leave all source tapes unchanged. -/
def idle (next : Option (Control State)) : Turing.Action (k + 1) Bool (Control State) where
  inputTape := 0
  workTapes := fun _ => (none, 0)
  output := none
  state := next

/-- Advance the budget head while leaving all source tapes unchanged. -/
def tick (next : Option State) : Turing.Action (k + 1) Bool (Control State) where
  inputTape := 0
  workTapes := Fin.lastCases (none, 1) (fun _ => (none, 0))
  output := none
  state := some (false, next)

/-- Perform one source tape action, then enter the clock-advance phase. -/
def liftAction (action : Turing.Action k Bool State) :
    Turing.Action (k + 1) Bool (Control State) where
  inputTape := action.inputTape
  workTapes := Fin.lastCases (none, 0) action.workTapes
  output := action.output
  state := some (true, action.state)

/-- Lift either a tape instruction or an oracle submission to the clock controller. -/
def liftInstruction : Action k Bool State Oracle → Action (k + 1) Bool (Control State) Oracle
  | .step action symbol move => .step (liftAction action) symbol move
  | .query oracle next => .query oracle (true, some next)

end Clock

/-- Run under a unary budget on the last work tape; its construction is a separate computation. -/
@[simps! initial] def withClock [Applicative Choose]
    (machine : MultiTapeMachine k Bool State Oracle Choose) :
    MultiTapeMachine (k + 1) Bool (Clock.Control State) Oracle Choose where
  initial := (false, some machine.initial)
  tr control symbol work answer :=
    if control.1 then pure (.step (Clock.tick control.2) (fun _ => none) (fun _ => 0))
    else if work (Fin.last k) = some true then
      match control.2 with
      | none => pure (.step (Clock.idle (some (true, none))) (fun _ => none) (fun _ => 0))
      | some state => Clock.liftInstruction <$>
        machine.tr state symbol (fun i => work i.castSucc) answer
    else pure (.step (Clock.idle none) (fun _ => none) (fun _ => 0))

/-- Unfold one controller instruction without unfolding the machine in its continuation. -/
theorem withClock_tr [Applicative Choose] (machine : MultiTapeMachine k Bool State Oracle Choose)
    (control : Clock.Control State) (symbol : Option Bool) (work : Fin (k + 1) → Option Bool)
    (answer : Oracle → Option Bool) :
    machine.withClock.tr control symbol work answer =
      if control.1 then pure (.step (Clock.tick control.2) (fun _ => none) (fun _ => 0))
      else if work (Fin.last k) = some true then
        match control.2 with
        | none => pure (.step (Clock.idle (some (true, none))) (fun _ => none) (fun _ => 0))
        | some state => Clock.liftInstruction <$>
          machine.tr state symbol (fun i => work i.castSucc) answer
      else pure (.step (Clock.idle none) (fun _ => none) (fun _ => 0)) := rfl

namespace Clock

@[simp] theorem config_state (cfg : Config k Bool State Oracle input) (tape : ℤ → Option Bool)
    (position : ℤ) (ticking : Bool) :
    (config cfg tape position ticking).tapes.state = some (ticking, cfg.tapes.state) := rfl

@[simp] theorem config_inputSymbol (cfg : Config k Bool State Oracle input)
    (tape : ℤ → Option Bool) (position : ℤ) (ticking : Bool) :
    (config cfg tape position ticking).tapes.inputSymbol = cfg.tapes.inputSymbol := rfl

@[simp] theorem config_workTapeSymbols_castSucc (cfg : Config k Bool State Oracle input)
    (tape : ℤ → Option Bool) (position : ℤ) (ticking : Bool) (i : Fin k) :
    (config cfg tape position ticking).tapes.workTapeSymbols i.castSucc =
      cfg.tapes.workTapeSymbols i := by simp [config, Cfg.workTapeSymbols]

@[simp] theorem config_workTapeSymbols_last (cfg : Config k Bool State Oracle input)
    (tape : ℤ → Option Bool) (position : ℤ) (ticking : Bool) :
    (config cfg tape position ticking).tapes.workTapeSymbols (Fin.last k) = tape position := by
  simp [config, Cfg.workTapeSymbols]

@[simp] theorem config_answerSymbols (cfg : Config k Bool State Oracle input)
    (tape : ℤ → Option Bool) (position : ℤ) (ticking : Bool) :
    (config cfg tape position ticking).answerSymbols = cfg.answerSymbols := rfl

@[simp] theorem config_channels (cfg : Config k Bool State Oracle input) (tape : ℤ → Option Bool)
    (position : ℤ) (ticking : Bool) :
    (config cfg tape position ticking).channels = cfg.channels := rfl

@[simp] theorem config_output (cfg : Config k Bool State Oracle input) (tape : ℤ → Option Bool)
    (position : ℤ) (ticking : Bool) :
    (config cfg tape position ticking).tapes.output = cfg.tapes.output := rfl

theorem step_liftAction (cfg : Config k Bool State Oracle input) (tape : ℤ → Option Bool)
    (position : ℤ) (action : Turing.Action k Bool State) (symbol : Oracle → Option Bool)
    (move : Oracle → SignType) :
    (config cfg tape position false).step (liftAction action) symbol move =
      config (cfg.step action symbol move) tape position true := by
  refine Config.ext ?_ rfl
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> induction i using Fin.lastCases <;>
    simp [config, liftAction, Config.step, Turing.Action.apply]

theorem receive_config [DecidableEq Oracle] (cfg : Config k Bool State Oracle input)
    (tape : ℤ → Option Bool) (position : ℤ) (oracle : Oracle) (next : State) (answer : List Bool) :
    (config cfg tape position false).receive oracle (true, some next) answer =
      config (cfg.receive oracle next answer) tape position true := rfl

theorem step_tick (cfg : Config k Bool State Oracle input) (tape : ℤ → Option Bool)
    (position : ℤ) :
    (config cfg tape position true).step (tick cfg.tapes.state) (fun _ => none) (fun _ => 0) =
      config cfg tape (position + 1) false := by
  refine Config.ext ?_ (by simp [Config.step, config])
  refine Cfg.ext rfl (by simp [config, tick, Config.step, Turing.Action.apply]) ?_ ?_
    (by simp [config, tick, Config.step, Turing.Action.apply]) <;>
    funext i <;> induction i using Fin.lastCases <;>
    simp [config, tick, Config.step, Turing.Action.apply]

theorem step_idle (cfg : Config k Bool State Oracle input) (tape : ℤ → Option Bool)
    (position : ℤ) (ticking : Bool) (next : Option (Control State)) :
    (config cfg tape position ticking).step (idle next) (fun _ => none) (fun _ => 0) =
      { config cfg tape position ticking with tapes :=
          (config cfg tape position ticking).tapes.withState next } := by
  simp [config, idle, Config.step, Turing.Action.apply, Cfg.withState]

theorem step_pause (cfg : Config k Bool State Oracle input) (tape : ℤ → Option Bool)
    (position : ℤ) :
    (config cfg tape position false).step (idle (some (true, cfg.tapes.state)))
        (fun _ => none) (fun _ => 0) = config cfg tape position true := by
  rw [step_idle]
  rfl

/-- Stop the controller, retaining the source tapes, channels, and exhausted budget tape. -/
def stopped (cfg : Config k Bool State Oracle input) (tape : ℤ → Option Bool) (position : ℤ) :
    Config (k + 1) Bool (Control State) Oracle input :=
  { config cfg tape position false with tapes :=
      (config cfg tape position false).tapes.withState none }

@[simp] theorem stopped_state (cfg : Config k Bool State Oracle input) (tape : ℤ → Option Bool)
    (position : ℤ) : (stopped cfg tape position).tapes.state = none := rfl

@[simp] theorem stopped_output (cfg : Config k Bool State Oracle input) (tape : ℤ → Option Bool)
    (position : ℤ) : (stopped cfg tape position).tapes.output = cfg.tapes.output := rfl

end Clock

variable [Applicative Choose] [DecidableEq Oracle]
  {Query : Type u} {spec : OracleSpec.{u, 0} Query} {OracleState : Type}
  (machine : MultiTapeMachine k Bool State Oracle Choose)
  (choose : {α : Type} → Choose α → OracleComp spec α)
  (hchoose : ∀ {α β : Type} (f : α → β) (choices : Choose α),
    choose (f <$> choices) = f <$> choose choices)
  (query : Oracle → List Bool → OracleComp spec (List Bool))
  (oracle : (q : Query) → StateT OracleState PMF (spec q))
  (hpure : ∀ {α : Type} (a : α) (s : OracleState),
    (OracleComp.interpret oracle (choose (pure a))).run s = PMF.pure (a, s))

include hpure

namespace Clock

/-- The clock-advance instruction leaves the source and private interpreter state unchanged. -/
theorem run_interpret_tick (cfg : Config k Bool State Oracle input)
    (tape : ℤ → Option Bool) (position : ℤ) (s : OracleState) :
    (OracleComp.interpret oracle
      (machine.withClock.runConfigFrom choose query 1 (config cfg tape position true))).run s =
      PMF.pure (config cfg tape (position + 1) false, s) := by
  simp only [runConfigFrom, config_state, withClock_tr, ↓reduceIte, step_tick,
    OracleComp.interpret_bind, StateT.run_bind, Probability.PMF.monad_bind_eq_bind,
    hpure, PMF.pure_bind, OracleComp.interpret_pure, StateT.run_pure,
    Probability.PMF.monad_pure_eq_pure]

include hchoose in
/-- One available budget cell permits one source instruction and one clock advance. -/
theorem run_interpret_pair (cfg : Config k Bool State Oracle input)
    (tape : ℤ → Option Bool) (position : ℤ) (s : OracleState)
    (hcell : tape position = some true) :
    (OracleComp.interpret oracle
      (machine.withClock.runConfigFrom choose query 2 (config cfg tape position false))).run s =
      ((OracleComp.interpret oracle (machine.runConfigFrom choose query 1 cfg)).run s).map
        (fun (final, s') => (config final tape (position + 1) false, s')) := by
  conv_lhs => rw [runConfigFrom]
  conv_rhs => rw [runConfigFrom]
  simp only [config_state, withClock_tr, Bool.false_eq_true, ↓reduceIte,
    config_workTapeSymbols_last, hcell, config_inputSymbol,
    config_workTapeSymbols_castSucc, config_answerSymbols]
  cases hs : cfg.tapes.state with
  | none =>
    simp only [OracleComp.interpret_bind, StateT.run_bind,
      Probability.PMF.monad_bind_eq_bind, hpure, PMF.pure_bind]
    rw [← hs, step_pause, run_interpret_tick machine choose query oracle hpure]
    simp
  | some state =>
    simp only [hchoose, bind_map_left, OracleComp.interpret_bind, StateT.run_bind,
      Probability.PMF.monad_bind_eq_bind, PMF.map_bind]
    congr 1
    funext result
    rcases result with ⟨instruction, s'⟩
    cases instruction with
    | step action symbol move =>
      simp [liftInstruction, step_liftAction, run_interpret_tick machine choose query oracle hpure]
    | query op next =>
      simp only [liftInstruction, config_channels, OracleComp.interpret_bind, StateT.run_bind,
        Probability.PMF.monad_bind_eq_bind, PMF.map_bind]
      congr 1
      funext result
      rcases result with ⟨answer, s''⟩
      simp [receive_config, run_interpret_tick machine choose query oracle hpure]

include hchoose in
/-- A bounded simulation advances the clock head once per source instruction. -/
theorem run_interpret_prefix (cfg : Config k Bool State Oracle input) (tape : ℤ → Option Bool)
    (position : ℤ) (fuel : ℕ) (s : OracleState)
    (hbudget : ∀ i : ℕ, i < fuel → tape (position + i) = some true) :
    (OracleComp.interpret oracle
      (machine.withClock.runConfigFrom choose query (2 * fuel)
        (config cfg tape position false))).run s =
      ((OracleComp.interpret oracle (machine.runConfigFrom choose query fuel cfg)).run s).map
        (fun (final, s') => (config final tape (position + fuel) false, s')) := by
  have hstep : ∀ i, i < fuel → ∀ (cfg : Config k Bool State Oracle input) (s : OracleState),
      (OracleComp.interpret oracle
        (machine.withClock.runConfigFrom choose query 2
          (config cfg tape (position + i) false))).run s =
        ((OracleComp.interpret oracle (machine.runConfigFrom choose query 1 cfg)).run s).map
          (fun (final, s') => (config final tape (position + (i + 1 : ℕ)) false, s')) := by
    intro i hi cfg s
    simpa [Nat.cast_add, add_assoc] using
      run_interpret_pair machine choose hchoose query oracle hpure cfg tape (position + i) s
        (hbudget i hi)
  simpa only [Nat.cast_zero, add_zero] using
    run_interpret_runConfigFrom_mul_indexed machine machine.withClock choose choose query query
      2 fuel (fun i cfg => config cfg tape (position + i) false) oracle hstep cfg s

/-- At the budget's end, halt without another source instruction or oracle call. -/
theorem run_interpret_stop (cfg : Config k Bool State Oracle input) (tape : ℤ → Option Bool)
    (position : ℤ) (s : OracleState) (hstop : tape position ≠ some true) :
    (OracleComp.interpret oracle
      (machine.withClock.runConfigFrom choose query 1 (config cfg tape position false))).run s =
      PMF.pure (stopped cfg tape position, s) := by
  simp only [runConfigFrom, config_state, withClock_tr, Bool.false_eq_true, ↓reduceIte,
    config_workTapeSymbols_last, hstop, OracleComp.interpret_bind, StateT.run_bind,
    Probability.PMF.monad_bind_eq_bind, hpure, PMF.pure_bind, step_idle,
    OracleComp.interpret_pure, StateT.run_pure, Probability.PMF.monad_pure_eq_pure]
  rfl

end Clock

include hchoose

/-- A prepared unary budget implements the source's external cutoff with actual halting.
All source tapes, channels, and private interpreter state are retained; the source control state
is discarded when the controller halts. Constant choices must have no interpreted effect. -/
theorem run_interpret_runConfigFrom_withClock (cfg : Config k Bool State Oracle input)
    (tape : ℤ → Option Bool) (position : ℤ) (budget : ℕ) (s : OracleState)
    (hbudget : ∀ i : ℕ, i < budget → tape (position + i) = some true)
    (hstop : tape (position + budget) ≠ some true) :
    (OracleComp.interpret oracle
      (machine.withClock.runConfigFrom choose query (2 * budget + 1)
        (Clock.config cfg tape position false))).run s =
      ((OracleComp.interpret oracle (machine.runConfigFrom choose query budget cfg)).run s).map
        (fun (final, s') => (Clock.stopped final tape (position + budget), s')) := by
  rw [runConfigFrom_add, OracleComp.interpret_bind, StateT.run_bind,
    Probability.PMF.monad_bind_eq_bind,
    Clock.run_interpret_prefix machine choose hchoose query oracle hpure cfg tape position budget s
      hbudget, PMF.bind_map]
  simp only [Function.comp_def,
    Clock.run_interpret_stop machine choose query oracle hpure _ tape _ _ hstop]
  rfl

/-- Extra time after budget exhaustion cannot change the configuration or private state. -/
theorem run_interpret_runConfigFrom_withClock_add (cfg : Config k Bool State Oracle input)
    (tape : ℤ → Option Bool) (position : ℤ) (budget padding : ℕ) (s : OracleState)
    (hbudget : ∀ i : ℕ, i < budget → tape (position + i) = some true)
    (hstop : tape (position + budget) ≠ some true) :
    (OracleComp.interpret oracle
      (machine.withClock.runConfigFrom choose query (2 * budget + 1 + padding)
        (Clock.config cfg tape position false))).run s =
      ((OracleComp.interpret oracle (machine.runConfigFrom choose query budget cfg)).run s).map
        (fun (final, s') => (Clock.stopped final tape (position + budget), s')) := by
  rw [runConfigFrom_add, OracleComp.interpret_bind, StateT.run_bind,
    Probability.PMF.monad_bind_eq_bind,
    run_interpret_runConfigFrom_withClock machine choose hchoose query oracle hpure cfg tape
      position budget s hbudget hstop, PMF.bind_map]
  simp only [Function.comp_def, runConfigFrom_halted _ _ _ _ _ (Clock.stopped_state ..),
    OracleComp.interpret_pure, StateT.run_pure, Probability.PMF.monad_pure_eq_pure]
  rfl

/-- In particular, the output and final private state agree with the original clocked run. -/
theorem run_interpret_runFrom_withClock (cfg : Config k Bool State Oracle input)
    (tape : ℤ → Option Bool) (position : ℤ) (budget padding : ℕ) (s : OracleState)
    (hbudget : ∀ i : ℕ, i < budget → tape (position + i) = some true)
    (hstop : tape (position + budget) ≠ some true) :
    (OracleComp.interpret oracle
      (machine.withClock.runFrom choose query (2 * budget + 1 + padding)
        (Clock.config cfg tape position false))).run s =
      (OracleComp.interpret oracle (machine.runFrom choose query budget cfg)).run s := by
  have h := congrArg (PMF.map (fun result => (result.1.tapes.output, result.2)))
    (run_interpret_runConfigFrom_withClock_add machine choose hchoose query oracle hpure cfg tape
      position budget padding s hbudget hstop)
  simpa [runFrom, OracleComp.interpret_map, StateT.run_map, PMF.map_comp, Function.comp_def] using h

/-- Every supported final configuration is halted when the prepared budget expires. -/
theorem withClock_halted (cfg : Config k Bool State Oracle input) (tape : ℤ → Option Bool)
    (position : ℤ) (budget padding : ℕ) (s : OracleState)
    (hbudget : ∀ i : ℕ, i < budget → tape (position + i) = some true)
    (hstop : tape (position + budget) ≠ some true)
    (final : Config (k + 1) Bool (Clock.Control State) Oracle input) (s' : OracleState)
    (hfinal : (final, s') ∈ ((OracleComp.interpret oracle
      (machine.withClock.runConfigFrom choose query (2 * budget + 1 + padding)
        (Clock.config cfg tape position false))).run s).support) : final.tapes.state = none := by
  rw [run_interpret_runConfigFrom_withClock_add machine choose hchoose query oracle hpure cfg tape
    position budget padding s hbudget hstop] at hfinal
  obtain ⟨⟨sourceFinal, sourceState⟩, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
  exact (congrArg (fun result => result.1.tapes.state) heq).symm

end Turing.MultiTapeMachine
