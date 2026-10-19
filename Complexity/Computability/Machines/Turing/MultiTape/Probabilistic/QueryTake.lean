/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Oracle
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Sequential
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindInput
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Defs

/-!
# Word-configuration phases and bounded-prefix oracle queries

`RunsWords` and `ComputesTidily` express that a probabilistic oracle machine starts from a word
configuration with empty query buffers, halts within a strict step bound with empty query buffers,
and realizes the exact joint distribution of resulting tape words, emitted output and external
oracle state.

`queryTakePTM op` realizes the primitive bounded-prefix oracle call on an encoded pair
`encPair encBits encUnary (q, limit)`: it unframes `q` into channel `op`'s query buffer, submits
the query once, copies at most `limit` reply bits while scanning the unary limit, and rewinds the
input head.

## Main definitions

* `Turing.MultiTapePTM.runOracleConfigFrom`: clocked configuration run with fair coins and named
  word queries.
* `Turing.MultiTapePTM.RunsWords`: word-configuration phase specification preserving external
  oracle state and empty query buffers.
* `Turing.MultiTapePTM.ComputesTidily`: tidy computation from blank work tapes to blank work tapes.
* `Turing.MultiTapePTM.coinMachine`: one-step fair-bit emitter.
* `Turing.MultiTapePTM.queryTakePTM`: tidy machine for `List.take limit <$> query (op, q)`.

## Main results

* `Turing.MultiTapePTM.RunsWords.of_transformsTapes`: lift deterministic `TransformsTapes` phases.
* `Turing.MultiTapePTM.RunsWords.seq_bind`: sequence two `RunsWords` phases.
* `Turing.MultiTapePTM.computesTidily_coinMachine`: tidy specification of `coinMachine`.
* `Turing.MultiTapePTM.computesTidily_queryTakePTM`: tidy specification of `queryTakePTM`.

## References

`RunsWords` and `ComputesTidily` adapt the deterministic `TransformsTapes` and tidy-machine
notions of cslib's `Plumbing/TransformsTapes` and `Plumbing/Tidy`, by Christian Reitwiessner, in
the run form of crei:crei/tidy-universal @7f7c0696, to the probabilistic oracle machines of the
cslib `crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib Cslib.Probability MultiTapeMachine MultiTapeMachine.Sequential MultiTapeTM

variable {k : ℕ} {Symbol State State₀ State₁ Operation OracleState : Type}
  {input : List Symbol} [DecidableEq Operation]

/-- `tapeOfList` is injective on words. -/
theorem tapeOfList_injective : Function.Injective (@tapeOfList Symbol) := by
  intro u v h
  exact List.ext_getElem? fun n => congrFun h n

/-- A `wordsCfg` uniquely determines its work-tape words and the suffix appended to `out₀`. -/
theorem wordsCfg_injective {q : Option State} {ws₁ ws₂ : Fin k → List Symbol}
    {out₀ e₁ e₂ : List Symbol}
    (h : wordsCfg input q ws₁ (out₀ ++ e₁) = wordsCfg input q ws₂ (out₀ ++ e₂)) :
    ws₁ = ws₂ ∧ e₁ = e₂ := by
  refine ⟨funext fun i => tapeOfList_injective (congrFun (congrArg Cfg.workTapes h) i), ?_⟩
  exact List.append_cancel_left (congrArg Cfg.output h)

/-- Retain the complete configuration of an open fair-coin run with external word queries. -/
noncomputable def runOracleConfigFrom (machine : MultiTapePTM k Symbol State Operation)
    (fuel : ℕ) (cfg : Config k Symbol State Operation input) :
    ProbOracleComp (fun _ : Operation × List Symbol => List Symbol)
      (Config k Symbol State Operation input) :=
  machine.runConfigFrom (ProbOracleComp.sample (ProbComp.uniform Bool))
    (fun op word => ProbOracleComp.query (op, word)) fuel cfg

/-- `runOracle` is the output projection of `runOracleConfigFrom` from the initial configuration. -/
theorem runOracle_eq_map (machine : MultiTapePTM k Symbol State Operation) (fuel : ℕ)
    (input : List Symbol) :
    machine.runOracle fuel input =
      (fun final => final.tapes.output) <$>
        machine.runOracleConfigFrom fuel (machine.initialConfig input) := rfl

omit [DecidableEq Operation] in
/-- Drawing one fair bit in `ProbOracleComp` leaves the external oracle state unchanged. -/
theorem run_interpret_sample_uniform_bool
    (oracle : Operation × List Symbol → StateT OracleState PMF (List Symbol)) (s : OracleState) :
    (OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (ProbOracleComp.sample (ProbComp.uniform Bool))).run s =
      (PMF.uniformOfFintype Bool).map (fun bit => (bit, s)) := by
  simp only [ProbOracleComp.run_interpret_sample, ProbComp.eval_uniform]

/-- Padding a halted oracle run preserves the joint configuration and external state
distribution. -/
theorem run_interpret_runOracleConfigFrom_add_of_halted
    (machine : MultiTapePTM k Symbol State Operation)
    (oracle : Operation × List Symbol → StateT OracleState PMF (List Symbol))
    (cfg : Config k Symbol State Operation input) (fuel padding : ℕ) (s : OracleState)
    (hhalt : ∀ final ∈ ((OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (machine.runOracleConfigFrom fuel cfg)).run s).support,
      final.1.tapes.state = none) :
    (OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (machine.runOracleConfigFrom (fuel + padding) cfg)).run s =
      (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (machine.runOracleConfigFrom fuel cfg)).run s :=
  MultiTapeMachine.run_interpret_runConfigFrom_add_of_halted machine _ _ _ cfg fuel padding s hhalt

/-- Any larger clock gives the same joint configuration and external state distribution after a
halting bound. -/
theorem run_interpret_runOracleConfigFrom_eq_of_halted
    (machine : MultiTapePTM k Symbol State Operation)
    (oracle : Operation × List Symbol → StateT OracleState PMF (List Symbol))
    (cfg : Config k Symbol State Operation input) {fuel larger : ℕ} (hle : fuel ≤ larger)
    (s : OracleState)
    (hhalt : ∀ final ∈ ((OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (machine.runOracleConfigFrom fuel cfg)).run s).support,
      final.1.tapes.state = none) :
    (OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (machine.runOracleConfigFrom larger cfg)).run s =
      (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (machine.runOracleConfigFrom fuel cfg)).run s := by
  simpa only [Nat.add_sub_of_le hle] using
    run_interpret_runOracleConfigFrom_add_of_halted machine oracle cfg fuel (larger - fuel) s hhalt

/-- A deterministic machine embedded in `MultiTapePTM` preserves channels and external state. -/
theorem run_interpret_runOracleConfigFrom_ofDeterministic
    (machine : MultiTapeTM k Symbol State)
    (oracle : Operation × List Symbol → StateT OracleState PMF (List Symbol))
    (fuel : ℕ) (cfg : Config k Symbol State Operation input) (s : OracleState) :
    (OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      ((ofDeterministic machine).runOracleConfigFrom fuel cfg)).run s =
      PMF.pure ({ cfg with tapes := machine.runFrom cfg.tapes fuel }, s) :=
  run_interpret_runConfigFrom_ofDeterministic machine _ _ _ (PMF.uniformOfFintype Bool)
    (run_interpret_sample_uniform_bool oracle) fuel cfg s

/-- Sequencing law for `runOracleConfigFrom` when both phases halt on all supported paths. -/
theorem run_interpret_runOracleConfigFrom_seq
    (first : MultiTapePTM k Symbol State₀ Operation)
    (second : MultiTapePTM k Symbol State₁ Operation)
    (oracle : Operation × List Symbol → StateT OracleState PMF (List Symbol))
    (cfg : Config k Symbol State₀ Operation input) (t₁ t₂ : ℕ) (s : OracleState)
    (h₁ : ∀ result ∈ ((OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (first.runOracleConfigFrom t₁ cfg)).run s).support,
      result.1.tapes.state = none)
    (h₂ : ∀ result ∈ ((OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (first.runOracleConfigFrom t₁ cfg)).run s).support,
      ∀ final ∈ ((OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (second.runOracleConfigFrom t₂ (Sequential.start second result.1))).run result.2).support,
        final.1.tapes.state = none) :
    (OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      ((first.seq second).runOracleConfigFrom (t₁ + t₂) (Sequential.left second cfg))).run s =
    ((OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (first.runOracleConfigFrom t₁ cfg)).run s).bind (fun result =>
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (second.runOracleConfigFrom t₂
          (Sequential.start second result.1))).run result.2).map
        (fun (final, s') => (Sequential.right final, s'))) :=
  run_interpret_runConfigFrom_seq first second _ _ _ cfg t₁ t₂ s h₁ h₂

/-- A live step whose transition does not depend on the coin bit advances the configuration
deterministically while preserving the external oracle state. -/
theorem run_interpret_runOracleConfigFrom_succ_step
    (machine : MultiTapePTM k Symbol State Operation)
    (oracle : Operation × List Symbol → StateT OracleState PMF (List Symbol))
    (fuel : ℕ) (cfg : Config k Symbol State Operation input) (s : OracleState)
    {state : State} (hstate : cfg.tapes.state = some state)
    {action : Turing.Action k Symbol State}
    {symbol : Operation → Option Symbol} {move : Operation → SignType}
    (htr : ∀ bit,
      machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols bit =
        .step action symbol move) :
    (OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (machine.runOracleConfigFrom (fuel + 1) cfg)).run s =
    (OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (machine.runOracleConfigFrom fuel (cfg.step action symbol move))).run s := by
  dsimp only [runOracleConfigFrom, runConfigFrom]
  rw [MultiTapeMachine.runConfigFrom]
  simp only [hstate, bind_map_left, htr, OracleComp.interpret_bind, StateT.run_bind,
    run_interpret_sample_uniform_bool, Probability.PMF.monad_bind_eq_bind, PMF.bind_map,
    Function.comp_def, PMF.bind_const]

/-- A live query step whose transition does not depend on the coin bit submits the accumulated
query on `op` and continues from the updated configuration. -/
theorem run_interpret_runOracleConfigFrom_succ_query
    (machine : MultiTapePTM k Symbol State Operation)
    (oracle : Operation × List Symbol → StateT OracleState PMF (List Symbol))
    (fuel : ℕ) (cfg : Config k Symbol State Operation input) (s : OracleState)
    {state : State} (hstate : cfg.tapes.state = some state)
    {op : Operation} {next : State}
    (htr : ∀ bit,
      machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols bit =
        .query op next) :
    (OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (machine.runOracleConfigFrom (fuel + 1) cfg)).run s =
    (oracle (op, (cfg.channels op).queryBuffer) s).bind (fun (answer, s') =>
      (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (machine.runOracleConfigFrom fuel (cfg.receive op next answer))).run s') := by
  dsimp only [runOracleConfigFrom, runConfigFrom]
  rw [MultiTapeMachine.runConfigFrom]
  simp only [hstate, bind_map_left, htr, OracleComp.interpret_bind, StateT.run_bind,
    ProbOracleComp.interpret_query, run_interpret_sample_uniform_bool,
    Probability.PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def, PMF.bind_const]
  rfl

/-- Starting from a `wordsCfg` with empty query buffers, `machine` halts within `time` steps with
empty query buffers, realizing `program` on the work tapes and emitted output while preserving the
joint distribution with any external oracle state. -/
def RunsWords (machine : MultiTapePTM k Bool State Operation) (x : List Bool)
    (ws₀ : Fin k → List Bool) (out₀ : List Bool) (time : ℕ)
    {α : Type} (program : ProbOracleComp (fun _ : Operation × List Bool => List Bool) α)
    (ws₁ : α → Fin k → List Bool) (emit : α → List Bool) : Prop :=
  ∀ (OracleState : Type) (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
    (s : OracleState) (cfg : Config k Bool State Operation x),
    cfg.tapes = wordsCfg x (some machine.initial) ws₀ out₀ →
    (∀ op, (cfg.channels op).queryBuffer = []) →
    let run := (OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (machine.runOracleConfigFrom time cfg)).run s
    run.map (fun (final, s') => (final.tapes, s')) =
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        program).run s).map
        (fun (a, s') => (wordsCfg x none (ws₁ a) (out₀ ++ emit a), s')) ∧
    ∀ final ∈ run.support, ∀ op, (final.1.channels op).queryBuffer = []

/-- A tidy probabilistic oracle computation starts with blank work tapes and empty query buffers,
and halts within `time` steps with blank work tapes, empty query buffers, the input head back at
position `1`, and `program`'s output appended to the output tape. -/
def ComputesTidily (machine : MultiTapePTM k Bool State Operation) (x : List Bool)
    (time : ℕ)
    (program : ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)) : Prop :=
  ∀ out₀, machine.RunsWords x (fun _ => []) out₀ time program (fun _ _ => []) id

namespace RunsWords

variable {machine : MultiTapePTM k Bool State Operation} {x : List Bool}
  {ws₀ : Fin k → List Bool} {out₀ : List Bool} {time time' : ℕ}
  {α β : Type}
  {program program' : ProbOracleComp (fun _ : Operation × List Bool => List Bool) α}
  {ws₁ : α → Fin k → List Bool} {emit : α → List Bool}

/-- Every supported final configuration of a `RunsWords` phase has halted. -/
theorem halted (h : machine.RunsWords x ws₀ out₀ time program ws₁ emit)
    (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
    (s : OracleState) (cfg : Config k Bool State Operation x)
    (htapes : cfg.tapes = wordsCfg x (some machine.initial) ws₀ out₀)
    (hbuf : ∀ op, (cfg.channels op).queryBuffer = []) :
    ∀ final ∈ ((OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (machine.runOracleConfigFrom time cfg)).run s).support,
      final.1.tapes.state = none := by
  intro final hfinal
  have hmap : (final.1.tapes, final.2) ∈
      (((OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (machine.runOracleConfigFrom time cfg)).run s).map
        (fun (final, s') => (final.tapes, s'))).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨final, hfinal, rfl⟩
  rw [(h OracleState oracle s cfg htapes hbuf).1] at hmap
  obtain ⟨⟨a, s'⟩, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hmap
  exact (congrArg (fun p => p.1.state) heq).symm

/-- Every supported final configuration of a `RunsWords` phase has the declared tapes and
clean query buffers for some supported value of `program`. -/
theorem mem_support (h : machine.RunsWords x ws₀ out₀ time program ws₁ emit)
    (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
    (s : OracleState) (cfg : Config k Bool State Operation x)
    (htapes : cfg.tapes = wordsCfg x (some machine.initial) ws₀ out₀)
    (hbuf : ∀ op, (cfg.channels op).queryBuffer = [])
    {final : Config k Bool State Operation x} {s' : OracleState}
    (hfinal : (final, s') ∈ ((OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (machine.runOracleConfigFrom time cfg)).run s).support) :
    (∃ a, (a, s') ∈ ((OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        program).run s).support ∧
      final.tapes = wordsCfg x none (ws₁ a) (out₀ ++ emit a)) ∧
    ∀ op, (final.channels op).queryBuffer = [] := by
  obtain ⟨hlaw, hclean⟩ := h OracleState oracle s cfg htapes hbuf
  refine ⟨?_, hclean (final, s') hfinal⟩
  have hmap : (final.tapes, s') ∈
      (((OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (machine.runOracleConfigFrom time cfg)).run s).map
        (fun (final, s') => (final.tapes, s'))).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨(final, s'), hfinal, rfl⟩
  rw [hlaw] at hmap
  obtain ⟨⟨a, s₁⟩, ha, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hmap
  rcases Prod.mk.inj heq with ⟨ht, rfl⟩
  exact ⟨a, ha, ht.symm⟩

/-- Increasing the step budget preserves `RunsWords`. -/
theorem mono (h : machine.RunsWords x ws₀ out₀ time program ws₁ emit) (hle : time ≤ time') :
    machine.RunsWords x ws₀ out₀ time' program ws₁ emit := by
  intro OracleState oracle s cfg htapes hbuf
  dsimp only
  rw [run_interpret_runOracleConfigFrom_eq_of_halted machine oracle cfg hle s
    (h.halted oracle s cfg htapes hbuf)]
  exact h OracleState oracle s cfg htapes hbuf

/-- Replace `program` by a stateful-distributionally equivalent program. -/
theorem congr (h : machine.RunsWords x ws₀ out₀ time program ws₁ emit)
    (heq : ∀ (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool)) (s : OracleState),
      (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        program).run s =
      (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        program').run s) :
    machine.RunsWords x ws₀ out₀ time program' ws₁ emit := by
  intro OracleState oracle s cfg htapes hbuf
  rw [← heq OracleState oracle s]
  exact h OracleState oracle s cfg htapes hbuf

/-- Map a function across the program result when the tape and output maps factor through it. -/
theorem of_map (f : α → β) (ws₁' : β → Fin k → List Bool) (emit' : β → List Bool)
    (h : machine.RunsWords x ws₀ out₀ time program (fun a => ws₁' (f a)) (fun a => emit' (f a))) :
    machine.RunsWords x ws₀ out₀ time (f <$> program) ws₁' emit' := by
  intro OracleState oracle s cfg htapes hbuf
  obtain ⟨hlaw, hclean⟩ := h OracleState oracle s cfg htapes hbuf
  refine ⟨?_, hclean⟩
  rw [hlaw, OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map, PMF.map_comp]
  rfl

/-- Lift a deterministic `TransformsTapes` specification to `ofDeterministic`. -/
theorem of_transformsTapes {tm : MultiTapeTM k Bool State}
    {P : List Bool → (Fin k → List Bool) → Prop}
    {Q : List Bool → (Fin k → List Bool) → (Fin k → List Bool) → List Bool → Prop}
    {t s : ℕ} (htm : TransformsTapes tm P Q t s)
    (hP : P x ws₀) {ws' : Fin k → List Bool} {emitted : List Bool}
    (hQ : ∀ ws₁ em, Q x ws₀ ws₁ em → ws₁ = ws' ∧ em = emitted) :
    (ofDeterministic tm : MultiTapePTM k Bool State Operation).RunsWords
      x ws₀ out₀ t (pure ()) (fun _ => ws') (fun _ => emitted) := by
  intro OracleState oracle state cfg htapes hbuf
  obtain ⟨ws₁, em, hrun, hQ₁, _⟩ := transformsTapes_iff_runFrom.mp htm x ws₀ out₀ hP
  obtain ⟨rfl, rfl⟩ := hQ ws₁ em hQ₁
  have htapes' : cfg.tapes = wordsCfg x (some tm.q₀) ws₀ out₀ := htapes
  dsimp only
  rw [run_interpret_runOracleConfigFrom_ofDeterministic, htapes', hrun]
  simp only [OracleComp.interpret_pure, StateT.run_pure, Probability.PMF.monad_pure_eq_pure,
    PMF.pure_map, PMF.support_pure, Set.mem_singleton_iff, forall_eq, true_and]
  exact hbuf

/-- Sequence two `RunsWords` phases when the first phase's resulting tape/output configuration
uniquely identifies its program value. -/
theorem seq_bind {first : MultiTapePTM k Bool State₀ Operation}
    {second : MultiTapePTM k Bool State₁ Operation}
    {t₁ t₂ : ℕ}
    {prog₁ : ProbOracleComp (fun _ : Operation × List Bool => List Bool) α}
    {prog₂ : α → ProbOracleComp (fun _ : Operation × List Bool => List Bool) β}
    {ws₁ : α → Fin k → List Bool} {emit₁ : α → List Bool}
    {ws₂ : α → β → Fin k → List Bool} {emit₂ : α → β → List Bool}
    (hinj : Function.Injective (fun a => (ws₁ a, emit₁ a)))
    (h₁ : first.RunsWords x ws₀ out₀ t₁ prog₁ ws₁ emit₁)
    (h₂ : ∀ a (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool)) (s s' : OracleState),
      (a, s') ∈ ((OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        prog₁).run s).support →
      second.RunsWords x (ws₁ a) (out₀ ++ emit₁ a) t₂ (prog₂ a) (ws₂ a) (emit₂ a)) :
    (first.seq second).RunsWords x ws₀ out₀ (t₁ + t₂)
      (prog₁ >>= fun a => (fun b => (a, b)) <$> prog₂ a)
      (fun p : α × β => ws₂ p.1 p.2) (fun p : α × β => emit₁ p.1 ++ emit₂ p.1 p.2) := by
  classical
  intro OracleState oracle s cfg htapes hbuf
  let cfg₀ : Config k Bool State₀ Operation x :=
    { tapes := wordsCfg x (some first.initial) ws₀ out₀, channels := cfg.channels }
  have hleft : cfg = Sequential.left second cfg₀ := by
    refine Config.ext ?_ rfl
    rw [htapes]
    rfl
  let f (a : α) : Cfg k Bool State₀ x := wordsCfg x none (ws₁ a) (out₀ ++ emit₁ a)
  have hf : Function.Injective f := by
    intro a₁ a₂ heq
    obtain ⟨hws, hem⟩ := wordsCfg_injective heq
    exact hinj (Prod.ext hws hem)
  have hhalt₁ := h₁.halted oracle s cfg₀ rfl hbuf
  have hhalt₂ : ∀ result ∈ ((OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (first.runOracleConfigFrom t₁ cfg₀)).run s).support,
      ∀ final ∈ ((OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (second.runOracleConfigFrom t₂ (Sequential.start second result.1))).run result.2).support,
        final.1.tapes.state = none := by
    rintro ⟨mid, s₁⟩ hmid
    obtain ⟨⟨a, ha, hmidTapes⟩, hmidBuf⟩ := h₁.mem_support oracle s cfg₀ rfl hbuf hmid
    have hstart : (Sequential.start second mid).tapes =
        wordsCfg x (some second.initial) (ws₁ a) (out₀ ++ emit₁ a) := by
      simp [Sequential.start, hmidTapes]
    exact (h₂ a OracleState oracle s s₁ ha).halted oracle s₁ (Sequential.start second mid)
      hstart hmidBuf
  dsimp only
  rw [hleft, run_interpret_runOracleConfigFrom_seq first second oracle cfg₀ t₁ t₂ s hhalt₁ hhalt₂]
  constructor
  · rw [PMF.map_bind]
    let g (p : Cfg k Bool State₀ x × OracleState) :
        PMF (Cfg k Bool (State₀ ⊕ State₁) x × OracleState) :=
      if h : ∃ a, p.1 = f a then
        ((OracleComp.interpret
          (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (prog₂ (Classical.choose h))).run p.2).map
          (fun (b, s₂) =>
            (wordsCfg x none (ws₂ (Classical.choose h) b)
              (out₀ ++ (emit₁ (Classical.choose h) ++ emit₂ (Classical.choose h) b)), s₂))
      else PMF.pure (wordsCfg x none ws₀ out₀, p.2)
    have hg (a : α) (s₁ : OracleState) :
        g (wordsCfg x none (ws₁ a) (out₀ ++ emit₁ a), s₁) =
          ((OracleComp.interpret
            (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
            (prog₂ a)).run s₁).map
            (fun (b, s₂) =>
              (wordsCfg x none (ws₂ a b) (out₀ ++ (emit₁ a ++ emit₂ a b)), s₂)) := by
      have hex : ∃ a', f a = f a' := ⟨a, rfl⟩
      have hchoose : Classical.choose hex = a := hf (Classical.choose_spec hex).symm
      change (if h : ∃ a', f a = f a' then _ else _) = _
      simp only [hex, ↓reduceDIte, hchoose]
    have hcongr :
        ((OracleComp.interpret
          (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (first.runOracleConfigFrom t₁ cfg₀)).run s).bind
          (fun result =>
            PMF.map (fun (final, s') => (final.tapes, s'))
              (PMF.map (fun (final, s') => (Sequential.right final, s'))
                ((OracleComp.interpret
                  (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
                  (second.runOracleConfigFrom t₂
                    (Sequential.start second result.1))).run result.2))) =
        ((OracleComp.interpret
          (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (first.runOracleConfigFrom t₁ cfg₀)).run s).bind
          (fun result => g (result.1.tapes, result.2)) := by
      apply PMF.bind_congr_on_support
      rintro ⟨mid, s₁⟩ hmid
      obtain ⟨⟨a, ha, hmidTapes⟩, hmidBuf⟩ := h₁.mem_support oracle s cfg₀ rfl hbuf hmid
      have hstart : (Sequential.start second mid).tapes =
          wordsCfg x (some second.initial) (ws₁ a) (out₀ ++ emit₁ a) := by
        simp [Sequential.start, hmidTapes]
      have hsecondLaw := ((h₂ a OracleState oracle s s₁ ha) OracleState oracle s₁
        (Sequential.start second mid) hstart hmidBuf).1
      have hright :
          PMF.map (fun p => (p.1.tapes, p.2))
            (PMF.map (fun p => (Sequential.right (State₀ := State₀) p.1, p.2))
              ((OracleComp.interpret
                (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
                (second.runOracleConfigFrom t₂ (Sequential.start second mid))).run s₁)) =
          PMF.map (fun p => (Cfg.mapState (Option.map (Sum.inr (α := State₀))) p.1, p.2))
            (PMF.map (fun p => (p.1.tapes, p.2))
              ((OracleComp.interpret
                (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
                (second.runOracleConfigFrom t₂ (Sequential.start second mid))).run s₁)) := by
        simp only [PMF.map_comp, Function.comp_def, Sequential.right]
      rw [hright, hsecondLaw, hmidTapes, hg a s₁, PMF.map_comp]
      congr 1
      funext ⟨b, s₂⟩
      simp only [Cfg.mapState, List.append_assoc, Function.comp_apply, wordsCfg_state,
        Option.map_none, wordsCfg_inputPos, wordsCfg_output, Prod.mk.injEq, and_true]
      rfl
    rw [hcongr]
    have hmapBind :
        ((OracleComp.interpret
          (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (first.runOracleConfigFrom t₁ cfg₀)).run s).bind
          (fun result => g (result.1.tapes, result.2)) =
        (((OracleComp.interpret
          (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (first.runOracleConfigFrom t₁ cfg₀)).run s).map
          (fun (final, s') => (final.tapes, s'))).bind g := by
      rw [PMF.bind_map]
      rfl
    rw [hmapBind, (h₁ OracleState oracle s cfg₀ rfl hbuf).1, PMF.bind_map]
    simp only [OracleComp.interpret_bind, OracleComp.interpret_map, StateT.run_bind,
      StateT.run_map, Probability.PMF.monad_bind_eq_bind, PMF.monad_map_eq_map,
      PMF.map_bind, PMF.map_comp, Function.comp_def, hg]
  · intro final hfinal op
    obtain ⟨⟨mid, s₁⟩, hmid, hfinal⟩ := (PMF.mem_support_bind_iff _ _ _).mp hfinal
    obtain ⟨⟨final₀, s₂⟩, hfinal₀, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
    obtain ⟨⟨a, ha, hmidTapes⟩, hmidBuf⟩ := h₁.mem_support oracle s cfg₀ rfl hbuf hmid
    have hstart : (Sequential.start second mid).tapes =
        wordsCfg x (some second.initial) (ws₁ a) (out₀ ++ emit₁ a) := by
      simp [Sequential.start, hmidTapes]
    exact ((h₂ a OracleState oracle s s₁ ha) OracleState oracle s₁
      (Sequential.start second mid) hstart hmidBuf).2 (final₀, s₂) hfinal₀ op

/-- Sequence a deterministic `pure ()` preparation phase before a `RunsWords` continuation. -/
theorem seq_pure_left {first : MultiTapePTM k Bool State₀ Operation}
    {second : MultiTapePTM k Bool State₁ Operation}
    {t₁ t₂ : ℕ} {ws₁ : Fin k → List Bool} {emit₁ : List Bool}
    {prog₂ : ProbOracleComp (fun _ : Operation × List Bool => List Bool) β}
    {ws₂ : β → Fin k → List Bool} {emit₂ : β → List Bool}
    (h₁ : first.RunsWords x ws₀ out₀ t₁ (pure ()) (fun _ => ws₁) (fun _ => emit₁))
    (h₂ : second.RunsWords x ws₁ (out₀ ++ emit₁) t₂ prog₂ ws₂ emit₂) :
    (first.seq second).RunsWords x ws₀ out₀ (t₁ + t₂) prog₂
      ws₂ (fun b => emit₁ ++ emit₂ b) := by
  have hseq := (h₁.seq_bind (Function.injective_of_subsingleton _)
    (fun _ _ _ _ _ _ => h₂)).of_map Prod.snd ws₂ (fun b => emit₁ ++ emit₂ b)
  have hid : (fun a : β => a) = id := rfl
  simpa only [pure_bind, Functor.map_map, hid, id_map] using hseq

/-- Sequence a deterministic `pure ()` cleanup phase after a `RunsWords` phase. -/
theorem seq_pure_right {first : MultiTapePTM k Bool State₀ Operation}
    {second : MultiTapePTM k Bool State₁ Operation}
    {t₁ t₂ : ℕ}
    {prog₁ : ProbOracleComp (fun _ : Operation × List Bool => List Bool) α}
    {ws₁ : α → Fin k → List Bool} {emit₁ : α → List Bool}
    {ws₂ : α → Fin k → List Bool} {emit₂ : α → List Bool}
    (hinj : Function.Injective (fun a => (ws₁ a, emit₁ a)))
    (h₁ : first.RunsWords x ws₀ out₀ t₁ prog₁ ws₁ emit₁)
    (h₂ : ∀ a (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool)) (s s' : OracleState),
      (a, s') ∈ ((OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        prog₁).run s).support →
      second.RunsWords x (ws₁ a) (out₀ ++ emit₁ a) t₂ (pure ())
        (fun _ => ws₂ a) (fun _ => emit₂ a)) :
    (first.seq second).RunsWords x ws₀ out₀ (t₁ + t₂) prog₁
      ws₂ (fun a => emit₁ a ++ emit₂ a) := by
  have hseq := (h₁.seq_bind hinj h₂).of_map Prod.fst ws₂ (fun a => emit₁ a ++ emit₂ a)
  have hid : (fun a : α => a) = id := rfl
  simpa only [map_pure, bind_pure_comp, Functor.map_map, hid, id_map] using hseq

end RunsWords

namespace ComputesTidily

variable {machine : MultiTapePTM k Bool State Operation} {x : List Bool} {time time' : ℕ}
  {program program' : ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}

/-- Increasing the step budget preserves `ComputesTidily`. -/
theorem mono (h : machine.ComputesTidily x time program) (hle : time ≤ time') :
    machine.ComputesTidily x time' program :=
  fun out₀ => (h out₀).mono hle

/-- Replace `program` by a stateful-distributionally equivalent program. -/
theorem congr (h : machine.ComputesTidily x time program)
    (heq : ∀ (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool)) (s : OracleState),
      (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        program).run s =
      (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        program').run s) :
    machine.ComputesTidily x time program' :=
  fun out₀ => (h out₀).congr heq

/-- A tidy machine realizes `program` under `runOracle` from `initialConfig`. -/
theorem runOracle (h : machine.ComputesTidily x time program)
    (oracle : Operation × List Bool → StateT OracleState PMF (List Bool)) (s : OracleState) :
    (OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (machine.runOracle time x)).run s =
    (OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      program).run s := by
  have hlaw := ((h []) OracleState oracle s (machine.initialConfig x)
    (Cfg.init_eq_wordsCfg machine.initial x) (fun _ => rfl)).1
  have hout := congrArg (PMF.map (fun p => (p.1.output, p.2))) hlaw
  rw [runOracle_eq_map, OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map]
  refine Eq.trans ?_ (hout.trans ?_)
  · rw [PMF.map_comp]
    congr 1
  · rw [PMF.map_comp]
    have hcomp :
        ((fun p : Cfg k Bool State x × OracleState => (p.1.output, p.2)) ∘
          fun (a, s') => (wordsCfg x none (fun _ => []) ([] ++ id a), s')) = id := by
      funext ⟨a, s'⟩
      simp
    rw [hcomp, PMF.map_id]

/-- A deterministic tidy machine lifts directly to `ComputesTidily` via `ofDeterministic`. -/
theorem of_deterministic {tm : MultiTapeTM k Bool State} {output : List Bool} {t s : ℕ}
    (htm : tm.ComputesTidilyInTimeAndSpace x output t s) :
    (ofDeterministic tm : MultiTapePTM k Bool State Operation).ComputesTidily
      x t (pure output) := by
  intro out₀
  have h := RunsWords.of_transformsTapes (Operation := Operation) (out₀ := out₀) htm
    ⟨rfl, rfl⟩ (fun _ _ hQ => hQ)
  simpa only [map_pure] using h.of_map (fun _ => output) (fun _ _ => []) id

end ComputesTidily

/-! ### Fair-bit machine -/

/-- One-state machine that emits a single fair bit and halts without moving any head. -/
def coinMachine : MultiTapePTM 0 Bool Unit Operation where
  initial := ()
  tr _ _ _ _ bit := .step
    { inputTape := 0, workTapes := Fin.elim0, output := some bit, state := none }
    (fun _ => none) (fun _ => 0)

/-- `coinMachine` tidily computes `encBool <$> sample (uniform Bool)` in `1` step. -/
theorem computesTidily_coinMachine (x : List Bool) :
    (coinMachine (Operation := Operation)).ComputesTidily x 1
      (encBool <$> ProbOracleComp.sample (ProbComp.uniform Bool)) := by
  intro out₀ OracleState oracle s cfg htapes hbuf
  have hs : cfg.tapes.state = some () := by rw [htapes]; rfl
  dsimp only [runOracleConfigFrom, runConfigFrom]
  simp only [MultiTapeMachine.runConfigFrom, hs, coinMachine, bind_map_left,
    OracleComp.interpret_bind, OracleComp.interpret_pure, OracleComp.interpret_map,
    StateT.run_bind, StateT.run_pure, StateT.run_map, run_interpret_sample_uniform_bool,
    Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
    PMF.monad_map_eq_map, PMF.bind_map, PMF.map_bind, PMF.pure_map, PMF.map_comp,
    Function.comp_def]
  constructor
  · change (PMF.uniformOfFintype Bool).map _ = (PMF.uniformOfFintype Bool).map _
    refine congrArg (fun f => (PMF.uniformOfFintype Bool).map f) (funext fun bit => ?_)
    refine Prod.ext ?_ rfl
    rw [Config.step, htapes]
    exact Cfg.ext_zero_tapes rfl rfl (by simp [Turing.Action.apply, wordsCfg])
  · rintro ⟨finalCfg, finalState⟩ hfinal op
    obtain ⟨bit, _, heq⟩ := (PMF.mem_support_bind_iff _ _ _).mp hfinal
    rw [PMF.mem_support_pure_iff] at heq
    rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
    simp [Config.step, hbuf op]

/-! ### Bounded-prefix query machine -/

/-- Control states of `queryTakeCore`: read frame marker, read framed query bit, submit query,
and copy reply bits while scanning the unary limit. -/
inductive QueryTakeState where
  | marker
  | bit
  | submit
  | copyReply
  deriving DecidableEq

instance : Finite QueryTakeState :=
  Finite.of_injective
    (fun
      | .marker => (0 : Fin 4)
      | .bit => 1
      | .submit => 2
      | .copyReply => 3)
    (fun a b h => by cases a <;> cases b <;> simp_all)

/-- Unframe the query word from the input into channel `op`, submit the query, and copy at most
`limit` reply bits while scanning the unary suffix. -/
def queryTakeCore (op : Operation) : MultiTapePTM 0 Bool QueryTakeState Operation where
  initial := .marker
  tr state symbol _ answer _ := match state with
    | .marker => match symbol with
      | some true => .step
        { inputTape := 1, workTapes := Fin.elim0, output := none, state := some .bit }
        (fun _ => none) (fun _ => 0)
      | some false => .step
        { inputTape := 1, workTapes := Fin.elim0, output := none, state := some .submit }
        (fun _ => none) (fun _ => 0)
      | none => .step
        { inputTape := 0, workTapes := Fin.elim0, output := none, state := none }
        (fun _ => none) (fun _ => 0)
    | .bit => match symbol with
      | some b => .step
        { inputTape := 1, workTapes := Fin.elim0, output := none, state := some .marker }
        (Function.update (fun _ => none) op (some b)) (fun _ => 0)
      | none => .step
        { inputTape := 0, workTapes := Fin.elim0, output := none, state := none }
        (fun _ => none) (fun _ => 0)
    | .submit => .query op .copyReply
    | .copyReply => match symbol with
      | some _ => .step
        { inputTape := 1, workTapes := Fin.elim0, output := answer op, state := some .copyReply }
        (fun _ => none) (Function.update (fun _ => 0) op 1)
      | none => .step
        { inputTape := 0, workTapes := Fin.elim0, output := none, state := none }
        (fun _ => none) (fun _ => 0)

/-- Run `queryTakeCore op` and then rewind the input head to position `1`. -/
noncomputable def queryTakePTM (op : Operation) :
    MultiTapePTM 0 Bool (QueryTakeState ⊕ RewindState) Operation :=
  (queryTakeCore op).seq (ofDeterministic (rewindInput Bool))

namespace QueryTakeCore

variable (op : Operation)

/-- Configuration of `queryTakeCore` at 0-based input index `idx ≤ x.length`. -/
def config (x : List Bool) (state : Option QueryTakeState) (idx : ℕ) (hidx : idx ≤ x.length)
    (out : List Bool) (ch : Operation → Channel Bool) :
    Config 0 Bool QueryTakeState Operation x where
  tapes :=
    { state := state
      inputPos := ⟨idx + 1, by lia⟩
      workTapes := Fin.elim0
      workTapePos := Fin.elim0
      output := out }
  channels := ch

omit [DecidableEq Operation] in
private theorem head_toList_append_tail_take (l : List Bool) (r : ℕ) :
    l.head?.toList ++ l.tail.take r = l.take (r + 1) := by
  cases l <;> simp

omit [DecidableEq Operation] in
private theorem getElem?_toList_append_drop_take (answer : List Bool) (pos r : ℕ) :
    (answer[pos]?).toList ++ (answer.drop (pos + 1)).take r =
      (answer.drop pos).take (r + 1) := by
  have hhead : answer[pos]? = (answer.drop pos).head? := by simp
  have htail : answer.drop (pos + 1) = (answer.drop pos).tail := by simp
  rw [hhead, htail, head_toList_append_tail_take]

/-- Scanning `List.replicate remLimit true` in state `.copyReply` appends `(answer.drop pos).take
remLimit` to `out` and halts at the right boundary in `remLimit + 1` steps. -/
theorem run_copyReply (x : List Bool)
    (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
    (remLimit : ℕ) :
    ∀ (pre : List Bool) (h : x = pre ++ List.replicate remLimit true)
      (pos : ℕ) (answer out : List Bool) (ch : Operation → Channel Bool)
      (_hch : ch op = ⟨[], answer, (pos : ℤ)⟩) (s : OracleState),
      (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        ((queryTakeCore op).runOracleConfigFrom (remLimit + 1)
          (config x (some .copyReply) pre.length (by subst h; simp) out ch))).run s =
        PMF.pure
          (config x none x.length le_rfl (out ++ (answer.drop pos).take remLimit)
            (Function.update ch op ⟨[], answer, (pos + remLimit : ℤ)⟩), s) := by
  induction remLimit with
  | zero =>
    intro pre h pos answer out ch hch s
    have hlen : pre.length = x.length := by subst h; simp
    have hsym := inputSymbol_eq_none_of_boundary
      (cfg := (config x (some .copyReply) pre.length (by lia) out ch).tapes)
      (Or.inr (by simp [config, hlen]))
    rw [run_interpret_runOracleConfigFrom_succ_step (queryTakeCore op) oracle 0
      (config x (some .copyReply) pre.length (by lia) out ch) s rfl
      (fun _ => by rw [hsym]; rfl)]
    dsimp only [runOracleConfigFrom, runConfigFrom, MultiTapeMachine.runConfigFrom]
    simp only [OracleComp.interpret_pure, StateT.run_pure, Probability.PMF.monad_pure_eq_pure]
    congr 1
    refine Prod.ext (Config.ext ?_ ?_) rfl
    · exact Cfg.ext_zero_tapes rfl
        (by simp [Config.step, config, Turing.Action.apply, hlen])
        (by simp [Config.step, config, Turing.Action.apply])
    · funext other
      by_cases heq : other = op
      · subst other
        simp [Config.step, config, hch]
      · simp [Config.step, config, heq]
  | succ remLimit ih =>
    intro pre h pos answer out ch hch s
    have hlt : pre.length < x.length := by subst h; simp
    have hget : x[pre.length]'hlt = true := by
      cases h
      simp
    have hsym : (config x (some .copyReply) pre.length hlt.le out ch).tapes.inputSymbol =
        some true := by
      rw [inputSymbolInner pre.length (by simp [config]; lia) hlt]
      exact congrArg some hget
    have hans : (config x (some .copyReply) pre.length hlt.le out ch).answerSymbols op =
        answer[pos]? := by
      simp [Config.answerSymbols, config, hch, Channel.answerSymbol]
    let ch' := Function.update ch op ⟨[], answer, ((pos + 1 : ℕ) : ℤ)⟩
    have hstep :
        (config x (some .copyReply) pre.length hlt.le out ch).step
          { inputTape := 1, workTapes := Fin.elim0, output := answer[pos]?,
            state := some .copyReply }
          (fun _ => none) (Function.update (fun _ => 0) op 1) =
        config x (some .copyReply) (pre ++ [true]).length
          (by subst h; simp) (out ++ (answer[pos]?).toList) ch' := by
      refine Config.ext ?_ ?_
      · refine Cfg.ext_zero_tapes rfl ?_ (by simp [Config.step, config, Turing.Action.apply])
        apply Fin.ext
        change (moveInputPos _ .pos).val = (pre ++ [true]).length + 1
        rw [moveInputPos_pos_of_ne_right _ (by simp only [config]; lia)]
        simp [config]
      · funext other
        by_cases heq : other = op
        · subst other
          simp [Config.step, config, ch', hch, Nat.cast_add]
        · simp [Config.step, config, ch', heq]
    have hsplit : pre ++ List.replicate (remLimit + 1) true =
        (pre ++ [true]) ++ List.replicate remLimit true := by
      rw [List.replicate_succ, ← List.singleton_append, List.append_assoc]
    rw [run_interpret_runOracleConfigFrom_succ_step (queryTakeCore op) oracle (remLimit + 1)
      (config x (some .copyReply) pre.length hlt.le out ch) s rfl
      (fun _ => by rw [hsym]; rfl),
      hans, hstep,
      ih (pre ++ [true]) (h.trans hsplit) (pos + 1) answer
        (out ++ (answer[pos]?).toList) ch' (by simp [ch']) s]
    congr 1
    refine Prod.ext (Config.ext ?_ ?_) rfl
    · refine Cfg.ext_zero_tapes rfl rfl ?_
      simp [config, List.append_assoc, getElem?_toList_append_drop_take]
    · funext other
      by_cases heq : other = op
      · subst other
        simp only [config, List.append_assoc, Nat.cast_add, Nat.cast_one, Function.update_idem,
          Function.update_self, Channel.mk.injEq, true_and, ch']
        lia
      · simp [config, ch', heq]

/-- Scanning `frame rem` in state `.marker` appends `rem` to channel `op`'s query buffer and
submits the accumulated query in `2 * rem.length + 2` steps, entering `.copyReply`. -/
theorem run_frame (x : List Bool)
    (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
    (rem : List Bool) :
    ∀ (pre suf : List Bool) (h : x = pre ++ frame rem ++ suf)
      (out : List Bool) (ch : Operation → Channel Bool) (s : OracleState),
      (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        ((queryTakeCore op).runOracleConfigFrom (2 * rem.length + 2)
          (config x (some .marker) pre.length (by subst h; simp) out ch))).run s =
        (oracle (op, (ch op).queryBuffer ++ rem) s).map
          (fun (answer, s') =>
            (config x (some .copyReply) (pre.length + (frame rem).length)
              (by subst h; simp) out (Function.update ch op ⟨[], answer, 0⟩), s')) := by
  induction rem with
  | nil =>
    intro pre suf h out ch s
    have hlt : pre.length < x.length := by subst h; simp
    have hget : x[pre.length]'hlt = false := by
      cases h
      simp
    have hsym : (config x (some .marker) pre.length hlt.le out ch).tapes.inputSymbol =
        some false := by
      rw [inputSymbolInner pre.length (by simp [config]; lia) hlt]
      exact congrArg some hget
    have hstep₁ :
        (config x (some .marker) pre.length hlt.le out ch).step
          { inputTape := 1, workTapes := Fin.elim0, output := none, state := some .submit }
          (fun _ => none) (fun _ => 0) =
        config x (some .submit) (pre.length + 1) (by subst h; simp) out ch := by
      refine Config.ext ?_ (funext fun _ => by simp [Config.step, config])
      refine Cfg.ext_zero_tapes rfl ?_ (by simp [Config.step, config, Turing.Action.apply])
      apply Fin.ext
      change (moveInputPos _ .pos).val = pre.length + 1 + 1
      rw [moveInputPos_pos_of_ne_right _ (by simp only [config]; lia)]
      rfl
    change (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        ((queryTakeCore op).runOracleConfigFrom (0 + 1 + 1)
          (config x (some .marker) pre.length hlt.le out ch))).run s = _
    rw [run_interpret_runOracleConfigFrom_succ_step (queryTakeCore op) oracle (0 + 1)
      (config x (some .marker) pre.length hlt.le out ch) s rfl
      (fun _ => by rw [hsym]; rfl),
      hstep₁,
      run_interpret_runOracleConfigFrom_succ_query (queryTakeCore op) oracle 0
        (config x (some .submit) (pre.length + 1) (by subst h; simp) out ch) s rfl
        (fun _ => rfl)]
    dsimp only [runOracleConfigFrom, runConfigFrom, MultiTapeMachine.runConfigFrom]
    simp only [OracleComp.interpret_pure, StateT.run_pure, Probability.PMF.monad_pure_eq_pure,
      List.append_nil]
    rfl
  | cons b rem ih =>
    intro pre suf h out ch s
    have hlt₁ : pre.length < x.length := by subst h; simp
    have hget₁ : x[pre.length]'hlt₁ = true := by
      cases h
      simp
    have hsym₁ : (config x (some .marker) pre.length hlt₁.le out ch).tapes.inputSymbol =
        some true := by
      rw [inputSymbolInner pre.length (by simp [config]; lia) hlt₁]
      exact congrArg some hget₁
    have hlt₂ : pre.length + 1 < x.length := by subst h; simp
    have hget₂ : x[pre.length + 1]'hlt₂ = b := by
      cases h
      simp [List.getElem_append_right]
    have hsym₂ : (config x (some .bit) (pre.length + 1) hlt₂.le out ch).tapes.inputSymbol =
        some b := by
      rw [inputSymbolInner (pre.length + 1) (by simp [config]; lia) hlt₂]
      exact congrArg some hget₂
    let ch' := Function.update ch op
      { ch op with queryBuffer := (ch op).queryBuffer ++ [b] }
    have hstep₁ :
        (config x (some .marker) pre.length hlt₁.le out ch).step
          { inputTape := 1, workTapes := Fin.elim0, output := none, state := some .bit }
          (fun _ => none) (fun _ => 0) =
        config x (some .bit) (pre.length + 1) hlt₂.le out ch := by
      refine Config.ext ?_ (funext fun _ => by simp [Config.step, config])
      refine Cfg.ext_zero_tapes rfl ?_ (by simp [Config.step, config, Turing.Action.apply])
      apply Fin.ext
      change (moveInputPos _ .pos).val = pre.length + 1 + 1
      rw [moveInputPos_pos_of_ne_right _ (by simp only [config]; lia)]
      rfl
    have hstep₂ :
        (config x (some .bit) (pre.length + 1) hlt₂.le out ch).step
          { inputTape := 1, workTapes := Fin.elim0, output := none, state := some .marker }
          (Function.update (fun _ => none) op (some b)) (fun _ => 0) =
        config x (some .marker) (pre ++ [true, b]).length
          (by subst h; simp) out ch' := by
      refine Config.ext ?_ ?_
      · refine Cfg.ext_zero_tapes rfl ?_ (by simp [Config.step, config, Turing.Action.apply])
        apply Fin.ext
        change (moveInputPos _ .pos).val = (pre ++ [true, b]).length + 1
        rw [moveInputPos_pos_of_ne_right _ (by simp only [config]; lia)]
        simp [config]
      · funext other
        by_cases heq : other = op
        · subst other
          simp [Config.step, config, ch']
        · simp [Config.step, config, ch', heq]
    have h2 : 2 * (b :: rem).length + 2 = (2 * rem.length + 2) + 1 + 1 := by simp; lia
    have hsplit : pre ++ frame (b :: rem) ++ suf = (pre ++ [true, b]) ++ frame rem ++ suf := by
      simp [frame_cons, List.append_assoc]
    rw [h2,
      run_interpret_runOracleConfigFrom_succ_step (queryTakeCore op) oracle
        ((2 * rem.length + 2) + 1)
        (config x (some .marker) pre.length hlt₁.le out ch) s rfl
        (fun _ => by rw [hsym₁]; rfl),
      hstep₁,
      run_interpret_runOracleConfigFrom_succ_step (queryTakeCore op) oracle
        (2 * rem.length + 2)
        (config x (some .bit) (pre.length + 1) hlt₂.le out ch) s rfl
        (fun _ => by rw [hsym₂]; rfl),
      hstep₂,
      ih (pre ++ [true, b]) suf (h.trans hsplit) out ch' s]
    congr 1
    · funext p
      refine Prod.ext (Config.ext ?_ ?_) rfl
      · refine Cfg.ext_zero_tapes rfl ?_ rfl
        apply Fin.ext
        simp only [config, List.length_append, List.length_cons, List.length_nil, zero_add,
          Nat.reduceAdd, length_frame, frame_cons, Nat.add_right_cancel_iff]
        lia
      · funext other
        by_cases heq : other = op
        · subst other
          simp [config, ch']
        · simp [config, ch', heq]
    · simp [ch', List.append_assoc]

end QueryTakeCore

/-- `queryTakePTM op` tidily computes `List.take limit <$> query (op, q)` on
`encPair encBits encUnary (q, limit)` in `4 * q.length + 2 * limit + 6` steps. -/
theorem computesTidily_queryTakePTM (op : Operation) (q : List Bool) (limit : ℕ) :
    (queryTakePTM op).ComputesTidily (encPair encBits encUnary (q, limit))
      (4 * q.length + 2 * limit + 6)
      (List.take limit <$> ProbOracleComp.query (op, q)) := by
  let x := encPair encBits encUnary (q, limit)
  have hx : x = frame q ++ List.replicate limit true := by
    simp [x, encPair_apply, encBits_apply, encUnary_apply]
  have hxlen : x.length = 2 * q.length + 1 + limit := by simp [hx]
  let t₁ := 2 * q.length + 2
  let t₂ := limit + 1
  let tCore := t₁ + t₂
  let tRew := 2 * q.length + limit + 3
  intro out₀ OracleState oracle s cfg htapes hbuf
  let cfg₀ : Config 0 Bool QueryTakeState Operation x :=
    QueryTakeCore.config x (some .marker) 0 (Nat.zero_le _) out₀ cfg.channels
  have hcfg : cfg = Sequential.left (ofDeterministic (rewindInput Bool)) cfg₀ := by
    refine Config.ext ?_ rfl
    rw [htapes]
    exact Cfg.ext_zero_tapes rfl rfl rfl
  -- Combine `run_frame` and `run_copyReply` for `queryTakeCore op`
  have hcore :
      (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        ((queryTakeCore op).runOracleConfigFrom tCore cfg₀)).run s =
      (oracle (op, q) s).map
        (fun (answer, s') =>
          (QueryTakeCore.config x none x.length le_rfl (out₀ ++ answer.take limit)
            (Function.update cfg.channels op ⟨[], answer, (limit : ℤ)⟩), s')) := by
    dsimp only [tCore, runOracleConfigFrom, runConfigFrom]
    rw [MultiTapeMachine.runConfigFrom_add, OracleComp.interpret_bind, StateT.run_bind,
      Probability.PMF.monad_bind_eq_bind]
    have hframe := QueryTakeCore.run_frame op x oracle q [] (List.replicate limit true)
      (by simp [hx]) out₀ cfg.channels s
    dsimp only [runOracleConfigFrom, runConfigFrom] at hframe
    simp only [List.length_nil, Nat.zero_add, hbuf op, List.nil_append] at hframe
    rw [hframe, PMF.bind_map]
    refine (PMF.bind_congr_on_support _ _ _ ?_).trans rfl
    rintro ⟨answer, s₁⟩ _
    dsimp only [Function.comp_def, t₂]
    have hcopy := QueryTakeCore.run_copyReply op x oracle limit (frame q) hx 0 answer out₀
      (Function.update cfg.channels op ⟨[], answer, 0⟩) (by simp) s₁
    dsimp only [runOracleConfigFrom, runConfigFrom] at hcopy
    simpa only [List.drop_zero, Nat.cast_zero, zero_add, Function.update_idem] using hcopy
  have hhalt₁ : ∀ result ∈ ((OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      ((queryTakeCore op).runOracleConfigFrom tCore cfg₀)).run s).support,
      result.1.tapes.state = none := by
    intro result hresult
    rw [hcore] at hresult
    obtain ⟨⟨answer, s₁⟩, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hresult
    rfl
  have hrew (answer : List Bool) :
      (rewindInput Bool).runFrom
        (Sequential.start (ofDeterministic (rewindInput Bool) :
          MultiTapePTM 0 Bool RewindState Operation)
          (QueryTakeCore.config x none x.length le_rfl (out₀ ++ answer.take limit)
            (Function.update cfg.channels op ⟨[], answer, (limit : ℤ)⟩))).tapes tRew =
        wordsCfg x none (fun _ => []) (out₀ ++ answer.take limit) := by
    have htime : tRew = (⟨x.length + 1, by lia⟩ : Fin (x.length + 2)).val - 1 + 2 := by
      dsimp only [tRew]
      lia
    rw [htime]
    exact (runFrom_rewindInput ⟨x.length + 1, by lia⟩ Fin.elim0 Fin.elim0
      (out₀ ++ answer.take limit)).trans (Cfg.ext_zero_tapes rfl rfl rfl)
  have hhalt₂ : ∀ result ∈ ((OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      ((queryTakeCore op).runOracleConfigFrom tCore cfg₀)).run s).support,
      ∀ final ∈ ((OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        ((ofDeterministic (rewindInput Bool)).runOracleConfigFrom tRew
          (Sequential.start (ofDeterministic (rewindInput Bool)) result.1))).run result.2).support,
        final.1.tapes.state = none := by
    rintro result hresult ⟨finalCfg, finalState⟩ hfinal
    rw [hcore] at hresult
    obtain ⟨⟨answer, s₁⟩, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hresult
    rw [run_interpret_runOracleConfigFrom_ofDeterministic, hrew answer,
      PMF.mem_support_pure_iff] at hfinal
    rcases Prod.mk.inj hfinal with ⟨rfl, rfl⟩
    rfl
  have htotal : 4 * q.length + 2 * limit + 6 = tCore + tRew := by
    dsimp only [tCore, t₁, t₂, tRew]
    lia
  dsimp only [queryTakePTM]
  rw [htotal, hcfg,
    run_interpret_runOracleConfigFrom_seq (queryTakeCore op) (ofDeterministic (rewindInput Bool))
      oracle cfg₀ tCore tRew s hhalt₁ hhalt₂,
    hcore]
  constructor
  · simp only [PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def,
      run_interpret_runOracleConfigFrom_ofDeterministic, hrew, PMF.pure_map,
      OracleComp.interpret_map, ProbOracleComp.interpret_query, StateT.run_map,
      PMF.monad_map_eq_map, Sequential.right, Cfg.mapState, wordsCfg_state, Option.map_none,
      id_eq]
    rfl
  · rintro ⟨finalCfg, finalState⟩ hfinal other
    rw [PMF.bind_map] at hfinal
    obtain ⟨⟨answer, s₁⟩, _, hfinal⟩ := (PMF.mem_support_bind_iff _ _ _).mp hfinal
    dsimp only [Function.comp_def] at hfinal
    rw [run_interpret_runOracleConfigFrom_ofDeterministic, hrew answer, PMF.pure_map,
      PMF.mem_support_pure_iff] at hfinal
    rcases Prod.mk.inj hfinal with ⟨rfl, rfl⟩
    by_cases heq : other = op
    · subst other
      simp [Sequential.right, Sequential.start, QueryTakeCore.config]
    · simp [Sequential.right, Sequential.start, QueryTakeCore.config, heq, hbuf other]

end Turing.MultiTapePTM
