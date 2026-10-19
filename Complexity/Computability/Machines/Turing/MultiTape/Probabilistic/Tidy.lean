/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Mathlib.Basic.Finite.Sum
public import Mathlib.Data.Fintype.Option
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Comp
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Ite
public import Complexity.Computability.Machines.Turing.MultiTape.Machine.OutputPrefix
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.OnWords
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.ExtendTapes
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.InputFromTape
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.OutputToTape
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.QueryTake

/-!
# Tidy combinators for probabilistic oracle machines

This module lifts the deterministic tidy-machine combinators (`extendTapes`, `outputToWord`,
`inputFromWord`, `onWords`, `comp`, `append`, and `branch`/`ite`) to `MultiTapePTM` specifications
in `RunsWords` and `ComputesTidily`. Every combinator preserves the exact joint distribution of
tape words, emitted output and external oracle state, and maintains clean query buffers at phase
boundaries.

## Main definitions

* `Turing.MultiTapePTM.outputToWord`: redirect output to a new last work tape and rewind its head.
* `Turing.MultiTapePTM.inputFromWord`: read input from a work tape flagged by `markFlag`.
* `Turing.MultiTapePTM.onWords`: run a tidy probabilistic machine between two work tapes.
* `Turing.MultiTapePTM.tidyComp`: sequential composition of tidy probabilistic machines.
* `Turing.MultiTapePTM.appendPTM`: concatenate the outputs of two tidy probabilistic machines.
* `Turing.MultiTapePTM.branch`: branch on whether a work tape is blank without executing the
  unselected branch.
* `Turing.MultiTapePTM.itePTM`: tidy case distinction on a work tape word.

## Main results

* `Turing.MultiTapePTM.RunsWords.of_nil_output`: an initial output prefix is retained automatically.
* `Turing.MultiTapePTM.ComputesTidily.length_output_le`: any supported output of a tidy run has
  length at most the step budget.
* `Turing.MultiTapePTM.RunsWords.extendTapes`, `Turing.MultiTapePTM.ComputesTidily.extendTapes`:
  tape-reindexing laws.
* `Turing.MultiTapePTM.ComputesTidily.outputToWord`,
  `Turing.MultiTapePTM.RunsWords.inputFromWord`, `Turing.MultiTapePTM.ComputesTidily.onWords`:
  word-redirection laws.
* `Turing.MultiTapePTM.ComputesTidily.comp`: tidy sequential composition.
* `Turing.MultiTapePTM.ComputesTidily.append`: tidy output concatenation.
* `Turing.MultiTapePTM.ComputesTidily.ite`: tidy conditional execution.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib Cslib.Probability MultiTapeMachine MultiTapeMachine.Sequential MultiTapeTM

variable {k k' k₀ k₁ k₂ : ℕ} {State State₀ State₁ State₂ Operation OracleState : Type}
  {x : List Bool} [DecidableEq Operation]

/-! ### Output-prefix invariance and output-length bounds -/

namespace RunsWords

variable {machine : MultiTapePTM k Bool State Operation}
  {ws₀ : Fin k → List Bool} {out₀ : List Bool} {time : ℕ}
  {α : Type} {program : ProbOracleComp (fun _ : Operation × List Bool => List Bool) α}
  {ws₁ : α → Fin k → List Bool} {emit : α → List Bool}

/-- `RunsWords` for arbitrary `out₀` follows from the `out₀ = []` case by output-prefix
invariance (`runConfigFrom_prependOutput`). -/
theorem of_nil_output (h : machine.RunsWords x ws₀ [] time program ws₁ emit) :
    machine.RunsWords x ws₀ out₀ time program ws₁ emit := by
  intro OracleState oracle s cfg htapes hbuf
  let cfg₀ : Config k Bool State Operation x :=
    { tapes := wordsCfg x (some machine.initial) ws₀ [], channels := cfg.channels }
  have hprep : cfg = cfg₀.prependOutput out₀ := by
    refine Config.ext ?_ rfl
    rw [htapes]
    exact Cfg.ext rfl rfl rfl rfl (by simp [cfg₀, Config.prependOutput, Cfg.prependOutput])
  have hrun :
      machine.runOracleConfigFrom time cfg =
        (fun final => final.prependOutput out₀) <$> machine.runOracleConfigFrom time cfg₀ := by
    rw [hprep]
    exact MultiTapeMachine.runConfigFrom_prependOutput machine _ _ time cfg₀ out₀
  obtain ⟨hlaw, hclean⟩ := h OracleState oracle s cfg₀ rfl hbuf
  dsimp only
  rw [hrun, OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map]
  constructor
  · have hmap :
        PMF.map (fun (final, s') => (final.tapes, s'))
          (PMF.map (fun (a, s') => (a.prependOutput out₀, s'))
            ((OracleComp.interpret
              (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
              (machine.runOracleConfigFrom time cfg₀)).run s)) =
        PMF.map (fun (tapes, s') => (tapes.prependOutput out₀, s'))
          (PMF.map (fun (final, s') => (final.tapes, s'))
            ((OracleComp.interpret
              (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
              (machine.runOracleConfigFrom time cfg₀)).run s)) := by
      simp only [PMF.map_comp, Function.comp_def, Config.prependOutput]
    rw [hmap, hlaw, PMF.map_comp]
    congr 1
  · intro final hfinal op
    obtain ⟨⟨final₀, s'⟩, hfinal₀, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
    exact hclean (final₀, s') hfinal₀ op

end RunsWords

/-- `ComputesTidily` is equivalent to `RunsWords` with `out₀ = []`. -/
theorem computesTidily_iff_nil_output {machine : MultiTapePTM k Bool State Operation}
    {time : ℕ}
    {program : ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)} :
    machine.ComputesTidily x time program ↔
      machine.RunsWords x (fun _ => []) [] time program (fun _ _ => []) id :=
  ⟨fun h => h [], fun h _ => h.of_nil_output⟩

/-- One step of `runOracleConfigFrom` appends at most one symbol to the output tape. -/
private theorem length_output_le_of_mem_support_one
    (machine : MultiTapePTM k Bool State Operation)
    (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
    (cfg : Config k Bool State Operation x) (s : OracleState)
    {mid : Config k Bool State Operation x} {s₁ : OracleState}
    (hmid : (mid, s₁) ∈ ((OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (machine.runOracleConfigFrom 1 cfg)).run s).support) :
    mid.tapes.output.length ≤ cfg.tapes.output.length + 1 := by
  dsimp only [runOracleConfigFrom, runConfigFrom, MultiTapeMachine.runConfigFrom] at hmid
  cases hstate : cfg.tapes.state with
  | none =>
    simp only [hstate, OracleComp.interpret_pure, StateT.run_pure,
      Probability.PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hmid
    rcases Prod.mk.inj hmid with ⟨rfl, rfl⟩
    omega
  | some q =>
    simp only [hstate, bind_map_left, OracleComp.interpret_bind, StateT.run_bind,
      run_interpret_sample_uniform_bool, Probability.PMF.monad_bind_eq_bind,
      PMF.bind_map, Function.comp_def] at hmid
    obtain ⟨bit, _, hstep⟩ := (PMF.mem_support_bind_iff _ _ _).mp hmid
    cases htr : machine.tr q cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
        cfg.answerSymbols bit with
    | step action symbol move =>
      simp only [htr, OracleComp.interpret_pure, StateT.run_pure,
        Probability.PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hstep
      rcases Prod.mk.inj hstep with ⟨rfl, rfl⟩
      simp only [Config.step, Turing.Action.apply, List.length_append]
      cases action.output <;> simp
    | query op next =>
      simp only [htr, OracleComp.interpret_bind, StateT.run_bind, ProbOracleComp.interpret_query,
        OracleComp.interpret_pure, StateT.run_pure, Probability.PMF.monad_bind_eq_bind,
        Probability.PMF.monad_pure_eq_pure] at hstep
      obtain ⟨⟨answer, s₂⟩, _, hpure⟩ := (PMF.mem_support_bind_iff _ _ _).mp hstep
      rw [PMF.mem_support_pure_iff] at hpure
      rcases Prod.mk.inj hpure with ⟨rfl, rfl⟩
      simp [Config.receive]

/-- Over `fuel` steps of `runOracleConfigFrom`, the output tape grows by at most `fuel` symbols. -/
theorem length_output_le_of_mem_support_runOracleConfigFrom
    (machine : MultiTapePTM k Bool State Operation)
    (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
    (fuel : ℕ) (cfg : Config k Bool State Operation x) (s : OracleState)
    {final : Config k Bool State Operation x} {s' : OracleState}
    (hfinal : (final, s') ∈ ((OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (machine.runOracleConfigFrom fuel cfg)).run s).support) :
    final.tapes.output.length ≤ cfg.tapes.output.length + fuel := by
  induction fuel generalizing cfg s with
  | zero =>
    dsimp only [runOracleConfigFrom, runConfigFrom, MultiTapeMachine.runConfigFrom] at hfinal
    simp only [OracleComp.interpret_pure, StateT.run_pure,
      Probability.PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hfinal
    rcases Prod.mk.inj hfinal with ⟨rfl, rfl⟩
    omega
  | succ fuel ih =>
    have hsplit : fuel + 1 = 1 + fuel := by omega
    rw [hsplit] at hfinal
    dsimp only [runOracleConfigFrom, runConfigFrom] at hfinal
    rw [MultiTapeMachine.runConfigFrom_add, OracleComp.interpret_bind, StateT.run_bind,
      Probability.PMF.monad_bind_eq_bind] at hfinal
    obtain ⟨⟨mid, s₁⟩, hmid, hrem⟩ := (PMF.mem_support_bind_iff _ _ _).mp hfinal
    have h₁ := length_output_le_of_mem_support_one machine oracle cfg s hmid
    have h₂ := ih mid s₁ hrem
    omega

/-- Any word emitted by a `RunsWords` phase has length at most `time`. -/
theorem RunsWords.length_emit_le {machine : MultiTapePTM k Bool State Operation}
    {ws₀ : Fin k → List Bool} {out₀ : List Bool} {time : ℕ}
    {α : Type} {program : ProbOracleComp (fun _ : Operation × List Bool => List Bool) α}
    {ws₁ : α → Fin k → List Bool} {emit : α → List Bool}
    (h : machine.RunsWords x ws₀ out₀ time program ws₁ emit)
    (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
    (s : OracleState) {a : α} {s' : OracleState}
    (ha : (a, s') ∈ ((OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      program).run s).support) :
    (emit a).length ≤ time := by
  let cfg : Config k Bool State Operation x :=
    { tapes := wordsCfg x (some machine.initial) ws₀ out₀
      channels := fun _ => ⟨[], [], 0⟩ }
  obtain ⟨hlaw, _⟩ := h OracleState oracle s cfg rfl (fun _ => rfl)
  have hmem : (wordsCfg x (none : Option State) (ws₁ a) (out₀ ++ emit a), s') ∈
      (((OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        program).run s).map
        (fun (a, s') => (wordsCfg x (none : Option State) (ws₁ a) (out₀ ++ emit a), s'))).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨(a, s'), ha, rfl⟩
  rw [← hlaw] at hmem
  obtain ⟨⟨final, s₁⟩, hfinal, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hmem
  rcases Prod.mk.inj heq with ⟨htapes, rfl⟩
  have hlen := length_output_le_of_mem_support_runOracleConfigFrom machine oracle time cfg s hfinal
  have hout : final.tapes.output = out₀ ++ emit a := by rw [htapes]; rfl
  have hcfg : cfg.tapes.output = out₀ := rfl
  rw [hout, hcfg, List.length_append] at hlen
  omega

/-- Any supported output of a `ComputesTidily` machine has length at most `time`. -/
theorem ComputesTidily.length_output_le {machine : MultiTapePTM k Bool State Operation}
    {time : ℕ}
    {program : ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}
    (h : machine.ComputesTidily x time program)
    (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
    (s : OracleState) {w : List Bool} {s' : OracleState}
    (hw : (w, s') ∈ ((OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      program).run s).support) :
    w.length ≤ time :=
  (h []).length_emit_le oracle s hw

/-! ### Tape extension -/

/-- Reindexing work tapes via `extendTapes` transforms the selected tapes according to `machine`
and preserves all unselected tape words. -/
theorem RunsWords.extendTapes {machine : MultiTapePTM k Bool State Operation}
    {ws₀ : Fin k' → List Bool} {out₀ : List Bool} {time : ℕ}
    {α : Type} {program : ProbOracleComp (fun _ : Operation × List Bool => List Bool) α}
    {ws₁ : α → Fin k → List Bool} {emit : α → List Bool} (e : Fin k ↪ Fin k')
    (h : machine.RunsWords x (fun j => ws₀ (e j)) out₀ time program ws₁ emit) :
    (machine.extendTapes e).RunsWords x ws₀ out₀ time program
      (fun a l => (MultiTapeTM.partialInv e l).elim (ws₀ l) (ws₁ a)) emit := by
  intro OracleState oracle s cfg htapes hbuf
  let cfg₀ : Config k Bool State Operation x :=
    { tapes := wordsCfg x (some machine.initial) (fun j => ws₀ (e j)) out₀
      channels := cfg.channels }
  have hembed : cfg = cfg₀.embed e (fun l => tapeOfList (ws₀ l)) (fun _ => 0) := by
    refine Config.ext ?_ rfl
    rw [htapes]
    exact (MultiTapeTM.embed_wordsCfg e (fun _ => rfl) (fun _ _ => rfl)).symm
  have hrun :
      (machine.extendTapes e).runOracleConfigFrom time cfg =
        (fun final => final.embed e (fun l => tapeOfList (ws₀ l)) (fun _ => 0)) <$>
          machine.runOracleConfigFrom time cfg₀ := by
    rw [hembed]
    exact MultiTapePTM.runConfigFrom_embed machine e _ _ cfg₀ _ _ time
  obtain ⟨hlaw, hclean⟩ := h OracleState oracle s cfg₀ rfl hbuf
  dsimp only
  rw [hrun, OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map]
  constructor
  · have hmap :
        PMF.map (fun (final, s') => (final.tapes, s'))
          (PMF.map (fun (a, s') => (a.embed e (fun l => tapeOfList (ws₀ l)) (fun _ => 0), s'))
            ((OracleComp.interpret
              (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
              (machine.runOracleConfigFrom time cfg₀)).run s)) =
        PMF.map (fun (tapes, s') =>
            (MultiTapeTM.embed e tapes (fun l => tapeOfList (ws₀ l)) (fun _ => 0), s'))
          (PMF.map (fun (final, s') => (final.tapes, s'))
            ((OracleComp.interpret
              (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
              (machine.runOracleConfigFrom time cfg₀)).run s)) := by
      simp only [PMF.map_comp, Function.comp_def, Config.embed]
    rw [hmap, hlaw, PMF.map_comp]
    congr 1
    funext ⟨a, s'⟩
    refine Prod.ext ?_ rfl
    exact MultiTapeTM.embed_wordsCfg e (fun j => by simp)
      (fun l hl => by simp [MultiTapeTM.partialInv_eq_none e hl])
  · intro final hfinal op
    obtain ⟨⟨final₀, s'⟩, hfinal₀, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
    exact hclean (final₀, s') hfinal₀ op

/-- Reindexing a tidy probabilistic machine preserves `ComputesTidily`. -/
theorem ComputesTidily.extendTapes {machine : MultiTapePTM k Bool State Operation}
    {time : ℕ}
    {program : ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}
    (h : machine.ComputesTidily x time program) (e : Fin k ↪ Fin k') :
    (machine.extendTapes e).ComputesTidily x time program := by
  intro out₀
  have hext := (h out₀).extendTapes (ws₀ := fun _ => []) e
  have hblank : (fun (a : List Bool) (l : Fin k') =>
      (MultiTapeTM.partialInv e l).elim ([] : List Bool) (fun _ => [])) =
      fun _ _ => [] := by
    funext a l
    cases MultiTapeTM.partialInv e l <;> rfl
  simpa only [hblank] using hext

/-! ### Redirecting output to a work-tape word (`outputToWord`) -/

/-- `machine` with its output redirected to a new last work tape, whose head is then rewound to
cell `0`. -/
noncomputable def outputToWord (machine : MultiTapePTM k Bool State Operation) :
    MultiTapePTM (k + 1) Bool (State ⊕ RewindWorkState) Operation :=
  machine.outputToTape.seq (ofDeterministic ((rewindWork Bool).extendTapes (tapeEmb (Fin.last k))))

/-- Redirecting the output of a blank `wordsCfg` configuration adds a blank last work tape. -/
private theorem outCfg_wordsCfg_nil (x : List Bool) (q : Option State) :
    outCfg (wordsCfg x q (fun _ : Fin k => []) []) = wordsCfg x q (fun _ => []) [] := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> induction l using Fin.lastCases <;>
    simp [outCfg, wordsCfg]

/-- Rewinding the last work tape of `outCfg (wordsCfg x _ (fun _ => []) w)` in `r + 2` steps for
any `w.length ≤ r` leaves `w` on the last work tape and halts. -/
private theorem runFrom_rewindLast {w : List Bool} {r : ℕ} (hr : w.length ≤ r) :
    ((rewindWork Bool).extendTapes (tapeEmb (Fin.last k))).runFrom
      (outCfg (wordsCfg x (some (rewindWork Bool).q₀) (fun _ : Fin k => []) w)) (r + 2) =
      wordsCfg x none (Function.update (fun _ => []) (Fin.last k) w) [] := by
  let cfg := outCfg (wordsCfg x (some (rewindWork Bool).q₀) (fun _ : Fin k => []) w)
  have hone : oneTapeCfg (Fin.last k) cfg =
      ⟨some (rewindWork Bool).q₀, 1, fun _ => tapeOfList w, fun _ => (w.length : ℤ), []⟩ := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext _ <;> simp [oneTapeCfg, cfg]
  have hrun₀ : (rewindWork Bool).runFrom (oneTapeCfg (Fin.last k) cfg) (w.length + 2) =
      ⟨none, 1, fun _ => tapeOfList w, fun _ => 0, []⟩ := by
    rw [hone]
    exact runFrom_rewindWork_none _ _ _ rfl le_rfl
  have hrun : (rewindWork Bool).runFrom (oneTapeCfg (Fin.last k) cfg) (r + 2) =
      ⟨none, 1, fun _ => tapeOfList w, fun _ => 0, []⟩ := by
    rw [runFrom_eq_of_halt _ _ (by omega : w.length + 2 ≤ r + 2) (by rw [hrun₀]), hrun₀]
  rw [runFrom_tapeEmb, hrun, embed_tapeEmb]
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> induction l using Fin.lastCases <;>
    simp [wordsCfg]

/-- If `machine` computes `program` tidily in `time` steps and every supported output of `program`
has length at most `l`, then `machine.outputToWord` writes `program`'s output onto its new last
work tape in `time + l + 2` steps and emits nothing. -/
theorem ComputesTidily.outputToWord_of_le {machine : MultiTapePTM k Bool State Operation}
    {time l : ℕ}
    {program : ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}
    (h : machine.ComputesTidily x time program)
    (hl : ∀ (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
      (s : OracleState) (w : List Bool) (s' : OracleState),
      (w, s') ∈ ((OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        program).run s).support → w.length ≤ l) :
    ∀ out₀, machine.outputToWord.RunsWords x (fun _ => []) out₀ (time + (l + 2)) program
      (fun w => Function.update (fun _ => []) (Fin.last k) w) (fun _ => []) := by
  intro out₀
  apply RunsWords.of_nil_output
  intro OracleState oracle s cfg htapes hbuf
  let rew : MultiTapePTM (k + 1) Bool RewindWorkState Operation :=
    ofDeterministic ((rewindWork Bool).extendTapes (tapeEmb (Fin.last k)))
  let cfg₀ : Config k Bool State Operation x :=
    { tapes := wordsCfg x (some machine.initial) (fun _ => []) [], channels := cfg.channels }
  have hleft : cfg = Sequential.left rew (OutputToTape.config cfg₀) := by
    refine Config.ext ?_ rfl
    rw [htapes]
    change wordsCfg x (some (Sum.inl machine.initial)) (fun _ => []) [] =
      (outCfg (wordsCfg x (some machine.initial) (fun _ => []) [])).mapState (Option.map Sum.inl)
    rw [outCfg_wordsCfg_nil]
    rfl
  have houtRun :
      machine.outputToTape.runOracleConfigFrom time (OutputToTape.config cfg₀) =
        OutputToTape.config <$> machine.runOracleConfigFrom time cfg₀ :=
    MultiTapePTM.runConfigFrom_outputToTape machine _ _ time cfg₀
  have hhalt₁ : ∀ result ∈ ((OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (machine.outputToTape.runOracleConfigFrom time (OutputToTape.config cfg₀))).run s).support,
      result.1.tapes.state = none := by
    intro result hres
    rw [houtRun, OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map] at hres
    obtain ⟨⟨mid, s₁⟩, hmid, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hres
    exact (h []).halted oracle s cfg₀ rfl hbuf (mid, s₁) hmid
  have hhalt₂ : ∀ result ∈ ((OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (machine.outputToTape.runOracleConfigFrom time (OutputToTape.config cfg₀))).run s).support,
      ∀ final ∈ ((OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (rew.runOracleConfigFrom (l + 2)
          (Sequential.start rew result.1))).run result.2).support,
        final.1.tapes.state = none := by
    intro result hres ⟨final₁, final₂⟩ hfinal
    rw [houtRun, OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map] at hres
    obtain ⟨⟨mid, s₁⟩, hmid, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hres
    obtain ⟨⟨w, hw, hmidTapes⟩, _⟩ := (h []).mem_support oracle s cfg₀ rfl hbuf hmid
    have hstart : (Sequential.start rew (OutputToTape.config mid)).tapes =
        outCfg (wordsCfg x (some (rewindWork Bool).q₀) (fun _ => []) w) := by
      simp only [Sequential.start, OutputToTape.config, outCfg, hmidTapes, id_eq,
        List.nil_append, wordsCfg_state, wordsCfg_inputPos, wordsCfg_output, wordsCfg_workTapePos]
      rfl
    rw [run_interpret_runOracleConfigFrom_ofDeterministic, hstart,
      runFrom_rewindLast (hl OracleState oracle s w s₁ hw),
      PMF.mem_support_pure_iff] at hfinal
    rcases Prod.mk.inj hfinal with ⟨rfl, rfl⟩
    rfl
  dsimp only [outputToWord]
  rw [hleft, run_interpret_runOracleConfigFrom_seq _ _ oracle (OutputToTape.config cfg₀)
    time (l + 2) s hhalt₁ hhalt₂]
  constructor
  · rw [houtRun, OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map,
      PMF.bind_map, PMF.map_bind]
    trans (((OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (machine.runOracleConfigFrom time cfg₀)).run s).bind
      (fun a =>
        PMF.pure
          (wordsCfg x none
            (Function.update (fun _ => []) (Fin.last k) a.1.tapes.output) [], a.2)))
    · apply PMF.bind_congr_on_support
      intro ⟨mid, s₁⟩ hmid
      dsimp only [Function.comp_def]
      obtain ⟨⟨w, hw, hmidTapes⟩, _⟩ := (h []).mem_support oracle s cfg₀ rfl hbuf hmid
      have hstart : (Sequential.start rew (OutputToTape.config mid)).tapes =
          outCfg (wordsCfg x (some (rewindWork Bool).q₀) (fun _ => []) w) := by
        simp only [Sequential.start, OutputToTape.config, outCfg, hmidTapes, id_eq,
          List.nil_append, wordsCfg_state, wordsCfg_inputPos, wordsCfg_output,
          wordsCfg_workTapePos]
        rfl
      have hout : mid.tapes.output = w := by rw [hmidTapes]; rfl
      rw [run_interpret_runOracleConfigFrom_ofDeterministic, hstart,
        runFrom_rewindLast (hl OracleState oracle s w s₁ hw), hout]
      simp only [Sequential.right, Cfg.mapState, PMF.pure_map, wordsCfg_state, Option.map_none,
        wordsCfg_inputPos, wordsCfg_output]
      rfl
    · have hlaw := ((h []) OracleState oracle s cfg₀ rfl hbuf).1
      have hmapOut := congrArg
        (PMF.map (fun (p : Cfg k Bool State x × OracleState) =>
          (wordsCfg x (none : Option (State ⊕ RewindWorkState))
            (Function.update (fun _ => []) (Fin.last k) p.1.output) [], p.2))) hlaw
      change ((OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (machine.runOracleConfigFrom time cfg₀)).run s).bind
        (PMF.pure ∘ fun a =>
          (wordsCfg x none
            (Function.update (fun _ => []) (Fin.last k) a.1.tapes.output) [], a.2)) = _
      rw [PMF.bind_pure_comp]
      simpa only [PMF.map_comp, Function.comp_def, List.nil_append, id_eq, wordsCfg] using hmapOut
  · intro final hfinal op
    obtain ⟨result, hmid, hfinal⟩ := (PMF.mem_support_bind_iff _ _ _).mp hfinal
    obtain ⟨⟨final₀, s₂⟩, hfinal₀, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
    rw [houtRun, OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map] at hmid
    obtain ⟨⟨mid₀, s₁⟩, hmid₀, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hmid
    rw [run_interpret_runOracleConfigFrom_ofDeterministic, PMF.mem_support_pure_iff] at hfinal₀
    rcases Prod.mk.inj hfinal₀ with ⟨rfl, rfl⟩
    exact ((h []).mem_support oracle s cfg₀ rfl hbuf hmid₀).2 op

/-- Unconditional `outputToWord` specification using `ComputesTidily.length_output_le`. -/
theorem ComputesTidily.outputToWord {machine : MultiTapePTM k Bool State Operation}
    {time : ℕ}
    {program : ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}
    (h : machine.ComputesTidily x time program) (out₀ : List Bool) :
    machine.outputToWord.RunsWords x (fun _ => []) out₀ (2 * time + 2) program
      (fun w => Function.update (fun _ => []) (Fin.last k) w) (fun _ => []) := by
  simpa only [Nat.two_mul, Nat.add_assoc] using
    h.outputToWord_of_le (fun _ oracle s _ _ hw => h.length_output_le oracle s hw) out₀

/-! ### Reading input from a work-tape word (`inputFromWord` and `onWords`) -/

/-- `machine` reading its input from the virtual input tape `Fin.natAdd k 0`, with `mark` written to
cell `-1` of the flag tape `Fin.natAdd k 1` before and erased after. -/
noncomputable def inputFromWord (machine : MultiTapePTM k Bool State Operation) (mark : Bool) :
    MultiTapePTM (k + 2) Bool (MarkWorkState ⊕ State ⊕ MarkWorkState) Operation :=
  (ofDeterministic (markFlag k (some mark))).seq
    (machine.inputFromTape.seq (ofDeterministic (markFlag k none)))

/-- Updating the flag tape of an appended family of tapes only changes the flag entry. -/
private theorem update_append_flag {α : Type*} (ws₀ : Fin k → α) (a b c : α) :
    Function.update (Fin.append ws₀ ![a, b]) (Fin.natAdd k 1) c = Fin.append ws₀ ![a, c] := by
  rw [← Fin.append_update_right]
  congr 1
  simp [funext_iff]

/-- Setting or erasing the flag on `Fin.natAdd k 1` in `2` deterministic steps. -/
private theorem runFrom_markFlag (write : Option Bool)
    (WS : Fin k → ℤ → Option Bool) (vip flag : ℤ → Option Bool) (out : List Bool)
    (ip : Fin (x.length + 2)) :
    (markFlag k write).runFrom
      ⟨some (markFlag k write).q₀, ip, Fin.append WS ![vip, flag], fun _ => 0, out⟩ 2 =
      ⟨none, ip, Fin.append WS ![vip, Function.update flag (-1) write], fun _ => 0, out⟩ := by
  let cfg : Cfg (k + 2) Bool MarkWorkState x :=
    ⟨some (markWork Bool write).q₀, ip, Fin.append WS ![vip, flag], fun _ => 0, out⟩
  have hone : oneTapeCfg (Fin.natAdd k 1) cfg =
      ⟨some (markWork Bool write).q₀, ip, fun _ => flag, fun _ => 0, out⟩ := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext _ <;> simp [oneTapeCfg, cfg, Fin.append_right]
  change (markFlag k write).runFrom cfg 2 = _
  rw [markFlag, runFrom_tapeEmb, hone, runFrom_markWork, embed_tapeEmb]
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · simpa [cfg] using update_append_flag WS vip flag (Function.update flag (-1) write)
  · funext l
    simp [cfg, Function.update_apply]

/-- A `wordsCfg` configuration whose last two words are `w` and `[]`, written out. -/
private theorem wordsCfg_append_words {State' : Type} {outer : List Bool} (q : Option State')
    (ws : Fin k → List Bool) (w out : List Bool) :
    wordsCfg outer q (Fin.append ws ![w, []]) out =
      ⟨q, 1, Fin.append (fun j => tapeOfList (ws j)) ![tapeOfList w, fun _ => none],
        fun _ => 0, out⟩ := by
  refine Cfg.ext rfl rfl
    ((Fin.comp_append tapeOfList ws ![w, []]).trans (congrArg _ (funext fun i => ?_))) rfl rfl
  match i with
  | 0 | 1 => simp

/-- If `machine` transforms `ws₀` to `ws₁ a` and emits `emit a` on input `w`, then
`machine.inputFromWord mark` transforms `Fin.append ws₀ ![w, []]` to `Fin.append (ws₁ a) ![w, []]`
and emits `emit a` on any outer input `x` in `time + 4` steps. -/
theorem RunsWords.inputFromWord {machine : MultiTapePTM k Bool State Operation}
    {w : List Bool} {ws₀ : Fin k → List Bool} {out₀ : List Bool} {time : ℕ}
    {α : Type} {program : ProbOracleComp (fun _ : Operation × List Bool => List Bool) α}
    {ws₁ : α → Fin k → List Bool} {emit : α → List Bool} (mark : Bool)
    (h : machine.RunsWords w ws₀ out₀ time program ws₁ emit) :
    (machine.inputFromWord mark).RunsWords x (Fin.append ws₀ ![w, []]) out₀ (time + 4)
      program (fun a => Fin.append (ws₁ a) ![w, []]) emit := by
  intro OracleState oracle s cfg htapes hbuf
  let setF : MultiTapePTM (k + 2) Bool MarkWorkState Operation :=
    ofDeterministic (markFlag k (some mark))
  let eraseF : MultiTapePTM (k + 2) Bool MarkWorkState Operation :=
    ofDeterministic (markFlag k none)
  let midM := machine.inputFromTape.seq eraseF
  let cfg₀ : Config (k + 2) Bool MarkWorkState Operation x :=
    { tapes := wordsCfg x (some (markFlag k (some mark)).q₀) (Fin.append ws₀ ![w, []]) out₀
      channels := cfg.channels }
  have hleft₀ : cfg = Sequential.left midM cfg₀ := by
    refine Config.ext ?_ rfl
    rw [htapes]
    rfl
  let cfgIn : Config k Bool State Operation w :=
    { tapes := wordsCfg w (some machine.initial) ws₀ out₀, channels := cfg.channels }
  let ready : Config (k + 2) Bool MarkWorkState Operation x :=
    { tapes := inCfg mark (wordsCfg w (none : Option MarkWorkState) ws₀ out₀) x
      channels := cfg.channels }
  have hset : (OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (setF.runOracleConfigFrom 2 cfg₀)).run s = PMF.pure (ready, s) := by
    rw [run_interpret_runOracleConfigFrom_ofDeterministic]
    congr 1
    refine Prod.ext (Config.ext ?_ rfl) rfl
    dsimp only [ready]
    change (markFlag k (some mark)).runFrom
      (wordsCfg x (some (markFlag k (some mark)).q₀) (Fin.append ws₀ ![w, []]) out₀) 2 = _
    rw [wordsCfg_append_words, inCfg_wordsCfg]
    exact runFrom_markFlag (some mark) _ _ _ _ _
  have hstartReady : Sequential.start midM ready =
      Sequential.left eraseF (InputFromTape.config mark cfgIn x 1) := by
    refine Config.ext ?_ rfl
    simp only [Sequential.start, Cfg.withState, inCfg_wordsCfg, Int.reduceNeg, Sequential.left,
      Cfg.mapState, InputFromTape.config, Option.elim_some, Cfg.mk.injEq, Option.some.injEq,
      and_self, and_true, cfgIn, ready]
    rfl
  have hinRun :
      machine.inputFromTape.runOracleConfigFrom time (InputFromTape.config mark cfgIn x 1) =
        (fun final => InputFromTape.config mark final x 1) <$>
          machine.runOracleConfigFrom time cfgIn :=
    MultiTapePTM.runConfigFrom_inputFromTape machine _ _ mark time cfgIn x 1
  have hhalt₁ : ∀ result ∈ ((OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (machine.inputFromTape.runOracleConfigFrom time
        (InputFromTape.config mark cfgIn x 1))).run s).support,
      result.1.tapes.state = none := by
    intro result hres
    rw [hinRun, OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map] at hres
    obtain ⟨⟨mid, s₁⟩, hmid, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hres
    exact h.halted oracle s cfgIn rfl hbuf (mid, s₁) hmid
  have hhalt₂ : ∀ result ∈ ((OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (machine.inputFromTape.runOracleConfigFrom time
        (InputFromTape.config mark cfgIn x 1))).run s).support,
      ∀ final ∈ ((OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (eraseF.runOracleConfigFrom 2
          (Sequential.start eraseF result.1))).run result.2).support,
        final.1.tapes.state = none := by
    intro result hres ⟨final₁, final₂⟩ hfinal
    rw [hinRun, OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map] at hres
    obtain ⟨⟨mid, s₁⟩, hmid, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hres
    obtain ⟨⟨a, _, hmidTapes⟩, _⟩ := h.mem_support oracle s cfgIn rfl hbuf hmid
    have hstartErase : (Sequential.start eraseF (InputFromTape.config mark mid x 1)).tapes =
        ⟨some (markFlag k (none : Option Bool)).q₀, 1,
          Fin.append (fun j => tapeOfList (ws₁ a j))
            ![tapeOfList w, Function.update (fun _ : ℤ => (none : Option Bool)) (-1) (some mark)],
          fun _ => 0, out₀ ++ emit a⟩ := by
      simp [Sequential.start, InputFromTape.config, hmidTapes, inCfg_wordsCfg, Cfg.withState,
        eraseF, ofDeterministic]
    rw [run_interpret_runOracleConfigFrom_ofDeterministic, hstartErase,
      runFrom_markFlag none, PMF.mem_support_pure_iff] at hfinal
    rcases Prod.mk.inj hfinal with ⟨rfl, rfl⟩
    rfl
  have hmidSeq := run_interpret_runOracleConfigFrom_seq machine.inputFromTape eraseF oracle
    (InputFromTape.config mark cfgIn x 1) time 2 s hhalt₁ hhalt₂
  have hhaltMid : ∀ final ∈ ((OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (midM.runOracleConfigFrom (time + 2) (Sequential.start midM ready))).run s).support,
      final.1.tapes.state = none := by
    intro final hfinal
    rw [hstartReady, hmidSeq] at hfinal
    obtain ⟨result, hres, hmap⟩ := (PMF.mem_support_bind_iff _ _ _).mp hfinal
    obtain ⟨⟨final₀, s₂⟩, hfinal₀, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hmap
    simpa [Sequential.right, Cfg.mapState] using hhalt₂ result hres (final₀, s₂) hfinal₀
  have hsplit : time + 4 = 2 + (time + 2) := by omega
  change
    PMF.map (fun (final, s') => (final.tapes, s'))
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        ((setF.seq midM).runOracleConfigFrom (time + 4) cfg)).run s) = _ ∧
    ∀ final ∈ ((OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      ((setF.seq midM).runOracleConfigFrom (time + 4) cfg)).run s).support, _
  rw [hleft₀, hsplit,
    run_interpret_runOracleConfigFrom_seq setF midM oracle cfg₀ 2 (time + 2) s
      (fun ⟨res₁, res₂⟩ hres => by
        rw [hset, PMF.mem_support_pure_iff] at hres
        rcases Prod.mk.inj hres with ⟨rfl, rfl⟩
        rfl)
      (fun ⟨res₁, res₂⟩ hres => by
        rw [hset, PMF.mem_support_pure_iff] at hres
        rcases Prod.mk.inj hres with ⟨rfl, rfl⟩
        exact hhaltMid),
    hset, PMF.pure_bind, hstartReady, hmidSeq]
  let F (c : Cfg k Bool State w) : Cfg (k + 2) Bool (MarkWorkState ⊕ State ⊕ MarkWorkState) x :=
    ⟨none, 1, Fin.append c.workTapes ![tapeOfList w, fun _ => none], fun _ => 0, c.output⟩
  have hF_wordsCfg (ws : Fin k → List Bool) (out : List Bool) :
      F (wordsCfg w none ws out) = wordsCfg x none (Fin.append ws ![w, []]) out := by
    rw [wordsCfg_append_words]
    rfl
  constructor
  · rw [hinRun, OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map,
      PMF.bind_map, PMF.map_bind, PMF.map_bind]
    trans (((OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (machine.runOracleConfigFrom time cfgIn)).run s).bind
      (fun p => PMF.pure (F p.1.tapes, p.2)))
    · apply PMF.bind_congr_on_support
      intro ⟨mid, s₁⟩ hmid
      dsimp only [Function.comp_def]
      obtain ⟨⟨a, _, hmidTapes⟩, _⟩ := h.mem_support oracle s cfgIn rfl hbuf hmid
      have hstartErase : (Sequential.start eraseF (InputFromTape.config mark mid x 1)).tapes =
          ⟨some (markFlag k (none : Option Bool)).q₀, 1,
            Fin.append (fun j => tapeOfList (ws₁ a j))
              ![tapeOfList w, Function.update (fun _ : ℤ => (none : Option Bool)) (-1) (some mark)],
            fun _ => 0, out₀ ++ emit a⟩ := by
        simp [Sequential.start, InputFromTape.config, hmidTapes, inCfg_wordsCfg, Cfg.withState,
          eraseF, ofDeterministic]
      rw [run_interpret_runOracleConfigFrom_ofDeterministic, hstartErase,
        runFrom_markFlag none, hmidTapes, Function.update_idem]
      simp [Sequential.right, Cfg.mapState, F, wordsCfg]
    · have hlaw := (h OracleState oracle s cfgIn rfl hbuf).1
      have hmapF := congrArg (PMF.map (fun (p : Cfg k Bool State w × OracleState) => (F p.1, p.2)))
        hlaw
      change ((OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (machine.runOracleConfigFrom time cfgIn)).run s).bind
        (PMF.pure ∘ fun p => (F p.1.tapes, p.2)) = _
      rw [PMF.bind_pure_comp]
      simpa only [PMF.map_comp, Function.comp_def, hF_wordsCfg] using hmapF
  · intro final hfinal op
    obtain ⟨p₁, hfinal₁, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
    obtain ⟨result, hres, hmap⟩ := (PMF.mem_support_bind_iff _ _ _).mp hfinal₁
    obtain ⟨⟨final₀, s₂⟩, hfinal₀, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hmap
    rw [hinRun, OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map] at hres
    obtain ⟨⟨mid₀, s₃⟩, hmid₀, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hres
    rw [run_interpret_runOracleConfigFrom_ofDeterministic, PMF.mem_support_pure_iff] at hfinal₀
    rcases Prod.mk.inj hfinal₀ with ⟨rfl, rfl⟩
    exact (h.mem_support oracle s cfgIn rfl hbuf hmid₀).2 op

/-- `machine` with its output written to work tape `(Fin.last k).castAdd 2` and its input read from
work tape `Fin.natAdd (k + 1) 0`, using `mark` to flag the left boundary. -/
noncomputable def onWords (machine : MultiTapePTM k Bool State Operation) (mark : Bool) :
    MultiTapePTM (k + 1 + 2) Bool
      (MarkWorkState ⊕ (State ⊕ RewindWorkState) ⊕ MarkWorkState) Operation :=
  machine.outputToWord.inputFromWord mark

/-- If `machine` computes `program` tidily on `w` in `time` steps and every supported output has
length at most `l`, then `machine.onWords mark` reads `w` from `Fin.natAdd (k + 1) 0` and writes
`program`'s output to `(Fin.last k).castAdd 2` in `time + l + 6` steps. -/
theorem ComputesTidily.onWords_of_le {machine : MultiTapePTM k Bool State Operation}
    {w : List Bool} {time l : ℕ}
    {program : ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}
    (mark : Bool) (h : machine.ComputesTidily w time program)
    (hl : ∀ (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
      (s : OracleState) (w' : List Bool) (s' : OracleState),
      (w', s') ∈ ((OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        program).run s).support → w'.length ≤ l) :
    ∀ out₀, (machine.onWords mark).RunsWords x
      (Function.update (fun _ => []) (Fin.natAdd (k + 1) 0) w) out₀ (time + l + 6) program
      (fun w' =>
        Function.update (Function.update (fun _ => []) (Fin.natAdd (k + 1) 0) w)
          ((Fin.last k).castAdd 2) w')
      (fun _ => []) := by
  intro out₀
  have hpost (w' : List Bool) :
      Fin.append (Function.update (fun _ : Fin (k + 1) => ([] : List Bool)) (Fin.last k) w')
          ![w, []] =
        Function.update (Function.update (fun _ => []) (Fin.natAdd (k + 1) 0) w)
          ((Fin.last k).castAdd 2) w' := by
    rw [Fin.append_update_left, append_nil_eq_update]
  have hin := ((h.outputToWord_of_le hl out₀).inputFromWord (x := x) mark).mono
    (time' := time + l + 6) (by omega)
  dsimp only [MultiTapePTM.onWords]
  simpa only [append_nil_eq_update, hpost] using hin

/-! ### Composing tidy probabilistic machines (`tidyComp` and `appendPTM`) -/

/-- Run `tm₁` with its output written to work tape `Fin.natAdd (max k₁ k₂) 0`, then run `tm₂`
reading its input from that tape (using `mark` on the last work tape), and finally clear that
tape. -/
noncomputable def tidyComp (tm₂ : MultiTapePTM k₂ Bool State₂ Operation)
    (tm₁ : MultiTapePTM k₁ Bool State₁ Operation) (mark : Bool) :
    MultiTapePTM (max k₁ k₂ + 2) Bool
      ((State₁ ⊕ RewindWorkState) ⊕
        (MarkWorkState ⊕ State₂ ⊕ MarkWorkState) ⊕ Unit ⊕ RewindWorkState) Operation :=
  ((tm₁.extendTapes (Fin.castLEEmb (le_max_left k₁ k₂))).outputToWord.extendTapes
      Fin.castSuccEmb).seq
    (((tm₂.extendTapes (Fin.castLEEmb (le_max_right k₁ k₂))).inputFromWord mark).seq
      (ofDeterministic ((clearWork Bool).extendTapes (tapeEmb (Fin.natAdd (max k₁ k₂) 0)))))

/-- If `tm₁` computes `prog₁` tidily on `x` in `t₁` steps with outputs of length at most `l`, and
`tm₂` computes `prog₂ w` tidily on every supported output `w` of `prog₁` in `t₂` steps, then
`tm₂.tidyComp tm₁ mark` computes `prog₁ >>= prog₂` tidily on `x` in `t₁ + t₂ + 4 * l + 9` steps. -/
theorem ComputesTidily.comp_of_le {tm₁ : MultiTapePTM k₁ Bool State₁ Operation}
    {tm₂ : MultiTapePTM k₂ Bool State₂ Operation} {t₁ t₂ l : ℕ}
    {prog₁ : ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}
    {prog₂ : List Bool → ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}
    (mark : Bool) (h₁ : tm₁.ComputesTidily x t₁ prog₁)
    (hl : ∀ (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
      (s : OracleState) (w : List Bool) (s' : OracleState),
      (w, s') ∈ ((OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        prog₁).run s).support → w.length ≤ l)
    (h₂ : ∀ w (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
      (s s' : OracleState),
      (w, s') ∈ ((OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        prog₁).run s).support → tm₂.ComputesTidily w t₂ (prog₂ w)) :
    (tm₂.tidyComp tm₁ mark).ComputesTidily x (t₁ + t₂ + 4 * l + 9) (prog₁ >>= prog₂) := by
  rw [computesTidily_iff_nil_output]
  let K := max k₁ k₂
  let A : Fin (K + 2) := Fin.natAdd K 0
  have hQ₁ (w : List Bool) :
      (fun l : Fin (K + 1 + 1) =>
        (MultiTapeTM.partialInv Fin.castSuccEmb l).elim ([] : List Bool)
          (Function.update (fun _ : Fin (K + 1) => []) (Fin.last K) w)) =
        Function.update (fun _ => []) A w := by
    funext idx
    induction idx using Fin.lastCases with
    | last =>
      rw [MultiTapeTM.partialInv_eq_none Fin.castSuccEmb
        (fun ⟨j, hj⟩ => Fin.castSucc_ne_last j hj)]
      simp [A, Fin.ext_iff]
    | cast j =>
      change (MultiTapeTM.partialInv Fin.castSuccEmb (Fin.castSuccEmb j)).elim _ _ = _
      rw [MultiTapeTM.partialInv_embed]
      simp [A, Function.update_apply, Fin.ext_iff]
  have hp₁ : ((tm₁.extendTapes (Fin.castLEEmb (le_max_left k₁ k₂))).outputToWord.extendTapes
      Fin.castSuccEmb).RunsWords x (fun _ => []) [] (t₁ + (l + 2)) prog₁
      (fun w => Function.update (fun _ => []) A w) (fun _ => []) := by
    have h₀ :=
      ((h₁.extendTapes (Fin.castLEEmb (le_max_left k₁ k₂))).outputToWord_of_le hl []).extendTapes
        (ws₀ := fun _ => []) Fin.castSuccEmb
    rw [← funext hQ₁]
    exact h₀
  have hinj₁ : Function.Injective
      (fun w : List Bool => (Function.update (fun _ => []) A w, ([] : List Bool))) := by
    intro w₁ w₂ heq
    have hfun := congrFun (congrArg Prod.fst heq) A
    simpa only [Function.update_self] using hfun
  have hp₂₃ : ∀ w (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
      (s s' : OracleState),
      (w, s') ∈ ((OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        prog₁).run s).support →
      (((tm₂.extendTapes (Fin.castLEEmb (le_max_right k₁ k₂))).inputFromWord mark).seq
        (ofDeterministic ((clearWork Bool).extendTapes (tapeEmb A)))).RunsWords
        x (Function.update (fun _ => []) A w) ([] ++ []) ((t₂ + 4) + 3 * (l + 1))
        (prog₂ w) (fun _ _ => []) id := by
    intro w OracleState oracle s s' hw
    have hwlen := hl OracleState oracle s w s' hw
    have hp₂ : ((tm₂.extendTapes (Fin.castLEEmb (le_max_right k₁ k₂))).inputFromWord mark).RunsWords
        x (Function.update (fun _ => []) A w) [] (t₂ + 4) (prog₂ w)
        (fun _ => Function.update (fun _ => []) A w) id := by
      have h₀ := (((h₂ w OracleState oracle s s' hw).extendTapes
        (Fin.castLEEmb (le_max_right k₁ k₂))) []).inputFromWord (x := x) mark
      simpa only [append_nil_eq_update] using h₀
    have hinj₂ : Function.Injective
        (fun y : List Bool => (Function.update (fun _ => []) A w, id y)) :=
      fun _ _ heq => congrArg Prod.snd heq
    have hp₃ : ∀ y (OracleState' : Type)
        (oracle' : Operation × List Bool → StateT OracleState' PMF (List Bool))
        (s₀ s₁ : OracleState'),
        (y, s₁) ∈ ((OracleComp.interpret
          (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle')
          (prog₂ w)).run s₀).support →
        (ofDeterministic (Oracle := Operation)
          ((clearWork Bool).extendTapes (tapeEmb A))).RunsWords
          x (Function.update (fun _ => []) A w) ([] ++ id y) (3 * (l + 1)) (pure ())
          (fun _ _ => []) (fun _ => []) := by
      intro y _ _ _ _ _
      exact (RunsWords.of_transformsTapes (Operation := Operation) (out₀ := [] ++ id y)
        (transformsTapes_clearWork_only A w) rfl (fun _ _ hQ => hQ)).mono
        (time' := 3 * (l + 1)) (by omega)
    have hseq := hp₂.seq_pure_right hinj₂ hp₃
    have happend : (fun a : List Bool => id a ++ []) = id := by
      funext a
      exact List.append_nil a
    simpa only [List.nil_append, happend] using hseq
  have hseq := (hp₁.seq_bind hinj₁ hp₂₃).of_map Prod.snd (fun _ _ => []) id
  have hbind : (Prod.snd <$> (prog₁ >>= fun a => (fun b => (a, b)) <$> prog₂ a)) =
      (prog₁ >>= prog₂) := by
    have hid : (fun b : List Bool => b) = id := rfl
    simp only [map_bind, Functor.map_map, hid, id_map]
  rw [hbind] at hseq
  exact hseq.mono (by omega)

/-- Unconditional tidy sequential composition using `h₁.length_output_le`. -/
theorem ComputesTidily.comp {tm₁ : MultiTapePTM k₁ Bool State₁ Operation}
    {tm₂ : MultiTapePTM k₂ Bool State₂ Operation} {t₁ t₂ : ℕ}
    {prog₁ : ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}
    {prog₂ : List Bool → ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}
    (mark : Bool) (h₁ : tm₁.ComputesTidily x t₁ prog₁)
    (h₂ : ∀ w (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
      (s s' : OracleState),
      (w, s') ∈ ((OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        prog₁).run s).support → tm₂.ComputesTidily w t₂ (prog₂ w)) :
    (tm₂.tidyComp tm₁ mark).ComputesTidily x (5 * t₁ + t₂ + 9) (prog₁ >>= prog₂) := by
  exact (h₁.comp_of_le mark (fun _ oracle s _ _ hw => h₁.length_output_le oracle s hw) h₂).mono
    (by omega)

/-- Run `tm₁` and then `tm₂` on the same input, both padded to `max k₁ k₂` work tapes. -/
noncomputable def appendPTM (tm₁ : MultiTapePTM k₁ Bool State₁ Operation)
    (tm₂ : MultiTapePTM k₂ Bool State₂ Operation) :
    MultiTapePTM (max k₁ k₂) Bool (State₁ ⊕ State₂) Operation :=
  (tm₁.extendTapes (Fin.castLEEmb (le_max_left k₁ k₂))).seq
    (tm₂.extendTapes (Fin.castLEEmb (le_max_right k₁ k₂)))

/-- If `tm₁` computes `prog₁` tidily in `t₁` steps and `tm₂` computes `prog₂ w₁` tidily in `t₂`
steps on the same input `x`, then `appendPTM tm₁ tm₂` computes
`prog₁ >>= fun w₁ => (fun w₂ => w₁ ++ w₂) <$> prog₂ w₁` tidily in `t₁ + t₂` steps. -/
theorem ComputesTidily.append {tm₁ : MultiTapePTM k₁ Bool State₁ Operation}
    {tm₂ : MultiTapePTM k₂ Bool State₂ Operation} {t₁ t₂ : ℕ}
    {prog₁ : ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}
    {prog₂ : List Bool → ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}
    (h₁ : tm₁.ComputesTidily x t₁ prog₁)
    (h₂ : ∀ w₁ (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
      (s s' : OracleState),
      (w₁, s') ∈ ((OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        prog₁).run s).support → tm₂.ComputesTidily x t₂ (prog₂ w₁)) :
    (appendPTM tm₁ tm₂).ComputesTidily x (t₁ + t₂)
      (prog₁ >>= fun w₁ => (fun w₂ => w₁ ++ w₂) <$> prog₂ w₁) := by
  rw [computesTidily_iff_nil_output]
  have hp₁ := (h₁.extendTapes (Fin.castLEEmb (le_max_left k₁ k₂))) []
  have hinj : Function.Injective
      (fun w₁ : List Bool => ((fun _ : Fin (max k₁ k₂) => ([] : List Bool)), id w₁)) :=
    fun _ _ heq => congrArg Prod.snd heq
  have hp₂ : ∀ w₁ (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
      (s s' : OracleState),
      (w₁, s') ∈ ((OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        prog₁).run s).support →
      (tm₂.extendTapes (Fin.castLEEmb (le_max_right k₁ k₂))).RunsWords
        x (fun _ => []) ([] ++ id w₁) t₂ (prog₂ w₁) (fun _ _ => []) id :=
    fun w₁ OracleState oracle s s' hw =>
      ((h₂ w₁ OracleState oracle s s' hw).extendTapes (Fin.castLEEmb (le_max_right k₁ k₂)))
        ([] ++ id w₁)
  have hseq := (hp₁.seq_bind hinj hp₂).of_map (fun p : List Bool × List Bool => p.1 ++ p.2)
    (fun _ _ => []) id
  dsimp only [appendPTM]
  simpa only [map_bind, Functor.map_map, id_eq] using hseq

/-- Prepend a deterministically computed prefix word before a tidy probabilistic computation. -/
theorem ComputesTidily.prefix {prep : MultiTapeTM k₁ Bool State₁}
    {source : MultiTapePTM k₂ Bool State₂ Operation} {pre : List Bool} {t₁ s₁ t₂ : ℕ}
    {program : ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}
    (hprep : prep.ComputesTidilyInTimeAndSpace x pre t₁ s₁)
    (hsource : source.ComputesTidily x t₂ program) :
    (appendPTM (ofDeterministic prep) source).ComputesTidily x (t₁ + t₂)
      ((fun y => pre ++ y) <$> program) := by
  have h := (ComputesTidily.of_deterministic (Operation := Operation) hprep).append
    (fun _ _ _ _ _ _ => hsource)
  simpa only [pure_bind] using h

/-! ### Conditional branching (`branch` and `itePTM`) -/

/-- Map control states across an effectful machine action. -/
def mapActionState {S S' : Type} (f : S → S') :
    MultiTapeMachine.Action k Bool S Operation → MultiTapeMachine.Action k Bool S' Operation
  | .step action symbol move => .step { action with state := action.state.map f } symbol move
  | .query op next => .query op (f next)

/-- Map control states across a machine configuration. -/
def mapConfigState {S S' : Type} (f : S → S') (cfg : Config k Bool S Operation x) :
    Config k Bool S' Operation x :=
  { cfg with tapes := cfg.tapes.mapState (Option.map f) }

/-- Read the cell under the head of work tape `i`, moving no head and writing nothing, then run
`tm₁` if the cell is not blank and `tm₂` if it is. -/
def branch (i : Fin k) (tm₁ : MultiTapePTM k Bool State₁ Operation)
    (tm₂ : MultiTapePTM k Bool State₂ Operation) :
    MultiTapePTM k Bool (Option (State₁ ⊕ State₂)) Operation where
  initial := none
  tr q inp work answer bit :=
    match q with
    | none => .step
      { inputTape := 0, workTapes := fun _ => (none, 0), output := none,
        state := some (some ((work i).elim (.inr tm₂.initial) fun _ => .inl tm₁.initial)) }
      (fun _ => none) (fun _ => 0)
    | some (.inl q) =>
      mapActionState (fun s => some (Sum.inl s)) (tm₁.tr q inp work answer bit)
    | some (.inr q) =>
      mapActionState (fun s => some (Sum.inr s)) (tm₂.tr q inp work answer bit)

namespace Branch

variable {i : Fin k} {tm₁ : MultiTapePTM k Bool State₁ Operation}
  {tm₂ : MultiTapePTM k Bool State₂ Operation}

/-- If `branch i tm₁ tm₂` acts on `f q` by mapping `tm`'s actions through `f`, then its clocked
run from `mapConfigState f cfg` maps `tm`'s clocked run through `mapConfigState f`. -/
theorem runOracleConfigFrom_mapState {S : Type} {tm : MultiTapePTM k Bool S Operation}
    {f : S → Option (State₁ ⊕ State₂)}
    (htr : ∀ q inp work answer bit,
      (branch i tm₁ tm₂).tr (f q) inp work answer bit =
        mapActionState f (tm.tr q inp work answer bit))
    (fuel : ℕ) (cfg : Config k Bool S Operation x) :
    (branch i tm₁ tm₂).runOracleConfigFrom fuel (mapConfigState f cfg) =
      mapConfigState f <$> tm.runOracleConfigFrom fuel cfg := by
  apply MultiTapeMachine.runConfigFrom_map tm (branch i tm₁ tm₂) _ _ _ _ (mapConfigState f)
  intro c
  cases hs : c.tapes.state with
  | none => simp [MultiTapeMachine.runConfigFrom, mapConfigState, Cfg.mapState, hs]
  | some q =>
    have hstate : (mapConfigState f c).tapes.state = some (f q) := by
      simp [mapConfigState, Cfg.mapState, hs]
    have hinp : (mapConfigState f c).tapes.inputSymbol = c.tapes.inputSymbol := rfl
    have hwork : (mapConfigState f c).tapes.workTapeSymbols = c.tapes.workTapeSymbols := rfl
    have hans : (mapConfigState f c).answerSymbols = c.answerSymbols := rfl
    dsimp only [MultiTapeMachine.runConfigFrom]
    rw [hstate, hs, hinp, hwork, hans]
    simp only [bind_map_left, map_bind, htr]
    congr 1
    funext bit
    cases tm.tr q c.tapes.inputSymbol c.tapes.workTapeSymbols c.answerSymbols bit with
    | step action symbol move =>
      simp [mapActionState, mapConfigState, Config.step, Turing.Action.apply, Cfg.mapState]
    | query op next =>
      simp [mapActionState, mapConfigState, Config.receive, Cfg.mapState]

end Branch

open Branch in
/-- When tape `i` is empty, `branch i tm₁ tm₂` transitions in `1` step to `tm₂` and never executes
`tm₁`. -/
theorem RunsWords.branch_nil (i : Fin k) (tm₁ : MultiTapePTM k Bool State₁ Operation)
    {tm₂ : MultiTapePTM k Bool State₂ Operation}
    {ws₀ : Fin k → List Bool} {out₀ : List Bool} {t₂ : ℕ}
    {α : Type} {program : ProbOracleComp (fun _ : Operation × List Bool => List Bool) α}
    {ws₁ : α → Fin k → List Bool} {emit : α → List Bool}
    (hi : ws₀ i = []) (h₂ : tm₂.RunsWords x ws₀ out₀ t₂ program ws₁ emit) :
    (branch i tm₁ tm₂).RunsWords x ws₀ out₀ (t₂ + 1) program ws₁ emit := by
  intro OracleState oracle s cfg htapes hbuf
  let cfg₂ : Config k Bool State₂ Operation x :=
    { tapes := wordsCfg x (some tm₂.initial) ws₀ out₀, channels := cfg.channels }
  have hsym : cfg.tapes.workTapeSymbols i = none := by
    rw [htapes]
    simp [Cfg.workTapeSymbols, wordsCfg, tapeOfList_zero, hi]
  have hstate : cfg.tapes.state = some (none : Option (State₁ ⊕ State₂)) := by
    rw [htapes]; rfl
  have hstep :
      (cfg.step
        { inputTape := 0, workTapes := fun _ => (none, 0), output := none,
          state := some (some (.inr tm₂.initial)) }
        (fun _ => none) (fun _ => 0)) =
      mapConfigState (fun s => some (Sum.inr s)) cfg₂ := by
    refine Config.ext ?_ (by funext op; simp [Config.step, mapConfigState, cfg₂])
    rw [Config.step, htapes]
    exact Cfg.ext rfl (by simp [Turing.Action.apply, wordsCfg, mapConfigState, Cfg.mapState, cfg₂])
      (by funext l; simp [Turing.Action.apply, wordsCfg, mapConfigState, Cfg.mapState, cfg₂])
      (by funext l; simp [Turing.Action.apply, wordsCfg, mapConfigState, Cfg.mapState, cfg₂])
      (by simp [Turing.Action.apply, wordsCfg, mapConfigState, Cfg.mapState, cfg₂])
  have htr_step : ∀ bit,
      (branch i tm₁ tm₂).tr none cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
        cfg.answerSymbols bit =
      MultiTapeMachine.Action.step
        { inputTape := 0, workTapes := fun _ => (none, 0), output := none,
          state := some (some (Sum.inr tm₂.initial)) }
        (fun _ => none) (fun _ => 0) := by
    intro _
    dsimp only [branch]
    rw [hsym]
    rfl
  dsimp only
  rw [run_interpret_runOracleConfigFrom_succ_step (branch i tm₁ tm₂) oracle t₂ cfg s hstate
      htr_step,
    hstep,
    runOracleConfigFrom_mapState (fun _ _ _ _ _ => rfl) t₂ cfg₂,
    OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map]
  obtain ⟨hlaw, hclean⟩ := h₂ OracleState oracle s cfg₂ rfl hbuf
  constructor
  · have hmap :
        PMF.map (fun (final : Config k Bool (Option (State₁ ⊕ State₂)) Operation x × OracleState) =>
            (final.1.tapes, final.2))
          (PMF.map (fun (a, s') =>
              (mapConfigState (fun s => (some (Sum.inr s) : Option (State₁ ⊕ State₂))) a, s'))
            ((OracleComp.interpret
              (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
              (tm₂.runOracleConfigFrom t₂ cfg₂)).run s)) =
        PMF.map (fun (tapes, s') =>
            (tapes.mapState (Option.map (fun s => (some (Sum.inr s) : Option (State₁ ⊕ State₂)))),
              s'))
          (PMF.map (fun (final, s') => (final.tapes, s'))
            ((OracleComp.interpret
              (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
              (tm₂.runOracleConfigFrom t₂ cfg₂)).run s)) := by
      simp only [PMF.map_comp, Function.comp_def, mapConfigState]
    rw [hmap, hlaw, PMF.map_comp]
    congr 1
  · intro final hfinal op
    obtain ⟨⟨final₀, s'⟩, hfinal₀, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
    exact hclean (final₀, s') hfinal₀ op

open Branch in
/-- When tape `i` is non-empty, `branch i tm₁ tm₂` transitions in `1` step to `tm₁` and never
executes `tm₂`. -/
theorem RunsWords.branch_ne_nil (i : Fin k) {tm₁ : MultiTapePTM k Bool State₁ Operation}
    (tm₂ : MultiTapePTM k Bool State₂ Operation)
    {ws₀ : Fin k → List Bool} {out₀ : List Bool} {t₁ : ℕ}
    {α : Type} {program : ProbOracleComp (fun _ : Operation × List Bool => List Bool) α}
    {ws₁ : α → Fin k → List Bool} {emit : α → List Bool}
    (hi : ws₀ i ≠ []) (h₁ : tm₁.RunsWords x ws₀ out₀ t₁ program ws₁ emit) :
    (branch i tm₁ tm₂).RunsWords x ws₀ out₀ (t₁ + 1) program ws₁ emit := by
  intro OracleState oracle s cfg htapes hbuf
  obtain ⟨b, bs, hbs⟩ := List.exists_cons_of_ne_nil hi
  let cfg₁ : Config k Bool State₁ Operation x :=
    { tapes := wordsCfg x (some tm₁.initial) ws₀ out₀, channels := cfg.channels }
  have hsym : cfg.tapes.workTapeSymbols i = some b := by
    rw [htapes]
    simp [Cfg.workTapeSymbols, wordsCfg, tapeOfList_zero, hbs]
  have hstate : cfg.tapes.state = some (none : Option (State₁ ⊕ State₂)) := by
    rw [htapes]; rfl
  have hstep :
      (cfg.step
        { inputTape := 0, workTapes := fun _ => (none, 0), output := none,
          state := some (some (.inl tm₁.initial)) }
        (fun _ => none) (fun _ => 0)) =
      mapConfigState (fun s => some (Sum.inl s)) cfg₁ := by
    refine Config.ext ?_ (by funext op; simp [Config.step, mapConfigState, cfg₁])
    rw [Config.step, htapes]
    exact Cfg.ext rfl (by simp [Turing.Action.apply, wordsCfg, mapConfigState, Cfg.mapState, cfg₁])
      (by funext l; simp [Turing.Action.apply, wordsCfg, mapConfigState, Cfg.mapState, cfg₁])
      (by funext l; simp [Turing.Action.apply, wordsCfg, mapConfigState, Cfg.mapState, cfg₁])
      (by simp [Turing.Action.apply, wordsCfg, mapConfigState, Cfg.mapState, cfg₁])
  have htr_step : ∀ bit,
      (branch i tm₁ tm₂).tr none cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
        cfg.answerSymbols bit =
      MultiTapeMachine.Action.step
        { inputTape := 0, workTapes := fun _ => (none, 0), output := none,
          state := some (some (Sum.inl tm₁.initial)) }
        (fun _ => none) (fun _ => 0) := by
    intro _
    dsimp only [branch]
    rw [hsym]
    rfl
  dsimp only
  rw [run_interpret_runOracleConfigFrom_succ_step (branch i tm₁ tm₂) oracle t₁ cfg s hstate
      htr_step,
    hstep,
    runOracleConfigFrom_mapState (fun _ _ _ _ _ => rfl) t₁ cfg₁,
    OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map]
  obtain ⟨hlaw, hclean⟩ := h₁ OracleState oracle s cfg₁ rfl hbuf
  constructor
  · have hmap :
        PMF.map (fun (final : Config k Bool (Option (State₁ ⊕ State₂)) Operation x × OracleState) =>
            (final.1.tapes, final.2))
          (PMF.map (fun (a, s') =>
              (mapConfigState (fun s => (some (Sum.inl s) : Option (State₁ ⊕ State₂))) a, s'))
            ((OracleComp.interpret
              (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
              (tm₁.runOracleConfigFrom t₁ cfg₁)).run s)) =
        PMF.map (fun (tapes, s') =>
            (tapes.mapState (Option.map (fun s => (some (Sum.inl s) : Option (State₁ ⊕ State₂)))),
              s'))
          (PMF.map (fun (final, s') => (final.tapes, s'))
            ((OracleComp.interpret
              (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
              (tm₁.runOracleConfigFrom t₁ cfg₁)).run s)) := by
      simp only [PMF.map_comp, Function.comp_def, mapConfigState]
    rw [hmap, hlaw, PMF.map_comp]
    congr 1
  · intro final hfinal op
    obtain ⟨⟨final₀, s'⟩, hfinal₀, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
    exact hclean (final₀, s') hfinal₀ op

/-- Run `tmc` with its output on a new last work tape, then `tm₁` if that word is non-empty and
`tm₂` otherwise, and clear the tape. -/
noncomputable def itePTM (tmc : MultiTapePTM k₀ Bool State₀ Operation)
    (tm₁ : MultiTapePTM k₁ Bool State₁ Operation)
    (tm₂ : MultiTapePTM k₂ Bool State₂ Operation) :
    MultiTapePTM (max k₀ (max k₁ k₂) + 1) Bool
      ((State₀ ⊕ RewindWorkState) ⊕
        Option (State₁ ⊕ State₂) ⊕ Unit ⊕ RewindWorkState) Operation :=
  (tmc.extendTapes (Fin.castLEEmb (le_max_left _ _))).outputToWord.seq
    ((branch (Fin.last _)
        ((tm₁.extendTapes (Fin.castLEEmb ((le_max_left k₁ k₂).trans
          (le_max_right k₀ _)))).extendTapes Fin.castSuccEmb)
        ((tm₂.extendTapes (Fin.castLEEmb ((le_max_right k₁ k₂).trans
          (le_max_right k₀ _)))).extendTapes Fin.castSuccEmb)).seq
      (ofDeterministic ((clearWork Bool).extendTapes (tapeEmb (Fin.last _)))))

/-- A tidy probabilistic machine padded to `K` work tapes and placed below a last work tape that
holds `w` throughout. -/
private theorem ComputesTidily.runsWords_padded {k K : ℕ} (hk : k ≤ K)
    {tm : MultiTapePTM k Bool State Operation} {w : List Bool} {t : ℕ}
    {program : ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}
    (h : tm.ComputesTidily x t program) :
    ((tm.extendTapes (Fin.castLEEmb hk)).extendTapes Fin.castSuccEmb).RunsWords
      x (Function.update (fun _ => []) (Fin.last K) w) [] t program
      (fun _ => Function.update (fun _ => []) (Fin.last K) w) id := by
  have hpre : (fun j : Fin K =>
      Function.update (fun _ : Fin (K + 1) => ([] : List Bool)) (Fin.last K) w
        (Fin.castSuccEmb j)) = fun _ => [] := by
    funext j
    simp [Fin.castSucc_ne_last]
  have h₀ : (tm.extendTapes (Fin.castLEEmb hk)).RunsWords x
      (fun j => Function.update (fun _ => []) (Fin.last K) w (Fin.castSuccEmb j))
      [] t program (fun _ _ => []) id := by
    rw [hpre]
    exact (h.extendTapes (Fin.castLEEmb hk)) []
  have hext := h₀.extendTapes (ws₀ := Function.update (fun _ => []) (Fin.last K) w) Fin.castSuccEmb
  have hpost : (fun (_ : List Bool) (l : Fin (K + 1)) =>
      (MultiTapeTM.partialInv Fin.castSuccEmb l).elim
        (Function.update (fun _ : Fin (K + 1) => ([] : List Bool)) (Fin.last K) w l)
        (fun _ => [])) =
      fun _ => Function.update (fun _ => []) (Fin.last K) w := by
    funext _ l
    induction l using Fin.lastCases with
    | last =>
      rw [MultiTapeTM.partialInv_eq_none Fin.castSuccEmb
        (fun ⟨j, hj⟩ => Fin.castSucc_ne_last j hj)]
      rfl
    | cast j =>
      change (MultiTapeTM.partialInv Fin.castSuccEmb (Fin.castSuccEmb j)).elim _ _ = _
      rw [MultiTapeTM.partialInv_embed]
      simp [Fin.castSucc_ne_last]
  simpa only [hpost] using hext

/-- If `tmc` computes the test word `w` from `x` tidily, `tm₁` computes `prog₁` tidily when
`w ≠ []` and `tm₂` computes `prog₂` tidily when `w = []`, then `itePTM tmc tm₁ tm₂` computes
`if w = [] then prog₂ else prog₁` tidily within the bounds of `tmc` plus those of the active
branch, never executing the unselected branch. -/
theorem ComputesTidily.ite {tmc : MultiTapePTM k₀ Bool State₀ Operation}
    {tm₁ : MultiTapePTM k₁ Bool State₁ Operation}
    {tm₂ : MultiTapePTM k₂ Bool State₂ Operation}
    {w : List Bool} {tc t₁ t₂ : ℕ}
    {prog₁ prog₂ : ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}
    (hc : tmc.ComputesTidily x tc (pure w))
    (h₁ : w ≠ [] → tm₁.ComputesTidily x t₁ prog₁)
    (h₂ : w = [] → tm₂.ComputesTidily x t₂ prog₂) :
    (itePTM tmc tm₁ tm₂).ComputesTidily x
      (tc + (if w = [] then t₂ else t₁) + 4 * w.length + 6)
      (if w = [] then prog₂ else prog₁) := by
  rw [computesTidily_iff_nil_output]
  set K := max k₀ (max k₁ k₂)
  let clearLast : MultiTapePTM (K + 1) Bool (Unit ⊕ RewindWorkState) Operation :=
    ofDeterministic ((clearWork Bool).extendTapes (tapeEmb (Fin.last K)))
  have hl : ∀ (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
      (s : OracleState) (w' : List Bool) (s' : OracleState),
      (w', s') ∈ ((OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (pure w)).run s).support → w'.length ≤ w.length := by
    intro _ _ _ w' s' hw'
    simp only [OracleComp.interpret_pure, StateT.run_pure,
      Probability.PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hw'
    rcases Prod.mk.inj hw' with ⟨rfl, rfl⟩
    exact le_rfl
  have hp₁ : (tmc.extendTapes (Fin.castLEEmb (le_max_left k₀ (max k₁ k₂)))).outputToWord.RunsWords
      x (fun _ => []) [] (tc + (w.length + 2)) (pure ())
      (fun _ => Function.update (fun _ => []) (Fin.last K) w) (fun _ => []) := by
    have h₀ := (hc.extendTapes (Fin.castLEEmb (le_max_left k₀ (max k₁ k₂)))).outputToWord_of_le
      hl []
    have hcongr : (tmc.extendTapes
        (Fin.castLEEmb (le_max_left k₀ (max k₁ k₂)))).outputToWord.RunsWords
        x (fun _ => []) [] (tc + (w.length + 2)) ((fun _ => w) <$> pure ())
        (fun w' => Function.update (fun _ => []) (Fin.last K) w') (fun _ => []) := by
      simpa only [map_pure] using h₀
    intro OracleState oracle s cfg htapes hbuf
    obtain ⟨hlaw, hclean⟩ := hcongr OracleState oracle s cfg htapes hbuf
    refine ⟨?_, hclean⟩
    simpa only [OracleComp.interpret_pure, OracleComp.interpret_map, StateT.run_pure,
      StateT.run_map, Probability.PMF.monad_pure_eq_pure, PMF.monad_map_eq_map, PMF.pure_map]
      using hlaw
  have hp₂ : (branch (Fin.last K)
      ((tm₁.extendTapes (Fin.castLEEmb ((le_max_left k₁ k₂).trans
        (le_max_right k₀ _)))).extendTapes Fin.castSuccEmb)
      ((tm₂.extendTapes (Fin.castLEEmb ((le_max_right k₁ k₂).trans
        (le_max_right k₀ _)))).extendTapes Fin.castSuccEmb)).RunsWords
      x (Function.update (fun _ => []) (Fin.last K) w) []
      ((if w = [] then t₂ else t₁) + 1)
      (if w = [] then prog₂ else prog₁)
      (fun _ => Function.update (fun _ => []) (Fin.last K) w) id := by
    by_cases hw : w = []
    · simp only [hw, ↓reduceIte]
      exact RunsWords.branch_nil (Fin.last K) _ (by simp)
        ((h₂ hw).runsWords_padded ((le_max_right k₁ k₂).trans (le_max_right k₀ _)))
    · simp only [hw, ↓reduceIte]
      exact RunsWords.branch_ne_nil (Fin.last K) _ (by simp [hw])
        ((h₁ hw).runsWords_padded ((le_max_left k₁ k₂).trans (le_max_right k₀ _)))
  have hinj₂ : Function.Injective
      (fun y : List Bool => (Function.update (fun _ => []) (Fin.last K) w, id y)) :=
    fun _ _ heq => congrArg Prod.snd heq
  have hp₃ : ∀ y (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
      (s s' : OracleState),
      (y, s') ∈ ((OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (if w = [] then prog₂ else prog₁)).run s).support →
      clearLast.RunsWords
        x (Function.update (fun _ => []) (Fin.last K) w) ([] ++ id y)
        (3 * (w.length + 1)) (pure ()) (fun _ _ => []) (fun _ => []) := by
    intro y _ _ _ _ _
    exact RunsWords.of_transformsTapes (Operation := Operation) (out₀ := [] ++ id y)
      (transformsTapes_clearWork_only (Fin.last K) w) rfl (fun _ _ hQ => hQ)
  have hp₂₃ := hp₂.seq_pure_right hinj₂ hp₃
  have happend : (fun a : List Bool => id a ++ []) = id := by
    funext a
    exact List.append_nil a
  rw [happend] at hp₂₃
  have hseq := (hp₁.seq_pure_left hp₂₃).mono
    (time' := tc + (if w = [] then t₂ else t₁) + 4 * w.length + 6)
    (by split_ifs <;> omega)
  dsimp only [itePTM]
  simpa only [List.nil_append] using hseq

end Turing.MultiTapePTM
