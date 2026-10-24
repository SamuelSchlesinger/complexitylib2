/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Probabilistic.Oracle.Normalization

/-! Exact normalization retains storage and handles halted and empty-control configurations. -/

open Cslib Cslib.Probability Cslib.Turing Turing Turing.MultiTapeTM Turing.MultiTapeMachine

example {k : ℕ} {Control Operation : Type} [Fintype Operation] [DecidableEq Operation]
    [Finite Control] (machine : MultiTapePTM k Bool Control Operation) :
    IsTidyOraclePPTOn (encPair encUnary encFiniteConfig) encFiniteConfig
      (fun pair : ℕ × FiniteConfig k Bool Control Operation => machine.finiteStep
        (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
        (fun op word => List.take pair.1 <$> ProbOracleComp.query (op, word)) pair.2) :=
  IsTidyOraclePPTOn.finiteStep machine

-- Halting retains the entire configuration, including accumulated output and pending buffers.
example {k : ℕ} {Control Operation : Type} [DecidableEq Operation]
    (machine : MultiTapePTM k Bool Control Operation)
    (cfg : FiniteConfig k Bool Control Operation) (halted : cfg.tapes.state = none) (limit : ℕ) :
    machine.finiteStep
      (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
      (fun op word => List.take limit <$> ProbOracleComp.query
        (spec := fun _ : Operation × List Bool => List Bool) (op, word)) cfg = pure cfg := by
  simp only [MultiTapeMachine.finiteStep, halted]

-- Empty control and channel types remain valid, with no hidden nonemptiness hypothesis.
example (machine : MultiTapePTM 0 Bool Empty Empty) (cfg : FiniteConfig 0 Bool Empty Empty) :
    machine.finiteStep
      (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
      (fun op word => List.take 0 <$> ProbOracleComp.query
        (spec := fun _ : Empty × List Bool => List Bool) (op, word)) cfg = pure cfg := by
  have halted : cfg.tapes.state = none := by
    cases h : cfg.tapes.state with
    | none => rfl
    | some state => exact state.elim
  simp only [MultiTapeMachine.finiteStep, halted]

-- Zero clocks and degree zero are permitted; normalization preserves the original joint law.
example (machine : MultiTapePTM 0 Bool Unit Empty) :
    IsTidyOraclePPTOn encBits encBits
      (fun word : List Bool => machine.runOracle (0 * (word.length + 1) ^ 0) word) :=
  IsTidyOraclePPTOn.runOracle machine 0 0

/-- info: 'Cslib.Probability.isOraclePPTOn_iff_isTidyOraclePPTOn' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isOraclePPTOn_iff_isTidyOraclePPTOn
