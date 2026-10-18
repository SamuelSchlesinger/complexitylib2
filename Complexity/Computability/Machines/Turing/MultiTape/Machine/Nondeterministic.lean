/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Machine.Equivalence
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape

/-!
# Fair-coin machines as nondeterministic machines

A closed fair-coin table offers one action for each coin at every running configuration. Its
nondeterministic machine `Turing.MultiTapePTM.toNTM` may take either action. A step of this
machine is a step of the table under some coin, and a halted configuration steps only to itself
on both sides. Hence the run paths of length `n` are exactly the replays of coin lists of length
`n`, and the configurations supported by a closed fair-coin run with clock `n` are exactly the
last configurations of these run paths.

In particular, a fair-coin machine that halts on every supported branch within its clock runs
within the same time as a nondeterministic machine, and its supported outputs are the outputs of
its computation paths.

## Main definitions

* `Turing.MultiTapePTM.toNTM`: the nondeterministic machine of a closed fair-coin table.

## Main results

* `Turing.MultiTapePTM.step_toNTM_iff`: a step is a deterministic step under some coin.
* `Turing.MultiTapePTM.exists_step_toNTM`: no configuration is stuck.
* `Turing.MultiTapePTM.exists_runPath_toNTM_iff`: run paths are the replays of coin lists.
* `Turing.MultiTapePTM.mem_support_runClosedConfigFrom_iff`: supported configurations are the last
  configurations of run paths of clock length.
* `Turing.MultiTapePTM.runsInTime_toNTM`: halting on every supported branch is a time bound.
-/

@[expose] public section

/-- A configuration without communication channels is determined by its tapes. -/
theorem Turing.MultiTapeMachine.Config.eq_iff_tapes_eq {k : ℕ} {Symbol State : Type}
    {input : List Symbol} {cfg cfg' : Config k Symbol State Empty input} :
    cfg = cfg' ↔ cfg.tapes = cfg'.tapes :=
  Config.emptyOracleEquiv.injective.eq_iff.symm

namespace Turing.MultiTapePTM

open Cslib MultiTapeMachine

variable {k : ℕ} {Symbol State : Type} {input : List Symbol}

/-- The nondeterministic machine of a closed fair-coin table: at a running configuration, it may
take the action selected by either coin. -/
def toNTM (machine : MultiTapePTM k Symbol State) : MultiTapeNTM k Symbol State where
  q₀ := machine.initial
  Tr state symbol work action := ∃ bit, (machine.withCoin bit).toTM.Tr state symbol work action

variable (machine : MultiTapePTM k Symbol State)

/-- The nondeterministic machine starts where the fair-coin table does. -/
theorem initCfg_toNTM (input : List Symbol) :
    machine.toNTM.initCfg input = (machine.initialConfig input).tapes := rfl

/-- A step of the nondeterministic machine is a deterministic step under some coin. -/
theorem step_toNTM_iff {c c' : Cfg k Symbol State input} :
    machine.toNTM.Step c c' ↔ ∃ bit, (machine.withCoin bit).toTM.step c = c' := by
  simp only [← MultiTapeTM.step_iff, MultiTapeNTM.Step]
  cases c.state with
  | none => simp
  | some state => simp only [toNTM]; grind

/-- The nondeterministic machine of a fair-coin table is never stuck: every configuration has a
successor. -/
theorem exists_step_toNTM (c : Cfg k Symbol State input) : ∃ c', machine.toNTM.Step c c' :=
  ⟨_, (machine.step_toNTM_iff).mpr ⟨false, rfl⟩⟩

/-- One deterministic step under each coin of a list, on upstream configurations. -/
noncomputable def stepCoins (coins : List Bool) (c : Cfg k Symbol State input) :
    Cfg k Symbol State input :=
  coins.foldl (fun c bit => (machine.withCoin bit).toTM.step c) c

/-- Replaying coins acts on the tapes by upstream deterministic steps. -/
theorem tapes_runClosedConfigFromCoins (coins : List Bool)
    (cfg : Config k Symbol State Empty input) :
    (machine.runClosedConfigFromCoins coins cfg).tapes = machine.stepCoins coins cfg.tapes := by
  induction coins generalizing cfg with
  | nil => rfl
  | cons bit coins ih =>
    rw [stepCoins, List.foldl_cons, ← step_toTM]
    exact ih _

/-- **Run paths are coin replays.** The nondeterministic machine has a run path of length `n` from
`c` to `c'` exactly when some coin list of length `n` replays `c` to `c'`. Halted configurations
ignore their coins and step only to themselves. -/
theorem exists_runPath_toNTM_iff {c c' : Cfg k Symbol State input} {n : ℕ} :
    (∃ p : machine.toNTM.RunPath input, p.head = c ∧ p.length = n ∧ p.last = c') ↔
      ∃ coins : List Bool, coins.length = n ∧ machine.stepCoins coins c = c' := by
  constructor
  · rintro ⟨p, rfl, rfl, rfl⟩
    induction p using RelSeries.inductionOn' with
    | singleton c => exact ⟨[], rfl, rfl⟩
    | snoc p c hc ih =>
      obtain ⟨coins, hlen, hcoins⟩ := ih
      obtain ⟨bit, hbit⟩ := (machine.step_toNTM_iff).mp hc
      refine ⟨coins ++ [bit], by simp [hlen], ?_⟩
      simp only [RelSeries.head_snoc, RelSeries.last_snoc, stepCoins, List.foldl_append,
        List.foldl_cons, List.foldl_nil] at hcoins ⊢
      rw [hcoins, hbit]
  · rintro ⟨coins, rfl, rfl⟩
    induction coins generalizing c with
    | nil => exact ⟨RelSeries.singleton _ c, rfl, rfl, rfl⟩
    | cons bit coins ih =>
      obtain ⟨p, hhead, hlen, hlast⟩ := ih (c := (machine.withCoin bit).toTM.step c)
      have hstep : machine.toNTM.Step c p.head :=
        (machine.step_toNTM_iff).mpr ⟨bit, hhead.symm⟩
      exact ⟨p.cons c hstep, rfl, by simp [hlen], by simp [hlast, stepCoins]⟩

/-- **Supported configurations are endpoints of run paths.** A configuration is supported by the
closed fair-coin run with clock `fuel` exactly when the nondeterministic machine has a run path of
length `fuel` to it. -/
theorem mem_support_runClosedConfigFrom_iff {fuel : ℕ}
    {cfg final : Config k Symbol State Empty input} :
    final ∈ (ProbComp.eval (machine.runClosedConfigFrom fuel cfg)).support ↔
      ∃ p : machine.toNTM.RunPath input, p.head = cfg.tapes ∧ p.length = fuel ∧
        p.last = final.tapes := by
  rw [exists_runPath_toNTM_iff, eval_runClosedConfigFrom_eq_map_coins, PMF.mem_support_map_iff]
  simp only [BitString.mem_support_uniformList_iff, Config.eq_iff_tapes_eq,
    tapes_runClosedConfigFromCoins]

/-- **Halting on every branch is a time bound.** If every configuration supported by the closed
fair-coin run with clock `t` is halted, then every computation path of the nondeterministic
machine with at least `t` steps ends halted. -/
theorem runsInTime_toNTM {t : ℕ}
    (h : ∀ final ∈ (ProbComp.eval (machine.runClosedConfigFrom t
      (machine.initialConfig input))).support, final.tapes.state = none) :
    machine.toNTM.RunsInTime input t := by
  intro p hp
  have ht : t < p.length + 1 := Nat.lt_succ_of_le hp
  have hmem := (machine.mem_support_runClosedConfigFrom_iff (cfg := machine.initialConfig input)
    (final := Config.emptyOracleEquiv.symm (p.toRunPath ⟨t, ht⟩))).mpr
    ⟨p.toRunPath.take ⟨t, ht⟩, by rw [RelSeries.head_take]; exact p.head_eq, rfl,
      RelSeries.last_take _ _⟩
  have hhalt : (p.toRunPath ⟨t, ht⟩).Halted := h _ hmem
  exact (MultiTapeNTM.RunPath.last_eq_of_halted p.toRunPath _ hhalt) ▸ hhalt

/-- The last configurations of computation paths of length `t` are the configurations supported
by the closed fair-coin run with clock `t`. -/
theorem exists_computationPath_toNTM_iff {t : ℕ} {P : Cfg k Symbol State input → Prop} :
    (∃ p : machine.toNTM.ComputationPath input, p.time = t ∧ P p.last) ↔
      ∃ final ∈ (ProbComp.eval (machine.runClosedConfigFrom t
        (machine.initialConfig input))).support, P final.tapes := by
  constructor
  · rintro ⟨p, rfl, hP⟩
    exact ⟨Config.emptyOracleEquiv.symm p.last, (machine.mem_support_runClosedConfigFrom_iff).mpr
      ⟨p.toRunPath, p.head_eq, rfl, rfl⟩, hP⟩
  · rintro ⟨final, hfinal, hP⟩
    obtain ⟨p, hhead, hlen, hlast⟩ := (machine.mem_support_runClosedConfigFrom_iff).mp hfinal
    exact ⟨⟨p, hhead⟩, hlen, hlast ▸ hP⟩

end Turing.MultiTapePTM
