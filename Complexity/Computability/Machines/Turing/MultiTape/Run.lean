/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (additions to `Configuration.lean` and `Deterministic.lean`)

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg

/-!
# Facts about runs of multi-tape machines

Small facts about configurations and runs that are not specific to any construction: the input
symbol under the head as a list lookup, the input head move on natural-number positions, the
contents of a work tape after an action as a case distinction, the distance a work head can
travel, and the initial configuration as a configuration of words.

## Main definitions

* `Turing.inputAt`: the symbol at a position of the input tape.
* `Turing.moveInputPosNat`: `Turing.moveInputPos` on positions as natural numbers.

## Main results

* `Turing.Cfg.inputSymbol_eq_inputAt`, `Turing.val_moveInputPos_eq_moveInputPosNat`.
* `Turing.Action.apply_workTapes_eq_ite`.
* `Turing.MultiTapeTM.abs_workTapePos_runFrom_le`: after `t` steps a work head is within `t` cells
  of the origin.
* `Turing.MultiTapeTM.initCfg_eq_wordsCfg`: the initial configuration has blank work tapes.
* `Turing.MultiTapeTM.runsInTime_iff_halted`, `Turing.MultiTapeTM.runsInSpace_iff`: the shared
  time and space bounds, read on the run of a deterministic machine.
-/

@[expose] public section

namespace Turing

variable {k : ℕ} {Symbol State : Type*}

/-! ### The input tape -/

/-- The symbol at position `j` of an input tape holding `x`: positions `0` and `x.length + 1` are
the blank end cells, and position `j + 1` holds `x[j]`. -/
def inputAt (x : List Symbol) (j : ℕ) : Option Symbol := if j = 0 then none else x[j - 1]?

theorem Cfg.inputSymbol_eq_inputAt {input : List Symbol} (cfg : Cfg k Symbol State input) :
    cfg.inputSymbol = inputAt input cfg.inputPos.val := by
  have hlt := cfg.inputPos.isLt
  by_cases h : cfg.inputPos.val = 0 ∨ cfg.inputPos.val = input.length + 1
  · rw [inputSymbol_eq_none_of_boundary h]
    rcases h with h | h <;> simp [inputAt, h]
  · push Not at h
    have hlt' : cfg.inputPos.val - 1 < input.length := by omega
    rw [inputSymbolInner (cfg.inputPos.val - 1) (by omega) hlt']
    simp [inputAt, h.1, List.getElem?_eq_getElem hlt']

/-- The input head position after a move `d` from position `j`, on an input of length `n`: the
head is clamped to `0, …, n + 1`. This is `Turing.moveInputPos` on positions as natural numbers. -/
def moveInputPosNat (n j : ℕ) (d : SignType) : ℕ :=
  (min ((n : ℤ) + 1) (max 0 ((j : ℤ) + (d : ℤ)))).toNat

theorem val_moveInputPos_eq_moveInputPosNat {n : ℕ} (pos : Fin (n + 2)) (d : SignType) :
    (moveInputPos pos d).val = moveInputPosNat n pos.val d := by
  have h := val_moveInputPos_eq pos d
  simp only [moveInputPosNat]
  omega

/-- A position on the input tape is reached by one move only from a neighbouring position. -/
theorem le_add_one_of_moveInputPosNat_eq {n j j' : ℕ} {d : SignType} (hj' : j' < n + 2)
    (h : moveInputPosNat n j' d = j) : j - 1 ≤ j' ∧ j' ≤ j + 1 := by
  subst h
  rcases d with _ | _ | _ <;>
    simp only [moveInputPosNat, SignType.zero_eq_zero, SignType.neg_eq_neg_one,
      SignType.pos_eq_one, SignType.coe_zero, SignType.coe_neg_one, SignType.coe_one] <;> omega

/-! ### Work tapes -/

/-- The contents of a work tape after applying an action: the written symbol under the head, if
the action writes one, and the old contents elsewhere. -/
theorem Action.apply_workTapes_eq_ite (a : Action k Symbol State) {input : List Symbol}
    (cfg : Cfg k Symbol State input) (i : Fin k) (z : ℤ) :
    (a.apply cfg).workTapes i z =
      if z = cfg.workTapePos i then ((a.workTapes i).1).getD (cfg.workTapes i z)
      else cfg.workTapes i z := by
  simp only [Action.apply_workTapes]
  rcases (a.workTapes i).1 with _ | s <;> split_ifs with hz <;> simp [hz]

namespace MultiTapeTM

variable {tm : MultiTapeTM k Symbol State}

/-- After `t` steps from the initial configuration, a work head is within `t` cells of the
origin. -/
theorem abs_workTapePos_runFrom_le (x : List Symbol) (t : ℕ) (i : Fin k) :
    |(tm.runFrom (tm.initCfg x) t).workTapePos i| ≤ t := by
  induction t with
  | zero => simp [runFrom]
  | succ t ih =>
    have h := workTapePos_step_le (tm := tm) (tm.runFrom (tm.initCfg x) t) i
    rw [runFrom_succ]
    rw [abs_le] at h ih ⊢
    push_cast
    omega

/-- The initial configuration is the configuration with the input and blank work tapes. -/
theorem initCfg_eq_wordsCfg (input : List Symbol) :
    tm.initCfg input = wordsCfg input (some tm.q₀) (fun _ => []) [] :=
  Cfg.init_eq_wordsCfg _ _

/-- One step of a run. -/
theorem runFrom_one {input : List Symbol} (c : Cfg k Symbol State input) :
    tm.runFrom c 1 = tm.step c :=
  rfl

/-- A deterministic machine satisfying the shared time bound `t` has halted after `t` steps. -/
theorem halted_of_runsInTime {input : List Symbol} {t : ℕ} (h : tm.RunsInTime input t) :
    (tm.runFrom (tm.initCfg input) t).Halted := by
  have := h (MultiTapeNTM.ComputationPath.ofDeterministic tm input t) le_rfl
  rwa [computationPath_last_eq_runFrom] at this

/-- A deterministic machine satisfies the shared time bound `t` exactly when it has halted after
`t` steps. -/
theorem runsInTime_iff_halted {input : List Symbol} {t : ℕ} :
    tm.RunsInTime input t ↔ (tm.runFrom (tm.initCfg input) t).Halted :=
  ⟨halted_of_runsInTime, runsInTime_of_halted⟩

/-- The space of the path of the first `t` steps is the space used by the run. -/
theorem space_ofDeterministic (input : List Symbol) (t : ℕ) :
    (MultiTapeNTM.ComputationPath.ofDeterministic tm input t).space =
      tm.spaceUsed (tm.initCfg input) t :=
  rfl

/-- A deterministic machine satisfying the shared space bound `s` uses at most `s` cells in every
prefix of its run. -/
theorem spaceUsed_le_of_runsInSpace {input : List Symbol} {s : ℕ} (h : tm.RunsInSpace input s)
    (t : ℕ) : tm.spaceUsed (tm.initCfg input) t ≤ s :=
  space_ofDeterministic (tm := tm) input t ▸ h _

/-- A deterministic machine satisfies the shared space bound `s` exactly when every prefix of its
run uses at most `s` cells. -/
theorem runsInSpace_iff {input : List Symbol} {s : ℕ} :
    tm.RunsInSpace input s ↔ ∀ t, tm.spaceUsed (tm.initCfg input) t ≤ s := by
  refine ⟨spaceUsed_le_of_runsInSpace, fun h p => ?_⟩
  rw [p.eq_ofDeterministic, space_ofDeterministic]
  exact h _

end MultiTapeTM

end Turing
