/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Counting.Execution
public import Complexity.Computability.Machines.Turing.MultiTape.Machine.ExtendTapes

/-!
# Reserving work tapes without changing counts

The shared tape compiler maps each transition occurrence once. Extra tapes retain their
contents and head positions throughout the entire List execution, with the same native clock.

## Main results

* `Turing.MultiTapeCTM.runList_embed`: exact configuration occurrences under tape extension.
* `Turing.MultiTapeCTM.HaltsWithin.embed`: preserve the native all-branches clock.

## References

The shared compiler and its original source credit are in `MultiTape.Machine.ExtendTapes`.
-/

@[expose] public section

namespace Turing.MultiTapeCTM

open Cslib MultiTapeMachine

variable {k k' : ℕ} {Symbol State : Type} {input : List Symbol}

/-- Reindexing work tapes maps every transition occurrence once. -/
theorem Nonblocking.extendTapes {machine : MultiTapeCTM k Symbol State}
    (h : machine.Nonblocking) (e : Fin k ↪ Fin k') : Nonblocking (machine.extendTapes e) := by
  intro state symbol work
  simpa [MultiTapeMachine.extendTapes] using h state symbol (fun i => work (e i))

/-- Tape extension preserves the entire List, including unused tape contents and heads. -/
theorem runList_embed (machine : MultiTapeCTM k Symbol State) (e : Fin k ↪ Fin k')
    (cfg : Config k Symbol State Empty input)
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) (fuel : ℕ) :
    runList (machine.extendTapes e) fuel (cfg.embed e extraTapes extraPos).tapes =
      (machine.runList fuel cfg.tapes).map
        (fun final =>
          ((Config.emptyOracleEquiv.symm final).embed e extraTapes extraPos).tapes) := by
  have h := congrArg
    (OracleComp.interpret (fun n => List.ofFn (id : Fin n → Fin n)))
    (MultiTapeMachine.runConfigFrom_embed machine e chooseOccurrence chooseOccurrence_map
      Empty.elim cfg extraTapes extraPos fuel)
  have hm := congrArg (List.map Config.tapes) h
  simpa [interpret_runConfigFrom_eq_map_runList, OracleComp.interpret_map,
    List.map_map, Function.comp_def, Config.emptyOracleEquiv] using hm

/-- Nonblocking tape extension preserves the native clock, even with dirty unused tapes. -/
theorem HaltsWithin.embed {machine : MultiTapeCTM k Symbol State}
    (hnon : machine.Nonblocking) (e : Fin k ↪ Fin k')
    (cfg : Config k Symbol State Empty input)
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) (fuel : ℕ)
    (h : machine.HaltsWithin fuel cfg.tapes) :
    MultiTapeCTM.HaltsWithin (machine.extendTapes e) fuel
      (cfg.embed e extraTapes extraPos).tapes := by
  apply haltsWithin_of_halted _ (hnon.extendTapes e).actions_ne_nil
  intro final hfinal
  rw [runList_embed] at hfinal
  obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hfinal
  exact h.halted_of_mem_runList horiginal

end Turing.MultiTapeCTM
