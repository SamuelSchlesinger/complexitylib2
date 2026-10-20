/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.WordRAM.RAMInput

/-!
# Word-RAM to RAM compiler boundary clients

Exercise source-register aliasing on indirect accesses, all equality and strict-order outcomes,
explicit halting with zero, and the length information lost by bare RAM input lists. These are
clients of the executable compiler and its proved padded and prepared input cost bounds.
-/

namespace ComplexityTests.WordRAMRAM

open Cslib Cslib.WordRAM

private def targetResult {r : ℕ} (p : Program r) (input : List ℕ) : ℕ × Bool :=
  let q := ToRAM.paddedProgram p
  let s := RAM.run q 40 (RAM.State.init (ToRAM.paddedInput r input))
  (s.regs.output, decide (s.isHalted q))

private def selfLoad : Program 1 := [.op (.const 0 1), .op (.load 0 0), .halt 0]

private def selfStore : Program 1 :=
  [.op (.const 0 1), .op (.store 0 0), .op (.load 0 0), .halt 0]

/-- The destination of a load may also hold its address. -/
example : targetResult selfLoad [7] = (7, true) := by decide

/-- A store may use the same source register for its address and value. -/
example : targetResult selfStore [7] = (1, true) := by decide

/-- The quantitative theorem applies to the aliasing load client. -/
example : RAM.HaltsWithResultInTime RAM.logCost (ToRAM.paddedProgram selfLoad)
    (ToRAM.paddedInput 1 [7]) 7 (8 * (RAM.bitLength 6 + 1) * 4 * 4) :=
  ToRAM.haltsWithResultInTime_padded (by decide) (w := 3) (by decide)
    (Executes.of_run (fuel := 5) (by decide))

private def compare (c : Cond 2) (a b : ℕ) : Program 2 :=
  [.op (.const 0 a), .op (.const 1 b), .branch c 5, .op (.const 0 0), .halt 0,
    .op (.const 0 1), .halt 0]

/-- Equality checks both truncated differences; either strict ordering must take the false arm. -/
example : targetResult (compare (.eq 0 1) 0 1) [] = (0, true) ∧
    targetResult (compare (.eq 0 1) 1 0) [] = (0, true) ∧
    targetResult (compare (.eq 0 1) 1 1) [] = (1, true) := by decide

/-- Strict order distinguishes equality from a positive difference. -/
example : targetResult (compare (.lt 0 1) 0 1) [] = (1, true) ∧
    targetResult (compare (.lt 0 1) 1 0) [] = (0, true) ∧
    targetResult (compare (.lt 0 1) 1 1) [] = (0, true) := by decide

/-- The target halts even when the output is zero: its final jump uses the permanent one. -/
example : targetResult [.halt (0 : Fin 1)] [] = (0, true) := by decide

/-- Zero-bit words are allowed: the empty input and the initial zero output fit. -/
example : RAM.HaltsWithResultInTime RAM.logCost (ToRAM.paddedProgram [.halt (0 : Fin 1)])
    (ToRAM.paddedInput 1 []) 0 (8 * (RAM.bitLength 6 + 1) * 2) := by
  simpa [ToRAM.memoryBase] using
    ToRAM.haltsWithResultInTime_padded (p := [.halt (0 : Fin 1)]) (by decide)
      (input := []) (w := 0) (v := 0) (n := 1) (by decide)
      (Executes.of_run (fuel := 1) (by decide))

/-- Charged preparation also works at width zero, despite its natural-number scratch values. -/
example : RAM.HaltsWithResultInTime RAM.logCost (ToRAM.preparedProgram [.halt (0 : Fin 1)])
    (RAM.Input.encode 5 []) 0 (212 * 2) :=
  ToRAM.haltsWithResultInTime_prepared (p := [.halt (0 : Fin 1)]) (by decide)
    (input := []) (w := 0) (v := 0) (n := 1) (by decide)
    (Executes.of_run (fuel := 1) (by decide))

/-- The uniform charged bound handles an indirect load after overlapping input relocation. -/
example : RAM.HaltsWithResultInTime RAM.logCost (ToRAM.preparedProgram selfLoad)
    (RAM.Input.encode 5 [7]) 7 (212 * 5 * 4) :=
  ToRAM.haltsWithResultInTime_prepared (by decide) (w := 3) (by decide)
    (Executes.of_run (fuel := 5) (by decide))

/-- The forward theorem intentionally does not reflect source faults. -/
example : run 1 [.op (.const (0 : Fin 1) 2), .halt 0] 4 (.init []) = none ∧
    targetResult [.op (.const (0 : Fin 1) 2), .halt 0] [] = (2, true) := by decide

/-- Falling off an empty source program faults; running off the target program halts. -/
example : run 0 ([] : Program 1) 1 (.init []) = none ∧
    targetResult ([] : Program 1) [] = (0, true) := by decide

/-- Bare RAM input lists do not retain their length when they end in zero. -/
example : RAM.State.init [] = RAM.State.init [0] := by
  apply RAM.State.ext
  · rfl
  · funext i
    cases i <;> rfl

/-- WordRAM's length header distinguishes the same two inputs. -/
example : (State.init [] : State 1) ≠ State.init [0] := by
  intro h
  have := congrArg (fun s : State 1 => s.data.mem 0) h
  simp [State.init] at this

/--
info: 'Cslib.WordRAM.ToRAM.executes_compile' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.WordRAM.ToRAM.executes_compile

/--
info: 'Cslib.WordRAM.ToRAM.haltsWithResultInTime_padded' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.WordRAM.ToRAM.haltsWithResultInTime_padded

/--
info: 'Cslib.WordRAM.ToRAM.haltsWithResultInTime_prepared' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.WordRAM.ToRAM.haltsWithResultInTime_prepared

end ComplexityTests.WordRAMRAM
