/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Algorithms.WordRAM.ElementDistinctness

/-!
# Word-RAM clients

Model regressions for the bounded-word RAM: overflow faults instead of wrapping, a program that
reads the word size can tell word sizes apart, the interpreter runs flat programs, the program
notation and `ram_eval` execute straight-line code symbolically, and the compiled element
distinctness program answers correctly on inputs with and without duplicates within its time
bound.
-/

namespace ComplexityTests.WordRAM

open Cslib.WordRAM

/-! ## The machine -/

/-- Writing `8` into a register faults at word size `3`, where words are below `8`, while `7`
fits. -/
example : run 3 [.op (.const (0 : Fin 1) 8), .halt 0] 5 (.init []) = none ∧
    run 3 [.op (.const (0 : Fin 1) 7), .halt 0] 5 (.init []) = some (7, 2) := by
  decide

/-- Adding past `2 ^ w` faults rather than wrapping around. -/
example :
    run 3 [.op (.const (0 : Fin 1) 5), .op (.bin .add 0 0 0), .halt 0] 5 (.init []) = none := by
  decide

/-- Running off the end of a program faults: a run must halt. -/
example : run 8 [.op (.const (0 : Fin 1) 5)] 5 (.init []) = none := by decide

/-- A program reading the word size tells word sizes apart. -/
example : run 4 [.op (.width (0 : Fin 1)), .halt 0] 5 (.init []) = some (4, 2) ∧
    run 5 [.op (.width (0 : Fin 1)), .halt 0] 5 (.init []) = some (5, 2) := by
  decide

/-- The input length is at address `0` and the words follow: this program halts with the length
after reading it through a register holding the address `0`. -/
example : run 8 [.op (.load (1 : Fin 2) 0), .halt 1] 5 (.init [5, 6, 7]) = some (3, 2) := by
  decide

example : Executes 8 [.op (.load (1 : Fin 2) 0), .halt 1] (.init [5, 6, 7]) 3 2 :=
  .of_run (fuel := 5) (by decide)

/-- Truncated subtraction, division by zero and the bitwise operations. -/
example : BinOp.sub.eval 3 5 = 0 ∧ BinOp.div.eval 7 0 = 0 ∧ BinOp.mod.eval 7 0 = 7 ∧
    BinOp.and.eval 6 3 = 2 ∧ BinOp.xor.eval 6 3 = 5 ∧ BinOp.shiftLeft.eval 3 2 = 12 := by
  decide

/-! ## Structured programs and notation -/

section Notation

/-- Register names for the examples. -/
abbrev a : Fin 3 := 0
/-- Register names for the examples. -/
abbrev b : Fin 3 := 1
/-- Register names for the examples. -/
abbrev c : Fin 3 := 2

/-- A straight-line program with a conditional and a store. -/
def straight : Code 3 := ram[
  b ← #5;
  c ← #7;
  c ← b + c;
  if b < c then [ c ← c - b ] else [ c ← #0 ];
  *b ← c ]

example : straight =
    .seq (.op (.const b 5)) (.seq (.op (.const c 7)) (.seq (.op (.bin .add c b c))
      (.seq (.branch (.lt b c) (.op (.bin .sub c c b)) (.op (.const c 0))) (.op (.store b c))))) :=
  rfl

/-- The interpreter counts the branch instruction of the taken alternative. -/
example : (straight.eval 8 0 (.init [])).map (·.2) = some 6 := by decide

/-- `ram_eval` executes the program symbolically on arbitrary data. -/
example (x : Data 3) : ∃ y, ExecWithin 8 straight x y 6 ∧ y.mem 5 = 7 := by
  refine ⟨?y, ?run, ?mem⟩
  case run => ram_eval [straight]
  case mem => simp

/-- A loop compiles to a branch, a jump out, the body and a jump back. -/
example : (ram[ while a < b do [ a ← a + c ] ] : Code 3).assemble 0 =
    [.branch (.lt a b) 2, .jump 4, .op (.bin .add a a c), .jump 0] := rfl

end Notation

/-! ## Element distinctness -/

section ElementDistinctness

open Cslib.Algorithms.WordRAM.ElementDistinctness

/-- Distinct entries: the compiled program answers `1`, within the bound `16 (n + 1)`. -/
example : (run 8 (program.program ans) 200 (.init [2, 0, 1])).map (·.1) = some 1 := by decide

/-- A duplicate: the compiled program answers `0`. -/
example : (run 8 (program.program ans) 200 (.init [1, 0, 1])).map (·.1) = some 0 := by decide

example : ∀ vn ∈ run 8 (program.program ans) 200 (.init [2, 0, 1]), vn.2 ≤ 16 * (3 + 1) := by
  decide

/-- The empty list has no duplicates. -/
example : (run 8 (program.program ans) 200 (.init [])).map (·.1) = some 1 := by decide

end ElementDistinctness

/-! ## Axioms -/

/--
info: 'Cslib.Algorithms.WordRAM.ElementDistinctness.linearTime_nodup' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Algorithms.WordRAM.ElementDistinctness.linearTime_nodup

/--
info: 'Cslib.WordRAM.Exec.runs' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.WordRAM.Exec.runs

/--
info: 'Cslib.WordRAM.DecidesInTime.of_code' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.WordRAM.DecidesInTime.of_code

/--
info: 'Cslib.WordRAM.DecidesInTime.at' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.WordRAM.DecidesInTime.at

/--
info: 'Cslib.WordRAM.Executes.mono' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.WordRAM.Executes.mono

/--
info: 'Cslib.WordRAM.executes_iff_run' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.WordRAM.executes_iff_run

/--
info: 'Cslib.WordRAM.ExecWithin.loop_invariant' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.WordRAM.ExecWithin.loop_invariant

/--
info: 'Cslib.WordRAM.Exec.rename' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.WordRAM.Exec.rename

/--
info: 'Cslib.WordRAM.alloc_exec' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.WordRAM.alloc_exec

end ComplexityTests.WordRAM
