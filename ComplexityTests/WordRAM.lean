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
example : run (B := .standard) 3 [.op (.const (0 : Fin 1) 8), .halt 0] 5 (.init []) = none ∧
    run (B := .standard) 3 [.op (.const (0 : Fin 1) 7), .halt 0] 5 (.init []) = some (7, 2) := by
  decide

/-- Adding past `2 ^ w` faults rather than wrapping around. -/
example :
    run 3 [.op (.const (0 : Fin 1) 5), .op (.bin .add 0 0 0), .halt 0] 5 (.init []) = none := by
  decide

/-- Running off the end of a program faults: a run must halt. -/
example : run (B := .standard) 8 [.op (.const (0 : Fin 1) 5)] 5 (.init []) = none := by decide

/-- A program reading the word size tells word sizes apart. -/
example : run 4 [.op (.width (0 : Fin 1)), .halt 0] 5 (.init []) = some (4, 2) ∧
    run 5 [.op (.width (0 : Fin 1)), .halt 0] 5 (.init []) = some (5, 2) := by
  decide

/-- The input length is at address `0` and the words follow: this program halts with the length
after reading it through a register holding the address `0`. -/
example :
    run (B := .standard) 8 [.op (.load (1 : Fin 2) 0), .halt 1] 5 (.init [5, 6, 7]) =
      some (3, 2) := by
  decide

example :
    Executes (B := .standard) 8 [.op (.load (1 : Fin 2) 0), .halt 1] (.init [5, 6, 7]) 3 2 :=
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
def straight : Code .standard 3 := ram[
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

/-- `ram_eval` at a symbolic word size, from facts stated with `Fits`. -/
example (w : ℕ) (x : Data 3) (h5 : Fits w 5) (h7 : Fits w 7) (h12 : Fits w 12) :
    ∃ y, ExecWithin w straight x y 6 ∧ y.mem 5 = 7 := by
  refine ⟨?y, ?run, ?mem⟩
  case run => ram_eval [straight, h5, h7, h12]
  case mem => simp

/-- Counting to three in a loop. -/
def count : Code .standard 3 := ram[ a ← #0; b ← #3; c ← #1; while a < b do [ a ← a + c ] ]

/-- `ram_eval` with three loop iterations: three constants, three iterations of an addition, a
branch and a jump, and a branch and a jump to leave the loop. -/
example (x : Data 3) : ∃ y, Exec 8 count x y 14 ∧ y.regs a = 3 := by
  refine ⟨?y, ?run, ?val⟩
  case run => ram_eval 3 [count]
  case val => simp

/-- A loop compiles to a branch, a jump out, the body and a jump back. -/
example : (ram[ while a < b do [ a ← a + c ] ] : Code .standard 3).assemble 0 =
    [.branch (.lt a b) 2, .jump 4, .op (.bin .add a a c), .jump 0] := rfl

/-- Reading the word size. -/
example :
    ((ram[ a ← width% ] : Code .standard 3).eval 7 0 (.init [])).map (·.1.regs a) = some 7 := by
  decide

/-- Registers a program never writes keep their contents; `Code.Preserves` is decidable. -/
example {w n : ℕ} {x y : Data 3} (h : Exec w straight x y n) : y.regs a = x.regs a :=
  h.regs_eq (by decide)

/-- The notation reserves no identifiers. -/
example (ram width : ℕ) : ram + width = width + ram := Nat.add_comm _ _

end Notation

/-! ## Running a program on other registers -/

section Rename

/-- Register names for a two-register program. -/
abbrev p : Fin 2 := 0
/-- Register names for a two-register program. -/
abbrev q : Fin 2 := 1

/-- A two-register program. -/
def double : Code .standard 2 := ram[ p ← #3; q ← p + p ]

/-- `double` runs on registers `2` and `0` of a three-register machine and leaves register `1`
alone, with the same instruction count. -/
example (x : Data 3) : ∃ y, Exec 8 (double.rename ![2, 0]) x y 2 ∧
    y.regs 2 = 3 ∧ y.regs 0 = 6 ∧ y.regs 1 = x.regs 1 := by
  have hf : Function.Injective (![2, 0] : Fin 2 → Fin 3) := by decide
  have e : Exec 8 double (x.comap ![2, 0]) (((x.comap ![2, 0]).set p 3).set q 6) 2 := by
    ram_eval [double]
  refine ⟨_, e.rename hf, ?_, ?_, ?_⟩
  · exact hf.extend_apply _ _ (0 : Fin 2)
  · exact hf.extend_apply _ _ (1 : Fin 2)
  · exact Function.extend_apply' _ _ _ (by decide)

end Rename

/-! ## Contract boundaries

These adversarial clients record the scope of the conditional time predicates. In particular,
word-count size alone does not bound input bit lengths, and an input-dependent prescribed width
can communicate information that the encoding does not contain.
-/

section Contracts

/-- The word size itself supplies the answer on two identically encoded instances. -/
private def widthAdvice : Program .standard 2 :=
  [.op (.width 0), .op (.const 1 1), .op (.bin .sub 0 0 1), .halt 0]

example :
    (∀ b : Bool, InputFits (if b then 2 else 1) []) ∧
    DecidableInTimeAt .standard {b : Bool | b = true} (fun _ => [])
      (fun _ => 4) (fun b => if b then 2 else 1) := by
  refine ⟨fun b => ⟨fits_zero _, by simp⟩, 2, widthAdvice, ?_⟩
  intro b _
  cases b
  · exact ⟨0, 4, .of_run (fuel := 4) (by decide), le_rfl, by decide, by decide⟩
  · exact ⟨1, 4, .of_run (fuel := 4) (by decide), le_rfl, by decide, by decide⟩

/-- No uniform decider separates the same two instances: at a common fitting width its initial
state is identical. Thus the unrestricted prescribed-width-to-uniform converse is false. -/
example (time bits : Bool → ℕ) :
    ¬DecidableInTime .standard {b : Bool | b = true} (fun _ => []) time bits := by
  rintro ⟨r, p, hp⟩
  let w := max (bits false) (bits true)
  have hi : InputFits w [] := ⟨fits_zero w, by simp⟩
  obtain ⟨v₀, n₀, he₀, _, _, hb₀⟩ := hp false w (le_max_left _ _) hi
  obtain ⟨v₁, n₁, he₁, _, _, hb₁⟩ := hp true w (le_max_right _ _) hi
  have hv := (he₀.unique he₁).1
  have h1 : v₁ = 1 := hb₁.mpr rfl
  have : false = true := hb₀.mp (hv.trans h1)
  cases this

/-- If the prescribed width never fits the input, the conditional contract accepts any set
without a successful run. -/
example (A : Set Bool) :
    DecidableInTimeAt .standard A (fun _ => [1]) (fun _ => 0) (fun _ => 0) := by
  refine ⟨0, [], ?_⟩
  intro b hi
  have h := hi.1
  change 1 < 1 at h
  exact False.elim (Nat.lt_irrefl 1 h)

/-- A constant-answer program works at every fitting width for arbitrary singleton words. -/
private def accept : Program .standard 1 := [.op (.const 0 1), .halt 0]

example : LinearTime .standard (Set.univ : Set ℕ) (fun n => [n]) (fun _ => 1) := by
  refine ⟨1, 0, 1, accept, ?_⟩
  intro n w _ hi
  have h1 : Fits w 1 := hi.1
  refine ⟨1, 2, .of_run (fuel := 2) ?_, le_rfl, le_rfl, by simp⟩
  simp [run, step, accept, Op.eval, Data.put, h1, Data.set, State.init]

/-- The encoding above is injective and has constant word-count size, but no width depending
only on that size can fit all its instances. -/
example (w : ℕ) : Function.Injective (fun n : ℕ => [n]) ∧ ¬∀ n, InputFits w [n] := by
  refine ⟨fun _ _ h => List.singleton_injective h, ?_⟩
  intro h
  have hi := (h (2 ^ w)).2 (2 ^ w) (by simp)
  exact Nat.lt_irrefl _ hi

end Contracts

/-! ## Element distinctness -/

section ElementDistinctness

open Cslib.Algorithms.WordRAM.ElementDistinctness Cslib.Algorithms.WordRAM.ElementDistinctness.Reg

/-- Distinct entries: the compiled decider answers `1`. -/
example : (run 8 (decider.program ans) 200 (.init [2, 0, 1])).map (·.1) = some 1 := by decide

/-- A duplicate: the compiled decider answers `0`. -/
example : (run 8 (decider.program ans) 200 (.init [1, 0, 1])).map (·.1) = some 0 := by decide

/-- The empty list has no duplicates. -/
example : (run 8 (decider.program ans) 200 (.init [])).map (·.1) = some 1 := by decide

/-- At the threshold word size `2 (⌊log₂ 3⌋ + 1) = 4`, the decider answers within its bound
`16 (n + 1)`; at word size `2` it faults. -/
example : logWidth 2 3 = 4 ∧ run 4 (decider.program ans) 200 (.init [2, 0, 1]) = some (1, 58) ∧
    58 ≤ 16 * (3 + 1) ∧ run 2 (decider.program ans) 200 (.init [2, 0, 1]) = none := by
  decide

/-- Neither the decider nor its compiled program reads the word size. -/
example : ¬decider.ReadsWidth ∧ ¬(decider.program ans).ReadsWidth := by decide

/-- The client has an input-fit certificate at its actual logarithmic threshold, so its
correctness contract gives an unconditional answer there for every promised instance. -/
example (a : Input) :
    (decider.program ans).Answers (logWidth 2 a.1.length) a.1 a.1.Nodup
      (16 * (a.1.length + 1)) :=
  decidesInTime_nodup a _ le_rfl (inputFits a le_rfl)

/-- The one-digit convention includes the empty input at its advertised threshold. -/
example : logWidth 2 0 = 2 ∧ InputFits (logWidth 2 0) [] ∧
    (run (logWidth 2 0) (decider.program ans) 16 (.init [])).map (·.1) = some 1 := by
  decide

/-- The decider also decides at any word size above its threshold, which it may read, and element
distinctness for small entries is in polynomial time. -/
example : (decider.program ans).DecidesInTimeAt (fun l : Input => l.1) {l | l.1.Nodup}
      (fun l => 16 * (l.1.length + 1)) (fun l => logWidth 2 l.1.length + 7) ∧
    PolynomialTime .standard {l : Input | l.1.Nodup} (fun l => l.1) (fun l => l.1.length) :=
  ⟨decidesInTime_nodup.decidesInTimeAt fun _ => Nat.le_add_right _ _,
    linearTime_nodup.polynomialTime⟩

end ElementDistinctness

/-! ## Axioms -/

/--
info: 'Cslib.Algorithms.WordRAM.ElementDistinctness.decidesInTime_nodup' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Algorithms.WordRAM.ElementDistinctness.decidesInTime_nodup

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
info: 'Cslib.WordRAM.DecidableInTime.of_code' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.WordRAM.DecidableInTime.of_code

/--
info: 'Cslib.WordRAM.DecidableInTime.decidableInTimeAt' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.WordRAM.DecidableInTime.decidableInTimeAt

/--
info: 'Cslib.WordRAM.Executes.mono_width' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.WordRAM.Executes.mono_width

/--
info: 'Cslib.WordRAM.executes_iff_exists_run_eq' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.WordRAM.executes_iff_exists_run_eq

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
