/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Structured

/-!
# Notation for structured word-RAM programs

`ram[ s₁; s₂; … ]` writes a structured program (`Cslib.WordRAM.Code`) as a sequence of statements,
one per data instruction, in the style of word-RAM pseudocode. Registers are named by identifiers,
for instance local abbreviations of elements of `Fin r`. The statements are:

* `d ← #v`: set register `d` to the constant `v`;
* `d ← s`: copy register `s` into register `d`;
* `d ← i + j`, and likewise `-`, `*`, `/`, `%`, `&&&`, `|||`, `^^^`, `<<<`, `>>>`: a binary
  operation (`Cslib.WordRAM.BinOp`) on registers `i` and `j`;
* `d ← *a`, `*a ← s`: load from and store to the memory cell whose address is in register `a`;
* `if i = j then [ … ] else [ … ]`, `if i < j then [ … ] else [ … ]`: a conditional;
* `while i = j do [ … ]`, `while i < j do [ … ]`: a loop;
* `⟪c⟫`: the structured program `c`, for instance a subroutine.

The notation unfolds to the constructors of `Cslib.WordRAM.Code`, so it adds nothing to the
semantics. It is scoped: `open Cslib.WordRAM` enables it. Its statements follow the word-RAM
syntax of Shreyas Srinivas's Algolean library. Registers are identifiers and the statement forms
use no identifier-like keywords, so the notation reserves no names.

## Tactics

* `ram_eval`: symbolically executes loop-free structured code. On a goal
  `Cslib.WordRAM.ExecWithin w c x y T`, it runs the interpreter `Cslib.WordRAM.Code.eval` on `c`
  and `x` with `simp`, using the given simp lemmas to decide which constants and results fit a
  word, and closes the goal when the result is `y` within `T` instructions; with `y` a
  metavariable, it determines `y`. Programs given by name must be unfolded by passing their
  definitions among the simp lemmas, as in `ram_eval [myProgram, h]`.
-/

public section

namespace Cslib.WordRAM

/-- A statement of a structured word-RAM program. -/
declare_syntax_cat wramStmt

/-- A block of statements, separated by semicolons. -/
syntax wramBlock := "[" sepBy1(wramStmt, "; ") "]"

/-- A structured word-RAM program, written as a block of statements. -/
scoped syntax "ram" wramBlock : term

/-- Internal: a single statement, as a structured program. -/
scoped syntax "ram_stmt%" wramStmt : term

/-- Set a register to a constant. -/
syntax ident " ← " "#" term:max : wramStmt
/-- Copy a register. -/
syntax ident " ← " ident : wramStmt
/-- Addition. -/
syntax ident " ← " ident " + " ident : wramStmt
/-- Truncated subtraction. -/
syntax ident " ← " ident " - " ident : wramStmt
/-- Multiplication. -/
syntax ident " ← " ident " * " ident : wramStmt
/-- Division. -/
syntax ident " ← " ident " / " ident : wramStmt
/-- Remainder. -/
syntax ident " ← " ident " % " ident : wramStmt
/-- Bitwise and. -/
syntax ident " ← " ident " &&& " ident : wramStmt
/-- Bitwise or. -/
syntax ident " ← " ident " ||| " ident : wramStmt
/-- Bitwise exclusive or. -/
syntax ident " ← " ident " ^^^ " ident : wramStmt
/-- Shift left. -/
syntax ident " ← " ident " <<< " ident : wramStmt
/-- Shift right. -/
syntax ident " ← " ident " >>> " ident : wramStmt
/-- Load from the memory cell whose address is in a register. -/
syntax ident " ← " "*" ident : wramStmt
/-- Store to the memory cell whose address is in a register. -/
syntax "*" ident " ← " ident : wramStmt
/-- A conditional on the equality of two registers. -/
syntax "if " ident " = " ident " then " wramBlock " else " wramBlock : wramStmt
/-- A conditional on the comparison of two registers. -/
syntax "if " ident " < " ident " then " wramBlock " else " wramBlock : wramStmt
/-- A loop while two registers are equal. -/
syntax "while " ident " = " ident " do " wramBlock : wramStmt
/-- A loop while one register is smaller than another. -/
syntax "while " ident " < " ident " do " wramBlock : wramStmt
/-- A structured program given as a term. -/
syntax "⟪" term "⟫" : wramStmt

macro_rules
  | `(ram [ $s:wramStmt ]) => `(ram_stmt% $s)
  | `(ram [ $s:wramStmt; $ss;* ]) => `(Cslib.WordRAM.Code.seq (ram_stmt% $s) (ram [ $ss;* ]))

macro_rules
  | `(ram_stmt% $d:ident ← #$v) => `(Cslib.WordRAM.Code.op (.const $d $v))
  | `(ram_stmt% $d:ident ← $s:ident) => `(Cslib.WordRAM.Code.op (.copy $d $s))
  | `(ram_stmt% $d:ident ← $i:ident + $j:ident) =>
    `(Cslib.WordRAM.Code.op (.bin .add $d $i $j))
  | `(ram_stmt% $d:ident ← $i:ident - $j:ident) =>
    `(Cslib.WordRAM.Code.op (.bin .sub $d $i $j))
  | `(ram_stmt% $d:ident ← $i:ident * $j:ident) =>
    `(Cslib.WordRAM.Code.op (.bin .mul $d $i $j))
  | `(ram_stmt% $d:ident ← $i:ident / $j:ident) =>
    `(Cslib.WordRAM.Code.op (.bin .div $d $i $j))
  | `(ram_stmt% $d:ident ← $i:ident % $j:ident) =>
    `(Cslib.WordRAM.Code.op (.bin .mod $d $i $j))
  | `(ram_stmt% $d:ident ← $i:ident &&& $j:ident) =>
    `(Cslib.WordRAM.Code.op (.bin .and $d $i $j))
  | `(ram_stmt% $d:ident ← $i:ident ||| $j:ident) =>
    `(Cslib.WordRAM.Code.op (.bin .or $d $i $j))
  | `(ram_stmt% $d:ident ← $i:ident ^^^ $j:ident) =>
    `(Cslib.WordRAM.Code.op (.bin .xor $d $i $j))
  | `(ram_stmt% $d:ident ← $i:ident <<< $j:ident) =>
    `(Cslib.WordRAM.Code.op (.bin .shiftLeft $d $i $j))
  | `(ram_stmt% $d:ident ← $i:ident >>> $j:ident) =>
    `(Cslib.WordRAM.Code.op (.bin .shiftRight $d $i $j))
  | `(ram_stmt% $d:ident ← *$a:ident) => `(Cslib.WordRAM.Code.op (.load $d $a))
  | `(ram_stmt% *$a:ident ← $s:ident) => `(Cslib.WordRAM.Code.op (.store $a $s))
  | `(ram_stmt% if $i:ident = $j:ident then $p:wramBlock else $n:wramBlock) =>
    `(Cslib.WordRAM.Code.branch (.eq $i $j) (ram $p) (ram $n))
  | `(ram_stmt% if $i:ident < $j:ident then $p:wramBlock else $n:wramBlock) =>
    `(Cslib.WordRAM.Code.branch (.lt $i $j) (ram $p) (ram $n))
  | `(ram_stmt% while $i:ident = $j:ident do $b:wramBlock) =>
    `(Cslib.WordRAM.Code.loop (.eq $i $j) (ram $b))
  | `(ram_stmt% while $i:ident < $j:ident do $b:wramBlock) =>
    `(Cslib.WordRAM.Code.loop (.lt $i $j) (ram $b))
  | `(ram_stmt% ⟪$c⟫) => `(($c : Cslib.WordRAM.Code _))

/-- Symbolically execute loop-free structured code on a goal `ExecWithin w c x y T`, deciding
with the given simp lemmas which written numbers fit a word. -/
syntax (name := ramEval) "ram_eval" (" [" Lean.Parser.Tactic.simpArg,* "]")? : tactic

macro_rules
  | `(tactic| ram_eval) => `(tactic| ram_eval [])
  | `(tactic| ram_eval [$args,*]) => `(tactic|
      (apply Cslib.WordRAM.ExecWithin.of_eval (fuel := 0)
       · set_option linter.unusedSimpArgs false in
         simp +decide only [Cslib.WordRAM.Code.eval, Cslib.WordRAM.Op.eval,
          Cslib.WordRAM.Data.put, Cslib.WordRAM.fits_iff, Cslib.WordRAM.BinOp.eval,
          Cslib.WordRAM.Cond.holds_eq, Cslib.WordRAM.Cond.holds_lt,
          Cslib.WordRAM.Data.set_regs, Cslib.WordRAM.Data.set_mem,
          Cslib.WordRAM.Data.write_regs, Cslib.WordRAM.Data.write_mem, Function.update_self,
          Function.update_apply, Option.map_some, Option.bind_some, Option.map_none,
          Option.bind_none, ↓reduceIte, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub,
          Nat.reduceDiv, Nat.reduceMod, Nat.reducePow, Nat.reduceAnd, Nat.reduceOr, Nat.reduceXor,
          Nat.reduceShiftLeft, Nat.reduceShiftRight, Nat.reduceLT, Nat.reduceLeDiff,
          Nat.reduceEqDiff, $args,*]
         try rfl
       · try omega))

end Cslib.WordRAM

end
