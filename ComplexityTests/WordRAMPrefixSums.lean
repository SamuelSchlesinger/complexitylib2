/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.PrefixSums.Dynamic

/-! Nonvacuity, boundary queries, persistence and actual interpreter checks for prefix sums. -/

@[expose] public section

open Cslib Cslib.WordRAM Cslib.Algorithms.WordRAM.PrefixSums

namespace WordRAMPrefixSumsTests

/-- The implementation has no code dependency on the height or word width. -/
example (h w h' w' : ℕ) : (program h w).code = (program h' w').code := rfl

/-- A represented four-element array exists, with its seven-word tree starting at address ten. -/
example : Rep 2 10 8 [0, 0, 0, 0] (zeroData 2 10) := rep_zeroData (by decide)

/-- Two updates followed by overlapping queries, preserving the array between calls. -/
def client : (spec 2 8).Client (List ℕ) :=
  .liftBind (.add 1 5) fun _ =>
  .liftBind (.add 3 7) fun _ =>
  .liftBind (.sum 2) fun a =>
  .liftBind (.sum 4) fun b => .pure [a, b]

/-- The generic adaptive theorem supplies the two answers, final array and cumulative bound. -/
example : ∃ y traces, Stateful.Executes ((program 2 8).ExecOp 8) client
      (zeroData 2 10) [5, 12] y traces ∧ Rep 2 10 8 [0, 5, 0, 7] y ∧
      Stateful.total DynamicProgram.OperationTrace.instructions traces ≤ 204 :=
  client_spec (by decide) client (rep_zeroData (by decide)) (by
    change (1 < 4 ∧ Fits 8 5) ∧ (3 < 4 ∧ Fits 8 12) ∧ 2 ≤ 4 ∧ 4 ≤ 4 ∧ True
    decide)

/-- A second call can be selected from the answer actually observed by the first. -/
def adaptive : (spec 2 8).Client ℕ :=
  .liftBind (.sum 4) fun (total : ℕ) =>
  .liftBind (.add 0 (total + 1)) fun _ =>
  .liftBind (.sum 1) fun first => .pure first

example : ∃ y traces, Stateful.Executes ((program 2 8).ExecOp 8) adaptive
      (zeroData 2 10) 1 y traces ∧ Rep 2 10 8 [1, 0, 0, 0] y ∧
      Stateful.total DynamicProgram.OperationTrace.instructions traces ≤ 153 :=
  client_spec (b := 10) (by decide) adaptive (rep_zeroData (by decide)) (by
    change 4 ≤ 4 ∧ (0 < 4 ∧ Fits 8 1) ∧ 1 ≤ 4 ∧ True
    decide)

/-- Run the actual structured interpreter repeatedly, retaining persistent memory. -/
def runCalls : List Operation → Data 14 → Option (Data 14 × List ℕ × ℕ)
  | [], x => some (x, [], 0)
  | o :: os, x => do
    let (y, n) ← dispatch.eval 8 4 ((program 2 8).prepare o x)
    let (z, answers, time) ← runCalls os y
    pure (z, y.regs Reg.ans :: answers, n + 1 + time)

-- Kernel reduction of six calls traverses nested register updates and requires a deeper stack.
set_option maxRecDepth 4096 in
/-- Boundary prefixes and both children are exercised on real machine execution. -/
example : ((runCalls [.sum 0, .add 0 2, .add 2 3, .sum 1, .sum 3, .sum 4]
    (zeroData 2 10)).map fun r => r.2.1) = some [0, 0, 0, 2, 5, 5] := by decide

/-- Out-of-range operations and overflowing updates are excluded by the specification. -/
example : ¬(spec 2 8).valid [0, 0, 0, 0] (.add 4 1) := by simp [spec]
example : ¬(spec 2 8).valid [255, 0, 0, 0] (.add 0 1) := by simp [spec, fits_iff]

/-- The bounded-word machine faults when an actual aggregate addition overflows. -/
example : (((zeroData 2 10).write 10 255) |> fun x =>
    dispatch.eval 8 4 ((program 2 8).prepare (.add 0 1) x)).isNone = true := by decide

#print axioms Tree.prefixSum_eq_sum_take
#print axioms Tree.leaves_add
#print axioms updateLoop_spec
#print axioms queryLoop_spec
#print axioms certificate
#print axioms instruction_bound
#print axioms instruction_bound_log
#print axioms execOp_frame
#print axioms client_spec

end WordRAMPrefixSumsTests

end
