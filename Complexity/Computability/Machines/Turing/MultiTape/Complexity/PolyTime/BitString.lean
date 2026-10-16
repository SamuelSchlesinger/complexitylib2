/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Foundations.Data.BitString.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Polynomial-time fixed-width bit lists

Replicating a fixed bit and reading fixed-width rows use the existing list and iteration
calculus. Runtime row counts and widths are computed in unary, charging the complete output.
The operations are total on empty and short lists.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsReplicate`: repeat a fixed bit.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsRowWithInput`: read one fixed-width row.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsRowsWithInput`: read a runtime number of rows.

## References

The row interface is adapted from `Computability/Probabilistic/BitString.lean` on the cslib
`crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- Repeat a fixed bit a unary number of times. -/
@[fun_prop]
theorem bitsReplicate (bit : Bool) :
    ComputableTidilyInPolyTime (fun n => List.replicate n bit) encUnary encBits := by
  have h (n : ℕ) : (List.cons bit)^[n] [] = List.replicate n bit := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [Function.iterate_succ_apply', ih, List.replicate_succ]
  simpa only [h, id_eq] using iterate_of_bounded_growth (count := id) (init := fun _ : ℕ => [])
    (step := List.cons bit) id' (const []) (by fun_prop) (growth := 1) (fun _ => by simp)

variable {α : Type} {input : α ↪ List Bool}

/-- Read a row of a computed word, including the cost of padding a short word. -/
@[fun_prop]
theorem bitsRowWithInput {width row : α → ℕ} {word : α → List Bool}
    (hwidth : ComputableTidilyInPolyTime width input encUnary)
    (hrow : ComputableTidilyInPolyTime row input encUnary)
    (hword : ComputableTidilyInPolyTime word input encBits) :
    ComputableTidilyInPolyTime (fun a => Cslib.BitString.listRow (width a) (row a) (word a))
      input encBits := by
  unfold Cslib.BitString.listRow
  fun_prop

/-- Extract rows from a word with polynomial-time unary dimensions. -/
@[fun_prop]
theorem bitsRowsWithInput {count width : α → ℕ} {word : α → List Bool}
    (hcount : ComputableTidilyInPolyTime count input encUnary)
    (hwidth : ComputableTidilyInPolyTime width input encUnary)
    (hword : ComputableTidilyInPolyTime word input encBits) :
    ComputableTidilyInPolyTime (fun a => Cslib.BitString.listRows (count a) (width a) (word a))
      input (encList encBits) := by
  unfold Cslib.BitString.listRows
  fun_prop

end Turing.MultiTapeTM.ComputableTidilyInPolyTime
