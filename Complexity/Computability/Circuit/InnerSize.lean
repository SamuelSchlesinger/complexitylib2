/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Computability/Circuit/Basic.lean`)

public import Cslib.Computability.Circuit.Basic
import Complexity.Computability.Circuit.Program

/-!
# Inner gates

A gate of arity zero is a constant: like an input, it is a leaf of the circuit. The *inner*
gates of a program are its gates of positive arity, and the *inner size* of a circuit counts
them. A lower bound that holds over every basis can only count inner gates, since every value of
the alphabet may be a constant gate of the basis.

## Main definitions

* `Cslib.Circuits.Program.innerGates`: the gates of positive arity.
* `Cslib.Circuits.Circuit.innerSize`: the number of gates of positive arity.

## Main results

* `Cslib.Circuits.Circuit.innerSize_le_size`: constant gates are free.
* `Cslib.Circuits.Circuit.innerSize_eq_zero_of_fanInAtMost_zero`: without arguments every gate is
  a constant.
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ : Signature} {n g m : ℕ}

/-- The *inner* gates of a program: those of positive arity. A gate of arity zero is a constant,
a leaf of the circuit like an input. -/
def Program.innerGates (p : Program σ n g) : Finset (Fin g) :=
  {k | σ.Arity (p.lines k).op ≠ 0}

@[simp] theorem Program.mem_innerGates {p : Program σ n g} {k : Fin g} :
    k ∈ p.innerGates ↔ σ.Arity (p.lines k).op ≠ 0 := by
  simp [Program.innerGates]

/-- The *inner size* of a circuit: the number of its gates of positive arity. Constant gates are
free. For arithmetic circuits this counts the additions and multiplications. -/
def Circuit.innerSize (c : Circuit σ n m) : ℕ :=
  c.program.innerGates.card

/-- Constant gates are free: the inner size is at most the size. -/
theorem Circuit.innerSize_le_size (c : Circuit σ n m) : c.innerSize ≤ c.size :=
  (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)

/-- Without arguments every gate is a constant, so a circuit of fan-in zero has inner size
zero. -/
theorem Circuit.innerSize_eq_zero_of_fanInAtMost_zero {c : Circuit σ n m}
    (h : c.FanInAtMost 0) : c.innerSize = 0 := by
  rw [Circuit.innerSize, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro k hk
  exact Program.mem_innerGates.mp hk (Nat.le_zero.mp (Program.fanInAtMost_iff.mp h k))

@[simp] theorem Circuit.innerSize_wiring (select : Fin m → Fin n) :
    (Circuit.wiring σ select).innerSize = 0 :=
  Nat.le_zero.mp ((Circuit.wiring σ select).innerSize_le_size)

end Cslib.Circuits
