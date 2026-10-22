/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Generic
public import Complexity.Computability.GenericRAM.Native
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Tactic.PolyTime.Init

/-!
# A native certificate for checked word addition

The width is a runtime input encoded in unary; operand values are encoded in binary. A single
native machine handles every width and both operands, returning `none` precisely when the sum
does not fit. Its polynomial bound is in the complete encoded input length, including the unary
width, not the bit length of a binary-encoded width. No claim about the other standard-basis
operations, memory access or whole-program simulation follows from this primitive certificate.
Computable width selection with charged costs and input fit remain separate obligations.

## Main results

* `checkedAdd_polyTime`: native polynomial time for checked standard-basis addition.
* `checkedAddCertificate`: arbitrary-bound interface obtained from that implementation.

## References

* [MIT–ULB CompGeom Group, *Undecidability of tiling with a tromino*][Tromino2025]

Uses Christian Reitwiessner's binary natural encodings and native machine arithmetic through the
library's polynomial-time calculus.
-/

@[expose] public section

namespace Cslib.WordRAM

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- Checked addition is polynomial in the full encoding: unary width and binary operands. -/
@[program_certificate]
theorem checkedAdd_polyTime :
    ComputableTidilyInPolyTime (Basis.standard.genericModel.checkedOp (.bin .add))
      (encPair encUnary (encPi encNat)) (encOption encNat) := by
  have hx := (pi_apply encNat (0 : Fin 2)).comp (snd encUnary (encPi encNat))
  have hy := (pi_apply encNat (1 : Fin 2)).comp (snd encUnary (encPi encNat))
  have hadd := binary_add.comp (hx.prod hy)
  have hpow := binary_two_pow.comp (fst encUnary (encPi encNat (Index := Fin 2)))
  change ComputableTidilyInPolyTime
    (fun p : ℕ × (Fin 2 → ℕ) => if decide (p.2 0 + p.2 1 < 2 ^ p.1)
      then some (p.2 0 + p.2 1) else none)
    (encPair encUnary (encPi encNat (Index := Fin 2))) (encOption encNat)
  simp only [decide_eq_true_eq]
  exact (binary_lt.comp (hadd.prod hpow)).ite_decide
    ((optionSome encNat).comp hadd) (const none)

/-- One native checked-add implementation works at every encoded width. -/
noncomputable def checkedAddCertificate :
    GenericRAM.NativeCertificate (Basis.standard.genericModel.checkedOp (.bin .add))
      (encPair encUnary (encPi encNat)) (encOption encNat) :=
  .ofPolyTime checkedAdd_polyTime

end Cslib.WordRAM
