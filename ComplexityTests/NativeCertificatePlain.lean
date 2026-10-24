/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.GenericRAM.Native.Combinators
import Complexity.Computability.GenericRAM.Native.Nat
import Complexity.Computability.GenericRAM.Simulation.Turing
import Mathlib.Data.Fin.VecNotation

/-! Plain native certificates retain workspace, output charges, and runtime input encodings. -/

open Cslib.GenericRAM Turing.MultiTapeTM

namespace ComplexityTests.NativeCertificatePlain

/-- Copy arbitrary input words using the existing zero-workspace realization. -/
def copy : NativeCertificate (id : List Bool → List Bool) encBits encBits :=
  .ofTimeAndSpace computableInTimeAndSpace_id

example (word : List Bool) : copy.time word = word.length + 1 := rfl

-- Output is unbounded over this infinite input type, so the certificate charges it to space.
example (word : List Bool) : copy.space word = word.length + 1 := by
  simp [copy, NativeCertificate.ofTimeAndSpace]

example : ¬ ComputableInO (id : List Bool → List Bool) encBits encBits
    List.length (fun _ => 0) := by
  rintro ⟨c, _, hlen⟩
  have h := hlen (List.replicate (c + 1) false)
  simp only [id_eq, encBits_apply, List.length_replicate, Nat.zero_add, Nat.mul_one] at h
  omega

theorem copy_isPolynomial : copy.IsPolynomial := by
  change PolyBounded List.length (fun w => w.length + 1) ∧
    PolyBounded List.length (fun w => 0 + (w.length + 1))
  simpa only [Nat.zero_add] using
    (show PolyBounded List.length (fun w => w.length + 1) ∧
      PolyBounded List.length (fun w => w.length + 1) from
      ⟨PolyBounded.self.add (.const 1), PolyBounded.self.add (.const 1)⟩)

-- Pair construction and projection preserve a real, unbounded payload.
example : ComputableInPolyTime (id : List Bool → List Bool) encBits encBits := by
  have hp := NativeCertificate.prod_isPolynomial copy
    (NativeCertificate.const (ei := encBits) (em := encBool) true)
    copy_isPolynomial (NativeCertificate.const_isPolynomial true)
  exact ((copy.prod (NativeCertificate.const true)).fst).polyTime
    (NativeCertificate.fst_isPolynomial _ hp)

example : ComputableInPolyTime (fun word : List Bool => some word)
    encBits (encOption encBits) :=
  copy.some.polyTime (NativeCertificate.some_isPolynomial copy copy_isPolynomial)

-- The counter is binary; every round handles the complete retained word.
example : (NativeCertificate.iterate
    (NativeCertificate.const (ei := encBits) (em := encNat) 3) copy copy).IsPolynomial := by
  apply NativeCertificate.iterate_isPolynomial _ copy copy
    (NativeCertificate.const_isPolynomial 3) copy_isPolynomial copy_isPolynomial
    (PolyBounded.const 3) (B := List.length) PolyBounded.self
  intro word j _
  simp

-- Clients can supply an ordinary plain certificate directly, without a tidy-facing constructor.
example {α β : Type} {f : α → β} {ei : α ↪ List Bool} {eo : β ↪ List Bool}
    (h : ComputableInPolyTime f ei eo) : (NativeCertificate.ofPolyTime h).IsPolynomial :=
  NativeCertificate.ofPolyTime_isPolynomial h

-- Actual checked scalar semantics distinguish overflow, faults, and a false test result.
example : BoundedNat.model.checkedOp () (10, ![3, 4]) = some 7 := by decide
example : BoundedNat.model.checkedOp () (5, ![3, 4]) = none := by decide
example : BoundedNat.model.evalTest 10 () ![4, 3] = some false := by decide
example : BoundedNat.model.evalTest 5 () ![5, 0] = none := by decide
example : BoundedNat.model.checkedConstant 0 0 = none := by decide

example : BoundedNat.nativePrimitives.IsPolynomial := BoundedNat.nativePrimitives_isPolynomial

end ComplexityTests.NativeCertificatePlain
