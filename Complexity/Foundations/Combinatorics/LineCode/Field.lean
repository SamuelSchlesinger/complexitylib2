/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Foundations.Data.BitString
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Binary fields as bit strings

Line-parity codes over a field `K` with `2 ^ b` elements are read and written by circuits through
an additive bijection `K ≃+ BitString b`. Such a bijection exists for every field of
characteristic two with `2 ^ b` elements: `K` is a `b`-dimensional vector space over `ZMod 2`,
and coordinates in a basis turn addition in `K` into coordinatewise exclusive or. Fields with
`2 ^ n` elements exist for every `n ≠ 0`.

## Main results

* `Cslib.LineCode.nonempty_addEquiv_bitString`: a field of characteristic two with `2 ^ b`
  elements is additively equivalent to `BitString b`.
* `Cslib.LineCode.exists_field_card_eq_two_pow`: there is a field of characteristic two with
  `2 ^ n` elements for every `n ≠ 0`.

## References

* Adapted from MassProduction/BinaryField.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.LineCode

/-- A field of characteristic two with `2 ^ b` elements is additively equivalent to `BitString b`,
whose addition is coordinatewise exclusive or. -/
theorem nonempty_addEquiv_bitString {K : Type*} [Field K] [Fintype K] [CharP K 2] {b : ℕ}
    (hK : Fintype.card K = 2 ^ b) : Nonempty (K ≃+ BitString b) := by
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  have hrank : Module.finrank (ZMod 2) K = b := by
    have hcard := Module.card_eq_pow_finrank (K := ZMod 2) (V := K)
    rw [hK, ZMod.card] at hcard
    exact (Nat.pow_right_injective le_rfl hcard).symm
  exact ⟨(Module.finBasisOfFinrankEq (ZMod 2) K hrank).equivFun.toAddEquiv.trans
    (AddEquiv.piCongrRight fun _ => (ZMod.ringEquivOfPrime Bool Nat.prime_two rfl).toAddEquiv)⟩

/-- For every `n ≠ 0` there is a field of characteristic two with exactly `2 ^ n` elements, for
example the Galois field `GaloisField 2 n`. -/
theorem exists_field_card_eq_two_pow {n : ℕ} (hn : n ≠ 0) :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K), CharP K 2 ∧ Fintype.card K = 2 ^ n :=
  ⟨GaloisField 2 n, inferInstance, Fintype.ofFinite _, inferInstance, by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 n hn]⟩

end Cslib.LineCode
