/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.AffineDisperser.BinaryField
public import Complexity.Foundations.Combinatorics.AffineDisperser.Bits
public import Mathlib.RingTheory.AdjoinRoot
import Complexity.Foundations.Data.BitString.Basic
import Mathlib.Algebra.CharP.Algebra

/-!
# Explicit binary fields of every degree

`Cslib.BinaryField w` is the field `𝔽₂[X] / (g)` for the irreducible binary polynomial `g` of
degree `w` with the least code (`Cslib.AffineDisperser.leastIrreducible`), found by exhaustive
search. For `w ≠ 0` its power basis `1, α, …, α ^ (w - 1)` at the root `α` of `g`
(`Cslib.BinaryField.basis`) encodes its elements by `w` bits (`Cslib.BinaryField.equivBits`), so
it has `2 ^ w` elements (`Cslib.BinaryField.card`); the class of a binary polynomial of degree
less than `w` is encoded by its coefficients (`Cslib.BinaryField.equivBits_mk`). Bit strings of
length `b ≤ w` embed as the polynomials of degree less than `b` (`Cslib.BinaryField.embed`).

The modulus is explicit: its code is the least code of an irreducible binary polynomial of degree
`w`, which is computed by trial division (`Cslib.AffineDisperser.leastIrreducibleCode`), so the
field arithmetic is a computation on bit strings. This is why the field is the quotient
`AdjoinRoot g` rather than Mathlib's `GaloisField 2 w`: the splitting field of `X ^ (2 ^ w) - X`
comes with no basis, the root `Cslib.AffineDisperser.binaryRoot` of `g` in it is chosen
noncomputably, and the field `Cslib.AffineDisperser.ExplicitField` of the explicit affine disperser
is a `GaloisField` with a basis of monomials in such roots, of degree a product of distinct primes.
In `AdjoinRoot g` the power basis is the coefficient list itself, for every degree `w`.

For `w = 0` the modulus is `X` and the field has two elements; the basis and the encoding by bits
need `w ≠ 0`.

## Main definitions

* `Cslib.BinaryField`: the explicit binary field of degree `w`.
* `Cslib.BinaryField.basis`: its power basis over `𝔽₂`.
* `Cslib.BinaryField.equivBits`: its encoding by `w` bits.
* `Cslib.BinaryField.embed`: the embedding of bit strings of length `b ≤ w`.

## Main results

* `Cslib.BinaryField.card`: the field has `2 ^ w` elements.
* `Cslib.BinaryField.equivBits_mk`: the encoding of a polynomial of degree less than `w` is its list
  of coefficients.

## References

* [R. Lidl, H. Niederreiter, *Finite Fields*, Chapters 1 and 3][LidlNiederreiter1997]
-/

@[expose] public section

namespace Cslib

open Polynomial

namespace AffineDisperser

/-- The least irreducible binary polynomial of degree zero is `X`, by the convention of
`Cslib.AffineDisperser.leastIrreducible`. -/
theorem leastIrreducible_zero : leastIrreducible 0 = X := by
  classical
  rw [leastIrreducible, dite_eq_right]
  rintro ⟨m, hm, hdeg⟩
  rw [natDegree_eq_zero] at hdeg
  obtain ⟨c, hc⟩ := hdeg
  rw [← hc] at hm
  rcases eq_or_ne c 0 with rfl | hc0
  · exact hm.ne_zero (by simp)
  · exact hm.not_isUnit (isUnit_C.2 (Ne.isUnit hc0))

/-- `leastIrreducible w` is irreducible for every degree, including `w = 0`. -/
theorem irreducible_leastIrreducible' (w : ℕ) : Irreducible (leastIrreducible w) := by
  rcases eq_or_ne w 0 with rfl | hw
  · rw [leastIrreducible_zero]
    exact irreducible_X
  · exact irreducible_leastIrreducible hw

/-- `leastIrreducible w` is monic for every degree, including `w = 0`
(`Cslib.AffineDisperser.monic_leastIrreducible` assumes `w ≠ 0`). -/
theorem monic_leastIrreducible' (w : ℕ) : (leastIrreducible w).Monic := by
  rcases eq_or_ne w 0 with rfl | hw
  · rw [leastIrreducible_zero]
    exact monic_X
  · exact monic_leastIrreducible hw

end AffineDisperser

open AffineDisperser

/-- **The explicit binary field of degree `w`**: binary polynomials modulo the irreducible
polynomial of degree `w` with the least code. -/
abbrev BinaryField (w : ℕ) : Type := AdjoinRoot (leastIrreducible w)

namespace BinaryField

/-- The modulus is irreducible, so the quotient is a field. -/
instance (w : ℕ) : Fact (Irreducible (leastIrreducible w)) :=
  ⟨irreducible_leastIrreducible' w⟩

/-- The explicit binary field is a field. -/
noncomputable instance (w : ℕ) : Field (BinaryField w) := AdjoinRoot.instField

/-- The explicit binary field is finite, through its coordinates in the power basis. -/
noncomputable instance (w : ℕ) : Fintype (BinaryField w) :=
  Fintype.ofEquiv _
    (AdjoinRoot.powerBasisAux' (monic_leastIrreducible' w)).equivFun.toEquiv.symm

-- `BinaryField w` is an abbreviation, so this classical instance applies to
-- `AdjoinRoot (leastIrreducible w)`; it is only used for counting and for `Finset.filter`, and
-- the programs computing in the field compare coordinate lists instead.
/-- Equality in the explicit binary field, decided classically. -/
noncomputable instance (w : ℕ) : DecidableEq (BinaryField w) := Classical.decEq _

/-- The explicit binary field has characteristic two. -/
instance (w : ℕ) : CharP (BinaryField w) 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) (BinaryField w)).injective 2

/-- **The power basis** `1, α, …, α ^ (w - 1)` at the root `α` of the modulus, for `w ≠ 0`. -/
noncomputable def basis {w : ℕ} (hw : w ≠ 0) : Module.Basis (Fin w) (ZMod 2) (BinaryField w) :=
  (AdjoinRoot.powerBasisAux' (monic_leastIrreducible' w)).reindex
    (finCongr (natDegree_leastIrreducible hw))

/-- The basis vector `i` is the power `α ^ i` of the root. -/
theorem basis_apply {w : ℕ} (hw : w ≠ 0) (i : Fin w) :
    basis hw i = AdjoinRoot.root (leastIrreducible w) ^ (i : ℕ) := by
  rw [basis, Module.Basis.reindex_apply]
  exact (AdjoinRoot.powerBasis' (monic_leastIrreducible' w)).basis_eq_pow
    ((finCongr (natDegree_leastIrreducible hw)).symm i)

/-- **The encoding by bits**: the `w` coordinates in the power basis, for `w ≠ 0`. -/
noncomputable def equivBits {w : ℕ} (hw : w ≠ 0) : BinaryField w ≃ BitString w :=
  (basis hw).equivFun.toEquiv.trans (Equiv.arrowCongr (Equiv.refl _) bitEquiv.toEquiv)

/-- Bit `j` of an element is its coordinate `j` in the power basis. -/
theorem equivBits_apply {w : ℕ} (hw : w ≠ 0) (x : BinaryField w) (j : Fin w) :
    equivBits hw x j = bitEquiv ((basis hw).repr x j) :=
  rfl

/-- The element with given bits is the combination of the basis vectors selected by the bits. -/
theorem equivBits_symm_apply {w : ℕ} (hw : w ≠ 0) (v : BitString w) :
    (equivBits hw).symm v = ∑ j, bitEquiv.symm (v j) • basis hw j := by
  simp [equivBits, Module.Basis.equivFun_symm_apply]

/-- **The explicit binary field of degree `w ≠ 0` has `2 ^ w` elements.** -/
theorem card {w : ℕ} (hw : w ≠ 0) : Fintype.card (BinaryField w) = 2 ^ w := by
  rw [Fintype.card_congr (equivBits hw), BitString.card]

/-- The encoding of the class of a binary polynomial of degree less than `w` is its list of
coefficients. -/
theorem equivBits_mk {w : ℕ} (hw : w ≠ 0) {p : (ZMod 2)[X]} (hp : p.degree < w) (j : Fin w) :
    equivBits hw (AdjoinRoot.mk (leastIrreducible w) p) j = bitEquiv (p.coeff j) := by
  have hdeg : p.degree < (leastIrreducible w).degree := by
    rw [degree_eq_natDegree (irreducible_leastIrreducible' w).ne_zero,
      natDegree_leastIrreducible hw]
    exact hp
  rw [equivBits_apply, basis, Module.Basis.repr_reindex_apply,
    AdjoinRoot.powerBasisAux'_repr_apply_to_fun, AdjoinRoot.modByMonicHom_mk,
    (modByMonic_eq_self_iff (monic_leastIrreducible' w)).2 hdeg]
  rfl

/-- **The embedding of bit strings of length `b ≤ w`**: a bit string is the polynomial with these
coefficients, padded with zeros to length `w`. -/
noncomputable def embed {w b : ℕ} (hw : w ≠ 0) (hbw : b ≤ w) : BitString b ↪ BinaryField w where
  toFun a := (equivBits hw).symm fun j => if h : (j : ℕ) < b then a ⟨j, h⟩ else false
  inj' a a' h := by
    have := congrArg (equivBits hw) h
    simp only [Equiv.apply_symm_apply] at this
    funext i
    have := congrFun this ⟨i, i.2.trans_le hbw⟩
    simpa [i.2] using this

/-- The embedded bit string is the element whose bits are those of the string, padded with
zeros. -/
theorem embed_apply {w b : ℕ} (hw : w ≠ 0) (hbw : b ≤ w) (a : BitString b) :
    embed hw hbw a = (equivBits hw).symm fun j => if h : (j : ℕ) < b then a ⟨j, h⟩ else false :=
  rfl

end BinaryField

end Cslib
