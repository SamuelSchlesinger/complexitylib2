/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Combinatorics.AffineDisperser.Moore
public import Mathlib.FieldTheory.Finite.Trace
import Mathlib

/-!
# Products of Moore determinants of independent subspaces

Let `F` be a finite field with `2 ^ n` elements in which every proper subfield has at most
`2 ^ s` elements. Given `𝔽₂`-subspaces `Yᵢ` of `F` of dimensions `dᵢ > s` and integers
`2 ≤ kᵢ < dᵢ` with `∑ᵢ (dᵢ - kᵢ) ≥ n + 1 - maxᵢ dᵢ`, every nonzero `𝔽₂`-linear functional
`z ↦ Tr (μ z)` is nonzero on some product `∏ᵢ Δ(uᵢ)` of Moore determinants of families
`uᵢ : Fin kᵢ → Yᵢ`. This is the algebraic heart of the disperser for independent affine sources
of Ben-Sasson and Kopparty [BenSassonKopparty2012, Theorem 6.1], with the hypothesis that no
`Yᵢ` lies in a multiple of a proper subfield replaced by `dᵢ > s`; for a field of prime degree
`s = 1`.

The proof follows [BenSassonKopparty2012]. Parametrize `Yᵢ` by its image-subspace polynomial
`Qᵢ`; then `w ↦ Tr (μ ∏ᵢ Δ(Qᵢ ∘ wᵢ))` is a reduced polynomial function whose coefficient at
`∏ᵢ ∏ₗ wᵢₗ ^ 2 ^ τᵢₗ` is `∑_ρ μ ^ 2 ^ ρ ∏ᵢ per(Mᵢ[τᵢ - ρ]) ^ 2 ^ ρ`, where
`Mᵢ[τ] = (aᵢ (τ l - m) ^ 2 ^ m)`. Using the zero pattern of the coefficients `aᵢ`
(`Cslib.FiniteField.CoeffPattern`) we choose `τ` so that every `Mᵢ[τᵢ]` is triangular with
nonzero diagonal while for every rotation `ρ ≠ 0` some `Mᵢ[τᵢ - ρ]` has a zero row
[BenSassonKopparty2012, Claims 6.2 and 6.3]. That coefficient is then `μ ∏ᵢ per(Mᵢ[τᵢ]) ≠ 0`,
and a reduced polynomial with a nonzero coefficient is a nonzero function.

## Main results

* `Cslib.AffineDisperser.eq_zero_of_forall_sum_mul_prod_pow_eq_zero`: distinct reduced monomial
  functions over a finite field are linearly independent.
* `Cslib.AffineDisperser.exists_trace_mul_prod_det_mooreMatrix_ne_zero`: the theorem above.

## References

* [E. Ben-Sasson, S. Kopparty, *Affine dispersers from subspace polynomials*][BenSassonKopparty2012]
-/

@[expose] public section

namespace Cslib.AffineDisperser

open Module Cslib.FiniteField

variable {F : Type*} [Field F]

/-- **Reduced monomials are independent**: over a finite field `F`, if a combination
`∑ₜ Cₜ ∏ᵥ xᵥ ^ eₜᵥ` of monomials with pairwise distinct exponent vectors, all exponents below
`|F|`, vanishes at every point, then all coefficients vanish. -/
theorem eq_zero_of_forall_sum_mul_prod_pow_eq_zero [Fintype F] {σ T : Type*} [Fintype σ] [Fintype T]
    (e : T → σ → ℕ) (he : Function.Injective e) (hlt : ∀ t v, e t v < Fintype.card F)
    (C : T → F) (h : ∀ x : σ → F, ∑ t, C t * ∏ v, x v ^ e t v = 0) (t : T) : C t = 0 := by
  sorry

variable [Finite F] [Algebra (ZMod 2) F]

/-- **Moore products of independent sources** (after [BenSassonKopparty2012, Theorem 6.1]): in a
field with `2 ^ n` elements whose proper subfields have at most `2 ^ s` elements, let `Yᵢ` be
subspaces of dimensions `dᵢ > s`, and `2 ≤ kᵢ < dᵢ` with `n < d_{i₀} + ∑ᵢ (dᵢ - kᵢ)` for some
`i₀`. Then for every `μ ≠ 0` there are families `uᵢ : Fin kᵢ → Yᵢ` whose Moore determinants
satisfy `Tr (μ ∏ᵢ Δ(uᵢ)) ≠ 0`. -/
theorem exists_trace_mul_prod_det_mooreMatrix_ne_zero {ι : Type*} [Fintype ι] {n s : ℕ}
    (hn : finrank (ZMod 2) F = n) (hs : ∀ K : Subfield F, K ≠ ⊤ → Nat.card K ≤ 2 ^ s)
    (Y : ι → Submodule (ZMod 2) F) (k : ι → ℕ) (hk : ∀ i, 2 ≤ k i)
    (hkY : ∀ i, k i < finrank (ZMod 2) (Y i)) (hsY : ∀ i, s < finrank (ZMod 2) (Y i)) (i₀ : ι)
    (hsum : n < finrank (ZMod 2) (Y i₀) + ∑ i, (finrank (ZMod 2) (Y i) - k i))
    {μ : F} (hμ : μ ≠ 0) :
    ∃ u : (i : ι) → Fin (k i) → F, (∀ i l, u i l ∈ Y i) ∧
      Algebra.trace (ZMod 2) F (μ * ∏ i, (mooreMatrix (u i)).det) ≠ 0 := by
  sorry

end Cslib.AffineDisperser
