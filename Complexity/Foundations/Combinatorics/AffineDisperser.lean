/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Combinatorics.AffineDisperser.IndependentSources
public import Complexity.Foundations.Combinatorics.AffineDisperser.PivotSpace
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib

/-!
# Affine dispersers from subspace polynomials

Let `F` be a finite field with `2 ^ n` elements and `μ ∈ F` nonzero. Ben-Sasson and Kopparty's
function on `r` blocks [BenSassonKopparty2012, Theorem 7.3] is
`f(x) = Tr (μ ∑_{|I| = t} ∏_{i ∈ I} xᵢ ^ (2 ^ (r + 1 - i) - 1))`, the trace of the `t`-th elementary
symmetric polynomial of the powers `xᵢ ^ (2 ^ (r + 1 - i) - 1)` (blocks numbered from `0`).
It is nonconstant on every `𝔽₂`-affine subspace `A ⊆ Fʳ` of large dimension.

Ben-Sasson and Kopparty take `n` prime, so that `𝔽₂` is the only proper subfield of `F`. We prove
the theorem for every `F` whose proper subfields have at most `2 ^ s` elements, replacing their
threshold `r + 1` on the dimensions of the useful blocks by `M = max (r + 1) s`: `f` is
nonconstant on every affine `A` with `dim A > r M + r (r + 1) + n t + ⌊n r / t⌋`. Composite
degrees `n` with no small proper divisors keep `s` small while allowing explicit field arithmetic.

The proof: let `Yᵢ` be the pivot spaces of the direction of `A` and lift a basis of each to vectors
of `A`'s direction vanishing below their block. Averaging gives `t` blocks `I₀` with `dᵢ > M` and
`∑_{I₀} (dᵢ - kᵢ) ≥ n`, `kᵢ = r + 1 - i`. Summing `f` over the cube spanned by `kᵢ` lifted
directions in each block `i ∈ I₀` expands every term `∏_{j ∈ J} xⱼ ^ (2 ^ kⱼ - 1)` into covering
assignments of factors to directions (`Cslib.sum_cube_prod_affine`). Because `kᵢ` decreases
strictly, a weighting argument [BenSassonKopparty2012, Claim 7.4] shows that only `J = I₀`
survives, where block-triangularity turns the sum into `∏_{I₀} Δ(uᵢ)` of Moore determinants. The
independent-sources theorem (`exists_trace_mul_prod_det_mooreMatrix_ne_zero`) chooses the `uᵢ` so
that its trace is nonzero, while a constant function would have zero cube sum.

## Main definitions

* `Cslib.AffineDisperser.traceSym`: Ben-Sasson and Kopparty's symmetric-power function.

## Main results

* `Cslib.AffineDisperser.eq_of_covering`: the weighting argument [BenSassonKopparty2012,
  Claim 7.4].
* `Cslib.AffineDisperser.exists_traceSym_ne`: `traceSym` is nonconstant on affine subspaces of
  dimension greater than `r * max (r + 1) s + r * (r + 1) + n * t + n * r / t`.
* `Cslib.AffineDisperser.card_subfield_le`: proper subfields of a field with `2 ^ n` elements have
  at most `2 ^ (n / 2)` elements.

## References

* [E. Ben-Sasson, S. Kopparty, *Affine dispersers from subspace polynomials*][BenSassonKopparty2012]
-/

@[expose] public section

namespace Cslib.AffineDisperser

open Module Cslib.FiniteField

/-- **Covering assignments respect blocks** [BenSassonKopparty2012, Claim 7.4]. Blocks `i < r`
carry `k i` slots, with `k` strictly decreasing and positive. Let `I, J` be sets of `t` blocks and
`ℓ` an assignment of the slots of `J` to the slots of `I` (or to nothing) that covers every slot of
`I` and never sends a slot to a higher block. Then `J = I`. -/
theorem eq_of_covering {r : ℕ} (k : Fin r → ℕ) (hk : StrictAnti k) (hk0 : ∀ i, 0 < k i)
    (I J : Finset (Fin r)) (hcard : J.card = I.card)
    (ℓ : (Σ j : J, Fin (k j)) → Option (Σ i : I, Fin (k i)))
    (hcov : ∀ v, ∃ p, ℓ p = some v) (hmono : ∀ p v, ℓ p = some v → (v.1 : Fin r) ≤ p.1) :
    J = I := by
  sorry

variable {F : Type*} [Field F] [Finite F]

/-- A proper subfield `K` of a finite field `F` satisfies `|K| ^ 2 ≤ |F|`. -/
theorem card_sq_le_of_ne_top {K : Subfield F} (hK : K ≠ ⊤) : Nat.card K ^ 2 ≤ Nat.card F := by
  sorry

variable [Algebra (ZMod 2) F]

/-- In a field with `2 ^ n` elements every proper subfield has at most `2 ^ (n / 2)` elements. -/
theorem card_subfield_le {n : ℕ} (hn : finrank (ZMod 2) F = n) (K : Subfield F) (hK : K ≠ ⊤) :
    Nat.card K ≤ 2 ^ (n / 2) := by
  sorry

/-- **Ben-Sasson and Kopparty's symmetric-power function** on `r` blocks of a field `F`
[BenSassonKopparty2012, Theorem 7.3]: the trace of `μ` times the `t`-th elementary symmetric
polynomial of `xᵢ ^ (2 ^ (r + 1 - i) - 1)`, blocks numbered from `0`. -/
noncomputable def traceSym (μ : F) (r t : ℕ) (x : Fin r → F) : ZMod 2 :=
  Algebra.trace (ZMod 2) F
    (μ * ∑ I ∈ Finset.univ.powersetCard t, ∏ i ∈ I, x i ^ (2 ^ (r + 1 - i) - 1))

/-- **Affine dispersers from subspace polynomials** [BenSassonKopparty2012, Theorem 7.3], for
fields whose proper subfields have at most `2 ^ s` elements: if `μ ≠ 0` and `0 < t`, then
`traceSym μ r t` is nonconstant on every `𝔽₂`-affine subspace `A` of `Fʳ` of dimension greater
than `r * max (r + 1) s + r * (r + 1) + n * t + n * r / t`, where `F` has `2 ^ n` elements. -/
theorem exists_traceSym_ne {n s r t : ℕ} (hn : finrank (ZMod 2) F = n)
    (hs : ∀ K : Subfield F, K ≠ ⊤ → Nat.card K ≤ 2 ^ s) {μ : F} (hμ : μ ≠ 0) (ht : 0 < t)
    (A : AffineSubspace (ZMod 2) (Fin r → F))
    (hA : r * max (r + 1) s + r * (r + 1) + n * t + n * r / t <
      finrank (ZMod 2) A.direction) :
    ∃ x ∈ A, ∃ y ∈ A, traceSym μ r t x ≠ traceSym μ r t y := by
  sorry

end Cslib.AffineDisperser
