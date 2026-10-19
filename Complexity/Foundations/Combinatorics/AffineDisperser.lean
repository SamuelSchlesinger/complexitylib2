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
  classical
  choose sec hsec using hcov
  -- weight `1 / k i` on every slot of block `i`
  let w : Fin r → ℚ := fun i => 1 / (k i : ℚ)
  have hw_pos : ∀ i, 0 < w i := fun i => by
    have := hk0 i
    positivity
  have hsumI : ∑ v : (Σ i : I, Fin (k i)), w v.1 = I.card := by
    rw [Fintype.sum_sigma]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, w]
    rw [Finset.sum_congr rfl fun i _ => mul_one_div_cancel (by have := hk0 i; positivity)]
    simp
  have hsumJ : ∑ p : (Σ j : J, Fin (k j)), w p.1 = J.card := by
    rw [Fintype.sum_sigma]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, w]
    rw [Finset.sum_congr rfl fun j _ => mul_one_div_cancel (by have := hk0 j; positivity)]
    simp
  have hsec_inj : Function.Injective sec := fun v v' h =>
    Option.some_injective _ ((hsec v).symm.trans ((congrArg ℓ h).trans (hsec v')))
  have hle : ∀ v, w v.1 ≤ w (sec v).1 := fun v => by
    have h := hk.antitone (hmono (sec v) v (hsec v))
    exact one_div_le_one_div_of_le (by have := hk0 (sec v).1; positivity) (by exact_mod_cast h)
  have h1 : ∑ v : (Σ i : I, Fin (k i)), w v.1 ≤ ∑ v, w (sec v).1 :=
    Finset.sum_le_sum fun v _ => hle v
  have himage : ∑ v : (Σ i : I, Fin (k i)), w (sec v).1 =
      ∑ p ∈ Finset.univ.image sec, w p.1 :=
    (Finset.sum_image (f := fun p : (Σ j : J, Fin (k j)) => w p.1)
      fun v _ v' _ h => hsec_inj h).symm
  have h2 : ∑ v : (Σ i : I, Fin (k i)), w (sec v).1 ≤ ∑ p : (Σ j : J, Fin (k j)), w p.1 := by
    rw [himage]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun p _ _ => (hw_pos _).le
  have hcardQ : ((I.card : ℕ) : ℚ) = J.card := by rw [hcard]
  -- every slot of `J` is the chosen preimage of a slot of `I`
  have hsurj : Function.Surjective sec := by
    intro p
    by_contra hp
    push Not at hp
    have : ∑ v : (Σ i : I, Fin (k i)), w (sec v).1 < ∑ p : (Σ j : J, Fin (k j)), w p.1 := by
      rw [himage]
      refine Finset.sum_lt_sum_of_subset (Finset.subset_univ _) (Finset.mem_univ p) ?_ (hw_pos _)
        fun _ _ _ => (hw_pos _).le
      rw [Finset.mem_image]
      rintro ⟨v, -, hv⟩
      exact hp v hv
    linarith
  -- and lies in the same block
  have hblock : ∀ v, ((sec v).1 : Fin r) = v.1 := by
    intro v
    by_contra hne
    have hlt : w v.1 < w (sec v).1 := by
      have h := hk (lt_of_le_of_ne (hmono (sec v) v (hsec v)) (Ne.symm hne))
      exact one_div_lt_one_div_of_lt (by have := hk0 (sec v).1; positivity) (by exact_mod_cast h)
    have : ∑ v : (Σ i : I, Fin (k i)), w v.1 < ∑ v, w (sec v).1 :=
      Finset.sum_lt_sum (fun v _ => hle v) ⟨v, Finset.mem_univ _, hlt⟩
    linarith
  refine Finset.eq_of_subset_of_card_le (fun j hj => ?_) hcard.ge
  obtain ⟨v, hv⟩ := hsurj ⟨⟨j, hj⟩, ⟨0, hk0 j⟩⟩
  have := hblock v
  rw [hv] at this
  rw [show j = (v.1 : Fin r) from this]
  exact v.1.2

variable {F : Type*} [Field F] [Finite F]

/-- A proper subfield `K` of a finite field `F` satisfies `|K| ^ 2 ≤ |F|`. -/
theorem card_sq_le_of_ne_top {K : Subfield F} (hK : K ≠ ⊤) : Nat.card K ^ 2 ≤ Nat.card F := by
  rw [Module.natCard_eq_pow_finrank (K := K) (V := F)]
  refine Nat.pow_le_pow_right Nat.card_pos ?_
  by_contra h
  have h1 : finrank K F = 1 := by
    have := Module.finrank_pos (R := K) (M := F)
    omega
  apply hK
  have hbij : Function.Bijective (Subtype.val : K → F) :=
    Subtype.val_injective.bijective_of_nat_card_le
      (by rw [Module.natCard_eq_pow_finrank (K := K) (V := F), h1, pow_one])
  exact eq_top_iff.2 fun x _ => by
    obtain ⟨y, rfl⟩ := hbij.2 x
    exact y.2

variable [Algebra (ZMod 2) F]

/-- In a field with `2 ^ n` elements every proper subfield has at most `2 ^ (n / 2)` elements. -/
theorem card_subfield_le {n : ℕ} (hn : finrank (ZMod 2) F = n) (K : Subfield F) (hK : K ≠ ⊤) :
    Nat.card K ≤ 2 ^ (n / 2) := by
  have := charP_two (F := F)
  cases nonempty_fintype F
  have : CharP K 2 := K.subtype.charP Subtype.val_injective 2
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨e, -, he⟩ := FiniteField.card K 2
  have hF : Nat.card F = 2 ^ n := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F), Nat.card_zmod, hn]
  have hsq := card_sq_le_of_ne_top hK
  rw [Nat.card_eq_fintype_card (α := K), he, hF, ← pow_mul] at hsq
  rw [Nat.card_eq_fintype_card (α := K), he]
  exact Nat.pow_le_pow_right two_pos
    (by have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hsq; omega)

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
