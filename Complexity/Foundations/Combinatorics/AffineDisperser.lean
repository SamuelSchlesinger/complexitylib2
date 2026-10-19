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
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.Finset.Powerset
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

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

/-- **Averaging**: some `t`-element subset `I` of `S` carries at least a `t / |S|` share of
`∑_{i ∈ S} d i`. -/
theorem exists_subset_card_eq_mul_sum_le {ι : Type*} (S : Finset ι) (d : ι → ℕ)
    {t : ℕ} (ht : t ≤ S.card) :
    ∃ I ⊆ S, I.card = t ∧ t * ∑ i ∈ S, d i ≤ S.card * ∑ i ∈ I, d i := by
  classical
  obtain ⟨I, hI, hmax⟩ := Finset.exists_max_image (S.powersetCard t) (fun I => ∑ i ∈ I, d i)
    (Finset.powersetCard_nonempty.2 ht)
  obtain ⟨hIS, hIcard⟩ := Finset.mem_powersetCard.1 hI
  refine ⟨I, hIS, hIcard, ?_⟩
  -- no element outside `I` beats an element of `I`
  have hex : ∀ i ∈ I, ∀ j ∈ S \ I, d j ≤ d i := by
    intro i hi j hj
    rw [Finset.mem_sdiff] at hj
    have hjI : j ∉ I.erase i := fun h => hj.2 (Finset.mem_of_mem_erase h)
    have := hmax (insert j (I.erase i)) (Finset.mem_powersetCard.2
      ⟨Finset.insert_subset hj.1 ((Finset.erase_subset _ _).trans hIS), by
        rw [Finset.card_insert_of_notMem hjI, Finset.card_erase_of_mem hi, hIcard]
        have := Finset.card_pos.2 ⟨i, hi⟩
        omega⟩)
    rw [Finset.sum_insert hjI, ← Finset.add_sum_erase I d hi] at this
    omega
  have h1 : t * ∑ j ∈ S \ I, d j ≤ (S \ I).card * ∑ i ∈ I, d i := by
    calc t * ∑ j ∈ S \ I, d j = ∑ j ∈ S \ I, ∑ _i ∈ I, d j := by
          rw [Finset.mul_sum]
          simp [Finset.sum_const, hIcard]
      _ ≤ ∑ j ∈ S \ I, ∑ i ∈ I, d i :=
          Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun i hi => hex i hi j hj
      _ = (S \ I).card * ∑ i ∈ I, d i := by rw [Finset.sum_const, smul_eq_mul]
  rw [← Finset.sum_sdiff hIS, ← Finset.card_sdiff_add_card_eq_card hIS, hIcard, mul_add,
    add_mul]
  omega

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
  classical
  have := charP_two (F := F)
  cases nonempty_fintype F
  set M := max (r + 1) s with hM
  have h2 : n * r < t * (n * r / t + 1) := Nat.lt_mul_div_succ (n * r) ht
  generalize n * r / t = q at hA h2
  -- the pivot spaces of the direction of `A`
  let Y : Fin r → Submodule (ZMod 2) F := pivotSpace A.direction
  let d : Fin r → ℕ := fun i => finrank (ZMod 2) (Y i)
  have hsumd : ∑ i, d i = finrank (ZMod 2) A.direction := sum_finrank_pivotSpace A.direction
  have hdn : ∀ i, d i ≤ n := fun i => hn ▸ Submodule.finrank_le _
  let k : Fin r → ℕ := fun i => r + 1 - i
  -- the blocks of dimension above `M`
  let S := Finset.univ.filter fun i => M < d i
  have hS : finrank (ZMod 2) A.direction ≤ r * M + ∑ i ∈ S, d i := by
    have hsmall : ∑ i ∈ Finset.univ.filter (fun i => ¬ M < d i), d i ≤ r * M := by
      calc ∑ i ∈ Finset.univ.filter (fun i => ¬ M < d i), d i
          ≤ ∑ _i ∈ Finset.univ.filter (fun i => ¬ M < d i), M :=
            Finset.sum_le_sum fun i hi => not_lt.1 (Finset.mem_filter.1 hi).2
        _ ≤ ∑ _i : Fin r, M := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        _ = r * M := by simp
    have := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => M < d i) d
    change ∑ i ∈ S, d i + _ = _ at this
    omega
  have hSr : S.card ≤ r := by simpa using Finset.card_filter_le Finset.univ fun i => M < d i
  have hSn : ∑ i ∈ S, d i ≤ S.card * n := by
    calc ∑ i ∈ S, d i ≤ ∑ _i ∈ S, n := Finset.sum_le_sum fun i _ => hdn i
      _ = S.card * n := by simp
  have hSt : t ≤ S.card := by
    by_contra h
    have : S.card * n ≤ t * n := Nat.mul_le_mul_right _ (by omega)
    have : S.card * n + n ≤ t * n := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ (by omega)
    rw [mul_comm n t] at hA
    omega
  obtain ⟨I₀, hI₀S, hI₀card, hI₀sum⟩ := exists_subset_card_eq_mul_sum_le S d hSt
  have hI₀big : ∀ i ∈ I₀, M < d i := fun i hi => (Finset.mem_filter.1 (hI₀S hi)).2
  have hkM : ∀ i, k i ≤ M := fun i => by simp only [k, hM]; omega
  -- `I₀` has `∑ (dᵢ - kᵢ) > n`
  have hI₀ : n < ∑ i ∈ I₀, (d i - k i) := by
    set X := ∑ i ∈ I₀, d i
    have h1 : t * (finrank (ZMod 2) A.direction - r * M) ≤ r * X :=
      (Nat.mul_le_mul_left t (by omega)).trans (hI₀sum.trans (Nat.mul_le_mul_right _ hSr))
    have h3 : r * (r + 1) + n * t + q + 1 ≤ finrank (ZMod 2) A.direction - r * M := by
      omega
    have h4 := (Nat.mul_le_mul_left t h3).trans h1
    have e1 : t * (r * (r + 1) + n * t + q + 1) =
        t * (r * (r + 1)) + t * (n * t) + t * (q + 1) := by ring
    have e2 : r * (t * (r + 1) + n) = t * (r * (r + 1)) + n * r := by ring
    rw [e1] at h4
    have h5 : r * (t * (r + 1) + n) < r * X := by
      rw [e2]
      omega
    have hX : t * (r + 1) + n < X := Nat.lt_of_mul_lt_mul_left h5
    have hsplit : ∑ i ∈ I₀, (d i - k i) + ∑ i ∈ I₀, k i = X := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i hi => Nat.sub_add_cancel ((hkM i).trans (hI₀big i hi).le)
    have hk : ∑ i ∈ I₀, k i ≤ t * (r + 1) := by
      calc ∑ i ∈ I₀, k i ≤ ∑ _i ∈ I₀, (r + 1) := Finset.sum_le_sum fun i _ => Nat.sub_le _ _
        _ = t * (r + 1) := by simp [hI₀card]
    omega
  -- families in the pivot spaces with nonzero trace of the product of Moore determinants
  have hI₀ne : I₀.Nonempty := Finset.card_pos.1 (hI₀card ▸ ht)
  obtain ⟨u, huY, hu⟩ := exists_trace_mul_prod_det_mooreMatrix_ne_zero (ι := I₀) hn hs
    (fun i => Y i) (fun i => k i)
    (fun i => show 2 ≤ r + 1 - ((i : Fin r) : ℕ) by have := (i.1 : Fin r).isLt; omega)
    (fun i => lt_of_le_of_lt (hkM i) (hI₀big i i.2))
    (fun i => lt_of_le_of_lt (le_max_right _ _) (hI₀big i i.2)) ⟨hI₀ne.choose, hI₀ne.choose_spec⟩
    (by
      rw [Finset.sum_coe_sort I₀ fun i => d i - k i]
      omega)
    hμ
  -- lift them to `A.direction`, vanishing below their block
  have hlift : ∀ (i : I₀) (l : Fin (k i)), ∃ v ∈ A.direction, (∀ j < (i : Fin r), v j = 0) ∧
      v i = u i l := fun i l => mem_pivotSpace.1 (huY i l)
  choose v hvA hvlow hvdiag using hlift
  -- a base point
  have hAne : (A : Set (Fin r → F)).Nonempty := by
    rw [AffineSubspace.nonempty_iff_ne_bot]
    rintro rfl
    rw [AffineSubspace.direction_bot, finrank_bot] at hA
    omega
  obtain ⟨γ, hγ⟩ := hAne
  -- the cube spanned by the lifted directions
  let κ := Σ i : I₀, Fin (k i)
  let x : (κ → ZMod 2) → Fin r → F := fun c => (∑ q : κ, c q • v q.1 q.2) +ᵥ γ
  have hxA : ∀ c, x c ∈ A := fun c => AffineSubspace.vadd_mem_of_mem_direction
    (Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (hvA _ _)) hγ
  by_contra hcon
  push Not at hcon
  -- a constant function has zero cube sum
  have hzero : ∑ c : κ → ZMod 2, traceSym μ r t (x c) = 0 := by
    have hκ : 0 < Fintype.card κ :=
      Fintype.card_pos_iff.2 ⟨⟨⟨_, hI₀ne.choose_spec⟩, ⟨0, by simp only [k]; omega⟩⟩⟩
    rw [Finset.sum_congr rfl fun c _ => hcon _ (hxA c) _ hγ, Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, ZMod.card, nsmul_eq_mul, Nat.cast_pow,
      show ((2 : ℕ) : ZMod 2) = 0 from rfl, zero_pow hκ.ne', zero_mul]
  -- the product of the powers of the coordinates, as a product of affine forms
  have hprod : ∀ (J : Finset (Fin r)) (c : κ → ZMod 2),
      ∏ j ∈ J, x c j ^ (2 ^ (r + 1 - j) - 1) =
        ∏ p : (Σ j : J, Fin (k j)), ((γ p.1) ^ 2 ^ (p.2 : ℕ) +
          ∑ q : κ, c q • (v q.1 q.2 p.1 ^ 2 ^ (p.2 : ℕ))) := by
    intro J c
    rw [← Finset.prod_coe_sort J, Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [pow_two_pow_sub_one_eq_prod]
    refine Finset.prod_congr rfl fun m _ => ?_
    simp only [x, vadd_eq_add, Pi.add_apply, Finset.sum_apply, Pi.smul_apply]
    rw [add_comm, add_pow_char_pow, sum_pow_char_pow]
    simp_rw [smul_pow, ZMod.pow_card_pow]
  have hk_anti : StrictAnti k := fun i j hij => by
    simp only [k]
    have := j.2
    have : (i : ℕ) < j := hij
    omega
  -- the terms `J ≠ I₀` vanish
  have hne : ∀ J ∈ Finset.univ.powersetCard t, J ≠ I₀ →
      ∑ c : κ → ZMod 2, ∏ j ∈ J, x c j ^ (2 ^ (r + 1 - j) - 1) = 0 := by
    intro J hJ hJI
    simp_rw [hprod J]
    refine Cslib.sum_cube_prod_affine_eq_zero _ _ fun ℓ hcov => ?_
    by_contra hall
    push Not at hall
    refine hJI (eq_of_covering k hk_anti (fun i => by simp only [k]; omega) I₀ J
      (by rw [(Finset.mem_powersetCard.1 hJ).2, hI₀card]) ℓ hcov fun p q hpq => ?_)
    by_contra hlt
    push Not at hlt
    exact hall p q hpq (by rw [hvlow q.1 q.2 _ hlt, zero_pow (pow_ne_zero _ two_ne_zero)])
  -- the term `J = I₀` is the product of the Moore determinants
  have hI₀term : ∑ c : κ → ZMod 2, ∏ j ∈ I₀, x c j ^ (2 ^ (r + 1 - j) - 1) =
      ∏ i : I₀, (mooreMatrix (u i)).det := by
    simp_rw [hprod I₀]
    rw [Cslib.sum_cube_prod_affine_eq_permanent, ← det_eq_permanent, ← Matrix.det_transpose]
    have hblock : (Matrix.of fun p q : κ => v q.1 q.2 p.1 ^ 2 ^ (p.2 : ℕ)).transpose.BlockTriangular
        Sigma.fst := by
      intro q p hpq
      simp only [Matrix.transpose_apply, Matrix.of_apply]
      rw [hvlow q.1 q.2 _ hpq, zero_pow (pow_ne_zero _ two_ne_zero)]
    rw [hblock.det_fintype]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Matrix.det_reindex_self (Equiv.sigmaSubtype i)]
    congr 1
    ext l m
    change v i l i ^ 2 ^ (m : ℕ) = u i l ^ 2 ^ (m : ℕ)
    rw [hvdiag]
  -- comparing the two computations of the cube sum
  apply hu
  have hsum : ∑ c : κ → ZMod 2, traceSym μ r t (x c) =
      Algebra.trace (ZMod 2) F (μ * ∏ i : I₀, (mooreMatrix (u i)).det) := by
    simp only [traceSym]
    rw [← map_sum, ← Finset.mul_sum, Finset.sum_comm,
      Finset.sum_eq_single_of_mem I₀ (Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hI₀card⟩)
        hne, hI₀term]
  rw [← hsum, hzero]

end Cslib.AffineDisperser
