/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Frontier.Extractor
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Aggregating good second-source fixings for sumset extractors

Conditional outcome mass on a large set of second-source inputs gives unconditional outcome mass on
the product of two flat source sets. Counting ordered pairs `(x, y) ∈ P ×ˢ Q` preserves repeated sum
values `x + y` with their multiplicity. This is the finite averaging step after the majority
analysis in the [Chattopadhyay and Liao][ChattopadhyayLiao2022] sumset-extractor route (Lemma 5.4).

We also prove that the finite-set formulation `FlatSumsetExtractor f K ν` is equivalent on finite
types to `SumsetBias {z | f z = true} K ν` from
`Complexity.Computability.Circuit.Frontier.Extractor`.

## Main definitions

* `Cslib.Circuits.Frontier.sumsetOnes`: the ordered pairs `(x, y) ∈ P ×ˢ Q` on which `f (x + y)` is
  `true`.
* `Cslib.Circuits.Frontier.FlatSumsetExtractor`: flat-source sumset bias bound on `Finset G`.

## Main results

* `Cslib.Circuits.Frontier.flatSumsetExtractor_iff_sumsetBias`: equivalence of
  `FlatSumsetExtractor f K ν` and `SumsetBias {z | f z = true} K ν` on finite types.
* `Cslib.Circuits.Frontier.FlatSumsetExtractor.of_many_good_fibers`,
  `Cslib.Circuits.Frontier.SumsetBias.of_many_good_fibers`: lower bounds on both Boolean outcomes on
  a `θ`-fraction of second-source fibers imply sumset bias `1 / 2 - ρ * θ`.
* `Cslib.Circuits.Frontier.FlatSumsetExtractor.of_half_good_fibers`,
  `Cslib.Circuits.Frontier.SumsetBias.of_half_good_fibers`: specialization to `θ = 1 / 2`.

## References

* [E. Chattopadhyay and J.-J. Liao, *Extractors for Sum of Two Sources*][ChattopadhyayLiao2022]
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

variable {G : Type*} [Add G]

/-- The ordered pairs `(x, y) ∈ P ×ˢ Q` whose sum `x + y` satisfies `f (x + y) = true`. -/
def sumsetOnes (f : G → Bool) (P Q : Finset G) : Finset (G × G) :=
  (P ×ˢ Q).filter fun xy => f (xy.1 + xy.2) = true

/-- `f : G → Bool` is a flat `(K, ν)`-sumset extractor if for all `P, Q : Finset G` of cardinality
at least `K`, the fraction of pairs `(x, y) ∈ P ×ˢ Q` with `f (x + y) = true` lies in
`[1 / 2 - ν, 1 / 2 + ν]`. -/
def FlatSumsetExtractor (f : G → Bool) (K : ℕ) (ν : ℝ) : Prop :=
  ∀ P Q : Finset G, K ≤ P.card → K ≤ Q.card →
    (1 / 2 - ν) * (P.card * Q.card) ≤ (sumsetOnes f P Q).card ∧
      ((sumsetOnes f P Q).card : ℝ) ≤ (1 / 2 + ν) * (P.card * Q.card)

theorem FlatSumsetExtractor.mono {f : G → Bool} {K K' : ℕ} {ν ν' : ℝ}
    (h : FlatSumsetExtractor f K ν) (hK : K ≤ K') (hν : ν ≤ ν') :
    FlatSumsetExtractor f K' ν' := by
  intro P Q hP hQ
  have hPQ := h P Q (hK.trans hP) (hK.trans hQ)
  have hprod : (0 : ℝ) ≤ (P.card : ℝ) * Q.card := by positivity
  exact ⟨by nlinarith [hPQ.1], by nlinarith [hPQ.2]⟩

private theorem ncard_sep_coe_prod_eq_card_sumsetOnes (f : G → Bool) (P Q : Finset G) :
    {p ∈ (P : Set G) ×ˢ (Q : Set G) | p.1 + p.2 ∈ {z | f z = true}}.ncard =
      (sumsetOnes f P Q).card := by
  have hset :
      {p ∈ (P : Set G) ×ˢ (Q : Set G) | p.1 + p.2 ∈ {z | f z = true}} =
        ((sumsetOnes f P Q : Finset (G × G)) : Set (G × G)) := by
    ext ⟨x, y⟩
    simp only [sumsetOnes, Set.mem_prod, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_product, Set.mem_ofPred_eq]
  rw [hset, Set.ncard_coe_finset]

/-- Every `SumsetBias {z | f z = true} K ν` witness induces `FlatSumsetExtractor f K ν`. -/
theorem SumsetBias.flatSumsetExtractor {f : G → Bool} {K : ℕ} {ν : ℝ}
    (h : SumsetBias {z | f z = true} K ν) : FlatSumsetExtractor f K ν := by
  intro P Q hP hQ
  have hA : K ≤ (P : Set G).ncard := by simpa only [Set.ncard_coe_finset] using hP
  have hB : K ≤ (Q : Set G).ncard := by simpa only [Set.ncard_coe_finset] using hQ
  have hbias := h (P : Set G) (Q : Set G) hA hB
  rw [ncard_sep_coe_prod_eq_card_sumsetOnes, Set.ncard_coe_finset, Set.ncard_coe_finset,
    abs_le] at hbias
  exact ⟨by linarith [hbias.1], by linarith [hbias.2]⟩

/-- On a finite type `G`, `FlatSumsetExtractor f K ν` implies `SumsetBias {z | f z = true} K ν`. -/
theorem FlatSumsetExtractor.sumsetBias [Finite G] {f : G → Bool} {K : ℕ} {ν : ℝ}
    (h : FlatSumsetExtractor f K ν) : SumsetBias {z | f z = true} K ν := by
  intro A B hA hB
  have hAfin : A.Finite := Set.toFinite A
  have hBfin : B.Finite := Set.toFinite B
  let P := hAfin.toFinset
  let Q := hBfin.toFinset
  have hPcard : P.card = A.ncard := Set.ncard_eq_toFinset_card A hAfin |>.symm
  have hQcard : Q.card = B.ncard := Set.ncard_eq_toFinset_card B hBfin |>.symm
  have hPQ := h P Q (hPcard.symm ▸ hA) (hQcard.symm ▸ hB)
  have hones : {p ∈ A ×ˢ B | p.1 + p.2 ∈ {z | f z = true}}.ncard = (sumsetOnes f P Q).card := by
    have hAcoe : (P : Set G) = A := hAfin.coe_toFinset
    have hBcoe : (Q : Set G) = B := hBfin.coe_toFinset
    simpa only [hAcoe, hBcoe] using ncard_sep_coe_prod_eq_card_sumsetOnes f P Q
  rw [hones, ← hPcard, ← hQcard, abs_le]
  exact ⟨by linarith [hPQ.1], by linarith [hPQ.2]⟩

/-- On a finite type `G`, `FlatSumsetExtractor f K ν` is equivalent to
`SumsetBias {z | f z = true} K ν`. -/
theorem flatSumsetExtractor_iff_sumsetBias [Finite G] {f : G → Bool} {K : ℕ} {ν : ℝ} :
    FlatSumsetExtractor f K ν ↔ SumsetBias {z | f z = true} K ν :=
  ⟨FlatSumsetExtractor.sumsetBias, SumsetBias.flatSumsetExtractor⟩

private theorem card_outcome_product {α β : Type*} (P : Finset α) (Q : Finset β)
    (f : α → β → Bool) (b : Bool) :
    ((P ×ˢ Q).filter fun xy => f xy.1 xy.2 = b).card =
      ∑ y ∈ Q, (P.filter fun x => f x y = b).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
  rw [Finset.sum_comm]

private theorem card_outcome_ge_of_good_fibers {α β : Type*}
    (P : Finset α) (Q Good : Finset β) (f : α → β → Bool) (b : Bool)
    (positive : 0 < P.card) (inside : Good ⊆ Q) {ρ θ : ℝ} (hρ : 0 ≤ ρ)
    (many : θ * Q.card ≤ Good.card)
    (fibers : ∀ y ∈ Good, ρ ≤ ∑ x ∈ P, if f x y = b then 1 / (P.card : ℝ) else 0) :
    ρ * θ * (P.card * Q.card) ≤
      (((P ×ˢ Q).filter fun xy => f xy.1 xy.2 = b).card : ℝ) := by
  have positiveReal : (0 : ℝ) < P.card := by exact_mod_cast positive
  have row : ∀ y ∈ Good, ρ * P.card ≤ ((P.filter fun x => f x y = b).card : ℝ) := by
    intro y hy
    have count : (∑ x ∈ P, if f x y = b then 1 / (P.card : ℝ) else 0) =
        (P.filter fun x => f x y = b).card / (P.card : ℝ) := by
      rw [← Finset.sum_filter]
      simp [div_eq_mul_inv]
    have bound := fibers y hy
    rw [count] at bound
    exact (le_div_iff₀ positiveReal).mp bound
  calc
    ρ * θ * (P.card * Q.card) = (ρ * P.card) * (θ * Q.card) := by ring
    _ ≤ (ρ * P.card) * Good.card :=
      mul_le_mul_of_nonneg_left many (mul_nonneg hρ (Nat.cast_nonneg _))
    _ = ∑ _y ∈ Good, ρ * P.card := by simp [mul_comm]
    _ ≤ ∑ y ∈ Good, ((P.filter fun x => f x y = b).card : ℝ) :=
      Finset.sum_le_sum row
    _ ≤ ∑ y ∈ Q, ((P.filter fun x => f x y = b).card : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg inside (fun _ _ _ => Nat.cast_nonneg _)
    _ = (((P ×ˢ Q).filter fun xy => f xy.1 xy.2 = b).card : ℝ) := by
      exact_mod_cast (card_outcome_product P Q f b).symm

/-- **Second-source fiber averaging (`FlatSumsetExtractor` form):** if on at least a `θ`-fraction
of second-source elements `y ∈ Q`, both Boolean outcomes `f (x + y) = b` have uniform probability at
least `ρ` over `x ∈ P`, then `f` is a flat `(K, 1 / 2 - ρ * θ)`-sumset extractor. -/
theorem FlatSumsetExtractor.of_many_good_fibers {K : ℕ} {f : G → Bool} {ρ θ : ℝ}
    (positive : 0 < K) (hρ : 0 ≤ ρ)
    (good : ∀ P Q : Finset G, K ≤ P.card → K ≤ Q.card →
      ∃ Good ⊆ Q, θ * Q.card ≤ Good.card ∧
        ∀ y ∈ Good, ∀ b : Bool,
          ρ ≤ ∑ x ∈ P, if f (x + y) = b then 1 / (P.card : ℝ) else 0) :
    FlatSumsetExtractor f K (1 / 2 - ρ * θ) := by
  intro P Q hP hQ
  obtain ⟨Good, inside, many, fibers⟩ := good P Q hP hQ
  have trueCount := card_outcome_ge_of_good_fibers P Q Good (fun x y => f (x + y))
    true (positive.trans_le hP) inside hρ many (fun y hy => fibers y hy true)
  have falseCount := card_outcome_ge_of_good_fibers P Q Good (fun x y => f (x + y))
    false (positive.trans_le hP) inside hρ many (fun y hy => fibers y hy false)
  have total : ((sumsetOnes f P Q).card : ℝ) +
      (((P ×ˢ Q).filter fun xy => f (xy.1 + xy.2) = false).card : ℝ) =
        (P.card : ℝ) * Q.card := by
    have partition := Finset.card_filter_add_card_filter_not
      (s := P ×ˢ Q) (p := fun xy => f (xy.1 + xy.2) = true)
    simp only [Bool.not_eq_true, Finset.card_product] at partition
    exact_mod_cast partition
  change ρ * θ * ((P.card : ℝ) * Q.card) ≤ (sumsetOnes f P Q).card at trueCount
  constructor <;> nlinarith only [trueCount, falseCount, total]

/-- **Second-source fiber averaging (`θ = 1 / 2`):** if at least half of the second-source fibers
give each Boolean outcome probability at least `ρ`, then `f` has flat sumset bias at most
`(1 - ρ) / 2`. -/
theorem FlatSumsetExtractor.of_half_good_fibers {K : ℕ} {f : G → Bool} {ρ : ℝ}
    (positive : 0 < K) (hρ : 0 ≤ ρ)
    (good : ∀ P Q : Finset G, K ≤ P.card → K ≤ Q.card →
      ∃ Good ⊆ Q, (Q.card : ℝ) / 2 ≤ Good.card ∧
        ∀ y ∈ Good, ∀ b : Bool,
          ρ ≤ ∑ x ∈ P, if f (x + y) = b then 1 / (P.card : ℝ) else 0) :
    FlatSumsetExtractor f K ((1 - ρ) / 2) := by
  have h := FlatSumsetExtractor.of_many_good_fibers (θ := 1 / 2) positive hρ fun P Q hP hQ => by
    obtain ⟨Good, inside, many, fibers⟩ := good P Q hP hQ
    exact ⟨Good, inside, by linarith, fibers⟩
  exact h.mono le_rfl (by linarith)

/-- **Second-source fiber averaging (`SumsetBias` form):** on a finite type `G`, if on at least a
`θ`-fraction of `y ∈ Q`, both Boolean outcomes `f (x + y) = b` have uniform probability at least `ρ`
over `x ∈ P`, then `{z | f z = true}` has sumset bias at most `1 / 2 - ρ * θ`. -/
theorem SumsetBias.of_many_good_fibers [Finite G] {K : ℕ} {f : G → Bool} {ρ θ : ℝ}
    (positive : 0 < K) (hρ : 0 ≤ ρ)
    (good : ∀ P Q : Finset G, K ≤ P.card → K ≤ Q.card →
      ∃ Good ⊆ Q, θ * Q.card ≤ Good.card ∧
        ∀ y ∈ Good, ∀ b : Bool,
          ρ ≤ ∑ x ∈ P, if f (x + y) = b then 1 / (P.card : ℝ) else 0) :
    SumsetBias {z | f z = true} K (1 / 2 - ρ * θ) :=
  (FlatSumsetExtractor.of_many_good_fibers positive hρ good).sumsetBias

/-- **Second-source fiber averaging (`SumsetBias` form with `θ = 1 / 2`).** -/
theorem SumsetBias.of_half_good_fibers [Finite G] {K : ℕ} {f : G → Bool} {ρ : ℝ}
    (positive : 0 < K) (hρ : 0 ≤ ρ)
    (good : ∀ P Q : Finset G, K ≤ P.card → K ≤ Q.card →
      ∃ Good ⊆ Q, (Q.card : ℝ) / 2 ≤ Good.card ∧
        ∀ y ∈ Good, ∀ b : Bool,
          ρ ≤ ∑ x ∈ P, if f (x + y) = b then 1 / (P.card : ℝ) else 0) :
    SumsetBias {z | f z = true} K ((1 - ρ) / 2) :=
  (FlatSumsetExtractor.of_half_good_fibers positive hρ good).sumsetBias

end Cslib.Circuits.Frontier
