/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.LowDegree
public import Complexity.Foundations.Data.BitString.Parity
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic.Ring

/-!
# Parity is far from low-degree functions

Over a field `F` in which `2` is invertible, a function of degree at most `D` agrees with parity on
at most as many inputs as there are sets of at most `n / 2 + D` coordinates
(`BitString.card_agree_parity_le`) [Smolensky1987]. In the signs `yᵢ = 1 - 2 xᵢ` parity is the
product of all signs (`BitString.signMonomial_univ`), and `yᵢ² = 1`. So on the inputs where a
function `P` of degree `D` agrees with parity, a product of more than `n / 2` signs equals `1 - 2 P`
times the product of the other signs, of degree at most `n / 2 + D`. Every function on these inputs
therefore agrees with one of degree at most `n / 2 + D`, and comparing dimensions bounds the number
of inputs. Both steps hold over any finite index type `ι` (`BitString.exists_agree_of_parity`,
`BitString.card_le_of_forall_exists_agree`).

## Main definitions

* `Cslib.BitString.signMonomial`: the product of the signs `1 - 2 xᵢ` over a set of coordinates.

## Main results

* `Cslib.BitString.card_agree_parity_le`: parity is far from low-degree functions.

## References

* [R. Smolensky, *Algebraic methods in the theory of lower bounds for Boolean circuit
  complexity*][Smolensky1987]
-/

@[expose] public section

namespace Cslib.BitString

open Finset

variable {F : Type*} [Field F] {ι : Type*}

variable (F) in
/-- The product of the signs `1 - 2 xᵢ` over `S`. -/
def signMonomial (S : Finset ι) (x : ι → Bool) : F :=
  ∏ i ∈ S, (1 - 2 * bitVal F (x i))

variable (F ι) in
/-- The span of the products of at most `H` signs. -/
def signSpan (H : ℕ) : Submodule F ((ι → Bool) → F) :=
  Submodule.span F (signMonomial F '' {S | S.card ≤ H})

theorem signMonomial_mem_lowDegree (S : Finset ι) :
    signMonomial F S ∈ lowDegree F ι S.card := by
  have hfun : signMonomial F S = ∏ i ∈ S, (1 - 2 * fun x : ι → Bool => bitVal F (x i)) := by
    funext x
    simp [signMonomial, Finset.prod_apply]
  rw [hfun]
  simpa using prod_mem_lowDegree S (a := 1) fun i _ =>
    Submodule.sub_mem _ (one_mem_lowDegree 1) (by
      simpa [two_mul] using Submodule.add_mem _ (bitVal_mem_lowDegree (R := F) i)
        (bitVal_mem_lowDegree (R := F) i))

theorem one_sub_two_mul_bitVal_sq (b : Bool) : (1 - 2 * bitVal F b) ^ 2 = 1 := by
  cases b
  · simp [bitVal]
  · simp only [bitVal, ↓reduceIte]
    ring

theorem signMonomial_sq (S : Finset ι) (x : ι → Bool) : signMonomial F S x ^ 2 = 1 := by
  rw [signMonomial, ← Finset.prod_pow]
  exact Finset.prod_eq_one fun i _ => one_sub_two_mul_bitVal_sq (x i)

theorem signMonomial_mul_compl [Fintype ι] [DecidableEq ι] (S : Finset ι) (x : ι → Bool) :
    signMonomial F S x * signMonomial F Sᶜ x = signMonomial F univ x :=
  Finset.prod_mul_prod_compl S _

/-- The product of the signs over `s` is the parity of the bits in `s`, in signs. -/
theorem signMonomial_eq_parityOn (s : Finset ι) (x : ι → Bool) :
    signMonomial F s x = 1 - 2 * bitVal F (parityOn s x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [signMonomial]
  | insert i s hi ih =>
    rw [signMonomial, prod_insert hi, ← signMonomial, ih, parityOn_insert hi]
    cases x i <;> cases parityOn s x <;> simp only [bitVal, Bool.xor_true, Bool.xor_false,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte] <;> ring

/-- The product of all signs is parity in signs. -/
theorem signMonomial_univ {n : ℕ} (x : BitString n) :
    signMonomial F univ x = 1 - 2 * bitVal F (parity n x) :=
  signMonomial_eq_parityOn univ x

theorem signSpan_mono {H K : ℕ} (hHK : H ≤ K) : signSpan F ι H ≤ signSpan F ι K :=
  Submodule.span_mono (Set.image_mono fun _ hS => le_trans hS hHK)

/-- Each monomial expands into products of signs over its subsets. -/
theorem monomial_mem_signSpan [Invertible (2 : F)] (S : Finset ι) :
    monomial F S ∈ signSpan F ι S.card := by
  classical
  have hfun : monomial F S = ∑ T ∈ S.powerset,
      (⅟2 ^ S.card * (-1) ^ T.card : F) • signMonomial F T := by
    funext x
    simp only [monomial, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, signMonomial]
    have hsplit : ∏ i ∈ S, bitVal F (x i) = ∏ i ∈ S, (⅟2 * (-(1 - 2 * bitVal F (x i)) + 1)) :=
      Finset.prod_congr rfl fun i _ => by
        rw [show -(1 - 2 * bitVal F (x i)) + 1 = 2 * bitVal F (x i) by ring, ← mul_assoc,
          invOf_mul_self, one_mul]
    rw [hsplit, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun T hT => ?_
    rw [Finset.prod_const_one, mul_one, Finset.prod_neg]
    ring
  rw [hfun]
  exact Submodule.sum_mem _ fun T hT => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨T, Finset.card_le_card (Finset.mem_powerset.mp hT), rfl⟩)

theorem lowDegree_le_signSpan [Invertible (2 : F)] (H : ℕ) :
    lowDegree F ι H ≤ signSpan F ι H := by
  rw [lowDegree, Submodule.span_le]
  rintro _ ⟨S, hS, rfl⟩
  exact signSpan_mono hS (monomial_mem_signSpan S)

variable [Fintype ι]

/-- If `Q` has degree at most `D` and agrees with the product of all signs on `G`, every function
agrees on `G` with a function of degree at most `|ι| / 2 + D`. -/
theorem exists_agree_of_parity [Invertible (2 : F)] {D : ℕ} {Q : (ι → Bool) → F}
    (hQ : Q ∈ lowDegree F ι D) (G : Finset (ι → Bool))
    (hG : ∀ x ∈ G, Q x = signMonomial F univ x) (f : (ι → Bool) → F) :
    ∃ p ∈ lowDegree F ι (Fintype.card ι / 2 + D), ∀ x ∈ G, p x = f x := by
  classical
  have hf : f ∈ signSpan F ι (Fintype.card ι) :=
    lowDegree_le_signSpan _ (mem_lowDegree_self f)
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨S, -, rfl⟩ := hg
    by_cases hS : S.card ≤ Fintype.card ι / 2
    · exact ⟨signMonomial F S, lowDegree_mono (by omega) (signMonomial_mem_lowDegree S),
        fun _ _ => rfl⟩
    · refine ⟨Q * signMonomial F Sᶜ, ?_, fun x hx => ?_⟩
      · have hc : Sᶜ.card ≤ Fintype.card ι / 2 := by
          rw [card_compl]
          omega
        exact lowDegree_mono (by omega) (mul_mem_lowDegree hQ (signMonomial_mem_lowDegree Sᶜ))
      · rw [Pi.mul_apply, hG x hx, ← signMonomial_mul_compl S x, mul_assoc, ← sq,
          signMonomial_sq, mul_one]
  | zero => exact ⟨0, Submodule.zero_mem _, fun _ _ => rfl⟩
  | add f g _ _ hf hg =>
    obtain ⟨p, hp, hpx⟩ := hf
    obtain ⟨q, hq, hqx⟩ := hg
    exact ⟨p + q, Submodule.add_mem _ hp hq, fun x hx => by simp [hpx x hx, hqx x hx]⟩
  | smul c f _ hf =>
    obtain ⟨p, hp, hpx⟩ := hf
    exact ⟨c • p, Submodule.smul_mem _ c hp, fun x hx => by simp [hpx x hx]⟩

/-- If every function agrees on `G` with a function of degree at most `H`, then `G` has at most as
many points as there are sets of at most `H` coordinates. -/
theorem card_le_of_forall_exists_agree {H : ℕ} (G : Finset (ι → Bool))
    (hG : ∀ f : (ι → Bool) → F, ∃ p ∈ lowDegree F ι H, ∀ x ∈ G, p x = f x) :
    #G ≤ #(univ.filter fun S : Finset ι => S.card ≤ H) := by
  classical
  -- restricting to `G` is onto
  let restrict : lowDegree F ι H →ₗ[F] (G → F) :=
    { toFun := fun p x => p.1 x.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hsurj : Function.Surjective restrict := fun g => by
    obtain ⟨p, hp, hpx⟩ := hG fun x => if hx : x ∈ G then g ⟨x, hx⟩ else 0
    refine ⟨⟨p, hp⟩, funext fun x => ?_⟩
    change p x.1 = g x
    simpa using hpx x.1 x.2
  have h := LinearMap.finrank_range_le restrict
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_fintype_fun_eq_card,
    Fintype.card_coe] at h
  exact h.trans (finrank_lowDegree_le H)

/-- **Parity is far from low-degree functions.** A function of degree at most `D` agrees with
parity on at most as many inputs as there are sets of at most `n / 2 + D` coordinates. -/
theorem card_agree_parity_le [DecidableEq F] [Invertible (2 : F)] {n D : ℕ}
    {P : BitString n → F} (hP : P ∈ lowDegree F (Fin n) D) :
    #(univ.filter fun x => P x = bitVal F (parity n x)) ≤
      #(univ.filter fun S : Finset (Fin n) => S.card ≤ n / 2 + D) := by
  have h := card_le_of_forall_exists_agree _ (exists_agree_of_parity (Q := 1 - 2 • P)
    (Submodule.sub_mem _ (one_mem_lowDegree D) (Submodule.smul_of_tower_mem _ 2 hP))
    (univ.filter fun x => P x = bitVal F (parity n x)) fun x hx => by
      rw [mem_filter] at hx
      rw [signMonomial_univ, ← hx.2]
      simp [two_mul])
  rwa [Fintype.card_fin] at h

end Cslib.BitString
