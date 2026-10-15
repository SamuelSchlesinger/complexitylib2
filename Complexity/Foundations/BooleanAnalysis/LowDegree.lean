/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Foundations.Data.BitString
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Low-degree functions on the Boolean cube

Reading the bits of `x : BitString n` as `0` and `1` in a commutative ring `R` (`BitString.bitVal`),
the monomial of a set `S` of coordinates is the function `x ↦ ∏_{i ∈ S} x i`
(`BitString.monomial`), and the functions of degree at most `D` are the `R`-linear combinations of
monomials of at most `D` coordinates (`BitString.lowDegree`). This is the degree of the multilinear
polynomial representing a function on the cube, without formal polynomials: on bits every monomial
is idempotent, so products of monomials are monomials (`BitString.monomial_mul`) and degrees add
under multiplication (`BitString.mul_mem_lowDegree`). Every function has degree at most `n`
(`BitString.mem_lowDegree_self`), and the functions of degree at most `D` span a space of dimension
at most the number of sets of at most `D` coordinates (`BitString.finrank_lowDegree_le`).

These are the polynomials of Razborov's and Smolensky's approximation method
[Razborov1987], [Smolensky1987].

## Main definitions

* `Cslib.BitString.bitVal`, `Cslib.BitString.monomial`, `Cslib.BitString.lowDegree`.

## Main results

* `Cslib.BitString.mul_mem_lowDegree`: degrees add under multiplication.
* `Cslib.BitString.mem_lowDegree_self`: every function has degree at most `n`.
* `Cslib.BitString.finrank_lowDegree_le`: the dimension of the functions of degree at most `D`.

## References

* [A. A. Razborov, *Lower bounds on the size of bounded depth circuits over a complete basis with
  logical addition*][Razborov1987]
* [R. Smolensky, *Algebraic methods in the theory of lower bounds for Boolean circuit
  complexity*][Smolensky1987]
-/

@[expose] public section

namespace Cslib.BitString

open Finset

variable (R : Type*) [CommRing R] {n : ℕ}

/-- A bit read as `0` or `1` in `R`. -/
def bitVal (b : Bool) : R :=
  if b then 1 else 0

/-- The monomial of a set `S` of coordinates: the product of the selected bits, read in `R`. The
empty monomial is the constant `1`. -/
def monomial (S : Finset (Fin n)) (x : BitString n) : R :=
  ∏ i ∈ S, bitVal R (x i)

/-- The functions on the cube of degree at most `D`: the `R`-linear span of the monomials of at most
`D` coordinates. -/
def lowDegree (n D : ℕ) : Submodule R (BitString n → R) :=
  Submodule.span R (monomial R '' {S | S.card ≤ D})

variable {R}

@[simp] theorem bitVal_true : bitVal R true = 1 := rfl

@[simp] theorem bitVal_false : bitVal R false = 0 := rfl

theorem bitVal_not (b : Bool) : bitVal R (!b) = 1 - bitVal R b := by
  cases b <;> simp [bitVal]

/-- A monomial is `1` where all its coordinates are true and `0` elsewhere. -/
theorem monomial_apply (S : Finset (Fin n)) (x : BitString n) :
    monomial R S x = if ∀ i ∈ S, x i = true then 1 else 0 := by
  unfold monomial bitVal
  rw [prod_boole]
  split_ifs <;> rfl

/-- The product of two monomials is the monomial of the union. -/
theorem monomial_mul (S T : Finset (Fin n)) :
    monomial R S * monomial R T = monomial R (S ∪ T) := by
  funext x
  simp only [Pi.mul_apply, monomial_apply, mem_union, or_imp, forall_and]
  split_ifs <;> simp_all

@[simp] theorem monomial_empty : monomial R (∅ : Finset (Fin n)) = 1 := by
  funext x
  simp [monomial]

theorem monomial_singleton (i : Fin n) : monomial R {i} = fun x => bitVal R (x i) := by
  funext x
  simp [monomial]

theorem monomial_mem_lowDegree {S : Finset (Fin n)} {D : ℕ} (hS : S.card ≤ D) :
    monomial R S ∈ lowDegree R n D :=
  Submodule.subset_span ⟨S, hS, rfl⟩

theorem lowDegree_mono {D E : ℕ} (hDE : D ≤ E) : lowDegree R n D ≤ lowDegree R n E :=
  Submodule.span_mono (Set.image_mono fun _ hS => le_trans hS hDE)

theorem one_mem_lowDegree (D : ℕ) : (1 : BitString n → R) ∈ lowDegree R n D := by
  rw [← monomial_empty]
  exact monomial_mem_lowDegree (by simp)

theorem const_mem_lowDegree (D : ℕ) (c : R) : (fun _ : BitString n => c) ∈ lowDegree R n D := by
  convert Submodule.smul_mem _ c (one_mem_lowDegree (R := R) (n := n) D) using 1
  funext x
  simp

theorem bitVal_mem_lowDegree (i : Fin n) :
    (fun x : BitString n => bitVal R (x i)) ∈ lowDegree R n 1 :=
  monomial_singleton (R := R) i ▸ monomial_mem_lowDegree (by simp)

/-- Degrees add under multiplication. -/
theorem lowDegree_mul_le (a b : ℕ) : lowDegree R n a * lowDegree R n b ≤ lowDegree R n (a + b) := by
  rw [lowDegree, lowDegree, Submodule.span_mul_span, Submodule.span_le]
  rintro _ ⟨_, ⟨S, hS, rfl⟩, _, ⟨T, hT, rfl⟩, rfl⟩
  change monomial R S * monomial R T ∈ lowDegree R n (a + b)
  rw [monomial_mul]
  exact monomial_mem_lowDegree ((card_union_le S T).trans (Nat.add_le_add hS hT))

theorem mul_mem_lowDegree {a b : ℕ} {f g : BitString n → R} (hf : f ∈ lowDegree R n a)
    (hg : g ∈ lowDegree R n b) : f * g ∈ lowDegree R n (a + b) :=
  lowDegree_mul_le a b (Submodule.mul_mem_mul hf hg)

theorem pow_mem_lowDegree {a : ℕ} {f : BitString n → R} (hf : f ∈ lowDegree R n a) (k : ℕ) :
    f ^ k ∈ lowDegree R n (k * a) := by
  induction k with
  | zero => simpa using one_mem_lowDegree (R := R) (n := n) 0
  | succ k ih =>
    rw [pow_succ, Nat.succ_mul]
    exact mul_mem_lowDegree ih hf

theorem prod_mem_lowDegree {ι : Type*} (s : Finset ι) {a : ℕ} {f : ι → BitString n → R}
    (hf : ∀ i ∈ s, f i ∈ lowDegree R n a) : ∏ i ∈ s, f i ∈ lowDegree R n (s.card * a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one_mem_lowDegree (R := R) (n := n) 0
  | insert i s hi ih =>
    rw [prod_insert hi, card_insert_of_notMem hi, Nat.succ_mul, Nat.add_comm]
    exact mul_mem_lowDegree (hf i (mem_insert_self i s))
      (ih fun j hj => hf j (mem_insert_of_mem hj))

theorem sum_mem_lowDegree {ι : Type*} (s : Finset ι) {a : ℕ} {f : ι → BitString n → R}
    (hf : ∀ i ∈ s, f i ∈ lowDegree R n a) : ∑ i ∈ s, f i ∈ lowDegree R n a :=
  Submodule.sum_mem _ hf

theorem one_sub_mem_lowDegree {a : ℕ} {f : BitString n → R} (hf : f ∈ lowDegree R n a) :
    1 - f ∈ lowDegree R n a :=
  Submodule.sub_mem _ (one_mem_lowDegree a) hf

/-- Negating all the bits of the input preserves the degree. -/
theorem comp_not_mem_lowDegree {D : ℕ} {f : BitString n → R} (hf : f ∈ lowDegree R n D) :
    (fun x => f fun i => !x i) ∈ lowDegree R n D := by
  suffices h : lowDegree R n D ≤
      (lowDegree R n D).comap (LinearMap.funLeft R R fun (x : BitString n) i => !x i) from h hf
  refine Submodule.span_le.2 ?_
  rintro _ ⟨S, hS, rfl⟩
  have h : (fun x : BitString n => monomial R S fun i => !x i) =
      ∏ i ∈ S, (1 - fun x : BitString n => bitVal R (x i)) := by
    funext x
    simp [monomial, Finset.prod_apply, bitVal_not]
  change (fun x : BitString n => monomial R S fun i => !x i) ∈ lowDegree R n D
  rw [h]
  exact lowDegree_mono (by simpa using hS)
    (prod_mem_lowDegree S fun i _ => one_sub_mem_lowDegree (bitVal_mem_lowDegree i))

/-- **Every function on the cube has degree at most `n`**: it is the sum, over the points `a`, of
its value at `a` times the indicator of `a`, a product of `n` functions of degree one. -/
theorem mem_lowDegree_self (f : BitString n → R) : f ∈ lowDegree R n n := by
  classical
  -- the indicator of `a`
  have hδ : ∀ a : BitString n, (fun x : BitString n => ∏ i, if a i then bitVal R (x i)
      else 1 - bitVal R (x i)) ∈ lowDegree R n n := fun a => by
    have := prod_mem_lowDegree (R := R) (n := n) (a := 1) univ
      (f := fun i x => if a i then bitVal R (x i) else 1 - bitVal R (x i)) fun i _ => by
        by_cases hi : a i
        · simp only [hi, ↓reduceIte]
          exact bitVal_mem_lowDegree i
        · simp only [hi, Bool.false_eq_true, ↓reduceIte]
          exact one_sub_mem_lowDegree (bitVal_mem_lowDegree i)
    simpa [card_univ, Fintype.card_fin, Finset.prod_fn] using this
  have hf : f = ∑ a, f a • fun x : BitString n => ∏ i, if a i then bitVal R (x i)
      else 1 - bitVal R (x i) := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single x]
    · rw [Finset.prod_eq_one fun i _ => by cases x i <;> simp [bitVal]]
      simp
    · intro a _ hax
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hax
      rw [Finset.prod_eq_zero (mem_univ i) (by cases ha : a i <;> cases hx : x i <;>
        simp_all [bitVal]), mul_zero]
    · simp
  rw [hf]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hδ a)

/-- **The dimension of the functions of degree at most `D`** is at most the number of sets of at
most `D` coordinates. -/
theorem finrank_lowDegree_le [StrongRankCondition R] (D : ℕ) :
    Module.finrank R (lowDegree R n D) ≤ #(univ.filter fun S : Finset (Fin n) => S.card ≤ D) := by
  classical
  rw [lowDegree, show monomial R '' {S | S.card ≤ D} =
      ((univ.filter fun S : Finset (Fin n) => S.card ≤ D).image (monomial R) : Set _) by
    ext f
    simp]
  exact (finrank_span_finset_le_card _).trans card_image_le

end Cslib.BitString
