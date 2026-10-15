/-
Copyright (c) 2026 Karn Seth, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.PairwiseIndependentHash.Affine
public import Complexity.Probability.PairwiseIndependentHash.Shift
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Toeplitz hashing

A *Toeplitz matrix* is constant along each diagonal: its entry in row `i` and column `j` depends
only on `i - j`. An `m × n` Toeplitz matrix is therefore determined by its first row and its first
column, `m + n - 1` entries in all (`Matrix.toeplitz`, `Matrix.exists_toeplitz_eq_iff`,
`Matrix.toeplitz_injective`).

Over a finite field `F`, the maps `x ↦ T x + v` from `F^n` to `F^m`, for a uniformly random
`m × n` Toeplitz matrix `T` and an independent uniformly random vector `v`, form a pairwise
independent hash family (`Cslib.Probability.isPairwiseIndependentHash_toeplitzHash`)
[Katz and Lindell, Exercise 4.26][KatzLindell2020]. This is the affine family
`Cslib.Probability.affineHash` restricted to Toeplitz matrices, with seeds of `n + 2 m - 1`
field elements instead of `m n + m` (`Cslib.Probability.card_toeplitzHash_seed`). The proof
uses the shift criterion `Cslib.Probability.isPairwiseIndependentHash_add_of_surjective`: for
every nonzero `d : F^n`, the Toeplitz matrices `T` reach every vector `T d`
(`Matrix.toeplitz_mulVec_surjective`). Indeed, if `j₀` is the last coordinate with
`d j₀ ≠ 0`, then on Toeplitz matrices supported on the `m` diagonals through column `j₀`, the
map `T ↦ T d` is triangular with diagonal `d j₀`.

## Main definitions

* `Matrix.toeplitz`: the `m × n` Toeplitz matrix with the given `m + n - 1` diagonals.
* `Cslib.Probability.toeplitzHash`: the map `x ↦ T x + v` with seed a Toeplitz matrix `T` and a
  vector `v`.

## Main results

* `Matrix.exists_toeplitz_eq_iff`, `Matrix.toeplitz_injective`: the matrices with at least one
  row and one column whose entries depend only on the difference of their indices are exactly
  the Toeplitz matrices, and each determines its diagonals.
* `Matrix.toeplitz_mulVec_surjective`: over a field, `T ↦ T d` maps Toeplitz matrices onto all
  vectors for every `d ≠ 0`.
* `Cslib.Probability.isPairwiseIndependentHash_toeplitzHash`: the Toeplitz hash family over a
  finite field is pairwise independent.
* `Cslib.Probability.card_toeplitzHash_seed`: its seeds consist of `n + 2 m - 1` field elements.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, Section 4.6][KatzLindell2020]
-/

@[expose] public section

open Finset
open scoped Matrix

namespace Matrix

variable {α : Type*} {m n : ℕ}

/-- The `m × n` *Toeplitz matrix* with diagonals `a`: its entry in row `i` and column `j` is
`a (i - j + n - 1)`. It is constant along each diagonal: `a 0` is the top right corner, the
first row is `a (n - 1), …, a 0`, the first column is `a (n - 1), …, a (m + n - 2)`, and the
last entry `a (m + n - 2)` is the bottom left corner [Katz and Lindell, Exercise 4.26]
[KatzLindell2020]. -/
def toeplitz (a : Fin (m + n - 1) → α) : Matrix (Fin m) (Fin n) α :=
  of fun i j => a ⟨i + (n - 1 - j), by omega⟩

@[simp]
theorem toeplitz_apply (a : Fin (m + n - 1) → α) (i : Fin m) (j : Fin n) :
    toeplitz a i j = a ⟨i + (n - 1 - j), by omega⟩ :=
  rfl

/-- The entries of a Toeplitz matrix depend only on the difference of their indices. -/
theorem toeplitz_apply_eq_of_add_eq (a : Fin (m + n - 1) → α) {i i' : Fin m} {j j' : Fin n}
    (h : (i : ℕ) + j' = i' + j) : toeplitz a i j = toeplitz a i' j' := by
  simp only [toeplitz_apply]
  congr 2
  omega

/-- A Toeplitz matrix with at least one row and one column determines its diagonals. -/
theorem toeplitz_injective (hm : m ≠ 0) (hn : n ≠ 0) :
    Function.Injective (toeplitz : (Fin (m + n - 1) → α) → Matrix (Fin m) (Fin n) α) := by
  intro a b h
  ext k
  obtain ⟨i, j, hij⟩ : ∃ (i : Fin m) (j : Fin n), (i : ℕ) + (n - 1 - j) = k := by
    by_cases hk : n - 1 ≤ (k : ℕ)
    · exact ⟨⟨(k : ℕ) - (n - 1), by omega⟩, ⟨0, by omega⟩, by simp only; omega⟩
    · exact ⟨⟨0, by omega⟩, ⟨n - 1 - (k : ℕ), by omega⟩, by simp only; omega⟩
  rw [show k = ⟨i + (n - 1 - j), by omega⟩ from Fin.ext hij.symm]
  exact congr_fun₂ h i j

/-- A matrix with at least one row and one column is a Toeplitz matrix exactly when its entries
depend only on the difference of their indices. -/
theorem exists_toeplitz_eq_iff (hm : m ≠ 0) (hn : n ≠ 0) {A : Matrix (Fin m) (Fin n) α} :
    (∃ a, toeplitz a = A) ↔
      ∀ (i i' : Fin m) (j j' : Fin n), (i : ℕ) + j' = i' + j → A i j = A i' j' := by
  constructor
  · rintro ⟨a, rfl⟩ i i' j j' h
    exact toeplitz_apply_eq_of_add_eq a h
  · intro hA
    refine ⟨fun k => if n - 1 ≤ (k : ℕ) then A ⟨(k : ℕ) - (n - 1), by omega⟩ ⟨0, by omega⟩
      else A ⟨0, by omega⟩ ⟨n - 1 - (k : ℕ), by omega⟩, ?_⟩
    ext i j
    simp only [toeplitz_apply]
    split_ifs with h
    · exact hA _ _ _ _ (by simp only; omega)
    · exact hA _ _ _ _ (by simp only; omega)

@[simp]
theorem toeplitz_zero [Zero α] : toeplitz (0 : Fin (m + n - 1) → α) = 0 :=
  ext fun _ _ => rfl

theorem toeplitz_add [Add α] (a b : Fin (m + n - 1) → α) :
    toeplitz (a + b) = toeplitz a + toeplitz b :=
  ext fun _ _ => rfl

theorem toeplitz_neg [Neg α] (a : Fin (m + n - 1) → α) : toeplitz (-a) = -toeplitz a :=
  ext fun _ _ => rfl

theorem toeplitz_sub [Sub α] (a b : Fin (m + n - 1) → α) :
    toeplitz (a - b) = toeplitz a - toeplitz b :=
  ext fun _ _ => rfl

theorem toeplitz_smul {R : Type*} [SMul R α] (c : R) (a : Fin (m + n - 1) → α) :
    toeplitz (c • a) = c • toeplitz a :=
  ext fun _ _ => rfl

/-- **Toeplitz matrices reach every vector**: over a field, for every nonzero vector `d`, every
vector is `T d` for some `m × n` Toeplitz matrix `T`. If `j₀` is the last coordinate with
`d j₀ ≠ 0`, then for a Toeplitz matrix `T` supported on the `m` diagonals through column `j₀`,
the `i`-th coordinate of `T d` is `d j₀` times the entry of `T` in row `i` and column `j₀`, plus
entries further down the diagonals; this triangular system can be solved for any `T d`. -/
theorem toeplitz_mulVec_surjective [Field α] {d : Fin n → α} (hd : d ≠ 0) :
    Function.Surjective fun a : Fin (m + n - 1) → α => toeplitz a *ᵥ d := by
  classical
  obtain ⟨j₀, hj₀, hmax⟩ : ∃ j₀, d j₀ ≠ 0 ∧ ∀ j, d j ≠ 0 → j ≤ j₀ := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hd
    obtain ⟨j₀, h₀, hmax⟩ := exists_max_image {j | d j ≠ 0} id (⟨j, by simpa using hj⟩)
    exact ⟨j₀, by simpa using h₀, fun j hj => hmax j (by simpa using hj)⟩
  -- `band w` writes `w` on the `m` diagonals through column `j₀`, starting from row `0`.
  let band : (Fin m → α) →ₗ[α] Fin (m + n - 1) → α := LinearMap.pi fun k =>
    if h : n - 1 - (j₀ : ℕ) ≤ k ∧ (k : ℕ) - (n - 1 - j₀) < m then
      LinearMap.proj (⟨(k : ℕ) - (n - 1 - j₀), h.2⟩ : Fin m)
    else 0
  let L : (Fin m → α) →ₗ[α] Fin m → α :=
    { toFun w := toeplitz (band w) *ᵥ d
      map_add' w w' := by
        rw [map_add, toeplitz_add, add_mulVec]
      map_smul' c w := by
        simp only [RingHom.id_apply]
        rw [map_smul, toeplitz_smul, smul_mulVec] }
  -- If `w` vanishes beyond `i`, then the `i`-th coordinate of `L w` is `w i * d j₀`.
  have hL (w : Fin m → α) (i : Fin m) (hw : ∀ i', i < i' → w i' = 0) : L w i = w i * d j₀ := by
    change ∑ j, toeplitz (band w) i j * d j = w i * d j₀
    rw [sum_eq_single j₀]
    · congr 1
      simp only [toeplitz_apply, band, LinearMap.pi_apply]
      rw [dite_eq_left (by omega)]
      simp only [LinearMap.proj_apply]
      congr 1
      ext
      simp only
      omega
    · intro j _ hj
      by_cases hdj : d j = 0
      · rw [hdj, mul_zero]
      have hlt : (j : ℕ) < j₀ := Fin.lt_def.1 (lt_of_le_of_ne (hmax j hdj) hj)
      simp only [toeplitz_apply, band, LinearMap.pi_apply]
      split_ifs with h
      · rw [LinearMap.proj_apply, hw _ (Fin.lt_def.2 (by simp only; omega)), zero_mul]
      · rw [LinearMap.zero_apply, zero_mul]
    · exact fun h => absurd (mem_univ _) h
  -- `L` is injective: if `L w = 0` with `w ≠ 0`, look at the last `i` with `w i ≠ 0`.
  have hinj : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).2 fun w hw => ?_
    by_contra hne
    obtain ⟨i₁, hi₁⟩ := Function.ne_iff.1 hne
    obtain ⟨i, hi, himax⟩ := exists_max_image {i | w i ≠ 0} id ⟨i₁, by simpa using hi₁⟩
    have hwi : w i ≠ 0 := by simpa using hi
    have hbeyond (i' : Fin m) (hi' : i < i') : w i' = 0 := by
      by_contra h
      exact (himax i' (by simpa using h)).not_gt hi'
    have hLi := hL w i hbeyond
    rw [hw, Pi.zero_apply] at hLi
    exact mul_ne_zero hwi hj₀ hLi.symm
  intro c
  obtain ⟨w, rfl⟩ := LinearMap.injective_iff_surjective.1 hinj c
  exact ⟨band w, rfl⟩

end Matrix

namespace Cslib.Probability

open Matrix

variable {F : Type*} {m n : ℕ}

/-- The affine map `x ↦ T x + v` from `F^n` to `F^m`, with seed `(a, v)` where `T` is the
Toeplitz matrix `Matrix.toeplitz a` with diagonals `a` [Katz and Lindell, Exercise 4.26]
[KatzLindell2020]. -/
def toeplitzHash [NonUnitalNonAssocSemiring F] (p : (Fin (m + n - 1) → F) × (Fin m → F))
    (x : Fin n → F) : Fin m → F :=
  toeplitz p.1 *ᵥ x + p.2

/-- The Toeplitz hash with seed `(a, v)` sends `x` to `T x + v`, where `T = Matrix.toeplitz a`. -/
@[simp]
theorem toeplitzHash_apply [NonUnitalNonAssocSemiring F] (a : Fin (m + n - 1) → F)
    (v : Fin m → F) (x : Fin n → F) : toeplitzHash (a, v) x = toeplitz a *ᵥ x + v :=
  rfl

/-- The Toeplitz hash is the affine hash `Cslib.Probability.affineHash` restricted to Toeplitz
matrices. -/
theorem toeplitzHash_eq_affineHash [NonUnitalNonAssocSemiring F]
    (p : (Fin (m + n - 1) → F) × (Fin m → F)) :
    toeplitzHash p = affineHash (toeplitz p.1, p.2) :=
  rfl

/-- **Toeplitz hashing is pairwise independent**: over a finite field `F`, the maps `x ↦ T x + v`
from `F^n` to `F^m`, for a uniformly random `m × n` Toeplitz matrix `T` and an independent
uniformly random vector `v`, form a pairwise independent hash family [Katz and Lindell,
Exercise 4.26][KatzLindell2020]. -/
theorem isPairwiseIndependentHash_toeplitzHash [Field F] [Fintype F] [DecidableEq F] :
    IsPairwiseIndependentHash
      (toeplitzHash : (Fin (m + n - 1) → F) × (Fin m → F) → (Fin n → F) → Fin m → F) :=
  isPairwiseIndependentHash_add_of_surjective
    (AddMonoidHom.mk' (fun (a : Fin (m + n - 1) → F) (x : Fin n → F) => toeplitz a *ᵥ x)
      fun a b => funext fun x => by rw [Pi.add_apply, toeplitz_add, add_mulVec])
    fun x₁ x₂ hx c => by
      obtain ⟨a, ha⟩ := toeplitz_mulVec_surjective (m := m) (sub_ne_zero.2 hx) c
      refine ⟨a, ?_⟩
      simpa only [AddMonoidHom.mk'_apply, mulVec_sub] using ha

/-- **The seed length of Toeplitz hashing**: the Toeplitz hash family from `F^n` to `F^m` has
`|F| ^ (n + 2 m - 1)` seeds, `m + n - 1` field elements for the matrix and `m` for the offset.
The affine family `Cslib.Probability.affineHash` with the same domain and range has
`|F| ^ (m n + m)` seeds, which is at least as many once `m` and `n` are positive, and strictly
more once they both exceed `1`. -/
theorem card_toeplitzHash_seed [Fintype F] :
    Fintype.card ((Fin (m + n - 1) → F) × (Fin m → F)) = Fintype.card F ^ (n + 2 * m - 1) := by
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    ← pow_add]
  congr 1
  omega

end Cslib.Probability
