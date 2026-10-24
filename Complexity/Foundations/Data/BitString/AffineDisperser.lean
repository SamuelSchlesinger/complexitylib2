/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Foundations.Data.BitString
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Affine dispersers

Over `𝔽₂`, a map between additive groups is *affine* when it preserves sums of three points:
`g (x + y + z) = g x + g y + g z` (`Cslib.BitString.IsAffine`). For maps between `𝔽₂`-vector
spaces this is the usual notion, a translate of a linear map (`Cslib.BitString.IsAffine.toAffineMap`
in `Complexity/Foundations/Combinatorics/AffineDisperser/AffineSubspace.lean`), and the image of an
injective affine map from `BitString d` is an affine subspace of dimension `d` of the cube
`BitString n` (`Cslib.BitString.IsAffine.finrank_direction_map_top`), so nonconstancy on every
`d`-dimensional affine subspace gives an affine disperser
(`Cslib.BitString.isAffineDisperser_of_forall_exists_ne`); everything in this file is stated in
terms of affine maps.

A Boolean function `f` on `n` bits is an *affine disperser for dimension `d`* when it is
nonconstant on the image of every injective affine map from `BitString d`
(`Cslib.BitString.IsAffineDisperser`), informally on every affine subspace of dimension `d`.
Dispersers for dimension `d` are dispersers for every larger dimension
(`IsAffineDisperser.mono`), and no function is a disperser for dimension `0`
(`not_isAffineDisperser_zero`).

Affine dispersers exist for every dimension `d` with `n (d + 1) + 1 < 2 ^ d`
(`exists_isAffineDisperser`), for instance for `n = 100` and `d = 11`. The proof counts: an affine
map from `BitString d` is determined by its values at `0` and at the unit vectors
(`IsAffine.ext_single`), so there are at most `2 ^ (n (d + 1))` of them (`card_isAffine_le`), and
at most `2 · 2 ^ (2 ^ n - 2 ^ d)` functions are constant on the image of each injective one
(`card_const_on_range_le`); together these are fewer than the `2 ^ 2 ^ n` functions on `n` bits.

## Main definitions

* `Cslib.BitString.IsAffine`: affine maps over `𝔽₂`.
* `Cslib.BitString.IsAffineDisperser`: affine dispersers.
* `Cslib.BitString.zeroExtend`: extension of a bit string by zeros to a longer length.

## Main results

* `Cslib.BitString.IsAffine.comp`: affine maps compose.
* `Cslib.BitString.IsAffineDisperser.mono`: dispersers for smaller dimension are dispersers for
  larger dimension.
* `Cslib.BitString.exists_isAffineDisperser`: affine dispersers exist for every dimension `d`
  with `n (d + 1) + 1 < 2 ^ d`.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*, Definition 2.1][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.BitString

/-- A map is affine over `𝔽₂` when it preserves sums of three points. -/
def IsAffine {α β : Type*} [Add α] [Add β] (g : α → β) : Prop :=
  ∀ x y z, g (x + y + z) = g x + g y + g z

/-- The composition of affine maps is affine. -/
theorem IsAffine.comp {α β γ : Type*} [Add α] [Add β] [Add γ] {g : β → γ} {h : α → β}
    (hg : IsAffine g) (hh : IsAffine h) : IsAffine (g ∘ h) := fun x y z => by
  simp only [Function.comp_apply, hh x y z, hg (h x) (h y) (h z)]

/-- Constant maps into a group in which every element is its own negative (`b + b = 0`) are
affine. -/
theorem isAffine_const {α β : Type*} [Add α] [AddGroup β] (h : ∀ b : β, b + b = 0) (c : β) :
    IsAffine (fun _ : α => c) := fun _ _ _ => by rw [h, zero_add]

/-- `f` is an affine disperser for dimension `d`: it is nonconstant on the image of every
injective affine map from `BitString d`. By `Cslib.BitString.IsAffine.finrank_direction_map_top`
each such image is an affine subspace of dimension `d`, so nonconstancy on `d`-dimensional affine
subspaces suffices (`Cslib.BitString.isAffineDisperser_of_forall_exists_ne`). -/
def IsAffineDisperser {n : ℕ} (f : BitString n → Bool) (d : ℕ) : Prop :=
  ∀ g : BitString d → BitString n, IsAffine g → Function.Injective g → ∃ x y, f (g x) ≠ f (g y)

/-- The extension of a point of `BitString d` by zeros to `BitString d'`, for `d ≤ d'`. -/
def zeroExtend {d d' : ℕ} (x : BitString d) : BitString d' :=
  fun i => if h : i.val < d then x ⟨i.val, h⟩ else false

/-- Extension by zeros is affine. -/
theorem isAffine_zeroExtend {d d' : ℕ} : IsAffine (zeroExtend (d := d) (d' := d')) := by
  intro x y z
  funext i
  simp only [zeroExtend, Pi.add_apply]
  split_ifs <;> rfl

/-- Extension by zeros from `BitString d` to `BitString d'` is injective when `d ≤ d'`. -/
theorem zeroExtend_injective {d d' : ℕ} (h : d ≤ d') :
    Function.Injective (zeroExtend (d := d) (d' := d')) := by
  intro x y hxy
  funext i
  have := congrFun hxy ⟨i.val, by omega⟩
  simpa [zeroExtend, i.isLt] using this

/-- Dispersers for dimension `d` are dispersers for every larger dimension. -/
theorem IsAffineDisperser.mono {n d d' : ℕ} {f : BitString n → Bool}
    (hf : IsAffineDisperser f d) (h : d ≤ d') : IsAffineDisperser f d' := by
  intro g hg hinj
  obtain ⟨x, y, hxy⟩ := hf (g ∘ zeroExtend) (hg.comp isAffine_zeroExtend)
    (hinj.comp (zeroExtend_injective h))
  exact ⟨_, _, hxy⟩

/-- No function is an affine disperser for dimension `0`: it is constant on every point. -/
theorem not_isAffineDisperser_zero {n : ℕ} (f : BitString n → Bool) :
    ¬ IsAffineDisperser f 0 := by
  intro hf
  obtain ⟨x, y, hxy⟩ := hf (fun _ => 0) (isAffine_const (β := BitString n)
    (fun b => funext fun i => BooleanRing.add_self (b i)) 0)
    (fun x y _ => Subsingleton.elim x y)
  exact hxy rfl

/-! ### Existence of affine dispersers by counting -/

section Counting

open Finset

/-- Affinity of a map between finite types is decidable. -/
instance {α β : Type*} [Fintype α] [DecidableEq β] [Add α] [Add β] (g : α → β) :
    Decidable (IsAffine g) :=
  inferInstanceAs (Decidable (∀ _ _ _, _))

/-- Affine maps from `BitString d` agreeing at `0` and at the unit vectors are equal. -/
theorem IsAffine.ext_single {d n : ℕ} {g g' : BitString d → BitString n} (hg : IsAffine g)
    (hg' : IsAffine g') (h0 : g 0 = g' 0) (hi : ∀ i, g (Pi.single i true) = g' (Pi.single i true)) :
    g = g' := by
  have key : ∀ s : Finset (Fin d), g (fun i => decide (i ∈ s)) = g' (fun i => decide (i ∈ s)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have : (fun i : Fin d => decide (i ∈ (∅ : Finset (Fin d)))) = 0 := by
        funext i; simp [Bool.zero_eq_false]
      rw [this, h0]
    | insert j s hj ih =>
      have hsplit : (fun i => decide (i ∈ insert j s)) =
          (fun i => decide (i ∈ s)) + Pi.single j true + 0 := by
        funext i
        by_cases hij : i = j
        · subst hij
          simp only [Finset.mem_insert, true_or, decide_true, hj, decide_false, Pi.single_eq_same,
            Pi.add_apply, Pi.zero_apply, Bool.zero_eq_false]
          rfl
        · simp only [Finset.mem_insert, hij, false_or, Pi.add_apply, Pi.single_eq_of_ne hij,
            Pi.zero_apply, Bool.zero_eq_false]
          cases decide (i ∈ s) <;> rfl
      rw [hsplit, hg, hg', ih, hi, h0]
  funext x
  have hx : x = fun i => decide (i ∈ Finset.univ.filter fun i => x i = true) := by
    funext i; simp
  rw [hx, key]

/-- At most `2 ^ (n (d + 1))` maps from `BitString d` to `BitString n` are affine. -/
theorem card_isAffine_le (d n : ℕ) :
    (univ.filter fun g : BitString d → BitString n => IsAffine g).card ≤ 2 ^ (n * (d + 1)) := by
  classical
  calc _ ≤ (univ : Finset (Option (Fin d) → BitString n)).card :=
        card_le_card_of_injOn (fun g o => g (o.elim 0 fun i => Pi.single i true))
          (fun _ _ => mem_univ _) fun g hg g' hg' h =>
            IsAffine.ext_single (mem_filter.1 hg).2 (mem_filter.1 hg').2 (congrFun h none)
              fun i => congrFun h (some i)
    _ = 2 ^ (n * (d + 1)) := by
      rw [card_univ, Fintype.card_fun, Fintype.card_fun, Fintype.card_option, Fintype.card_fin,
        Fintype.card_bool, Fintype.card_fin, ← pow_mul]

/-- At most `2 · 2 ^ (2 ^ n - 2 ^ d)` functions on `n` bits are constant on the image of an
injective map from `BitString d`. -/
theorem card_const_on_range_le {d n : ℕ} {g : BitString d → BitString n}
    (hg : Function.Injective g) :
    (univ.filter fun f : BitString n → Bool => ∀ x y, f (g x) = f (g y)).card ≤
      2 * 2 ^ (2 ^ n - 2 ^ d) := by
  classical
  calc _ ≤ (univ : Finset (Bool × ({p // p ∉ Set.range g} → Bool))).card :=
        card_le_card_of_injOn (fun f => (f (g 0), fun p => f p.1)) (fun _ _ => mem_univ _)
          fun f hf f' hf' h => by
            simp only [Prod.mk.injEq] at h
            funext p
            by_cases hp : p ∈ Set.range g
            · obtain ⟨x, rfl⟩ := hp
              rw [(mem_filter.1 hf).2 x 0, (mem_filter.1 hf').2 x 0, h.1]
            · exact congrFun h.2 ⟨p, hp⟩
    _ = 2 * 2 ^ (2 ^ n - 2 ^ d) := by
      rw [card_univ, Fintype.card_prod, Fintype.card_bool, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_subtype_compl, Set.card_range_of_injective hg]
      simp

/-- **Affine dispersers exist** for every dimension `d` with `n (d + 1) + 1 < 2 ^ d`: fewer
functions on `n` bits are constant on the image of some injective affine map from `BitString d`
than there are functions. -/
theorem exists_isAffineDisperser {n d : ℕ} (h : n * (d + 1) + 1 < 2 ^ d) :
    ∃ f : BitString n → Bool, IsAffineDisperser f d := by
  classical
  by_contra hno
  push Not at hno
  set A := univ.filter fun g : BitString d → BitString n => IsAffine g ∧ Function.Injective g
  have hsub : (univ : Finset (BitString n → Bool)) ⊆
      A.biUnion fun g => univ.filter fun f => ∀ x y, f (g x) = f (g y) := by
    intro f _
    have := hno f
    unfold IsAffineDisperser at this
    push Not at this
    obtain ⟨g, hg, hinj, hconst⟩ := this
    exact mem_biUnion.2 ⟨g, mem_filter.2 ⟨mem_univ _, hg, hinj⟩, mem_filter.2 ⟨mem_univ _, hconst⟩⟩
  have hcard := (card_le_card hsub).trans (card_biUnion_le_card_mul A _ (2 * 2 ^ (2 ^ n - 2 ^ d))
    fun g hg => card_const_on_range_le (mem_filter.1 hg).2.2)
  rw [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin] at hcard
  rcases A.eq_empty_or_nonempty with hA | ⟨g, hg⟩
  · rw [hA, card_empty, zero_mul] at hcard
    exact absurd hcard (Nat.not_le.2 (Nat.two_pow_pos _))
  · have hdn : 2 ^ d ≤ 2 ^ n := by
      have := Fintype.card_le_of_injective g (mem_filter.1 hg).2.2
      simpa [Fintype.card_fun] using this
    have hA : A.card ≤ 2 ^ (n * (d + 1)) := (card_le_card fun g hg =>
      mem_filter.2 ⟨mem_univ _, (mem_filter.1 hg).2.1⟩).trans (card_isAffine_le d n)
    have hlt : A.card * (2 * 2 ^ (2 ^ n - 2 ^ d)) < 2 ^ 2 ^ n :=
      calc A.card * (2 * 2 ^ (2 ^ n - 2 ^ d)) ≤ 2 ^ (n * (d + 1)) * (2 * 2 ^ (2 ^ n - 2 ^ d)) :=
            Nat.mul_le_mul_right _ hA
        _ = 2 ^ (n * (d + 1) + 1 + (2 ^ n - 2 ^ d)) := by rw [pow_add, pow_add, pow_one]; ring
        _ < 2 ^ 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega

end Counting

end Cslib.BitString
