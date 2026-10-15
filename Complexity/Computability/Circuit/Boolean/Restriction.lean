/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Substitution
public import Mathlib.Data.Finset.Piecewise
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Logic.Function.DependsOn
import Complexity.Foundations.Data.BitString.Agree
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Restrictions

A *restriction* of `n` bits fixes some of them and leaves the others free: a map
`ρ : Fin n → Option Bool` with `ρ i = some b` when bit `i` is fixed to `b`. Restricting a Boolean
function `f` by `ρ` gives `f ∘ ρ.fill`, Jukna's `f↾ρ` [Jukna, Section 1.6][Jukna2012], where
`ρ.fill x` takes the fixed bits from `ρ` and the free bits from `x`. A restriction is the
substitution that replaces each bit by itself or by a constant
(`Restriction.substitute_toSubstitution`).

The *subfunctions* of `f` on a set `Y` of bits are its restrictions by the restrictions that fix
exactly the bits outside `Y` (`subfunctions`, `mem_subfunctions_iff`); counting them is the method
of Nechiporuk.

## Main definitions

* `Cslib.Circuits.Boolean.Restriction`: restrictions of `n` bits.
* `Cslib.Circuits.Boolean.Restriction.fill`: complete an input by the fixed bits.
* `Cslib.Circuits.Boolean.Restriction.free`: the free bits.
* `Cslib.Circuits.Boolean.subfunctions`: the subfunctions of a function on a set of bits.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Function

/-- A restriction of `n` bits: `some b` fixes a bit to `b`, and `none` leaves it free. -/
abbrev Restriction (n : ℕ) : Type :=
  Fin n → Option Bool

namespace Restriction

variable {n : ℕ} {ρ : Restriction n} {i j : Fin n} {b : Bool}

/-- Complete `x` by the bits fixed by `ρ`. -/
def fill (ρ : Restriction n) (x : BitString n) : BitString n :=
  fun i => (ρ i).getD (x i)

/-- The bits left free by `ρ`. -/
def free (ρ : Restriction n) : Finset (Fin n) :=
  {i | ρ i = none}

/-- The substitution replacing each fixed bit by its value and each free bit by itself. -/
def toSubstitution (ρ : Restriction n) : Fin n → Fin n ⊕ Bool :=
  fun i => (ρ i).elim (.inl i) .inr

/-- Restricting is substituting constants for the fixed bits. -/
theorem substitute_toSubstitution (ρ : Restriction n) : substitute ρ.toSubstitution = ρ.fill := by
  funext x i
  cases h : ρ i <;> simp [toSubstitution, fill, h]

@[simp] theorem mem_free : i ∈ ρ.free ↔ ρ i = none := by
  simp [free]

@[simp] theorem fill_of_eq_none (hi : ρ i = none) (x : BitString n) : ρ.fill x i = x i := by
  simp [fill, hi]

@[simp] theorem fill_of_eq_some (hi : ρ i = some b) (x : BitString n) : ρ.fill x i = b := by
  simp [fill, hi]

/-- Fixing nothing changes nothing. -/
@[simp] theorem fill_none (x : BitString n) : fill (fun _ => none) x = x :=
  rfl

@[simp] theorem free_none : free (fun _ : Fin n => none) = Finset.univ := by
  ext
  simp

/-- Filling after fixing one more free bit is filling twice. -/
theorem fill_fill_update (hi : ρ i = none) (b : Bool) (x : BitString n) :
    ρ.fill (fill (update ρ i (some b)) x) = fill (update ρ i (some b)) x := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [fill, hi]
  · simp only [fill, update_of_ne hj]
    cases ρ j <;> rfl

/-- Changing a fixed bit does not change the filled input. -/
theorem fill_update_of_ne_none (hi : ρ i ≠ none) (x : BitString n) (c : Bool) :
    ρ.fill (update x i c) = ρ.fill x := by
  funext j
  by_cases hj : j = i
  · subst hj
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 hi
    simp [fill, hb]
  · simp [fill, update_of_ne hj]

@[simp] theorem free_update (ρ : Restriction n) (i : Fin n) (b : Bool) :
    free (update ρ i (some b)) = ρ.free.erase i := by
  ext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [hj]

/-- Filling preserves agreement away from bit `i`. -/
theorem fill_eq_fill_of_forall_ne {x y : BitString n} (h : ∀ j, j ≠ i → x j = y j) (j : Fin n)
    (hj : j ≠ i) : ρ.fill x j = ρ.fill y j := by
  simp [fill, h j hj]

/-- A function that ignores bit `i` still ignores it once bits are hardwired. -/
theorem dependsOn_comp_fill {β : Type*} {f : BitString n → β} (hf : DependsOn f {i}ᶜ)
    (ρ : Restriction n) : DependsOn (f ∘ ρ.fill) {i}ᶜ :=
  fun _ _ h => hf fun j hj => fill_eq_fill_of_forall_ne (fun k hk => h k hk) j hj

/-- Fix the bits of `S` to their values in `a`. -/
def assign (ρ : Restriction n) (S : Finset (Fin n)) (a : BitString n) : Restriction n :=
  S.piecewise (fun i => some (a i)) ρ

@[simp] theorem assign_of_mem {S : Finset (Fin n)} (hi : i ∈ S) (a : BitString n) :
    ρ.assign S a i = some (a i) :=
  Finset.piecewise_eq_of_mem _ _ _ hi

@[simp] theorem assign_of_notMem {S : Finset (Fin n)} (hi : i ∉ S) (a : BitString n) :
    ρ.assign S a i = ρ i :=
  Finset.piecewise_eq_of_notMem _ _ _ hi

@[simp] theorem free_assign (ρ : Restriction n) (S : Finset (Fin n)) (a : BitString n) :
    (ρ.assign S a).free = ρ.free \ S := by
  ext i
  by_cases hi : i ∈ S <;> simp [hi]

@[simp] theorem assign_assign (ρ : Restriction n) (S : Finset (Fin n)) (a b : BitString n) :
    (ρ.assign S a).assign S b = ρ.assign S b :=
  Finset.piecewise_idem_right _ _ _ _

/-- Fixing bits to the values they already have changes nothing. -/
theorem assign_eq_self {S : Finset (Fin n)} {a : BitString n} (h : ∀ i ∈ S, ρ i = some (a i)) :
    ρ.assign S a = ρ := by
  funext i
  by_cases hi : i ∈ S
  · simp [hi, h i hi]
  · simp [hi]

/-- Fixing free bits to the values of `x` does not change the input filled from `x`. -/
theorem fill_assign {S : Finset (Fin n)} (hS : S ⊆ ρ.free) {a x : BitString n}
    (h : ∀ i ∈ S, a i = x i) : (ρ.assign S a).fill x = ρ.fill x := by
  funext i
  by_cases hi : i ∈ S
  · simp [fill, hi, h i hi, mem_free.1 (hS hi)]
  · simp [fill, hi]

/-- Free the bits of `S`. -/
def unassign (ρ : Restriction n) (S : Finset (Fin n)) : Restriction n :=
  S.piecewise (fun _ => none) ρ

@[simp] theorem unassign_of_mem {S : Finset (Fin n)} (hi : i ∈ S) : ρ.unassign S i = none :=
  Finset.piecewise_eq_of_mem _ _ _ hi

@[simp] theorem unassign_of_notMem {S : Finset (Fin n)} (hi : i ∉ S) : ρ.unassign S i = ρ i :=
  Finset.piecewise_eq_of_notMem _ _ _ hi

@[simp] theorem unassign_empty (ρ : Restriction n) : ρ.unassign ∅ = ρ :=
  Finset.piecewise_empty _ _

/-- Fixing free bits and freeing them again gives back the restriction. -/
theorem unassign_union_assign {S Q : Finset (Fin n)} (hS : S ⊆ ρ.free) (a : BitString n) :
    (ρ.assign S a).unassign (Q ∪ S) = ρ.unassign Q := by
  funext i
  by_cases hiS : i ∈ S
  · by_cases hiQ : i ∈ Q <;> simp [hiS, hiQ, mem_free.1 (hS hiS)]
  · by_cases hiQ : i ∈ Q <;> simp [hiS, hiQ]

/-! ### Extensions -/

/-- `ρ'` extends `ρ`: it fixes every bit that `ρ` fixes, to the same value. This is the
information order on restrictions; the order on `Option` in core is a different one. -/
def Extends (ρ' ρ : Restriction n) : Prop :=
  ∀ i b, ρ i = some b → ρ' i = some b

instance (ρ' ρ : Restriction n) : Decidable (ρ'.Extends ρ) :=
  inferInstanceAs (Decidable (∀ i b, ρ i = some b → ρ' i = some b))

@[refl] theorem Extends.refl (ρ : Restriction n) : ρ.Extends ρ := fun _ _ h => h

theorem Extends.trans {ρ ρ' ρ'' : Restriction n} (h₁ : ρ''.Extends ρ') (h₂ : ρ'.Extends ρ) :
    ρ''.Extends ρ :=
  fun i b h => h₁ i b (h₂ i b h)

/-- A free bit of an extension is free in the restriction it extends. -/
theorem Extends.free_subset {ρ ρ' : Restriction n} (h : ρ'.Extends ρ) : ρ'.free ⊆ ρ.free :=
  fun i hi => mem_free.2 <| by
    cases hρ : ρ i with
    | none => rfl
    | some b => exact absurd (h i b hρ) (by rw [mem_free.1 hi]; simp)

/-- Fixing free bits extends a restriction. -/
theorem extends_assign {S : Finset (Fin n)} (hS : S ⊆ ρ.free) (a : BitString n) :
    (ρ.assign S a).Extends ρ := fun i b hi => by
  have : i ∉ S := fun h => by simp [mem_free.1 (hS h)] at hi
  simpa [this] using hi

/-- Filling from an extension of `ρ` is not changed by filling from `ρ`. -/
theorem fill_fill_of_extends {ρ ρ' : Restriction n} (h : ρ'.Extends ρ) (x : BitString n) :
    ρ.fill (ρ'.fill x) = ρ'.fill x := by
  funext i
  cases hρ : ρ i with
  | none => simp [fill, hρ]
  | some b => simp [fill, hρ, h i b hρ]

/-- The extensions of `ρ₀` leaving exactly `ℓ` bits free. -/
def extensions (ρ₀ : Restriction n) (ℓ : ℕ) : Finset (Restriction n) :=
  Finset.univ.filter fun ρ => ρ.Extends ρ₀ ∧ ρ.free.card = ℓ

@[simp] theorem mem_extensions {ρ₀ : Restriction n} {ℓ : ℕ} :
    ρ ∈ ρ₀.extensions ℓ ↔ ρ.Extends ρ₀ ∧ ρ.free.card = ℓ := by
  simp [extensions]

/-- There are `(m choose ℓ) 2 ^ (m - ℓ)` extensions of `ρ₀` leaving `ℓ` of the `m` free bits of
`ρ₀` free. -/
theorem card_extensions (ρ₀ : Restriction n) (ℓ : ℕ) :
    (ρ₀.extensions ℓ).card = ρ₀.free.card.choose ℓ * 2 ^ (ρ₀.free.card - ℓ) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := free) (t := Finset.powersetCard ℓ ρ₀.free)
    fun ρ hρ => Finset.mem_powersetCard.2
      ⟨(mem_extensions.1 hρ).1.free_subset, (mem_extensions.1 hρ).2⟩]
  rw [Finset.sum_congr rfl (g := fun _ => 2 ^ (ρ₀.free.card - ℓ)), Finset.sum_const,
    Finset.card_powersetCard, smul_eq_mul]
  intro S hS
  obtain ⟨hSsub, hS⟩ := Finset.mem_powersetCard.1 hS
  -- an extension with free bits `S` chooses a value for each free bit of `ρ₀` outside `S`
  have : (ρ₀.extensions ℓ).filter (fun ρ => ρ.free = S) = Fintype.piFinset fun i =>
      if i ∈ S then {none} else if i ∈ ρ₀.free then {some false, some true} else {ρ₀ i} := by
    ext ρ
    simp only [Finset.mem_filter, mem_extensions, Fintype.mem_piFinset]
    constructor
    · rintro ⟨⟨hext, -⟩, rfl⟩ i
      by_cases hi : i ∈ ρ.free
      · simp [hi, mem_free.1 hi]
      · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 fun h => hi (mem_free.2 h)
        by_cases hi₀ : i ∈ ρ₀.free
        · cases b <;> simp [hi, hi₀, hb]
        · obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 fun h => hi₀ (mem_free.2 h)
          simp only [hi, ↓reduceIte, hi₀, Finset.mem_singleton]
          rw [hext i c hc, hc]
    · intro h
      have hfree : ρ.free = S := by
        ext i
        have := h i
        by_cases hi : i ∈ S
        · simp_all
        · by_cases hi₀ : i ∈ ρ₀.free
          · cases hρ : ρ i <;> simp_all
          · simp only [hi, ↓reduceIte, hi₀, Finset.mem_singleton] at this
            simp only [mem_free, this, hi, iff_false]
            exact fun h' => hi₀ (mem_free.2 h')
      refine ⟨⟨fun i b hb => ?_, hfree ▸ hS⟩, hfree⟩
      have hi₀ : i ∉ ρ₀.free := by simp [mem_free, hb]
      have hi : i ∉ S := fun hi => hi₀ (hSsub hi)
      simpa [hi, hi₀, hb] using h i
  rw [this, Fintype.card_piFinset]
  simp only [apply_ite Finset.card, Finset.card_singleton,
    Finset.card_pair (show some false ≠ some true by simp)]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_ite, Finset.prod_const,
    Finset.prod_const_one, mul_one, Finset.filter_filter,
    show Finset.univ.filter (fun a => a ∉ S ∧ a ∈ ρ₀.free) = ρ₀.free \ S by
      ext a
      simp [and_comm], Finset.card_sdiff_of_subset hSsub, hS]

/-- The restrictions of `n` bits leaving exactly `ℓ` of them free: the extensions of the
restriction fixing nothing. -/
abbrev withFree (n ℓ : ℕ) : Finset (Restriction n) :=
  extensions (fun _ => none) ℓ

/-- Every restriction extends the restriction fixing nothing. -/
@[simp] theorem extends_none (ρ : Restriction n) : ρ.Extends fun _ => none :=
  fun _ _ h => by simp at h

theorem mem_withFree {ℓ : ℕ} : ρ ∈ withFree n ℓ ↔ ρ.free.card = ℓ := by
  simp

/-- There are `(n choose ℓ) 2 ^ (n - ℓ)` restrictions leaving exactly `ℓ` bits free. -/
theorem card_withFree (n ℓ : ℕ) : (withFree n ℓ).card = n.choose ℓ * 2 ^ (n - ℓ) := by
  rw [card_extensions, free_none, Finset.card_univ, Fintype.card_fin]

/-- A restriction with `ℓ'` free bits extends `C(n - ℓ', ℓ - ℓ')` of the restrictions with
`ℓ ≥ ℓ'` free bits: those that free `ℓ - ℓ'` of its fixed bits. -/
theorem card_filter_extends_withFree {ρ' : Restriction n} {ℓ : ℕ} (hℓ : ρ'.free.card ≤ ℓ) :
    ((withFree n ℓ).filter fun ρ => ρ'.Extends ρ).card =
      (n - ρ'.free.card).choose (ℓ - ρ'.free.card) := by
  have h := Finset.card_filter_powersetCard_subset ρ'.free Finset.univ ℓ (Finset.subset_univ _) hℓ
  rw [Finset.card_univ, Fintype.card_fin] at h
  rw [← h]
  refine Finset.card_nbij' free (fun F i => if i ∈ F then none else ρ' i) (fun ρ hρ => ?_)
    (fun F hF => ?_) (fun ρ hρ => ?_) (fun F hF => ?_)
  · obtain ⟨hρ, hext⟩ := Finset.mem_filter.1 hρ
    exact Finset.mem_filter.2 ⟨Finset.mem_powersetCard.2 ⟨Finset.subset_univ _,
      (mem_withFree.1 hρ)⟩, hext.free_subset⟩
  · obtain ⟨hF, hsub⟩ := Finset.mem_filter.1 hF
    have hfree : free (fun i => if i ∈ F then none else ρ' i) = F := by
      ext i
      by_cases hi : i ∈ F
      · simp [hi]
      · simp only [mem_free, hi, ↓reduceIte, iff_false]
        exact fun h => hi (hsub (mem_free.2 h))
    refine Finset.mem_filter.2 ⟨mem_withFree.2 ?_, fun i b hb => ?_⟩
    · rw [hfree]
      exact (Finset.mem_powersetCard.1 hF).2
    · by_cases hi : i ∈ F
      · simp [hi] at hb
      · simpa [hi] using hb
  · obtain ⟨-, hext⟩ := Finset.mem_filter.1 hρ
    funext i
    by_cases hi : i ∈ ρ.free
    · simp [hi, mem_free.1 hi]
    · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 fun h => hi (mem_free.2 h)
      simp [hi, hb, hext i b hb]
  · obtain ⟨-, hsub⟩ := Finset.mem_filter.1 hF
    ext i
    by_cases hi : i ∈ F
    · simp [hi]
    · simp only [mem_free, hi, ↓reduceIte, iff_false]
      exact fun h => hi (hsub (mem_free.2 h))

/-- The restriction fixing the bits outside `Y` to their values in `z`. -/
def outside (Y : Finset (Fin n)) (z : BitString n) : Restriction n :=
  fun j => if j ∈ Y then none else some (z j)

@[simp] theorem fill_outside (Y : Finset (Fin n)) (z x : BitString n) :
    (outside Y z).fill x = Y.piecewise x z := by
  funext j
  by_cases hj : j ∈ Y <;> simp [outside, fill, hj]

@[simp] theorem free_outside (Y : Finset (Fin n)) (z : BitString n) : (outside Y z).free = Y := by
  ext j
  by_cases hj : j ∈ Y <;> simp [outside, hj]

/-! ### Drawing random restrictions -/

open Finset

/-- The words agreeing with a restriction outside its free bits: `2 ^ ℓ` of them for `ℓ` free
bits. -/
theorem card_filter_outside_eq (ρ : Restriction n) :
    #{z : BitString n | outside ρ.free z = ρ} = 2 ^ #ρ.free := by
  rw [← BitString.card_filter_forall_notMem_eq ρ.free (ρ.fill fun _ => false)]
  congr 1
  ext z
  simp only [mem_filter, mem_univ, true_and, funext_iff, outside]
  refine forall_congr' fun i => ?_
  by_cases hi : i ∈ ρ.free
  · simp [hi, mem_free.1 hi]
  · obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 fun h => hi (mem_free.2 h)
    simp [hi, hc, fill]

/-- **Drawing a free set and a word**: fixing the coordinates outside a set `J` of `ℓ`
coordinates to a word `z` draws every restriction with `ℓ` free bits `2 ^ ℓ` times. -/
theorem sum_card_filter_outside (Q : Restriction n → Prop) [DecidablePred Q] (ℓ : ℕ) :
    ∑ J ∈ (univ : Finset (Fin n)).powersetCard ℓ, #{z : BitString n | Q (outside J z)} =
      2 ^ ℓ * #{ρ ∈ withFree n ℓ | Q ρ} := by
  rw [← card_sigma, card_eq_sum_card_fiberwise (f := fun p => outside p.1 p.2)
    (t := (withFree n ℓ).filter Q) fun p hp => ?_]
  · rw [sum_congr rfl fun ρ hρ => ?_, sum_const, smul_eq_mul, mul_comm]
    have hfree : #ρ.free = ℓ := mem_withFree.1 (mem_filter.1 hρ).1
    rw [← hfree, ← card_filter_outside_eq ρ]
    refine card_nbij' (fun p => p.2) (fun z => ⟨ρ.free, z⟩) (fun p hp => ?_) (fun z hz => ?_)
      (fun p hp => ?_) (fun z _ => rfl)
    · obtain ⟨-, hpρ⟩ := mem_filter.1 hp
      have h1 : p.1 = ρ.free := by rw [← hpρ, free_outside]
      exact mem_filter.2 ⟨mem_univ _, h1 ▸ hpρ⟩
    · have hz' : outside ρ.free z = ρ := (mem_filter.1 hz).2
      refine mem_filter.2 ⟨mem_sigma.2 ⟨mem_powersetCard.2 ⟨subset_univ _, rfl⟩, ?_⟩, hz'⟩
      refine mem_filter.2 ⟨mem_univ _, ?_⟩
      change Q (outside ρ.free z)
      rw [hz']
      exact (mem_filter.1 hρ).2
    · obtain ⟨-, hpρ⟩ := mem_filter.1 hp
      have h1 : p.1 = ρ.free := by rw [← hpρ, free_outside]
      exact Sigma.ext h1.symm HEq.rfl
  · obtain ⟨hJ, hz⟩ := mem_sigma.1 hp
    exact mem_filter.2 ⟨mem_withFree.2 (by rw [free_outside]; exact (mem_powersetCard.1 hJ).2),
      (mem_filter.1 hz).2⟩

/-- **Double counting extensions.** Summed over the restrictions with `ℓ` free bits, the extensions
with `ℓ' ≤ ℓ` free bits satisfying `P` count each restriction with `ℓ'` free bits satisfying `P`
once for each of the `C(n - ℓ', ℓ - ℓ')` restrictions it extends. -/
theorem sum_card_filter_extensions (P : Restriction n → Prop) [DecidablePred P] {ℓ ℓ' : ℕ}
    (hℓ : ℓ' ≤ ℓ) :
    ∑ ρ ∈ withFree n ℓ, #{ρ' ∈ ρ.extensions ℓ' | P ρ'} =
      #{ρ' ∈ withFree n ℓ' | P ρ'} * (n - ℓ').choose (ℓ - ℓ') := by
  have h := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := withFree n ℓ)
    (t := (withFree n ℓ').filter P) (r := fun ρ ρ' => ρ'.Extends ρ)
  have habove (ρ : Restriction n) : #{ρ' ∈ ρ.extensions ℓ' | P ρ'} =
      #(((withFree n ℓ').filter P).bipartiteAbove (fun ρ ρ' => ρ'.Extends ρ) ρ) := by
    congr 1
    ext ρ'
    simp only [mem_filter, mem_extensions, bipartiteAbove]
    tauto
  rw [sum_congr rfl fun ρ _ => habove ρ, h, sum_congr rfl fun ρ' hρ' => ?_, sum_const,
    smul_eq_mul]
  have hfree : #ρ'.free = ℓ' := mem_withFree.1 (mem_filter.1 hρ').1
  rw [bipartiteBelow, ← hfree, card_filter_extends_withFree (hfree ▸ hℓ)]

end Restriction

/-- The subfunctions of `f` on the bits `Y`: for each assignment `z` of the other bits, the
function that reads the bits in `Y` from its input and the other bits from `z`. -/
def subfunctions (f : BooleanFunction n) (Y : Finset (Fin n)) : Finset (BooleanFunction n) :=
  Finset.univ.image fun z x => f (Y.piecewise x z)

@[simp] theorem mem_subfunctions {f g : BooleanFunction n} {Y : Finset (Fin n)} :
    g ∈ subfunctions f Y ↔ ∃ z, (fun x => f (Y.piecewise x z)) = g := by
  simp [subfunctions]

/-- The subfunctions on `Y` are the restrictions fixing exactly the bits outside `Y`. -/
theorem mem_subfunctions_iff {f g : BooleanFunction n} {Y : Finset (Fin n)} :
    g ∈ subfunctions f Y ↔ ∃ z, f ∘ (Restriction.outside Y z).fill = g := by
  simp only [mem_subfunctions]
  exact exists_congr fun z => by rw [show f ∘ (Restriction.outside Y z).fill =
    fun x => f (Y.piecewise x z) from funext fun x => by simp]

end Cslib.Circuits.Boolean
