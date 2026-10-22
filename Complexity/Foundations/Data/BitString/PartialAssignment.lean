/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Foundations.Data.BitString
public import Mathlib.Data.Finset.Piecewise
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Part
public import Mathlib.Logic.Function.DependsOn
import Complexity.Foundations.Data.BitString.Agree
import Complexity.Foundations.Data.Nat.Choose
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Partial assignments

A *partial assignment* of the coordinates `ι` fixes some of them and leaves the others free: a map
`ρ : ι → Option Bool` with `ρ i = some b` when coordinate `i` is fixed to `b`. In circuit complexity
it is called a *restriction*, Jukna's `ρ : ι → {0, 1, *}` [Jukna, Section 1.6][Jukna2012],
[Hastad1986]. Restricting a function `f` on `ι → Bool` by `ρ` gives `f ∘ ρ.fill`, Jukna's `f↾ρ`,
where `ρ.fill x` takes the fixed coordinates from `ρ` and the free ones from `x`.

Over a finite index type, the partial assignments extending `ρ₀` with exactly `ℓ` free coordinates
number `(m choose ℓ) 2 ^ (m - ℓ)` for the `m` free coordinates of `ρ₀`
(`PartialAssignment.card_extensions`), so `(|ι| choose ℓ) 2 ^ (|ι| - ℓ)` partial assignments leave
exactly `ℓ` coordinates free (`PartialAssignment.card_withFree`). Drawing such a partial assignment
uniformly is drawing a set of `ℓ` free coordinates and a word for the others
(`PartialAssignment.sum_card_filter_outside`), and double counting relates partial assignments
with different numbers of free coordinates (`PartialAssignment.sum_card_filter_extensions`); these
are the random restrictions of Håstad's switching lemma.

The *subfunctions* of `f` on a set `Y` of coordinates are its restrictions by the partial
assignments that fix exactly the coordinates outside `Y` (`subfunctions`, `mem_subfunctions_iff`);
counting them is the method of Nechiporuk.

## Main definitions

* `Cslib.BitString.PartialAssignment`: partial assignments of the coordinates `ι`, and
  `Cslib.BitString.PartialAssignment.empty` the one fixing nothing.
* `Cslib.BitString.PartialAssignment.fill`: complete an input by the fixed coordinates.
* `Cslib.BitString.PartialAssignment.Agrees`: an input agrees with a partial assignment.
* `Cslib.BitString.PartialAssignment.free`, `Cslib.BitString.PartialAssignment.support`: the free
  and the fixed coordinates.
* `Cslib.BitString.PartialAssignment.Extends`, `Cslib.BitString.PartialAssignment.extensions`,
  `Cslib.BitString.PartialAssignment.withFree`: extensions, and partial assignments with `ℓ` free
  coordinates.
* `Cslib.BitString.subfunctions`: the subfunctions of a function on a set of coordinates.

## Main results

* `Cslib.BitString.PartialAssignment.agrees_iff_fill_eq`: an input agrees with a partial
  assignment when filling it changes nothing.
* `Cslib.BitString.PartialAssignment.extends_iff_ofOption_le`: extension is the pointwise order of
  `Part Bool`.
* `Cslib.BitString.PartialAssignment.card_extensions`,
  `Cslib.BitString.PartialAssignment.card_withFree`,
  `Cslib.BitString.PartialAssignment.card_filter_extensions_free_subset`,
  `Cslib.BitString.PartialAssignment.card_extensions_le_two_mul_card_filter_forall_nonempty`:
  counting partial assignments by their free coordinates and union-bounding block survival.
* `Cslib.BitString.PartialAssignment.sum_card_filter_outside`,
  `Cslib.BitString.PartialAssignment.sum_card_filter_extensions`,
  `Cslib.BitString.PartialAssignment.sum_extensions_update`: drawing random restrictions and
  double counting extensions.
* `Cslib.BitString.PartialAssignment.mul_card_filter_withFree_le`: two stages of restrictions,
  counted.
* `Cslib.BitString.mem_subfunctions_iff`: subfunctions are restrictions.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
* [J. Håstad, *Almost optimal lower bounds for small depth circuits*][Hastad1986]
-/

@[expose] public section

namespace Cslib.BitString

open Function Finset

/-- A partial assignment (a restriction, in circuit complexity) of the coordinates `ι`: `some b`
fixes a coordinate to `b`, and `none` leaves it free.

Being an abbreviation of `ι → Option Bool`, a partial assignment inherits the pointwise order of
the order of core on `Option Bool`, in which `none < some false < some true`. That order is not the
information order: `ρ ≤ ρ'` does not say that `ρ'` extends `ρ`. The information order is
`PartialAssignment.Extends`, the pointwise order on `Part Bool`
(`PartialAssignment.extends_iff_ofOption_le`). -/
abbrev PartialAssignment (ι : Type*) : Type _ :=
  ι → Option Bool

namespace PartialAssignment

variable {ι : Type*} {ρ : PartialAssignment ι} {i j : ι} {b : Bool}

/-- The partial assignment fixing nothing. -/
def empty : PartialAssignment ι :=
  fun _ => none

@[simp] theorem empty_apply (i : ι) : (empty : PartialAssignment ι) i = none :=
  rfl

/-- Complete `x` by the coordinates fixed by `ρ`. -/
def fill (ρ : PartialAssignment ι) (x : ι → Bool) : ι → Bool :=
  fun i => (ρ i).getD (x i)

@[simp] theorem fill_of_eq_none (hi : ρ i = none) (x : ι → Bool) : ρ.fill x i = x i := by
  simp [fill, hi]

@[simp] theorem fill_of_eq_some (hi : ρ i = some b) (x : ι → Bool) : ρ.fill x i = b := by
  simp [fill, hi]

/-- Fixing nothing changes nothing. -/
@[simp] theorem fill_empty (x : ι → Bool) : (empty : PartialAssignment ι).fill x = x :=
  rfl

/-- `fill_empty`, for the partial assignment fixing nothing written as a function. -/
@[simp] theorem fill_none (x : ι → Bool) : fill (fun _ => none) x = x :=
  fill_empty x

/-! ### Agreement -/

/-- The input `x` *agrees* with `ρ`: it takes the value fixed by `ρ` at every fixed coordinate. -/
def Agrees (ρ : PartialAssignment ι) (x : ι → Bool) : Prop :=
  ∀ i b, ρ i = some b → x i = b

instance [Fintype ι] (ρ : PartialAssignment ι) (x : ι → Bool) : Decidable (ρ.Agrees x) :=
  inferInstanceAs (Decidable (∀ i b, ρ i = some b → x i = b))

/-- An input agrees with `ρ` exactly when filling it from `ρ` does not change it. -/
theorem agrees_iff_fill_eq {x : ι → Bool} : ρ.Agrees x ↔ ρ.fill x = x := by
  refine ⟨fun h => funext fun i => ?_, fun h i b hi => by rw [← h, fill_of_eq_some hi]⟩
  cases hρ : ρ i with
  | none => exact fill_of_eq_none hρ x
  | some c => rw [fill_of_eq_some hρ, h i c hρ]

/-- A filled input agrees with the partial assignment it was filled from. -/
theorem agrees_fill (ρ : PartialAssignment ι) (x : ι → Bool) : ρ.Agrees (ρ.fill x) :=
  fun _ _ hi => fill_of_eq_some hi x

@[simp] theorem agrees_empty (x : ι → Bool) : (empty : PartialAssignment ι).Agrees x :=
  fun _ _ h => by simp at h

/-- Filling preserves agreement away from coordinate `i`. -/
theorem fill_eq_fill_of_forall_ne {x y : ι → Bool} (h : ∀ j, j ≠ i → x j = y j) (j : ι)
    (hj : j ≠ i) : ρ.fill x j = ρ.fill y j := by
  simp [fill, h j hj]

/-- A function that ignores coordinate `i` still ignores it once coordinates are hardwired. -/
theorem dependsOn_comp_fill {β : Type*} {f : (ι → Bool) → β} (hf : DependsOn f {i}ᶜ)
    (ρ : PartialAssignment ι) : DependsOn (f ∘ ρ.fill) {i}ᶜ :=
  fun _ _ h => hf fun j hj => fill_eq_fill_of_forall_ne (fun k hk => h k hk) j hj

/-! ### Fixing and freeing coordinates -/

section DecidableEq

variable [DecidableEq ι]

/-- Filling after fixing coordinate `i` to `b` updates the filled input at `i`. -/
@[simp] theorem fill_update (ρ : PartialAssignment ι) (i : ι) (b : Bool) (x : ι → Bool) :
    fill (update ρ i (some b)) x = update (ρ.fill x) i b := by
  funext j
  by_cases hj : j = i <;> simp [fill, hj]

/-- Fixing a single coordinate `i` to `b` in the empty partial assignment updates the input at
`i`. -/
theorem fill_update_empty (i : ι) (b : Bool) (x : ι → Bool) :
    fill (update empty i (some b)) x = update x i b := by
  simp

/-- Filling after fixing one more free coordinate is filling twice. -/
theorem fill_fill_update (hi : ρ i = none) (b : Bool) (x : ι → Bool) :
    ρ.fill (fill (update ρ i (some b)) x) = fill (update ρ i (some b)) x := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [fill, hi]
  · simp only [fill, update_of_ne hj]
    cases ρ j <;> rfl

/-- Changing a fixed coordinate does not change the filled input. -/
theorem fill_update_of_ne_none (hi : ρ i ≠ none) (x : ι → Bool) (c : Bool) :
    ρ.fill (update x i c) = ρ.fill x := by
  funext j
  by_cases hj : j = i
  · subst hj
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 hi
    simp [fill, hb]
  · simp [fill, update_of_ne hj]

/-- Changing a free coordinate changes the filled input there. -/
theorem fill_update_of_eq_none (hi : ρ i = none) (x : ι → Bool) (c : Bool) :
    ρ.fill (update x i c) = update (ρ.fill x) i c := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [fill, hi]
  · simp [fill, update_of_ne hj]

/-- Fix the coordinates of `S` to their values in `a`. -/
def assign (ρ : PartialAssignment ι) (S : Finset ι) (a : ι → Bool) : PartialAssignment ι :=
  S.piecewise (fun i => some (a i)) ρ

@[simp] theorem assign_of_mem {S : Finset ι} (hi : i ∈ S) (a : ι → Bool) :
    ρ.assign S a i = some (a i) :=
  piecewise_eq_of_mem _ _ _ hi

@[simp] theorem assign_of_notMem {S : Finset ι} (hi : i ∉ S) (a : ι → Bool) :
    ρ.assign S a i = ρ i :=
  piecewise_eq_of_notMem _ _ _ hi

@[simp] theorem assign_assign (ρ : PartialAssignment ι) (S : Finset ι) (a b : ι → Bool) :
    (ρ.assign S a).assign S b = ρ.assign S b :=
  piecewise_idem_right _ _ _ _

/-- Fixing coordinates to the values they already have changes nothing. -/
theorem assign_eq_self {S : Finset ι} {a : ι → Bool} (h : ∀ i ∈ S, ρ i = some (a i)) :
    ρ.assign S a = ρ := by
  funext i
  by_cases hi : i ∈ S
  · simp [hi, h i hi]
  · simp [hi]

/-- Free the coordinates of `S`. -/
def unassign (ρ : PartialAssignment ι) (S : Finset ι) : PartialAssignment ι :=
  S.piecewise empty ρ

@[simp] theorem unassign_of_mem {S : Finset ι} (hi : i ∈ S) : ρ.unassign S i = none :=
  piecewise_eq_of_mem _ _ _ hi

@[simp] theorem unassign_of_notMem {S : Finset ι} (hi : i ∉ S) : ρ.unassign S i = ρ i :=
  piecewise_eq_of_notMem _ _ _ hi

@[simp] theorem unassign_empty (ρ : PartialAssignment ι) : ρ.unassign ∅ = ρ :=
  piecewise_empty _ _

/-- The partial assignment fixing the coordinates outside `Y` to their values in `z`. -/
def outside (Y : Finset ι) (z : ι → Bool) : PartialAssignment ι :=
  fun j => if j ∈ Y then none else some (z j)

@[simp] theorem fill_outside (Y : Finset ι) (z x : ι → Bool) :
    (outside Y z).fill x = Y.piecewise x z := by
  funext j
  by_cases hj : j ∈ Y <;> simp [outside, fill, hj]

end DecidableEq

/-! ### Free coordinates -/

section Fintype

variable [Fintype ι]

/-- The coordinates left free by `ρ`. -/
def free (ρ : PartialAssignment ι) : Finset ι :=
  {i | ρ i = none}

@[simp] theorem mem_free : i ∈ ρ.free ↔ ρ i = none := by
  simp [free]

@[simp] theorem free_empty : (empty : PartialAssignment ι).free = univ := by
  ext
  simp

/-- `free_empty`, for the partial assignment fixing nothing written as a function. -/
@[simp] theorem free_none : free (fun _ : ι => none) = univ :=
  free_empty

/-- The coordinates fixed by `ρ`, the complement of its free coordinates (`compl_free`). -/
def support (ρ : PartialAssignment ι) : Finset ι :=
  {i | (ρ i).isSome}

@[simp] theorem mem_support : i ∈ ρ.support ↔ (ρ i).isSome := by
  simp [support]

@[simp] theorem support_empty : (empty : PartialAssignment ι).support = ∅ := by
  ext
  simp

/-- A restricted function `f ∘ ρ.fill` depends only on the free coordinates of `ρ`. -/
theorem dependsOn_comp_fill_free {β : Type*} (f : (ι → Bool) → β) (ρ : PartialAssignment ι) :
    DependsOn (f ∘ ρ.fill) ρ.free := by
  intro x y h
  simp only [comp_apply]
  congr 1
  funext i
  by_cases hi : i ∈ ρ.free
  · rw [fill_of_eq_none (mem_free.1 hi), fill_of_eq_none (mem_free.1 hi), h i hi]
  · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 fun h' => hi (mem_free.2 h')
    rw [fill_of_eq_some hb, fill_of_eq_some hb]

variable [DecidableEq ι]

/-- The free coordinates are those outside the support. -/
theorem compl_free (ρ : PartialAssignment ι) : ρ.freeᶜ = ρ.support := by
  ext i
  simp [Option.isSome_iff_ne_none]

theorem compl_support (ρ : PartialAssignment ι) : ρ.supportᶜ = ρ.free := by
  rw [← compl_free, compl_compl]

@[simp] theorem free_update (ρ : PartialAssignment ι) (i : ι) (b : Bool) :
    free (update ρ i (some b)) = ρ.free.erase i := by
  ext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [hj]

@[simp] theorem free_assign (ρ : PartialAssignment ι) (S : Finset ι) (a : ι → Bool) :
    (ρ.assign S a).free = ρ.free \ S := by
  ext i
  by_cases hi : i ∈ S <;> simp [hi]

/-- Fixing free coordinates to the values of `x` does not change the input filled from `x`. -/
theorem fill_assign {S : Finset ι} (hS : S ⊆ ρ.free) {a x : ι → Bool}
    (h : ∀ i ∈ S, a i = x i) : (ρ.assign S a).fill x = ρ.fill x := by
  funext i
  by_cases hi : i ∈ S
  · simp [fill, hi, h i hi, mem_free.1 (hS hi)]
  · simp [fill, hi]

/-- Fixing free coordinates and freeing them again gives back the partial assignment. -/
theorem unassign_union_assign {S Q : Finset ι} (hS : S ⊆ ρ.free) (a : ι → Bool) :
    (ρ.assign S a).unassign (Q ∪ S) = ρ.unassign Q := by
  funext i
  by_cases hiS : i ∈ S
  · by_cases hiQ : i ∈ Q <;> simp [hiS, hiQ, mem_free.1 (hS hiS)]
  · by_cases hiQ : i ∈ Q <;> simp [hiS, hiQ]

@[simp] theorem free_outside (Y : Finset ι) (z : ι → Bool) : (outside Y z).free = Y := by
  ext j
  by_cases hj : j ∈ Y <;> simp [outside, hj]

/-- Restricting `f ∘ ρ.fill` by fixing a free coordinate `i` of `ρ` to `b` is restricting `f` by
`update ρ i (some b)`. -/
theorem comp_fill_update_empty_of_mem_free {β : Type*} {ρ : PartialAssignment ι} {i : ι}
    (hi : i ∈ ρ.free) (b : Bool) (f : (ι → Bool) → β) :
    (f ∘ ρ.fill) ∘ fill (update empty i (some b)) = f ∘ fill (update ρ i (some b)) := by
  funext x
  simp [fill_update_of_eq_none (mem_free.1 hi)]

end Fintype

/-! ### Extensions -/

/-- `ρ'` extends `ρ`: it fixes every coordinate that `ρ` fixes, to the same value. This is the
information order on partial assignments; the order on `Option` in core is a different one. -/
def Extends (ρ' ρ : PartialAssignment ι) : Prop :=
  ∀ i b, ρ i = some b → ρ' i = some b

instance [Fintype ι] (ρ' ρ : PartialAssignment ι) : Decidable (ρ'.Extends ρ) :=
  inferInstanceAs (Decidable (∀ i b, ρ i = some b → ρ' i = some b))

@[refl] theorem Extends.refl (ρ : PartialAssignment ι) : ρ.Extends ρ := fun _ _ h => h

theorem Extends.trans {ρ ρ' ρ'' : PartialAssignment ι} (h₁ : ρ''.Extends ρ') (h₂ : ρ'.Extends ρ) :
    ρ''.Extends ρ :=
  fun i b h => h₁ i b (h₂ i b h)

/-- **The information order**: `ρ'` extends `ρ` exactly when it is above `ρ` pointwise in the
order of `Part Bool`, where an undefined value is below every value and distinct values are
incomparable. -/
theorem extends_iff_ofOption_le {ρ ρ' : PartialAssignment ι} :
    ρ'.Extends ρ ↔ (fun i => Part.ofOption (ρ i)) ≤ fun i => Part.ofOption (ρ' i) := by
  simp only [Pi.le_def]
  exact forall_congr' fun i => forall_congr' fun b => by
    simp only [Part.mem_ofOption, Option.mem_def]

/-- Every partial assignment extends the one fixing nothing. -/
@[simp] theorem extends_empty (ρ : PartialAssignment ι) : ρ.Extends empty :=
  fun _ _ h => by simp at h

/-- An input agreeing with `ρ'` agrees with every partial assignment that `ρ'` extends. -/
theorem Extends.agrees {ρ ρ' : PartialAssignment ι} (h : ρ'.Extends ρ) {x : ι → Bool}
    (hx : ρ'.Agrees x) : ρ.Agrees x :=
  fun i b hi => hx i b (h i b hi)

/-- Filling from an extension of `ρ` is not changed by filling from `ρ`. -/
theorem fill_fill_of_extends {ρ ρ' : PartialAssignment ι} (h : ρ'.Extends ρ) (x : ι → Bool) :
    ρ.fill (ρ'.fill x) = ρ'.fill x := by
  funext i
  cases hρ : ρ i with
  | none => simp [fill, hρ]
  | some b => simp [fill, hρ, h i b hρ]

section Fintype

variable [Fintype ι]

/-- A free coordinate of an extension is free in the partial assignment it extends. -/
theorem Extends.free_subset {ρ ρ' : PartialAssignment ι} (h : ρ'.Extends ρ) : ρ'.free ⊆ ρ.free :=
  fun i hi => mem_free.2 <| by
    cases hρ : ρ i with
    | none => rfl
    | some b => exact absurd (h i b hρ) (by rw [mem_free.1 hi]; simp)

variable [DecidableEq ι]

/-- Fixing free coordinates extends a partial assignment. -/
theorem extends_assign {S : Finset ι} (hS : S ⊆ ρ.free) (a : ι → Bool) :
    (ρ.assign S a).Extends ρ := fun i b hi => by
  have : i ∉ S := fun h => by simp [mem_free.1 (hS h)] at hi
  simpa [this] using hi

/-- The extensions of `ρ₀` leaving exactly `ℓ` coordinates free. -/
def extensions (ρ₀ : PartialAssignment ι) (ℓ : ℕ) : Finset (PartialAssignment ι) :=
  {ρ | ρ.Extends ρ₀ ∧ #ρ.free = ℓ}

@[simp] theorem mem_extensions {ρ₀ : PartialAssignment ι} {ℓ : ℕ} :
    ρ ∈ ρ₀.extensions ℓ ↔ ρ.Extends ρ₀ ∧ #ρ.free = ℓ := by
  simp [extensions]

/-- For a fixed subset `S ∈ powersetCard ℓ ρ₀.free`, there are `2 ^ (#ρ₀.free - ℓ)` extensions in
`ρ₀.extensions ℓ` whose free set is `S`. -/
theorem card_filter_extensions_free_eq (ρ₀ : PartialAssignment ι) (ℓ : ℕ)
    {S : Finset ι} (hS : S ∈ powersetCard ℓ ρ₀.free) :
    #{ρ ∈ ρ₀.extensions ℓ | ρ.free = S} = 2 ^ (#ρ₀.free - ℓ) := by
  obtain ⟨hSsub, hScard⟩ := mem_powersetCard.1 hS
  have : {ρ ∈ ρ₀.extensions ℓ | ρ.free = S} = Fintype.piFinset fun i =>
      if i ∈ S then {none} else if i ∈ ρ₀.free then {some false, some true} else {ρ₀ i} := by
    ext ρ
    simp only [mem_filter, mem_extensions, Fintype.mem_piFinset]
    constructor
    · rintro ⟨⟨hext, -⟩, rfl⟩ i
      by_cases hi : i ∈ ρ.free
      · simp [hi, mem_free.1 hi]
      · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 fun h => hi (mem_free.2 h)
        by_cases hi₀ : i ∈ ρ₀.free
        · cases b <;> simp [hi, hi₀, hb]
        · obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 fun h => hi₀ (mem_free.2 h)
          simp only [hi, ↓reduceIte, hi₀, mem_singleton]
          rw [hext i c hc, hc]
    · intro h
      have hfree : ρ.free = S := by
        ext i
        have := h i
        by_cases hi : i ∈ S
        · simp_all
        · by_cases hi₀ : i ∈ ρ₀.free
          · cases hρ : ρ i <;> simp_all
          · simp only [hi, ↓reduceIte, hi₀, mem_singleton] at this
            simp only [mem_free, this, hi, iff_false]
            exact fun h' => hi₀ (mem_free.2 h')
      refine ⟨⟨fun i b hb => ?_, hfree ▸ hScard⟩, hfree⟩
      have hi₀ : i ∉ ρ₀.free := by simp [mem_free, hb]
      have hi : i ∉ S := fun hi => hi₀ (hSsub hi)
      simpa [hi, hi₀, hb] using h i
  rw [this, Fintype.card_piFinset]
  simp only [apply_ite card, card_singleton,
    card_pair (show some false ≠ some true by simp)]
  rw [prod_ite, prod_const_one, one_mul, prod_ite, prod_const,
    prod_const_one, mul_one, filter_filter,
    show ({a | a ∉ S ∧ a ∈ ρ₀.free} : Finset ι) = ρ₀.free \ S by
      ext a
      simp [and_comm], card_sdiff_of_subset hSsub, hScard]

/-- There are `(m choose ℓ) 2 ^ (m - ℓ)` extensions of `ρ₀` leaving `ℓ` of the `m` free
coordinates of `ρ₀` free. -/
theorem card_extensions (ρ₀ : PartialAssignment ι) (ℓ : ℕ) :
    #(ρ₀.extensions ℓ) = (#ρ₀.free).choose ℓ * 2 ^ (#ρ₀.free - ℓ) := by
  rw [card_eq_sum_card_fiberwise (f := free) (t := powersetCard ℓ ρ₀.free)
    fun ρ hρ => mem_powersetCard.2
      ⟨(mem_extensions.1 hρ).1.free_subset, (mem_extensions.1 hρ).2⟩]
  rw [sum_congr rfl fun S hS => card_filter_extensions_free_eq ρ₀ ℓ hS,
    sum_const, card_powersetCard, smul_eq_mul]

/-- The number of extensions in `ρ₀.extensions ℓ` whose free coordinates lie inside `U ⊆ ρ₀.free` is
`C(|U|, ℓ) * 2 ^ (#ρ₀.free - ℓ)`. -/
theorem card_filter_extensions_free_subset (ρ₀ : PartialAssignment ι) (ℓ : ℕ)
    {U : Finset ι} (hU : U ⊆ ρ₀.free) :
    #{ρ ∈ ρ₀.extensions ℓ | ρ.free ⊆ U} = (#U).choose ℓ * 2 ^ (#ρ₀.free - ℓ) := by
  rw [card_eq_sum_card_fiberwise (f := free) (t := powersetCard ℓ U)
    fun ρ hρ => by
      obtain ⟨hρ_ext, hρ_sub⟩ := mem_filter.1 hρ
      exact mem_powersetCard.2 ⟨hρ_sub, (mem_extensions.1 hρ_ext).2⟩]
  rw [sum_congr rfl (g := fun _ => 2 ^ (#ρ₀.free - ℓ)), sum_const, card_powersetCard, smul_eq_mul]
  intro S hS
  obtain ⟨hSsub, hScard⟩ := mem_powersetCard.1 hS
  have hfilter :
      {ρ ∈ {ρ ∈ ρ₀.extensions ℓ | ρ.free ⊆ U} | ρ.free = S} =
        {ρ ∈ ρ₀.extensions ℓ | ρ.free = S} := by
    ext ρ
    simp only [mem_filter]
    exact ⟨fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨h1, h2 ▸ hSsub⟩, h2⟩⟩
  rw [hfilter]
  exact card_filter_extensions_free_eq ρ₀ ℓ (mem_powersetCard.2 ⟨hSsub.trans hU, hScard⟩)

/-- The number of extensions in `ρ₀.extensions ℓ` that fix every coordinate of `B ⊆ ρ₀.free` is
`C(#ρ₀.free - |B|, ℓ) * 2 ^ (#ρ₀.free - ℓ)`. -/
theorem card_filter_extensions_not_nonempty_inter (ρ₀ : PartialAssignment ι) (ℓ : ℕ)
    {B : Finset ι} (hB : B ⊆ ρ₀.free) :
    #{ρ ∈ ρ₀.extensions ℓ | ¬(ρ.free ∩ B).Nonempty} =
      (#ρ₀.free - #B).choose ℓ * 2 ^ (#ρ₀.free - ℓ) := by
  have heq :
      {ρ ∈ ρ₀.extensions ℓ | ¬(ρ.free ∩ B).Nonempty} =
        {ρ ∈ ρ₀.extensions ℓ | ρ.free ⊆ ρ₀.free \ B} := by
    ext ρ
    simp only [mem_filter, not_nonempty_iff_eq_empty]
    refine and_congr_right fun hρ => ?_
    have hsub := (mem_extensions.1 hρ).1.free_subset
    constructor
    · intro hemp i hi
      refine mem_sdiff.2 ⟨hsub hi, fun hiB => ?_⟩
      have : i ∈ (∅ : Finset ι) := hemp ▸ mem_inter.2 ⟨hi, hiB⟩
      exact notMem_empty i this
    · intro hsub'
      ext i
      simp only [mem_inter, notMem_empty, iff_false, not_and]
      intro hi
      exact (mem_sdiff.1 (hsub' hi)).2
  rw [heq, card_filter_extensions_free_subset ρ₀ ℓ sdiff_subset, card_sdiff_of_subset hB]

variable (ι) in
/-- The partial assignments leaving exactly `ℓ` coordinates free: the extensions of the one fixing
nothing. -/
abbrev withFree (ℓ : ℕ) : Finset (PartialAssignment ι) :=
  extensions empty ℓ

theorem mem_withFree {ℓ : ℕ} : ρ ∈ withFree ι ℓ ↔ #ρ.free = ℓ := by
  simp

/-- There are `(|ι| choose ℓ) 2 ^ (|ι| - ℓ)` partial assignments leaving exactly `ℓ` coordinates
free. -/
theorem card_withFree (ℓ : ℕ) :
    #(withFree ι ℓ) = (Fintype.card ι).choose ℓ * 2 ^ (Fintype.card ι - ℓ) := by
  rw [card_extensions, free_empty, card_univ]

/-- A partial assignment with `ℓ'` free coordinates extends `C(|ι| - ℓ', ℓ - ℓ')` of the ones
with `ℓ ≥ ℓ'` free coordinates: those that free `ℓ - ℓ'` of its fixed coordinates. -/
theorem card_filter_extends_withFree {ρ' : PartialAssignment ι} {ℓ : ℕ} (hℓ : #ρ'.free ≤ ℓ) :
    #((withFree ι ℓ).filter fun ρ => ρ'.Extends ρ) =
      (Fintype.card ι - #ρ'.free).choose (ℓ - #ρ'.free) := by
  have h := card_filter_powersetCard_subset ρ'.free univ ℓ (subset_univ _) hℓ
  rw [card_univ] at h
  rw [← h]
  refine card_nbij' free (fun F i => if i ∈ F then none else ρ' i) (fun ρ hρ => ?_)
    (fun F hF => ?_) (fun ρ hρ => ?_) (fun F hF => ?_)
  · obtain ⟨hρ, hext⟩ := mem_filter.1 hρ
    exact mem_filter.2 ⟨mem_powersetCard.2 ⟨subset_univ _, (mem_withFree.1 hρ)⟩,
      hext.free_subset⟩
  · obtain ⟨hF, hsub⟩ := mem_filter.1 hF
    have hfree : free (fun i => if i ∈ F then none else ρ' i) = F := by
      ext i
      by_cases hi : i ∈ F
      · simp [hi]
      · simp only [mem_free, hi, ↓reduceIte, iff_false]
        exact fun h => hi (hsub (mem_free.2 h))
    refine mem_filter.2 ⟨mem_withFree.2 ?_, fun i b hb => ?_⟩
    · rw [hfree]
      exact (mem_powersetCard.1 hF).2
    · by_cases hi : i ∈ F
      · simp [hi] at hb
      · simpa [hi] using hb
  · obtain ⟨-, hext⟩ := mem_filter.1 hρ
    funext i
    by_cases hi : i ∈ ρ.free
    · simp [hi, mem_free.1 hi]
    · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 fun h => hi (mem_free.2 h)
      simp [hi, hb, hext i b hb]
  · obtain ⟨-, hsub⟩ := mem_filter.1 hF
    ext i
    by_cases hi : i ∈ F
    · simp [hi]
    · simp only [mem_free, hi, ↓reduceIte, iff_false]
      exact fun h => hi (hsub (mem_free.2 h))

/-! ### Drawing random restrictions -/

/-- The words agreeing with a partial assignment outside its free coordinates: `2 ^ ℓ` of them for
`ℓ` free coordinates. -/
theorem card_filter_outside_eq (ρ : PartialAssignment ι) :
    #{z : ι → Bool | outside ρ.free z = ρ} = 2 ^ #ρ.free := by
  rw [← card_filter_forall_notMem_eq ρ.free (ρ.fill fun _ => false)]
  congr 1
  ext z
  simp only [mem_filter, mem_univ, true_and, funext_iff, outside]
  refine forall_congr' fun i => ?_
  by_cases hi : i ∈ ρ.free
  · simp [hi, mem_free.1 hi]
  · obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 fun h => hi (mem_free.2 h)
    simp [hi, hc, fill]

/-- **Drawing a free set and a word**: fixing the coordinates outside a set `J` of `ℓ`
coordinates to a word `z` draws every partial assignment with `ℓ` free coordinates `2 ^ ℓ`
times. -/
theorem sum_card_filter_outside (Q : PartialAssignment ι → Prop) [DecidablePred Q] (ℓ : ℕ) :
    ∑ J ∈ (univ : Finset ι).powersetCard ℓ, #{z : ι → Bool | Q (outside J z)} =
      2 ^ ℓ * #{ρ ∈ withFree ι ℓ | Q ρ} := by
  rw [← card_sigma, card_eq_sum_card_fiberwise (f := fun p => outside p.1 p.2)
    (t := (withFree ι ℓ).filter Q) fun p hp => ?_]
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

/-- **Double counting extensions.** Summed over the partial assignments with `ℓ` free coordinates,
the extensions with `ℓ' ≤ ℓ` free coordinates satisfying `P` count each partial assignment with `ℓ'`
free coordinates satisfying `P` once for each of the `C(|ι| - ℓ', ℓ - ℓ')` ones it extends. -/
theorem sum_card_filter_extensions (P : PartialAssignment ι → Prop) [DecidablePred P] {ℓ ℓ' : ℕ}
    (hℓ : ℓ' ≤ ℓ) :
    ∑ ρ ∈ withFree ι ℓ, #{ρ' ∈ ρ.extensions ℓ' | P ρ'} =
      #{ρ' ∈ withFree ι ℓ' | P ρ'} * (Fintype.card ι - ℓ').choose (ℓ - ℓ') := by
  have h := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := withFree ι ℓ)
    (t := (withFree ι ℓ').filter P) (r := fun ρ ρ' => ρ'.Extends ρ)
  have habove (ρ : PartialAssignment ι) : #{ρ' ∈ ρ.extensions ℓ' | P ρ'} =
      #(((withFree ι ℓ').filter P).bipartiteAbove (fun ρ ρ' => ρ'.Extends ρ) ρ) := by
    congr 1
    ext ρ'
    simp only [mem_filter, mem_extensions, bipartiteAbove]
    tauto
  rw [sum_congr rfl fun ρ _ => habove ρ, h, sum_congr rfl fun ρ' hρ' => ?_, sum_const,
    smul_eq_mul]
  have hfree : #ρ'.free = ℓ' := mem_withFree.1 (mem_filter.1 hρ').1
  rw [bipartiteBelow, ← hfree, card_filter_extends_withFree (hfree ▸ hℓ)]

/-- **Double counting one-step extensions.** Summing `g (update ρ i (some b))` over all extensions
`ρ ∈ ρ₀.extensions t`, free coordinates `i ∈ ρ.free`, and constants `b : Bool` counts each
extension `ρ' ∈ ρ₀.extensions (t - 1)` once for each of the `#ρ₀.free - (t - 1)` coordinates of
`ρ₀.free` fixed by `ρ'`. -/
theorem sum_extensions_update (ρ₀ : PartialAssignment ι) {t : ℕ} (ht1 : 1 ≤ t)
    (g : PartialAssignment ι → ℕ) :
    ∑ ρ ∈ ρ₀.extensions t, ∑ i ∈ ρ.free,
        (g (update ρ i (some false)) + g (update ρ i (some true))) =
      (#ρ₀.free - (t - 1)) * ∑ ρ' ∈ ρ₀.extensions (t - 1), g ρ' := by
  have h1 : ∑ ρ ∈ ρ₀.extensions t, ∑ i ∈ ρ.free,
        (g (update ρ i (some false)) + g (update ρ i (some true))) =
      ∑ x ∈ ((ρ₀.extensions t).sigma fun ρ => ρ.free) ×ˢ (univ : Finset Bool),
        g (update x.1.1 x.1.2 (some x.2)) := by
    rw [sum_product, sum_sigma]
    refine sum_congr rfl fun ρ _ => sum_congr rfl fun i _ => ?_
    have : (univ : Finset Bool) = {false, true} := by decide
    rw [this, sum_pair (by decide)]
  have h2 : (#ρ₀.free - (t - 1)) * ∑ ρ' ∈ ρ₀.extensions (t - 1), g ρ' =
      ∑ p ∈ (ρ₀.extensions (t - 1)).sigma (fun ρ' => ρ₀.free \ ρ'.free), g p.1 := by
    rw [sum_sigma, mul_sum]
    refine sum_congr rfl fun ρ' hρ' => ?_
    obtain ⟨hext, hfree⟩ := mem_extensions.1 hρ'
    dsimp only
    rw [sum_const, smul_eq_mul, card_sdiff_of_subset hext.free_subset, hfree]
  rw [h1, h2]
  refine sum_nbij' (fun x => ⟨update x.1.1 x.1.2 (some x.2), x.1.2⟩)
    (fun y => ⟨⟨update y.1 y.2 none, y.2⟩, (y.1 y.2).getD false⟩)
    (fun x hx => ?_) (fun y hy => ?_) (fun x hx => ?_) (fun y hy => ?_) (fun _ _ => rfl)
  · obtain ⟨hx1, _⟩ := mem_product.1 hx
    obtain ⟨hρ, hi⟩ := mem_sigma.1 hx1
    obtain ⟨hext, hfree⟩ := mem_extensions.1 hρ
    refine mem_sigma.2 ⟨mem_extensions.2 ⟨fun j c hj => ?_, ?_⟩, ?_⟩
    · have hne : j ≠ x.1.2 := fun h => by
        subst h
        rw [mem_free.1 (hext.free_subset hi)] at hj
        cases hj
      simpa [hne] using hext j c hj
    · rw [free_update, card_erase_of_mem hi, hfree]
    · rw [mem_sdiff, free_update]
      exact ⟨hext.free_subset hi, notMem_erase _ _⟩
  · obtain ⟨hρ', hi⟩ := mem_sigma.1 hy
    obtain ⟨hext, hfree⟩ := mem_extensions.1 hρ'
    obtain ⟨hi₀, hi'⟩ := mem_sdiff.1 hi
    refine mem_product.2 ⟨mem_sigma.2 ⟨mem_extensions.2 ⟨fun j c hj => ?_, ?_⟩,
      ?_⟩, mem_univ _⟩
    · have hne : j ≠ y.2 := fun h => by
        subst h
        rw [mem_free.1 hi₀] at hj
        cases hj
      simpa [hne] using hext j c hj
    · have hfree_up : free (update y.1 y.2 none) = insert y.2 y.1.free := by
        ext j
        by_cases hj : j = y.2 <;> simp [hj]
      rw [hfree_up, card_insert_of_notMem hi', hfree]
      omega
    · simp
  · obtain ⟨hx1, _⟩ := mem_product.1 hx
    obtain ⟨_, hi⟩ := mem_sigma.1 hx1
    ext : 1
    · refine Sigma.ext ?_ HEq.rfl
      funext j
      by_cases hj : j = x.1.2
      · subst hj
        simpa using (mem_free.1 hi).symm
      · simp [hj]
    · simp
  · obtain ⟨_, hi⟩ := mem_sigma.1 hy
    obtain ⟨_, hi'⟩ := mem_sdiff.1 hi
    refine Sigma.ext ?_ HEq.rfl
    funext j
    by_cases hj : j = y.2
    · subst hj
      obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 fun h => hi' (mem_free.2 h)
      simp [hc]
    · simp [hj]

/-- Relating the number of extensions with `t - 1` and `t` free coordinates:
`(#ρ₀.free - (t - 1)) * #(ρ₀.extensions (t - 1)) = 2 * t * #(ρ₀.extensions t)`. -/
theorem mul_card_extensions_sub_one (ρ₀ : PartialAssignment ι) {t : ℕ} (ht1 : 1 ≤ t) :
    (#ρ₀.free - (t - 1)) * #(ρ₀.extensions (t - 1)) = 2 * t * #(ρ₀.extensions t) := by
  have h := (sum_extensions_update ρ₀ ht1 (fun _ => 1)).symm
  rw [sum_const, smul_eq_mul, mul_one] at h
  have hinner (ρ : PartialAssignment ι) (hρ : ρ ∈ ρ₀.extensions t) :
      ∑ i ∈ ρ.free, (1 + 1) = 2 * t := by
    rw [sum_const, smul_eq_mul, (mem_extensions.1 hρ).2]
    ring
  rw [h, sum_congr rfl hinner, sum_const, smul_eq_mul]
  ring

/-- **Union bound for block survival**: if `ρ₀` has `b * m` free coordinates and `B 0, …, B (b - 1)`
are `b` subsets of `ρ₀.free` of size `m`, then for `1 ≤ b` and `2 * b ≤ 2 ^ r`, at least half of
all extensions in `ρ₀.extensions (b * r)` leave at least one free coordinate in every block
`B j`. -/
theorem card_extensions_le_two_mul_card_filter_forall_nonempty
    (ρ₀ : PartialAssignment ι) {b m : ℕ} (hb : 1 ≤ b) (hfree : #ρ₀.free = b * m)
    {B : Fin b → Finset ι} (hBsub : ∀ j, B j ⊆ ρ₀.free) (hBcard : ∀ j, #(B j) = m)
    {r : ℕ} (hbr : 2 * b ≤ 2 ^ r) :
    #(ρ₀.extensions (b * r)) ≤
      2 * #{ρ ∈ ρ₀.extensions (b * r) | ∀ j : Fin b, (ρ.free ∩ B j).Nonempty} := by
  set k := b * r
  set E := ρ₀.extensions k
  set A := {ρ ∈ E | ∀ j : Fin b, (ρ.free ∩ B j).Nonempty}
  set Bad : Fin b → Finset (PartialAssignment ι) :=
    fun j => {ρ ∈ E | ¬(ρ.free ∩ B j).Nonempty}
  have hcompl_sub : E \ A ⊆ univ.biUnion Bad := by
    intro ρ hρ
    obtain ⟨hρE, hρA⟩ := mem_sdiff.1 hρ
    rw [mem_filter, not_and] at hρA
    obtain ⟨j, hj⟩ := not_forall.1 (hρA hρE)
    exact mem_biUnion.2 ⟨j, mem_univ j, mem_filter.2 ⟨hρE, hj⟩⟩
  have hBad_card (j : Fin b) : #(Bad j) = (b * m - m).choose k * 2 ^ (b * m - k) := by
    rw [card_filter_extensions_not_nonempty_inter ρ₀ k (hBsub j), hfree, hBcard j]
  have hE_card : #E = (b * m).choose k * 2 ^ (b * m - k) := by
    rw [card_extensions, hfree]
  have h2sdiff : 2 * #(E \ A) ≤ #E := by
    calc 2 * #(E \ A)
        ≤ 2 * #(univ.biUnion Bad) := Nat.mul_le_mul_left 2 (card_le_card hcompl_sub)
      _ ≤ 2 * ∑ j : Fin b, #(Bad j) := Nat.mul_le_mul_left 2 card_biUnion_le
      _ = 2 * (b * ((b * m - m).choose k * 2 ^ (b * m - k))) := by
          rw [sum_congr rfl fun j _ => hBad_card j, sum_const, card_univ, Fintype.card_fin,
            smul_eq_mul]
      _ = 2 * b * (b * m - m).choose k * 2 ^ (b * m - k) := by ring
      _ ≤ 2 ^ r * (b * m - m).choose k * 2 ^ (b * m - k) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hbr)
      _ ≤ (b * m).choose k * 2 ^ (b * m - k) :=
          Nat.mul_le_mul_right _ (Nat.two_pow_mul_choose_sub_le hb r)
      _ = #E := hE_card.symm
  have hAsub : A ⊆ E := filter_subset _ _
  have hpart : #(E \ A) + #A = #E := card_sdiff_add_card_eq_card hAsub
  omega

end Fintype

/-- **Two stages of restrictions, counted.** Drawing a restriction with `ℓ'` free bits by first
drawing one with `ℓ ≥ ℓ'` free bits and then an extension of it: if at most a `G / c` fraction of
the restrictions with `ℓ` free bits satisfy `B`, and for each other one at most an `H / c` fraction
of its extensions with `ℓ'` free bits satisfy `B'`, then at most a `(G + H) / c` fraction of the
restrictions with `ℓ'` free bits satisfy `B'`. -/
theorem mul_card_filter_withFree_le {n c G H G' ℓ ℓ' : ℕ} (hℓ'ℓ : ℓ' ≤ ℓ) (hℓn : ℓ ≤ n)
    {B B' : PartialAssignment (Fin n) → Prop} [DecidablePred B] [DecidablePred B']
    (h₁ : c * #{ρ ∈ withFree (Fin n) ℓ | B ρ} ≤ G * #(withFree (Fin n) ℓ))
    (h₂ : ∀ ρ ∈ withFree (Fin n) ℓ, ¬ B ρ →
      c * #{ρ' ∈ ρ.extensions ℓ' | B' ρ'} ≤ H * #(ρ.extensions ℓ'))
    (hG : G + H ≤ G') :
    c * #{ρ ∈ withFree (Fin n) ℓ' | B' ρ} ≤ G' * #(withFree (Fin n) ℓ') := by
  set W := withFree (Fin n) ℓ
  set F := (n - ℓ').choose (ℓ - ℓ')
  have hF : 0 < F := Nat.choose_pos (by omega)
  set T := ℓ.choose ℓ' * 2 ^ (ℓ - ℓ')
  have hT : ∀ ρ ∈ W, #(ρ.extensions ℓ') = T := fun ρ hρ => by
    rw [card_extensions, mem_withFree.1 hρ]
  -- each restriction with `ℓ` free bits has few bad extensions, unless it satisfies `B`
  have hper : ∀ ρ ∈ W, c * #{ρ' ∈ ρ.extensions ℓ' | B' ρ'} ≤
      (if B ρ then c else 0) * T + H * T := fun ρ hρ => by
    by_cases hb : B ρ
    · simp only [hb, ↓reduceIte]
      rw [← hT ρ hρ]
      exact (Nat.mul_le_mul_left _ (card_filter_le _ _)).trans (Nat.le_add_right _ _)
    · simp only [hb, ↓reduceIte, zero_mul, zero_add]
      rw [← hT ρ hρ]
      exact h₂ ρ hρ hb
  -- double counting the extensions, with and without the condition
  have hdc := sum_card_filter_extensions B' hℓ'ℓ
  have hall := sum_card_filter_extensions (ι := Fin n) (fun _ => True) hℓ'ℓ
  simp only [filter_true] at hall
  rw [Fintype.card_fin] at hdc hall
  rw [sum_congr rfl hT, sum_const, smul_eq_mul] at hall
  refine Nat.le_of_mul_le_mul_right (?_ : _ * F ≤ _ * F) hF
  calc c * #{ρ ∈ withFree (Fin n) ℓ' | B' ρ} * F
      = ∑ ρ ∈ W, c * #{ρ' ∈ ρ.extensions ℓ' | B' ρ'} := by
        rw [mul_assoc, ← hdc, mul_sum]
    _ ≤ ∑ ρ ∈ W, ((if B ρ then c else 0) * T + H * T) := sum_le_sum hper
    _ = c * #{ρ ∈ W | B ρ} * T + #W * H * T := by
        rw [sum_add_distrib, ← sum_mul, sum_ite, sum_const_zero, add_zero, sum_const,
          smul_eq_mul, sum_const, smul_eq_mul]
        ring
    _ ≤ G * #W * T + #W * H * T := by gcongr
    _ = (G + H) * #(withFree (Fin n) ℓ') * F := by
        rw [mul_assoc _ #(withFree (Fin n) ℓ'), ← hall]
        ring
    _ ≤ G' * #(withFree (Fin n) ℓ') * F := by gcongr

end PartialAssignment

/-! ### Subfunctions -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The subfunctions of `f` on the coordinates `Y`: for each assignment `z` of the other
coordinates, the function that reads the coordinates in `Y` from its input and the others from
`z`. -/
def subfunctions (f : (ι → Bool) → Bool) (Y : Finset ι) : Finset ((ι → Bool) → Bool) :=
  univ.image fun z x => f (Y.piecewise x z)

@[simp] theorem mem_subfunctions {f g : (ι → Bool) → Bool} {Y : Finset ι} :
    g ∈ subfunctions f Y ↔ ∃ z, (fun x => f (Y.piecewise x z)) = g := by
  simp [subfunctions]

/-- The subfunctions on `Y` are the restrictions by the partial assignments fixing exactly the
coordinates outside `Y`. -/
theorem mem_subfunctions_iff {f g : (ι → Bool) → Bool} {Y : Finset ι} :
    g ∈ subfunctions f Y ↔ ∃ z, f ∘ (PartialAssignment.outside Y z).fill = g := by
  simp only [mem_subfunctions]
  exact exists_congr fun z => by rw [show f ∘ (PartialAssignment.outside Y z).fill =
    fun x => f (Y.piecewise x z) from funext fun x => by simp]

end Cslib.BitString
