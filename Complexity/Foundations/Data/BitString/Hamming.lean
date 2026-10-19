/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Weight

/-!
# The Hamming geometry of the Boolean cube

Points of the cube `ι → Bool` are compared by Mathlib's Hamming distance, the number of
coordinates where they differ. The Boolean operations act on points coordinatewise, and their
geometry is exact. For `f g h : ι → Bool` on a finite set `ι`:

* conjunction and disjunction sort a pair coordinatewise, so the distances from `f ∧ g` and
  `f ∨ g` to any `h` add up to those from `f` and `g`
  (`Cslib.BitString.hammingDist_and_add_hammingDist_or`);
* `f ∧ g` and `f ∨ g` lie on geodesics from `f` to `g`
  (`Cslib.BitString.hammingDist_add_hammingDist_and`,
  `Cslib.BitString.hammingDist_add_hammingDist_or`), and both are `1`-Lipschitz in each argument;
* adding a fixed point, which is the coordinatewise exclusive or, and negation are isometries
  (`Cslib.BitString.hammingDist_add_right`, `Cslib.BitString.hammingDist_not`);
* the cube is a median algebra for the coordinatewise majority
  `m(f,g,h) = (f ∧ g) ∨ (g ∧ h) ∨ (h ∧ f)` (`Cslib.BitString.median`), the lattice median of the
  distributive lattice `ι → Bool`: it satisfies the majority law, symmetry and the associative law,
  and it distributes over itself. The median lies between any two of its arguments and minimizes
  the total distance to the three of them.

The truth tables of Boolean functions are points of the cube `(ι → Bool) → Bool`. The parities on
two distinct sets `S` and `T` disagree exactly where the parity on the symmetric difference
`S ∆ T` is true, which happens on half of the inputs, so they differ on exactly half of the inputs
(`Cslib.BitString.two_mul_hammingDist_parityOn`). Two distinct coordinate projections `x ↦ x i`
and `x ↦ x j` are the parities on `{i}` and `{j}`, so they differ on exactly half of the inputs
(`Cslib.BitString.two_mul_hammingDist_proj`), and so do their shifts `f + x_i` and `f + x_j` by
any common function `f` (`Cslib.BitString.two_mul_hammingDist_add_proj`), however complicated `f`
is.

## Main definitions

* `Cslib.BitString.median`: the coordinatewise majority of three points.

## Main results

* `Cslib.BitString.hammingDist_and_add_hammingDist_or`: conjunction and disjunction sort.
* `Cslib.BitString.hammingDist_add_hammingDist_and`,
  `Cslib.BitString.hammingDist_add_hammingDist_or`: geodesics.
* `Cslib.BitString.hammingDist_and_le`, `Cslib.BitString.hammingDist_or_le`: Lipschitz gates.
* `Cslib.BitString.hammingDist_add_right`, `Cslib.BitString.hammingDist_add_left`,
  `Cslib.BitString.hammingDist_not`: isometries.
* `Cslib.BitString.median_self_left`, `Cslib.BitString.median_swap_left`,
  `Cslib.BitString.median_swap_right`, `Cslib.BitString.median_assoc`: the median algebra laws.
* `Cslib.BitString.median_median_distrib`: distributivity.
* `Cslib.BitString.hammingDist_add_hammingDist_median`, `Cslib.BitString.hammingDist_median_le`:
  betweenness and minimality of the median.
* `Cslib.BitString.two_mul_hammingDist_parityOn`: distinct parities are half the cube apart.
* `Cslib.BitString.two_mul_hammingDist_proj`, `Cslib.BitString.hammingDist_proj_div`,
  `Cslib.BitString.two_mul_hammingDist_add_proj`: projections and their shifts are half the cube
  apart.

## References

* [F. J. MacWilliams, N. J. A. Sloane, *The Theory of Error-Correcting Codes*]
  [MacWilliamsSloane1977]
-/

@[expose] public section

namespace Cslib.BitString

open Finset

variable {ι : Type*}

/-! ### The median -/

/-- The median of three points: their coordinatewise majority `(f ∧ g) ∨ (g ∧ h) ∨ (h ∧ f)`.
This is the lattice median `(f ⊓ g) ⊔ (g ⊓ h) ⊔ (h ⊓ f)` of the distributive lattice
`ι → Bool`. -/
def median (f g h : ι → Bool) : ι → Bool :=
  fun i => f i && g i || g i && h i || h i && f i

/-- The median is the majority of three bits at each coordinate. -/
theorem median_apply_eq_majority (f g h : ι → Bool) (i : ι) :
    median f g h i = majority 3 ![f i, g i, h i] := by
  have key : ∀ a b c : Bool, (a && b || b && c || c && a) = majority 3 ![a, b, c] := by
    decide
  exact key (f i) (g i) (h i)

/-- **The majority law**: a point repeated twice is the median. -/
@[simp] theorem median_self_left (f g : ι → Bool) : median f f g = f := by
  funext i
  have key : ∀ a b : Bool, (a && a || a && b || b && a) = a := by decide
  exact key (f i) (g i)

theorem median_swap_left (f g h : ι → Bool) : median f g h = median g f h := by
  funext i
  have key : ∀ a b c : Bool, (a && b || b && c || c && a) = (b && a || a && c || c && b) := by
    decide
  exact key (f i) (g i) (h i)

theorem median_swap_right (f g h : ι → Bool) : median f g h = median f h g := by
  funext i
  have key : ∀ a b c : Bool, (a && b || b && c || c && a) = (a && c || c && b || b && a) := by
    decide
  exact key (f i) (g i) (h i)

/-- **The associative law** of median algebras. Together with the majority law and symmetry it
makes the cube a median algebra. -/
theorem median_assoc (f g h k : ι → Bool) :
    median (median f k g) k h = median f k (median g k h) := by
  funext i
  have key : ∀ a b c d : Bool,
      ((a && d || d && b || b && a) && d || d && c || c && (a && d || d && b || b && a)) =
        (a && d || d && (b && d || d && c || c && b) || (b && d || d && c || c && b) && a) := by
    decide
  exact key (f i) (g i) (h i) (k i)

/-- **The median distributes over itself.** -/
theorem median_median_distrib (f g h k l : ι → Bool) :
    median (median f g h) k l = median (median f k l) (median g k l) (median h k l) := by
  funext i
  have key : ∀ a b c d e : Bool,
      ((a && b || b && c || c && a) && d || d && e || e && (a && b || b && c || c && a)) =
        ((a && d || d && e || e && a) && (b && d || d && e || e && b) ||
          (b && d || d && e || e && b) && (c && d || d && e || e && c) ||
          (c && d || d && e || e && c) && (a && d || d && e || e && a)) := by
    decide
  exact key (f i) (g i) (h i) (k i) (l i)

section Fintype

variable [Fintype ι]

/-- The Hamming distance counts the coordinates of disagreement. -/
private theorem hammingDist_eq_sum (u v : ι → Bool) :
    hammingDist u v = ∑ i, if u i ≠ v i then 1 else 0 :=
  card_filter _ _

/-! ### Conjunction and disjunction -/

/-- **Conjunction and disjunction sort a pair**, so their distances to any `h` add up to those of
the pair. -/
theorem hammingDist_and_add_hammingDist_or (f g h : ι → Bool) :
    hammingDist (fun i => f i && g i) h + hammingDist (fun i => f i || g i) h =
      hammingDist f h + hammingDist g h := by
  simp only [hammingDist_eq_sum, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  have key : ∀ a b c : Bool,
      ((if (a && b) ≠ c then 1 else 0) + if (a || b) ≠ c then 1 else 0 : ℕ) =
        (if a ≠ c then 1 else 0) + if b ≠ c then 1 else 0 := by
    decide
  exact key (f i) (g i) (h i)

/-- **The conjunction lies on a geodesic** from `f` to `g`. -/
theorem hammingDist_add_hammingDist_and (f g : ι → Bool) :
    hammingDist f (fun i => f i && g i) + hammingDist (fun i => f i && g i) g =
      hammingDist f g := by
  simp only [hammingDist_eq_sum, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  have key : ∀ a b : Bool,
      ((if a ≠ (a && b) then 1 else 0) + if (a && b) ≠ b then 1 else 0 : ℕ) =
        if a ≠ b then 1 else 0 := by
    decide
  exact key (f i) (g i)

/-- **The disjunction lies on a geodesic** from `f` to `g`. -/
theorem hammingDist_add_hammingDist_or (f g : ι → Bool) :
    hammingDist f (fun i => f i || g i) + hammingDist (fun i => f i || g i) g =
      hammingDist f g := by
  simp only [hammingDist_eq_sum, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  have key : ∀ a b : Bool,
      ((if a ≠ (a || b) then 1 else 0) + if (a || b) ≠ b then 1 else 0 : ℕ) =
        if a ≠ b then 1 else 0 := by
    decide
  exact key (f i) (g i)

/-- Conjunction is `1`-Lipschitz in each argument. -/
theorem hammingDist_and_le (f f' g g' : ι → Bool) :
    hammingDist (fun i => f i && g i) (fun i => f' i && g' i) ≤
      hammingDist f f' + hammingDist g g' :=
  (hammingDist_triangle _ (fun i => f' i && g i) _).trans (Nat.add_le_add
    (hammingDist_comp_le_hammingDist fun i b => b && g i)
    (hammingDist_comp_le_hammingDist fun i b => f' i && b))

/-- Disjunction is `1`-Lipschitz in each argument. -/
theorem hammingDist_or_le (f f' g g' : ι → Bool) :
    hammingDist (fun i => f i || g i) (fun i => f' i || g' i) ≤
      hammingDist f f' + hammingDist g g' :=
  (hammingDist_triangle _ (fun i => f' i || g i) _).trans (Nat.add_le_add
    (hammingDist_comp_le_hammingDist fun i b => b || g i)
    (hammingDist_comp_le_hammingDist fun i b => f' i || b))

/-! ### Isometries -/

/-- Adding a fixed point, coordinatewise the exclusive or, is an isometry. -/
@[simp] theorem hammingDist_add_right (f g a : ι → Bool) :
    hammingDist (f + a) (g + a) = hammingDist f g :=
  hammingDist_comp (fun i b => b + a i) fun i => add_left_injective (a i)

/-- Adding a fixed point on the left is an isometry. -/
@[simp] theorem hammingDist_add_left (a f g : ι → Bool) :
    hammingDist (a + f) (a + g) = hammingDist f g :=
  hammingDist_comp (fun i b => a i + b) fun i => add_right_injective (a i)

/-- Negation is an isometry. -/
@[simp] theorem hammingDist_not (f g : ι → Bool) :
    hammingDist (fun i => !f i) (fun i => !g i) = hammingDist f g :=
  hammingDist_comp (fun _ => not) fun _ => Function.LeftInverse.injective Bool.not_not

/-! ### Distances to the median -/

/-- **The median lies between any two of its arguments.** -/
theorem hammingDist_add_hammingDist_median (f g h : ι → Bool) :
    hammingDist f (median f g h) + hammingDist (median f g h) g = hammingDist f g := by
  simp only [hammingDist_eq_sum, ← sum_add_distrib, median]
  refine sum_congr rfl fun i _ => ?_
  have key : ∀ a b c : Bool,
      ((if a ≠ (a && b || b && c || c && a) then 1 else 0) +
        if (a && b || b && c || c && a) ≠ b then 1 else 0 : ℕ) = if a ≠ b then 1 else 0 := by
    decide
  exact key (f i) (g i) (h i)

/-- **The median minimizes the total distance** to its three arguments. -/
theorem hammingDist_median_le (f g h k : ι → Bool) :
    hammingDist (median f g h) f + hammingDist (median f g h) g + hammingDist (median f g h) h ≤
      hammingDist k f + hammingDist k g + hammingDist k h := by
  simp only [hammingDist_eq_sum, ← sum_add_distrib, median]
  refine sum_le_sum fun i _ => ?_
  have key : ∀ a b c d : Bool,
      ((if (a && b || b && c || c && a) ≠ a then 1 else 0) +
          (if (a && b || b && c || c && a) ≠ b then 1 else 0) +
          if (a && b || b && c || c && a) ≠ c then 1 else 0 : ℕ) ≤
        (if d ≠ a then 1 else 0) + (if d ≠ b then 1 else 0) + if d ≠ c then 1 else 0 := by
    decide
  exact key (f i) (g i) (h i) (k i)

/-! ### Parities and coordinate projections -/

variable [DecidableEq ι]

/-- **Distinct parities differ on exactly half of the inputs**: they disagree where the parity on
the symmetric difference is true. -/
theorem two_mul_hammingDist_parityOn {S T : Finset ι} (h : S ≠ T) :
    2 * hammingDist (parityOn S) (parityOn T) = 2 ^ Fintype.card ι := by
  have hfilter : (univ.filter fun x : ι → Bool => parityOn S x ≠ parityOn T x) =
      univ.filter fun x => parityOn (symmDiff S T) x = true := by
    refine filter_congr fun x _ => ?_
    rw [parityOn_symmDiff]
    cases parityOn S x <;> cases parityOn T x <;> decide
  have hne : (symmDiff S T).Nonempty := symmDiff_nonempty.2 h
  rw [hammingDist, hfilter, card_filter_parityOn_eq hne, mul_comm,
    Nat.two_pow_pred_mul_two (Fintype.card_pos_iff.2 ⟨hne.choose⟩)]

/-- **Two distinct coordinate projections differ on exactly half of the inputs**: they are the
parities on `{i}` and `{j}`. -/
theorem two_mul_hammingDist_proj {i j : ι} (hij : i ≠ j) :
    2 * hammingDist (fun x : ι → Bool => x i) (fun x => x j) = 2 ^ Fintype.card ι := by
  have hproj (k : ι) : (fun x : ι → Bool => x k) = parityOn {k} :=
    funext fun x => by rw [parityOn_eq_sum, sum_singleton]
  rw [hproj i, hproj j]
  exact two_mul_hammingDist_parityOn (singleton_injective.ne hij)

/-- The relative Hamming distance between two distinct coordinate projections is one half. -/
theorem hammingDist_proj_div {𝕜 : Type*} [Semifield 𝕜] [CharZero 𝕜] {i j : ι} (hij : i ≠ j) :
    (hammingDist (fun x : ι → Bool => x i) (fun x => x j) : 𝕜) / 2 ^ Fintype.card ι = 1 / 2 := by
  have h : (2 * hammingDist (fun x : ι → Bool => x i) (fun x => x j) : 𝕜) =
      2 ^ Fintype.card ι := by
    exact_mod_cast two_mul_hammingDist_proj hij
  have h2 : (2 : 𝕜) ≠ 0 := OfNat.ofNat_ne_zero 2
  rw [div_eq_div_iff (pow_ne_zero _ h2) h2, one_mul, ← h, mul_comm]

/-- **Shifts of distinct projections by a common function differ on half of the inputs**, however
complicated the common function `f` is. -/
theorem two_mul_hammingDist_add_proj (f : (ι → Bool) → Bool) {i j : ι} (hij : i ≠ j) :
    2 * hammingDist (f + fun x => x i) (f + fun x => x j) = 2 ^ Fintype.card ι := by
  rw [hammingDist_add_left]
  exact two_mul_hammingDist_proj hij

end Fintype

end Cslib.BitString
