/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Kolmogorov.Basic
public import Mathlib.Data.Set.Card
import Mathlib.Data.Vector.Basic

/-!
# Incompressibility

There are only `2 ^ r - 1` binary programs of length below `r`, and each describes at most one
object. So, for every description method, fewer than `2 ^ r` objects have complexity below `r`,
whatever the time bound. Counting strings of length `n` then shows that some string of every
length `n` has complexity at least `n`, and that fewer than a `2 ^ (-c)` fraction of the strings
of length `n` have complexity below `n - c` [Li and Vitányi, Chapter 2][LiVitanyi2019],
[Sipser, Section 6.4][Sipser2013].

## Main results

* `Cslib.Kolmogorov.encard_setOf_length_eq`, `Cslib.Kolmogorov.encard_setOf_length_lt_add_one`:
  there are `2 ^ n` binary strings of length `n` and `2 ^ n - 1` of length below `n`.
* `Cslib.Kolmogorov.DescriptionMethod.encard_setOf_complexity_lt`,
  `Cslib.Kolmogorov.DescriptionMethod.encard_setOf_timeBoundedComplexity_lt`: fewer than `2 ^ r`
  objects have (time-bounded) complexity below `r`.
* `Cslib.Kolmogorov.DescriptionMethod.exists_mem_le_complexity`: a set of at least `2 ^ r`
  objects has an element of complexity at least `r`.
* `Cslib.Kolmogorov.DescriptionMethod.ncard_lt_ncard_setOf_le_complexity_add`: all but fewer than
  `2 ^ r` elements of a finite set have complexity at least `r`.
* `Cslib.Kolmogorov.DescriptionMethod.exists_length_eq_forall_le_timeBoundedComplexity`: for every
  `n` some string of length `n` has complexity at least `n` under every time bound.
* `Cslib.Kolmogorov.DescriptionMethod.encard_setOf_length_eq_complexity_lt`,
  `Cslib.Kolmogorov.DescriptionMethod.two_pow_lt_ncard_setOf_length_eq_le_complexity_add`: fewer
  than `2 ^ (n - c)` strings of length `n` have complexity below `n - c`.

## References

* [M. Li, P. Vitányi, *An Introduction to Kolmogorov Complexity and Its
  Applications*][LiVitanyi2019]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Cslib.Kolmogorov

/-! ### Counting binary strings -/

/-- There are `2 ^ n` binary strings of length `n`. -/
theorem encard_setOf_length_eq (n : ℕ) : {p : List Bool | p.length = n}.encard = 2 ^ n := by
  change ENat.card (List.Vector Bool n) = _
  rw [ENat.card_eq_coe_fintype_card, card_vector]
  simp

/-- There are `2 ^ n - 1` binary strings of length below `n`. -/
theorem encard_setOf_length_lt_add_one (n : ℕ) :
    {p : List Bool | p.length < n}.encard + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hunion : {p : List Bool | p.length < n + 1} =
        {p | p.length < n} ∪ {p | p.length = n} := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_union]
      omega
    have hdisj : Disjoint {p : List Bool | p.length < n} {p | p.length = n} :=
      Set.disjoint_left.mpr fun _ hlt heq => Nat.ne_of_lt hlt heq
    rw [hunion, Set.encard_union_eq hdisj, add_right_comm, ih, encard_setOf_length_eq, pow_succ,
      mul_two]

namespace DescriptionMethod

variable {α : Type*} (M : DescriptionMethod α)

/-! ### Few objects have low complexity -/

/-- **Incompressibility.** Fewer than `2 ^ r` objects have complexity below `r`: they have
distinct shortest programs, all of length below `r`. -/
theorem encard_setOf_complexity_lt (r : ℕ) : {x | M.complexity x < r}.encard < 2 ^ r := by
  classical
  let f (x : α) : List Bool :=
    if h : ∃ p : List Bool, p.length < r ∧ M.Produces p x then h.choose else []
  have hf {x : α} (hx : M.complexity x < r) : (f x).length < r ∧ M.Produces (f x) x := by
    have h := complexity_lt_natCast_iff.mp hx
    simpa only [f, h, ↓reduceDIte] using h.choose_spec
  have hle : {x | M.complexity x < r}.encard ≤ {p : List Bool | p.length < r}.encard :=
    Set.encard_le_encard_of_injOn (fun _ hx => (hf hx).1)
      fun _ hx _ hy hxy => (hf hx).2.unique (hxy ▸ (hf hy).2)
  have htop : {p : List Bool | p.length < r}.encard ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (le_self_add.trans_eq (encard_setOf_length_lt_add_one r))
  rw [← ENat.add_one_le_iff (ne_top_of_le_ne_top htop hle), ← encard_setOf_length_lt_add_one r]
  exact add_le_add_left hle 1

/-- Fewer than `2 ^ r` objects have time-bounded complexity below `r`, for every time bound. -/
theorem encard_setOf_timeBoundedComplexity_lt (t r : ℕ) :
    {x | M.timeBoundedComplexity t x < r}.encard < 2 ^ r :=
  (Set.encard_le_encard fun _ hx =>
    (M.complexity_le_timeBoundedComplexity t _).trans_lt hx).trans_lt
    (M.encard_setOf_complexity_lt r)

/-- A set of at least `2 ^ r` objects has an element of complexity at least `r`. -/
theorem exists_mem_le_complexity {s : Set α} {r : ℕ} (hs : 2 ^ r ≤ s.encard) :
    ∃ x ∈ s, r ≤ M.complexity x := by
  by_contra! h
  exact (hs.trans (Set.encard_le_encard h)).not_gt (M.encard_setOf_complexity_lt r)

/-- All but fewer than `2 ^ r` elements of a finite set have complexity at least `r`. -/
theorem ncard_lt_ncard_setOf_le_complexity_add {s : Set α} (hs : s.Finite) (r : ℕ) :
    s.ncard < {x ∈ s | r ≤ M.complexity x}.ncard + 2 ^ r := by
  have hsub : s ⊆ {x ∈ s | r ≤ M.complexity x} ∪ {x | M.complexity x < r} := fun x hx => by
    by_cases h : (r : ℕ∞) ≤ M.complexity x
    · exact .inl ⟨hx, h⟩
    · exact .inr (not_le.mp h)
  have hfin : {x ∈ s | r ≤ M.complexity x}.Finite := hs.subset fun _ hx => hx.1
  rw [← ENat.natCast_lt_natCast, Nat.cast_add, hs.cast_ncard_eq, hfin.cast_ncard_eq, Nat.cast_pow,
    Nat.cast_ofNat]
  exact (Set.encard_le_encard hsub).trans_lt <| (Set.encard_union_le _ _).trans_lt <|
    WithTop.add_lt_add_left hfin.encard_lt_top.ne (M.encard_setOf_complexity_lt r)

/-! ### Incompressible strings -/

section Strings

variable (M : DescriptionMethod (List Bool))

/-- **Incompressible strings exist.** For every `n`, some string of length `n` has complexity at
least `n`. -/
theorem exists_length_eq_le_complexity (n : ℕ) :
    ∃ x : List Bool, x.length = n ∧ n ≤ M.complexity x :=
  M.exists_mem_le_complexity (encard_setOf_length_eq n).ge

/-- For every `n`, some string of length `n` has complexity at least `n` under every time
bound. -/
theorem exists_length_eq_forall_le_timeBoundedComplexity (n : ℕ) :
    ∃ x : List Bool, x.length = n ∧ ∀ t, n ≤ M.timeBoundedComplexity t x :=
  let ⟨x, hx, hn⟩ := M.exists_length_eq_le_complexity n
  ⟨x, hx, fun t => hn.trans (M.complexity_le_timeBoundedComplexity t x)⟩

/-- **Most strings are nearly incompressible.** Fewer than `2 ^ (n - c)` strings of length `n`
have complexity below `n - c`. -/
theorem encard_setOf_length_eq_complexity_lt (n c : ℕ) :
    {x : List Bool | x.length = n ∧ M.complexity x < (n - c : ℕ)}.encard < 2 ^ (n - c) :=
  (Set.encard_le_encard fun _ hx => hx.2).trans_lt (M.encard_setOf_complexity_lt (n - c))

/-- Fewer than `2 ^ (n - c)` strings of length `n` have time-bounded complexity below `n - c`. -/
theorem encard_setOf_length_eq_timeBoundedComplexity_lt (t n c : ℕ) :
    {x : List Bool | x.length = n ∧ M.timeBoundedComplexity t x < (n - c : ℕ)}.encard <
      2 ^ (n - c) :=
  (Set.encard_le_encard fun _ hx => hx.2).trans_lt
    (M.encard_setOf_timeBoundedComplexity_lt t (n - c))

/-- All but fewer than `2 ^ (n - c)` of the `2 ^ n` strings of length `n` have complexity at least
`n - c`. -/
theorem two_pow_lt_ncard_setOf_length_eq_le_complexity_add (n c : ℕ) :
    2 ^ n < {x : List Bool | x.length = n ∧ (n - c : ℕ) ≤ M.complexity x}.ncard + 2 ^ (n - c) := by
  have hfin : {x : List Bool | x.length = n}.Finite :=
    Set.finite_of_encard_eq_coe (encard_setOf_length_eq n)
  have hcard : {x : List Bool | x.length = n}.ncard = 2 ^ n := by
    rw [← ENat.natCast_inj, hfin.cast_ncard_eq, encard_setOf_length_eq, Nat.cast_pow,
      Nat.cast_ofNat]
  simpa only [hcard, Set.mem_ofPred_eq] using M.ncard_lt_ncard_setOf_le_complexity_add hfin (n - c)

end Strings

end DescriptionMethod

end Cslib.Kolmogorov
