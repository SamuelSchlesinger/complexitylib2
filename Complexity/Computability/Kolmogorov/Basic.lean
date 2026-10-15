/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.ENat.Lattice

/-!
# Kolmogorov complexity relative to a description method

A *description method* runs binary programs against a clock: `M.run p t` is the output of the
program `p` after `t` steps, or `none` if `p` has not halted by then. Once a program has halted,
its output stays fixed, so every program describes at most one object. The *plain Kolmogorov
complexity* `M.complexity x` of an object `x` is the length of a shortest program that eventually
outputs `x`, and its *time-bounded Kolmogorov complexity* `M.timeBoundedComplexity t x` is the
length of a shortest program that outputs `x` within `t` steps
[Li and Vitányi, Chapters 2 and 7][LiVitanyi2019]. Both take values in `ℕ∞`, and are `⊤` when no
program describes `x`.

Nothing here depends on a machine model. A multi-tape Turing machine gives a description method
(`Cslib.Kolmogorov.DescriptionMethod.ofMultiTapeTM`), and so does any other model with a clocked
semantics. The usual machine-independent complexity is the complexity of a method that simulates
every other one with constant program overhead (`Cslib.Kolmogorov.DescriptionMethod.Simulation`).

## Main definitions

* `Cslib.Kolmogorov.DescriptionMethod`: binary programs run against a clock.
* `Cslib.Kolmogorov.DescriptionMethod.Produces`: a program eventually outputs an object.
* `Cslib.Kolmogorov.DescriptionMethod.complexity`: the plain complexity `C_M(x)`.
* `Cslib.Kolmogorov.DescriptionMethod.timeBoundedComplexity`: the time-bounded complexity
  `C_M^t(x)`.
* `Cslib.Kolmogorov.DescriptionMethod.literal`: the method in which every program prints itself.

## Main results

* `Cslib.Kolmogorov.DescriptionMethod.Produces.unique`: a program describes at most one object.
* `Cslib.Kolmogorov.DescriptionMethod.complexity_le_natCast_iff`,
  `Cslib.Kolmogorov.DescriptionMethod.timeBoundedComplexity_le_natCast_iff`: the complexity is at
  most `k` exactly when some program of length at most `k` describes the object (within the time
  bound); the strict versions are `complexity_lt_natCast_iff` and
  `timeBoundedComplexity_lt_natCast_iff`.
* `Cslib.Kolmogorov.DescriptionMethod.exists_length_eq_complexity`: a finite complexity is the
  length of a describing program.
* `Cslib.Kolmogorov.DescriptionMethod.timeBoundedComplexity_antitone`: more time cannot increase
  the time-bounded complexity.
* `Cslib.Kolmogorov.DescriptionMethod.iInf_timeBoundedComplexity`,
  `Cslib.Kolmogorov.DescriptionMethod.exists_timeBoundedComplexity_eq_complexity`: the plain
  complexity is the time-bounded complexity for a large enough time bound.

## References

* [M. Li, P. Vitányi, *An Introduction to Kolmogorov Complexity and Its
  Applications*][LiVitanyi2019]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Cslib.Kolmogorov

/-- A *description method* for objects of type `α`: `run p t` is the output of the binary program
`p` after `t` steps of computation, or `none` if `p` has not halted by then. A program that has
halted keeps its output. This is the clocked analogue of a partial function from programs to
objects [Li and Vitányi, Chapter 2][LiVitanyi2019], in the style of
`Nat.Partrec.Code.evaln`. -/
structure DescriptionMethod (α : Type*) where
  /-- The output of the program `p` after `t` steps, if `p` has halted by then. -/
  run : List Bool → ℕ → Option α
  /-- A program that has halted with an output keeps that output. -/
  run_mono {p : List Bool} {t₁ t₂ : ℕ} {x : α} : t₁ ≤ t₂ → x ∈ run p t₁ → x ∈ run p t₂

namespace DescriptionMethod

variable {α : Type*} (M : DescriptionMethod α)

/-- The program `p` eventually outputs `x`. -/
def Produces (p : List Bool) (x : α) : Prop :=
  ∃ t, x ∈ M.run p t

/-- The *plain Kolmogorov complexity* `C_M(x)` of `x`: the length of a shortest program that
outputs `x`, or `⊤` if there is none [Sipser, Section 6.4][Sipser2013]. -/
noncomputable def complexity (x : α) : ℕ∞ :=
  ⨅ (p : List Bool) (_ : M.Produces p x), (p.length : ℕ∞)

/-- The *time-bounded Kolmogorov complexity* `C_M^t(x)` of `x`: the length of a shortest program
that outputs `x` within `t` steps, or `⊤` if there is none
[Li and Vitányi, Chapter 7][LiVitanyi2019].
-/
noncomputable def timeBoundedComplexity (t : ℕ) (x : α) : ℕ∞ :=
  ⨅ (p : List Bool) (_ : x ∈ M.run p t), (p.length : ℕ∞)

variable {M} {p : List Bool} {t : ℕ} {x y : α}

/-! ### Programs and their outputs -/

theorem Produces.of_mem_run (h : x ∈ M.run p t) : M.Produces p x :=
  ⟨t, h⟩

/-- Two outputs of the same program, at any two times, are equal. -/
theorem eq_of_mem_run {t₁ t₂ : ℕ} (hx : x ∈ M.run p t₁) (hy : y ∈ M.run p t₂) : x = y := by
  have hx' := M.run_mono (le_max_left t₁ t₂) hx
  have hy' := M.run_mono (le_max_right t₁ t₂) hy
  rw [Option.mem_def] at hx' hy'
  exact Option.some_injective _ (hx'.symm.trans hy')

/-- A program describes at most one object. -/
theorem Produces.unique (hx : M.Produces p x) (hy : M.Produces p y) : x = y :=
  let ⟨_, hx⟩ := hx
  let ⟨_, hy⟩ := hy
  eq_of_mem_run hx hy

/-! ### Plain complexity -/

theorem complexity_le_length (h : M.Produces p x) : M.complexity x ≤ p.length :=
  iInf₂_le p h

/-- The complexity is below `r` exactly when a program shorter than `r` describes the object. -/
theorem complexity_lt_iff {r : ℕ∞} :
    M.complexity x < r ↔ ∃ p : List Bool, (p.length : ℕ∞) < r ∧ M.Produces p x := by
  simp only [complexity, iInf_lt_iff, exists_prop]
  exact exists_congr fun _ => and_comm

/-- The complexity is below `k` exactly when a program of length below `k` describes the
object. -/
theorem complexity_lt_natCast_iff {k : ℕ} :
    M.complexity x < k ↔ ∃ p : List Bool, p.length < k ∧ M.Produces p x := by
  simp [complexity_lt_iff, ENat.natCast_lt_natCast]

/-- **Threshold characterization.** The complexity is at most `k` exactly when a program of
length at most `k` describes the object. -/
theorem complexity_le_natCast_iff {k : ℕ} :
    M.complexity x ≤ k ↔ ∃ p : List Bool, p.length ≤ k ∧ M.Produces p x := by
  rw [← ENat.lt_add_one_iff (ENat.natCast_ne_top k), ← Nat.cast_succ,
    complexity_lt_natCast_iff]
  simp

theorem complexity_eq_top_iff : M.complexity x = ⊤ ↔ ∀ p, ¬M.Produces p x := by
  simp [complexity]

theorem complexity_ne_top_iff : M.complexity x ≠ ⊤ ↔ ∃ p, M.Produces p x := by
  simp [complexity_eq_top_iff]

/-- A finite complexity is the length of a describing program. -/
theorem exists_length_eq_complexity (h : M.complexity x ≠ ⊤) :
    ∃ p, M.Produces p x ∧ (p.length : ℕ∞) = M.complexity x := by
  obtain ⟨p, hp, hpx⟩ := complexity_le_natCast_iff.mp (ENat.natCast_toNat h).ge
  refine ⟨p, hpx, le_antisymm ?_ (complexity_le_length hpx)⟩
  exact (ENat.natCast_le_natCast.mpr hp).trans_eq (ENat.natCast_toNat h)

/-! ### Time-bounded complexity -/

theorem timeBoundedComplexity_le_length (h : x ∈ M.run p t) :
    M.timeBoundedComplexity t x ≤ p.length :=
  iInf₂_le p h

theorem timeBoundedComplexity_lt_iff {r : ℕ∞} :
    M.timeBoundedComplexity t x < r ↔ ∃ p : List Bool, (p.length : ℕ∞) < r ∧ x ∈ M.run p t := by
  simp only [timeBoundedComplexity, iInf_lt_iff, exists_prop]
  exact exists_congr fun _ => and_comm

theorem timeBoundedComplexity_lt_natCast_iff {k : ℕ} :
    M.timeBoundedComplexity t x < k ↔ ∃ p : List Bool, p.length < k ∧ x ∈ M.run p t := by
  simp [timeBoundedComplexity_lt_iff, ENat.natCast_lt_natCast]

/-- **Threshold characterization.** The time-bounded complexity `C_M^t(x)` is at most `k` exactly
when a program of length at most `k` outputs `x` within `t` steps. -/
theorem timeBoundedComplexity_le_natCast_iff {k : ℕ} :
    M.timeBoundedComplexity t x ≤ k ↔ ∃ p : List Bool, p.length ≤ k ∧ x ∈ M.run p t := by
  rw [← ENat.lt_add_one_iff (ENat.natCast_ne_top k), ← Nat.cast_succ,
    timeBoundedComplexity_lt_natCast_iff]
  simp

theorem timeBoundedComplexity_eq_top_iff :
    M.timeBoundedComplexity t x = ⊤ ↔ ∀ p, x ∉ M.run p t := by
  simp [timeBoundedComplexity]

/-- A finite time-bounded complexity is the length of a program outputting the object in time. -/
theorem exists_length_eq_timeBoundedComplexity (h : M.timeBoundedComplexity t x ≠ ⊤) :
    ∃ p, x ∈ M.run p t ∧ (p.length : ℕ∞) = M.timeBoundedComplexity t x := by
  obtain ⟨p, hp, hpx⟩ := timeBoundedComplexity_le_natCast_iff.mp (ENat.natCast_toNat h).ge
  refine ⟨p, hpx, le_antisymm ?_ (timeBoundedComplexity_le_length hpx)⟩
  exact (ENat.natCast_le_natCast.mpr hp).trans_eq (ENat.natCast_toNat h)

/-- **Monotonicity in the time bound.** More time cannot increase the time-bounded complexity. -/
theorem timeBoundedComplexity_antitone (M : DescriptionMethod α) (x : α) :
    Antitone (M.timeBoundedComplexity · x) := fun _ _ h =>
  le_iInf₂ fun _ hp => timeBoundedComplexity_le_length (M.run_mono h hp)

theorem timeBoundedComplexity_mono {t₁ t₂ : ℕ} (h : t₁ ≤ t₂) :
    M.timeBoundedComplexity t₂ x ≤ M.timeBoundedComplexity t₁ x :=
  M.timeBoundedComplexity_antitone x h

/-- Dropping the time bound cannot increase the complexity. -/
theorem complexity_le_timeBoundedComplexity (M : DescriptionMethod α) (t : ℕ) (x : α) :
    M.complexity x ≤ M.timeBoundedComplexity t x :=
  le_iInf₂ fun _ hp => complexity_le_length (.of_mem_run hp)

/-- A large enough time bound attains the plain complexity. -/
theorem exists_timeBoundedComplexity_eq_complexity (M : DescriptionMethod α) (x : α) :
    ∃ t, M.timeBoundedComplexity t x = M.complexity x := by
  by_cases h : M.complexity x = ⊤
  · exact ⟨0, h ▸ top_le_iff.mp (h ▸ M.complexity_le_timeBoundedComplexity 0 x)⟩
  obtain ⟨p, ⟨t, ht⟩, hp⟩ := exists_length_eq_complexity h
  exact ⟨t, le_antisymm (hp ▸ timeBoundedComplexity_le_length ht)
    (M.complexity_le_timeBoundedComplexity t x)⟩

/-- The plain complexity is the limit of the time-bounded complexities. -/
theorem iInf_timeBoundedComplexity (M : DescriptionMethod α) (x : α) :
    ⨅ t, M.timeBoundedComplexity t x = M.complexity x := by
  obtain ⟨t, ht⟩ := M.exists_timeBoundedComplexity_eq_complexity x
  exact le_antisymm (ht ▸ iInf_le _ t) (le_iInf (M.complexity_le_timeBoundedComplexity · x))

/-! ### The literal description method -/

/-- The description method for binary strings in which every program prints itself, taking one
step per bit. -/
def literal : DescriptionMethod (List Bool) where
  run p t := if p.length ≤ t then some p else none
  run_mono {p t₁ t₂ x} h hx := by
    simp only [Option.mem_def, Option.ite_none_right_eq_some, Option.some.injEq] at hx ⊢
    exact ⟨hx.1.trans h, hx.2⟩

theorem mem_literal_run {p x : List Bool} : x ∈ literal.run p t ↔ p.length ≤ t ∧ p = x := by
  simp [literal]

theorem literal_produces {p x : List Bool} : literal.Produces p x ↔ p = x := by
  simp only [Produces, mem_literal_run]
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨p.length, le_rfl, h⟩⟩

/-- Every string is its own shortest literal description. -/
@[simp]
theorem complexity_literal (x : List Bool) : literal.complexity x = x.length :=
  le_antisymm (complexity_le_length (literal_produces.mpr rfl))
    (le_iInf₂ fun _ hp => (literal_produces.mp hp) ▸ le_rfl)

theorem timeBoundedComplexity_literal {x : List Bool} (h : x.length ≤ t) :
    literal.timeBoundedComplexity t x = x.length :=
  le_antisymm (timeBoundedComplexity_le_length (mem_literal_run.mpr ⟨h, rfl⟩))
    ((complexity_literal x).symm.trans_le (literal.complexity_le_timeBoundedComplexity t x))

theorem timeBoundedComplexity_literal_eq_top {x : List Bool} (h : t < x.length) :
    literal.timeBoundedComplexity t x = ⊤ :=
  timeBoundedComplexity_eq_top_iff.mpr fun _ hp =>
    absurd ((mem_literal_run.mp hp).2 ▸ (mem_literal_run.mp hp).1) h.not_ge

end DescriptionMethod

end Cslib.Kolmogorov
