/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Hierarchy.Time
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# Exponential time

`Cslib.Complexity.EXP enc` is the union of the deterministic time classes
`Cslib.Complexity.DTIME enc (2 ^ n ^ k)` over `k` [Arora and Barak][AroraBarak09], as in the
classes proposed upstream in cslib pull request #767. There `P` is the union of the classes
`DTIME (n ^ k)`; the class `Cslib.Complexity.P` agrees with it
(`Cslib.Complexity.mem_P_iff_exists_mem_DTIME`), so `P enc ⊆ EXP enc`
(`Cslib.Complexity.P_subset_EXP`).

The inclusion is strict for problems on bit words (`Cslib.Complexity.P_ssubset_EXP`): the diagonal
problem of `Cslib.Complexity.diagonal` is decided within time `O(2 ^ (4 * n))`, which is within
`2 ^ n ^ 2` from `n = 4` on, and is not in `P` by the diagonal argument of the time hierarchy
theorem [Arora and Barak, Theorem 3.1][AroraBarak09], [Sipser, Theorem 9.10][Sipser2013].

## Main definitions

* `Cslib.Complexity.EXP`: deterministic exponential time.

## Main results

* `Cslib.Complexity.mem_P_iff_exists_mem_DTIME`: `P` is the union of the classes of time
  `O(n ^ k)`.
* `Cslib.Complexity.P_subset_EXP`: polynomial time is within exponential time.
* `Cslib.Complexity.P_ssubset_EXP`: polynomial time is strictly within exponential time.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM Filter

variable {α : Type*} {enc : α ↪ List Bool} {A : Set α}

/-- The problems decidable within time `O(2 ^ n ^ k)` for some `k`, on instances whose encoding
under `enc` has length `n`. -/
def EXP (enc : α ↪ List Bool) : Set (Set α) := ⋃ k, DTIME enc fun n => 2 ^ n ^ k

theorem mem_EXP_iff : A ∈ EXP enc ↔ ∃ k, A ∈ DTIME enc fun n => 2 ^ n ^ k :=
  Set.mem_iUnion

/-- **`P` is the union of the classes `DTIME (n ^ k)`**, the definition of `P` in the classes
proposed upstream. -/
theorem mem_P_iff_exists_mem_DTIME : A ∈ P enc ↔ ∃ k, A ∈ DTIME enc (· ^ k) := by
  constructor
  · intro hA
    obtain ⟨t, s, ⟨d, hd⟩, -, h⟩ := mem_P_iff_exists_decidableInTimeAndSpace.mp hA
    refine ⟨d, DTIME_mono_of_eventually_le hd ⟨1, 0, s, ?_⟩⟩
    simpa only [one_mul, add_zero] using h
  · rintro ⟨k, c₁, c₂, s, h⟩
    exact mem_P_of_decidableInTimeAndSpace (t := fun n => c₁ * n ^ k + c₂)
      (.of_forall_le (c₁ + c₂) k fun n => by
        have h₁ : n ^ k ≤ (n + 1) ^ k := Nat.pow_le_pow_left (Nat.le_succ n) k
        have h₂ : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (Nat.succ_pos n)
        nlinarith) h

/-- **Polynomial time is within exponential time.** -/
theorem P_subset_EXP : P enc ⊆ EXP enc := by
  intro A hA
  obtain ⟨k, hk⟩ := mem_P_iff_exists_mem_DTIME.mp hA
  refine mem_EXP_iff.mpr ⟨1, DTIME_mono_of_eventually_le ?_ hk⟩
  filter_upwards [PolynomiallyBounded.eventually_lt_two_pow (f := (· ^ k)) (by fun_prop)]
    with n hn
  simpa only [pow_one] using hn.le

/-- The diagonal problem is in exponential time. -/
theorem setOf_diagonal_mem_EXP : {x | diagonal x = true} ∈ EXP encBits :=
  mem_EXP_iff.mpr ⟨2, DTIME_mono_of_eventually_le
    (t₁ := fun n => 2 ^ (4 * n)) (eventually_atTop.mpr ⟨4, fun n hn =>
      Nat.pow_le_pow_right (by norm_num) (by nlinarith)⟩)
    (setOf_mem_DTIME_of_computableTidilyInO computableTidilyInO_diagonal
      (s := fun n => 2 ^ (2 * n)) (fun _ => le_rfl) fun _ => le_rfl)⟩

/-- **Polynomial time is strictly within exponential time**, for problems on bit words: the
diagonal problem is in `EXP` and not in `P` [Arora and Barak, Theorem 3.1][AroraBarak09]. -/
theorem P_ssubset_EXP : P encBits ⊂ EXP encBits :=
  (Set.ssubset_iff_of_subset P_subset_EXP).mpr
    ⟨_, setOf_diagonal_mem_EXP, diagonal_not_mem_P⟩

end Cslib.Complexity
