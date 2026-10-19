/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.NaturalProof

/-! Truth-table languages on concrete words, a `P/poly`-natural property, a large property useful
against `P/poly`, circuit tests, the Razborov–Rudich distinguisher on the property of hard
functions at every input length from `16` on, and the axioms of the headline theorems. -/

namespace ComplexityTests.NaturalProofs

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.MCSP Filter
open scoped NNReal

/-! ### Truth-table languages -/

/-- A word of length `2 ^ n` is in the truth-table language of `C` exactly when the function it
tabulates is in `C n`. -/
example (C : ∀ n, Set (BooleanFunction n)) (T : BitString (2 ^ 1)) :
    List.ofFn T ∈ truthTableLanguage C ↔ (truthTable 1).symm T ∈ C 1 :=
  ofFn_mem_truthTableLanguage

/-- A word whose length is not a power of two is in no truth-table language. -/
example (C : ∀ n, Set (BooleanFunction n)) : [true, false, true] ∉ truthTableLanguage C := by
  rintro ⟨m, h, -⟩
  rcases m with _ | _ | m
  · simp at h
  · simp at h
  · have : 4 ≤ 2 ^ (m + 2) := by
      rw [pow_add]
      exact Nat.le_mul_of_pos_left 4 (Nat.two_pow_pos m)
    simp only [List.length_cons, List.length_nil] at h
    omega

/-- The empty property has an empty truth-table language. -/
example (w : List Bool) : w ∉ truthTableLanguage fun n => (∅ : Set (BooleanFunction n)) :=
  fun ⟨_, _, h⟩ => h

/-! ### A `P/poly`-natural property -/

/-- The words of length a power of two form a language in `P/poly`: each slice is constant. -/
theorem truthTableLanguage_univ_mem_PPoly :
    truthTableLanguage (fun n => (Set.univ : Set (BooleanFunction n))) ∈ PPoly := by
  classical
  refine PPoly.of_slice_const (fun N => decide (∃ n, N = 2 ^ n)) fun N x => ?_
  rw [Bool.eq_iff_iff, Language.slice_eq_true_iff, decide_eq_true_iff]
  constructor
  · rintro ⟨n, h, -⟩
    exact ⟨n, by simpa only [List.length_ofFn] using h⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, List.length_ofFn, Set.mem_univ _⟩

/-- The property satisfied by every function is large. -/
theorem isLarge_univ : IsLarge fun n => (Set.univ : Set (BooleanFunction n)) :=
  ⟨0, Eventually.of_forall fun n => by
    simp [Set.ncard_univ, Nat.card_eq_fintype_card]⟩

/-- So the hypotheses of `IsNatural PPoly` can be met. -/
example : IsNatural PPoly fun n => (Set.univ : Set (BooleanFunction n)) :=
  ⟨_, fun _ => le_rfl, isLarge_univ, truthTableLanguage_univ_mem_PPoly⟩

/-! ### A large property useful against `P/poly` -/

/-- The hard functions are large and useful against `P/poly`, so both hypotheses can be met at
once; by `truthTableLanguage_setOf_lt_complexity_notMem_PPoly` the property is not natural for
`P/poly` if an exponentially secure family exists. -/
example : IsLarge (fun n => {f : BooleanFunction n |
      2 ^ n / (5 * n) < complexity interpretation (single f)}) ∧
    IsUseful PPoly fun n => {f : BooleanFunction n |
      2 ^ n / (5 * n) < complexity interpretation (single f)} :=
  ⟨isLarge_setOf_lt_complexity, isUseful_PPoly_setOf_lt_complexity⟩

/-- Every property is useful against the empty class. -/
example (C : ∀ n, Set (BooleanFunction n)) : IsUseful ∅ C := fun _ h => h.elim

/-- A property useful against `P/poly` eventually holds only for functions needing more than
`n ^ 3` gates. -/
example (C : ∀ n, Set (BooleanFunction n)) (hC : IsUseful PPoly C) :
    ∀ᶠ n in atTop, ∀ f ∈ C n, n ^ 3 < complexity interpretation (single f) :=
  isUseful_PPoly_iff.1 hC _ (by fun_prop)

/-! ### Circuit tests -/

/-- A constant test is computed with one gate. -/
example (m : ℕ) (b : Bool) : IsCircuitTest (m := m) 1 fun _ => PMF.pure b :=
  ⟨fun _ => b, (Synthesis.const b).complexity_le, rfl⟩

/-- Circuit tests with more gates include those with fewer. -/
example {m t t' : ℕ} (h : t ≤ t') {A : Crypto.PRG.Adversary (BitString m)}
    (hA : IsCircuitTest t A) : IsCircuitTest t' A :=
  let ⟨test, htest, hA⟩ := hA
  ⟨test, htest.trans h, hA⟩

/-! ### The distinguisher on hard functions -/

section Hard

variable {n : ℕ} {Key : Type} [Fintype Key] [Nonempty Key]

/-- The functions that need more than `2 ^ n / (5 n)` gates. -/
abbrev hard (n : ℕ) : Set (BooleanFunction n) :=
  {f | 2 ^ n / (5 * n) < complexity interpretation (single f)}

/-- The test for hard functions rejects every member of a family of functions with at most
`2 ^ n / (5 n)` gates, so its advantage is the density of the hard functions. -/
example (F : Key → BooleanFunction n)
    (hF : ∀ key, complexity interpretation (single (F key)) ≤ 2 ^ n / (5 * n)) :
    (truthTableGenerator F).advantage (fun T => PMF.pure (truthTableTest (hard n) T)) =
      (hard n).ncard / 2 ^ 2 ^ n :=
  advantage_truthTableGenerator_truthTableTest F fun key hkey => (not_lt.2 (hF key)) hkey

/-- For `n ≥ 16`, no family of functions with at most `2 ^ n / (5 n)` gates is pseudorandom with
error `1 / 4` against circuits as large as the test for hard functions. -/
example (hn : 16 ≤ n) (F : Key → BooleanFunction n)
    (hF : ∀ key, complexity interpretation (single (F key)) ≤ 2 ^ n / (5 * n)) :
    ¬ (truthTableGenerator F).Secure
      (IsCircuitTest (complexity interpretation (single (truthTableTest (hard n))))) (1 / 4) := by
  refine not_secure_truthTableGenerator le_rfl (fun _ hf => hf) hF ?_
  have h := two_pow_two_pow_le_two_mul_ncard_setOf_lt_complexity hn
  have hpos : (0 : ℝ) < 2 ^ 2 ^ n := by positivity
  have h' : (2 : ℝ) ^ 2 ^ n ≤ 2 * (hard n).ncard := by exact_mod_cast h
  have hε : ((1 / 4 : ℝ≥0) : ℝ) = 1 / 4 := by norm_num
  rw [lt_div_iff₀ hpos, hε]
  linarith

end Hard

/-! ### Axioms -/

/--
info: 'Cslib.Circuits.Boolean.advantage_truthTableGenerator_truthTableTest' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.advantage_truthTableGenerator_truthTableTest

/--
info: 'Cslib.Circuits.Boolean.not_secure_truthTableGenerator' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.not_secure_truthTableGenerator

/--
info: 'Cslib.Circuits.Boolean.not_isUseful_PPoly_of_isNatural' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.not_isUseful_PPoly_of_isNatural

/--
info: 'Cslib.Circuits.Boolean.truthTableLanguage_setOf_lt_complexity_notMem_PPoly' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.truthTableLanguage_setOf_lt_complexity_notMem_PPoly

/--
info: 'Cslib.Circuits.Boolean.isUseful_PPoly_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.isUseful_PPoly_iff

/--
info: 'Cslib.Circuits.Boolean.IsNatural.PPoly_of_P' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.IsNatural.PPoly_of_P

/--
info: 'Cslib.Circuits.Boolean.isLarge_setOf_lt_complexity' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.isLarge_setOf_lt_complexity

/--
info: 'Cslib.Circuits.Boolean.isUseful_PPoly_setOf_lt_complexity' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.isUseful_PPoly_setOf_lt_complexity

end ComplexityTests.NaturalProofs
