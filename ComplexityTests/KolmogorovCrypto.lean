/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Kolmogorov.Uncomputability
import Complexity.Crypto.Computational.PRGToOneWay
import Complexity.Foundations.Data.BitString.ShortWords

/-!
Regression clients for the growth and uncomputability of plain Kolmogorov complexity, the binary
words of bounded length, and one-way functions from pseudorandom generators.
-/

namespace ComplexityTests.KolmogorovCrypto

open Cslib Cslib.Kolmogorov Cslib.Kolmogorov.DescriptionMethod Cslib.Crypto Filter Finset
open scoped NNReal

/-! ### Growth and uncomputability of plain Kolmogorov complexity -/

-- All but finitely many numbers have complexity at least ten.
example : ∀ᶠ x in atTop, 10 ≤ universal.complexity x :=
  tendsto_atTop.1 tendsto_complexity_universal 10

-- `K(2 ^ x) ≤ x + O(1)`: the binary representation of `2 ^ x` has `x + 1` bits.
example : ∃ c, ∀ x, universal.complexity (2 ^ x) ≤ x + c := by
  obtain ⟨c, hc⟩ := exists_complexity_universal_le_size_add
  refine ⟨c + 1, fun x => ?_⟩
  have h := hc (2 ^ x)
  rw [Nat.size_pow] at h
  omega

-- The successor increases complexity by at most a constant.
example : ∃ c, ∀ x, universal.complexity (x + 1) ≤ universal.complexity x + c :=
  exists_complexity_universal_comp_le Computable.succ

-- The integer square root is not a lower bound for `K`, not even eventually.
example : ∃ᶠ x in atTop, universal.complexity x < Nat.sqrt x :=
  frequently_complexity_universal_lt_of_computable Primrec.nat_sqrt.to_comp
    fun k => ⟨k * k, (Nat.sqrt_eq k).ge⟩

example : ¬ Computable universal.complexity := not_computable_complexity_universal

/-! ### Binary words of bounded length -/

example : [true, false] ∈ BitString.shortWords 2 := by simp

example : [true, false, true] ∉ BitString.shortWords 2 := by simp

example : #(BitString.shortWords 3) = 15 := by simp [BitString.card_shortWords]

/-! ### One-way functions from pseudorandom generators -/

-- A generator stretching `n` bits to `2 n + 1` bits is one-way.
example {G : List Bool → List Bool} (hG : PseudorandomGenerator G fun n => 2 * n + 1) :
    OneWay G :=
  hG.oneWay fun n => by omega

/-- The stretch `n ↦ n + (⌊log₂ n⌋ + 1) ^ 2`, below `2 n` for large `n`. -/
private abbrev logSqStretch (n : ℕ) : ℕ := n + (Nat.log 2 n + 1) ^ 2

-- It is a valid stretch: it is strictly increasing and expands every length.
example (n : ℕ) : n < logSqStretch n := Nat.lt_add_of_pos_right (by positivity)

private theorem strictMono_logSqStretch : StrictMono logSqStretch := fun _ _ hab =>
  Nat.add_lt_add_of_lt_of_le hab
    (Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.log_mono_right hab.le) 1) 2)

example : logSqStretch 64 < 2 * 64 := by decide

example {G : List Bool → List Bool} (hG : PseudorandomGenerator G logSqStretch)
    (hgap : Negligible fun n => (1 / 2 : ℝ≥0) ^ (logSqStretch n - n)) : OneWay G :=
  hG.oneWay_of_injective strictMono_logSqStretch.injective hgap

example {G : List Bool → List Bool} {ℓ : ℕ → ℕ} (hG : PseudorandomGenerator G ℓ) :
    ∃ f : List Bool → List Bool, OneWay f :=
  hG.exists_oneWay

example :
    (∃ f : List Bool → List Bool, OneWay f) ↔
      ∃ (G : List Bool → List Bool) (ℓ : ℕ → ℕ), PseudorandomGenerator G ℓ :=
  exists_oneWay_iff_exists_pseudorandomGenerator

/-! ### Axiom guards -/

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.frequently_complexity_universal_lt_of_computable' depends
on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms frequently_complexity_universal_lt_of_computable

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.exists_complexity_universal_le_size_add' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_complexity_universal_le_size_add

/--
info: 'Cslib.BitString.card_shortWords' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BitString.card_shortWords

/--
info: 'Cslib.Crypto.PseudorandomGenerator.oneWay_of_card_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms PseudorandomGenerator.oneWay_of_card_le

/--
info: 'Cslib.Crypto.PseudorandomGenerator.oneWay_of_injective' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms PseudorandomGenerator.oneWay_of_injective

end ComplexityTests.KolmogorovCrypto
