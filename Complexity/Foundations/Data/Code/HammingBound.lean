/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Code.Basic
public import Complexity.Foundations.Data.HammingBound

/-!
# The Hamming and Gilbert–Varshamov bounds for the minimum distance

The Hamming bound and the Gilbert–Varshamov bound of `Complexity.Foundations.Data.HammingBound`,
stated there for codes whose distinct words are pairwise far apart, restated in terms of the
minimum distance `Cslib.Code.minDist`. Over an alphabet of `q` letters at each of `n` positions, a
code of minimum distance more than `2 r` has at most `q ^ n / V` words, where `V` is the size of a
ball of radius `r` (`Cslib.Code.card_mul_sum_choose_le_of_two_mul_lt_minDist`) [Hamming1950]; and
for `d ≥ 1` some code of minimum distance at least `d` has at least `q ^ n / V` words, where `V` is
the size of a ball of radius `d - 1`
(`Cslib.Code.exists_le_minDist_and_pow_le_card_mul_sum_choose`) [Gilbert1952].

## Main results

* `Cslib.Code.card_mul_sum_choose_le_of_two_mul_lt_minDist`: the Hamming bound.
* `Cslib.Code.exists_le_minDist_and_pow_le_card_mul_sum_choose`: the Gilbert–Varshamov bound.

## References

* [R. W. Hamming, *Error detecting and error correcting codes*][Hamming1950]
* [E. N. Gilbert, *A comparison of signalling alphabets*][Gilbert1952]
-/

@[expose] public section

namespace Cslib.Code

open Finset

variable {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]
  {q : ℕ}

/-- **The Hamming bound** [Hamming1950] over a `q`-letter alphabet at each of `n` positions: a code
of minimum distance more than `2 r` has at most `q ^ n / V` words, where
`V = ∑_{j ≤ r} C(n, j) (q - 1) ^ j` is the size of a ball of radius `r`. -/
theorem card_mul_sum_choose_le_of_two_mul_lt_minDist (hq : ∀ i, Fintype.card (β i) = q)
    {C : Finset (∀ i, β i)} {r : ℕ} (hC : 2 * (r : ℕ∞) < minDist (C : Set (∀ i, β i))) :
    #C * ∑ j ∈ range (r + 1), (Fintype.card ι).choose j * (q - 1) ^ j ≤ q ^ Fintype.card ι :=
  card_mul_sum_choose_le_of_two_mul_lt_hammingDist hq fun x hx y hy hxy =>
    natCast_lt_minDist_iff.1 (by exact_mod_cast hC) x hx y hy hxy

/-- **The Gilbert–Varshamov bound** [Gilbert1952] over a `q`-letter alphabet at each of `n`
positions: for `d ≥ 1` some code of minimum distance at least `d` has at least `q ^ n / V` words,
where `V = ∑_{j < d} C(n, j) (q - 1) ^ j` is the size of a ball of radius `d - 1`. -/
theorem exists_le_minDist_and_pow_le_card_mul_sum_choose (hq : ∀ i, Fintype.card (β i) = q)
    {d : ℕ} (hd : 0 < d) :
    ∃ C : Finset (∀ i, β i), (d : ℕ∞) ≤ minDist (C : Set (∀ i, β i)) ∧
      q ^ Fintype.card ι ≤ #C * ∑ j ∈ range d, (Fintype.card ι).choose j * (q - 1) ^ j := by
  obtain ⟨C, hCd, hC⟩ := exists_pow_le_card_mul_sum_choose_of_le_hammingDist hq hd
  exact ⟨C, le_minDist_iff.2 fun x hx y hy hxy => Nat.cast_le.2 (hCd hx hy hxy), hC⟩

end Cslib.Code
