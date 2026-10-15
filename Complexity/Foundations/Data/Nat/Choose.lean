/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (to Mathlib's `Mathlib/Combinatorics/Choose/Bounds.lean` or cslib)

public import Complexity.Init
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring

/-!
# Scaling bounds for binomial coefficients

Scaling the ground set by `q` scales the number of `d`-subsets by at least `q ^ d`
(`Nat.pow_mul_choose_le_choose_mul`). Consequently a fixed `d`-subset of the ground set lies in at
most a `q ^ (-d)` fraction of the `k`-subsets when the ground set has at least `q k` elements
(`Nat.pow_mul_choose_sub_le_choose`). Lowering `ℓ` by `s` scales the number of `ℓ`-subsets of an
`m`-set by at most `(ℓ / (m - ℓ + 1)) ^ s` (`Nat.choose_sub_mul_pow_le`), so by at most
`q ^ (-s)` when `(q + 1) ℓ ≤ m` (`Nat.pow_mul_choose_sub_le_choose_of_mul_le`).
-/

@[expose] public section

namespace Nat

/-- Scaling the ground set by `q ≥ 1` scales a descending factorial by at least `q ^ d`. -/
theorem pow_mul_descFactorial_le {q : ℕ} (hq : 1 ≤ q) {k d : ℕ} (hd : d ≤ k) :
    q ^ d * k.descFactorial d ≤ (q * k).descFactorial d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hqk : q * (k - d) ≤ q * k - d := by
      rw [Nat.mul_sub_left_distrib]
      exact Nat.sub_le_sub_left (Nat.le_mul_of_pos_left d (by omega)) (q * k)
    rw [Nat.pow_succ, descFactorial_succ, descFactorial_succ]
    calc q ^ d * q * ((k - d) * k.descFactorial d)
        = (q * (k - d)) * (q ^ d * k.descFactorial d) := by ac_rfl
      _ ≤ (q * k - d) * (q * k).descFactorial d := Nat.mul_le_mul hqk (ih (by omega))

/-- Scaling the ground set by `q ≥ 1` scales the number of `d`-subsets by at least `q ^ d`. -/
theorem pow_mul_choose_le_choose_mul {q : ℕ} (hq : 1 ≤ q) {k d : ℕ} (hd : d ≤ k) :
    q ^ d * k.choose d ≤ (q * k).choose d := by
  have h := pow_mul_descFactorial_le hq hd
  rw [descFactorial_eq_factorial_mul_choose, descFactorial_eq_factorial_mul_choose] at h
  refine Nat.le_of_mul_le_mul_left (c := d.factorial) ?_ (factorial_pos d)
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

/-- A `d`-subset of an `n`-set lies in at most a `q ^ (-d)` fraction of its `k`-subsets when
`q k ≤ n`. -/
theorem pow_mul_choose_sub_le_choose {q n k d : ℕ} (hq : 1 ≤ q) (hd : d ≤ k) (hn : q * k ≤ n) :
    q ^ d * (n - d).choose (k - d) ≤ n.choose k := by
  have h : q ^ d * k.choose d * (n - d).choose (k - d) ≤ n.choose d * (n - d).choose (k - d) :=
    Nat.mul_le_mul_right _ ((pow_mul_choose_le_choose_mul hq hd).trans (choose_le_choose d hn))
  rw [← choose_mul (n := n) hd] at h
  refine Nat.le_of_mul_le_mul_left (c := k.choose d) ?_ (choose_pos hd)
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

/-- Lowering `ℓ` by `s` scales the number of `ℓ`-subsets of an `m`-set by at most
`(ℓ / (m - ℓ + 1)) ^ s`. -/
theorem choose_sub_mul_pow_le {m ℓ s : ℕ} (hs : s ≤ ℓ) (hℓ : ℓ ≤ m) :
    m.choose (ℓ - s) * (m - ℓ + 1) ^ s ≤ m.choose ℓ * ℓ ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    -- one step down: `C(m, j) (m - j) = C(m, j + 1) (j + 1)` at `j = ℓ - s - 1`
    have hstep := choose_succ_right_eq m (ℓ - (s + 1))
    rw [show ℓ - (s + 1) + 1 = ℓ - s by omega] at hstep
    have h₁ : m.choose (ℓ - (s + 1)) * (m - ℓ + 1) ≤ m.choose (ℓ - s) * ℓ :=
      calc m.choose (ℓ - (s + 1)) * (m - ℓ + 1)
          ≤ m.choose (ℓ - (s + 1)) * (m - (ℓ - (s + 1))) := Nat.mul_le_mul_left _ (by omega)
        _ = m.choose (ℓ - s) * (ℓ - s) := hstep.symm
        _ ≤ m.choose (ℓ - s) * ℓ := Nat.mul_le_mul_left _ (by omega)
    calc m.choose (ℓ - (s + 1)) * (m - ℓ + 1) ^ (s + 1)
        = m.choose (ℓ - (s + 1)) * (m - ℓ + 1) * (m - ℓ + 1) ^ s := by ring
      _ ≤ m.choose (ℓ - s) * ℓ * (m - ℓ + 1) ^ s := Nat.mul_le_mul_right _ h₁
      _ = m.choose (ℓ - s) * (m - ℓ + 1) ^ s * ℓ := by ring
      _ ≤ m.choose ℓ * ℓ ^ s * ℓ := Nat.mul_le_mul_right _ (ih (by omega))
      _ = m.choose ℓ * ℓ ^ (s + 1) := by ring

/-- If `ℓ` and `q ℓ` together fit into `m`, lowering `ℓ` by `s ≤ ℓ` divides the number of
`ℓ`-subsets of an `m`-set by at least `q ^ s`. -/
theorem pow_mul_choose_sub_le_choose_of_mul_le {m ℓ s q : ℕ} (hs : s ≤ ℓ)
    (hℓ : (q + 1) * ℓ ≤ m) : q ^ s * m.choose (ℓ - s) ≤ m.choose ℓ := by
  have hℓm : ℓ ≤ m := le_trans (Nat.le_mul_of_pos_left ℓ (by omega)) hℓ
  have hqℓ : q * ℓ ≤ m - ℓ + 1 := by
    have : (q + 1) * ℓ = q * ℓ + ℓ := by ring
    omega
  refine Nat.le_of_mul_le_mul_right (?_ : _ * (m - ℓ + 1) ^ s ≤ _ * (m - ℓ + 1) ^ s)
    (Nat.pow_pos (by omega))
  calc q ^ s * m.choose (ℓ - s) * (m - ℓ + 1) ^ s
      = q ^ s * (m.choose (ℓ - s) * (m - ℓ + 1) ^ s) := by ring
    _ ≤ q ^ s * (m.choose ℓ * ℓ ^ s) := Nat.mul_le_mul_left _ (choose_sub_mul_pow_le hs hℓm)
    _ = m.choose ℓ * (q * ℓ) ^ s := by rw [Nat.mul_pow]; ring
    _ ≤ m.choose ℓ * (m - ℓ + 1) ^ s := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hqℓ s)

end Nat
