/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Data.BitString.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Positive conjunction masks and the Fast Zeta Transform on bit strings

A bit string `p : BitString n` acts as a positive conjunction mask on `x : BitString n` via
`evalMask p x`, which tests whether `p ≤ x` coordinatewise (`p i = true → x i = true`). On
concatenations `Fin.append x₁ x₂`, a mask factors into its left `n₁` and right `n₂` coordinates
(`evalMask_append`).

The **Boolean-lattice Zeta transform** (`zetaTransform f x`) sums a table `f : BitString m → ℕ`
over all submasks `p` satisfied by `x`. The divide-and-conquer **Fast Zeta Transform** (`fastZeta`,
Yates's algorithm / sum-over-subsets recurrence) recursively computes the Zeta transform on the
two `(m - 1)`-dimensional subcubes `p 0 = false` and `p 0 = true` and combines them with a single
addition when `x 0 = true`, agreeing with `zetaTransform` at every point of `{0, 1} ^ m`
(`fastZeta_eq_zetaTransform`) [Williams, Section 3.2][Williams2014].

## Main definitions

* `Cslib.BitString.evalMask`: whether the positive conjunction with mask `p` is satisfied by `x`.
* `Cslib.BitString.zetaTransform`: the Boolean-lattice Zeta transform (sum over submasks).
* `Cslib.BitString.fastZeta`: divide-and-conquer Fast Zeta Transform (Yates's algorithm).

## Main results

* `Cslib.BitString.evalMask_cons_false`, `Cslib.BitString.evalMask_cons_true`,
  `Cslib.BitString.evalMask_append`: decomposition of `evalMask` along `Fin.cons` and `Fin.append`.
* `Cslib.BitString.fastZeta_eq_zetaTransform`: correctness of the Fast Zeta Transform.

## References

* [R. Williams, *Nonuniform ACC Circuit Lower Bounds*][Williams2014]
-/

@[expose] public section

namespace Cslib.BitString

/-- Whether the positive conjunction with mask `p` is satisfied by `x`: every coordinate where `p`
is `true` is also `true` in `x`. -/
def evalMask {n : ℕ} (p x : BitString n) : Bool :=
  decide (∀ i : Fin n, p i = true → x i = true)

theorem evalMask_eq_true_iff {n : ℕ} {p x : BitString n} :
    evalMask p x = true ↔ ∀ i : Fin n, p i = true → x i = true :=
  decide_eq_true_iff

@[simp] theorem evalMask_false {n : ℕ} (x : BitString n) :
    evalMask (fun _ => false) x = true := by
  simp [evalMask]

@[simp] theorem evalMask_self {n : ℕ} (x : BitString n) :
    evalMask x x = true := by
  simp [evalMask]

/-- On `Fin.cons b q`, a mask `Fin.cons false q` ignores the first bit `x 0` and tests `q` on
`Fin.tail x`. -/
theorem evalMask_cons_false {m : ℕ} (q : BitString m) (x : BitString (m + 1)) :
    evalMask (Fin.cons false q) x = evalMask q (Fin.tail x) := by
  rw [Bool.eq_iff_iff, evalMask_eq_true_iff, evalMask_eq_true_iff, Fin.forall_fin_succ]
  simp [Fin.tail]

/-- On `Fin.cons true q`, a mask `Fin.cons true q` tests both `x 0 = true` and `q` on
`Fin.tail x`. -/
theorem evalMask_cons_true {m : ℕ} (q : BitString m) (x : BitString (m + 1)) :
    evalMask (Fin.cons true q) x = (x 0 && evalMask q (Fin.tail x)) := by
  rw [Bool.eq_iff_iff, Bool.and_eq_true, evalMask_eq_true_iff, evalMask_eq_true_iff,
    Fin.forall_fin_succ]
  simp [Fin.tail]

/-- On `Fin.append x₁ x₂`, a mask `p : BitString (n₁ + n₂)` factors into its left `n₁` coordinates
on `x₁` and its right `n₂` coordinates on `x₂`. -/
theorem evalMask_append {n₁ n₂ : ℕ} (p : BitString (n₁ + n₂))
    (x₁ : BitString n₁) (x₂ : BitString n₂) :
    evalMask p (Fin.append x₁ x₂) =
      (evalMask (fun i => p (Fin.castAdd n₂ i)) x₁ &&
        evalMask (fun i => p (Fin.natAdd n₁ i)) x₂) := by
  rw [Bool.eq_iff_iff, Bool.and_eq_true, evalMask_eq_true_iff, evalMask_eq_true_iff,
    evalMask_eq_true_iff]
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · simpa [Fin.append_left] using h (Fin.castAdd n₂ i) hi
    · simpa [Fin.append_right] using h (Fin.natAdd n₁ i) hi
  · rintro ⟨h₁, h₂⟩ k
    refine Fin.addCases (fun i hi => ?_) (fun i hi => ?_) k
    · simpa [Fin.append_left] using h₁ i hi
    · simpa [Fin.append_right] using h₂ i hi

/-- **The Boolean-lattice Zeta transform** (subset-sum transform): sums `f p` over all submasks
`p ≤ x` (`evalMask p x = true`). -/
def zetaTransform {m : ℕ} (f : BitString m → ℕ) (x : BitString m) : ℕ :=
  ∑ p : BitString m, if evalMask p x then f p else 0

/-- **Divide-and-conquer Fast Zeta Transform** (Yates's algorithm / sum-over-subsets recurrence)
[Williams, Section 3.2][Williams2014]: recursively computes the Zeta transform on the two
`(m - 1)`-dimensional subcubes `p 0 = false` and `p 0 = true` and combines them with a single
addition when `x 0 = true`. -/
def fastZeta : {m : ℕ} → (BitString m → ℕ) → BitString m → ℕ
  | 0, f, x => f x
  | _ + 1, f, x =>
    let z₀ := fastZeta (fun q => f (Fin.cons false q)) (Fin.tail x)
    let z₁ := fastZeta (fun q => f (Fin.cons true q)) (Fin.tail x)
    if x 0 then z₀ + z₁ else z₀

/-- **Correctness of the Fast Zeta Transform**: `fastZeta` computes `zetaTransform` at every point
of the Boolean hypercube. -/
theorem fastZeta_eq_zetaTransform {m : ℕ} (f : BitString m → ℕ) (x : BitString m) :
    fastZeta f x = zetaTransform f x := by
  induction m with
  | zero =>
    simp only [fastZeta, zetaTransform]
    rw [Fintype.sum_eq_single x fun p hp => absurd (Subsingleton.elim p x) hp]
    simp
  | succ m ih =>
    simp only [fastZeta, ih, zetaTransform]
    rw [← (Fin.consEquiv fun _ : Fin (m + 1) => Bool).sum_comp, Fintype.sum_prod_type,
      Fintype.sum_bool]
    simp only [Fin.consEquiv_apply, evalMask_cons_false, evalMask_cons_true]
    cases x 0
    · simp
    · simp [add_comm]

end Cslib.BitString
