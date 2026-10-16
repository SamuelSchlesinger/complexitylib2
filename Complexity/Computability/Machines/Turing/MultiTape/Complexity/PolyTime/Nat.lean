/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Nat.Pairing

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Lists
import Mathlib.Data.Nat.Size

/-!
# Polynomial-time arithmetic on unary counters

Arithmetic on `encUnary`, built from Christian Reitwiessner's encodings and machine calculus.
Addition concatenates the unary words; multiplication folds addition while keeping a quadratic
bound on the accumulator. Fixed powers and fixed polynomials follow by composition. These
operations support polynomially bounded counters and list enumeration in reductions.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_add`, `.unary_sub`, `.unary_mul`:
  arithmetic on unary naturals.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_le`, `.unary_lt`, `.unary_pair`:
  comparisons and the natural-number pairing function.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_pow`, `.unary_eval`:
  evaluation of a fixed power or polynomial, with input and output in unary.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_to_binary`:
  conversion from unary to the binary encoding `encNat`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- Addition of unary naturals, by concatenating their encodings. -/
@[fun_prop]
theorem unary_add : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1 + p.2)
    (encPair encUnary encUnary) encUnary :=
  (fst encUnary encUnary).append (snd encUnary encUnary)
    (fun _ => by simp only [encUnary_apply, List.replicate_add])

/-- Truncated subtraction of unary naturals. -/
@[fun_prop]
theorem unary_sub : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1 - p.2)
    (encPair encUnary encUnary) encUnary :=
  ComputableTidilyInDegree.unary_sub.computableTidilyInPolyTime

/-- Multiplication of unary naturals, by repeated addition. -/
@[fun_prop]
theorem unary_mul : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1 * p.2)
    (encPair encUnary encUnary) encUnary := by
  have hq := fst (encPair encUnary encUnary) encBool
  have h := foldlWith (encA := encBool) (encL := encBits) (encB := encUnary)
    (par := fun p : ℕ × ℕ => p.1) (list := fun p => List.replicate p.2 true)
    (step := fun a n _ => n + a) (fst encUnary encUnary)
    ((of_eq (encIn := encUnary) (encMid := encBits) fun _ => rfl).comp (snd encUnary encUnary))
    (const 0) (unary_add.comp (hq.snd'.prod hq.fst'))
    (B := fun p => (encPair encUnary encUnary p).length * (encPair encUnary encUnary p).length)
    (PolyBounded.self.mul .self) (fun p i _ => by
      have ha : p.1 ≤ (encPair encUnary encUnary p).length := by
        simp only [length_encPair, encUnary_apply, List.length_replicate]
        lia
      have hb : min i p.2 ≤ (encPair encUnary encUnary p).length := by
        simp only [length_encPair, encUnary_apply, List.length_replicate]
        lia
      simpa [List.foldl_const] using Nat.mul_le_mul hb ha)
  simpa [List.foldl_const, Nat.mul_comm] using h

/-- Compare unary naturals. -/
@[fun_prop]
theorem unary_le : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => decide (p.1 ≤ p.2))
    (encPair encUnary encUnary) encBool := by
  simpa only [Function.comp_def, Nat.sub_eq_zero_iff_le] using
    ComputableTidilyInDegree.unary_isZero.computableTidilyInPolyTime.comp unary_sub

/-- Strict comparison of unary naturals. -/
@[fun_prop]
theorem unary_lt : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => decide (p.1 < p.2))
    (encPair encUnary encUnary) encBool := by
  simpa only [Function.comp_def, ← decide_not, Nat.not_le] using bool_not.comp
    (unary_le.comp ((snd encUnary encUnary).prod (fst encUnary encUnary)))

/-- The natural-number pairing function, with both arguments and the result in unary. -/
@[fun_prop]
theorem unary_pair : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => Nat.pair p.1 p.2)
    (encPair encUnary encUnary) encUnary := by
  have hleft : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.2 * p.2 + p.1)
      (encPair encUnary encUnary) encUnary := by fun_prop
  have hright : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1 * p.1 + p.1 + p.2)
      (encPair encUnary encUnary) encUnary := by fun_prop
  simpa [Nat.pair] using unary_lt.ite' hleft hright

/-- A fixed power of a unary natural. -/
@[fun_prop]
theorem unary_pow (d : ℕ) : ComputableTidilyInPolyTime (fun n : ℕ => n ^ d)
    encUnary encUnary := by
  induction d with
  | zero => simpa using (const (encIn := encUnary) (encMid := encUnary) 1)
  | succ d ih => simpa only [pow_succ, Function.comp_def] using unary_mul.comp (ih.prod id')

/-- Evaluate a fixed polynomial on unary naturals, with its result also in unary. -/
@[fun_prop]
theorem unary_eval (p : Polynomial ℕ) : ComputableTidilyInPolyTime p.eval encUnary encUnary := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [Polynomial.eval_add, Function.comp_def] using unary_add.comp (hp.prod hq)
  | monomial d c =>
    simpa only [Polynomial.eval_monomial, Function.comp_def] using
      unary_mul.comp ((const c).prod (unary_pow d))

/-- Convert a unary natural to its binary encoding by incrementing a binary counter. -/
@[fun_prop]
theorem unary_to_binary : ComputableTidilyInPolyTime (fun n : ℕ => n) encUnary encNat := by
  have hsize (n : ℕ) : (encNat n).length ≤ n := by
    rw [encNat_apply, Nat.size_eq_bits_len]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  have h := foldl' (encA := encBool) (encL := encBits) (list := fun n => List.replicate n true)
    (step := fun n _ => n + 1)
    (of_eq (encIn := encUnary) (encMid := encBits) fun _ => rfl) (const 0)
    (computableTidilyInPolyTime_succ.comp (fst encNat encBool))
    (B := fun n => (encUnary n).length) .self (fun n i _ => by
      simpa [List.foldl_const] using (hsize (min i n)).trans (Nat.min_le_right i n))
  simpa [List.foldl_const] using h

end Turing.MultiTapeTM.ComputableTidilyInPolyTime
