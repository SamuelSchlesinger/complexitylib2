/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Rational
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log

/-!
# Rational hitting lists: polynomial-time parameters

The parameters of the hitting-list generator are computed in polynomial time from the number of
variables `n` and the node-count bound `s`, both in unary. Every parameter is polynomial in
`n + s + 1` (`Cslib.Circuits.Rational.Parameters.polynomial_M`,
`Cslib.Circuits.Rational.Parameters.polynomial_H`), so its unary encoding has polynomial length;
the later stages use these parameters as loop counts, dimensions and moduli. The rank bound, the
dimension allowance and the threshold `rankBound s * delta n s` are fixed polynomials. The
exponent is a binary logarithm of the threshold. The ambient dimension `2 ^ (exponent + 1)` is the
power of two at the ceiling logarithm of the threshold plus one (`ambientDimension_eq`), and the
cyclotomic degree is half of it. The truncation, the grid size and the matrix dimension follow by
unary arithmetic.

Each certificate is stated compositionally, for parameters computed in unary from an arbitrary
input, and registered with `fun_prop`.

## Main definitions

* `Cslib.Circuits.Rational.Runtime.threshold`: the rank expansion threshold
  `rankBound s * delta n s`.
* `Cslib.Circuits.Rational.Runtime.parameters`: the parameters
  `(truncation, exponent, ambientDimension, degree, gridSize, matrixDimension)` of the generator.

## Main results

* `Cslib.Circuits.Rational.Runtime.ambientDimension_eq`,
  `Cslib.Circuits.Rational.Runtime.degree_eq`: the ambient dimension and the cyclotomic degree in
  certifiable form.
* `Cslib.Circuits.Rational.Runtime.exponent_polytime`,
  `Cslib.Circuits.Rational.Runtime.ambientDimension_polytime`,
  `Cslib.Circuits.Rational.Runtime.truncation_polytime`,
  `Cslib.Circuits.Rational.Runtime.gridSize_polytime`,
  `Cslib.Circuits.Rational.Runtime.matrixDimension_polytime` and their companions: unary
  certificates for every parameter.
* `Cslib.Circuits.Rational.Runtime.parameters_polytime`: all parameters at once, from unary
  `(n, s)`.
* `Cslib.Circuits.Rational.Runtime.hittingList_dimension_polytime`,
  `Cslib.Circuits.Rational.Runtime.hittingList_dimension_polytime_binary`: the common dimension of
  the hitting list, in unary and in binary.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits.Rational.Runtime

open Turing MultiTapeTM MultiTapeTM.ComputableTidilyInPolyTime

/-- The rank expansion threshold: the ambient dimension is the least power of two above it. -/
def threshold (n s : ℕ) : ℕ := Parameters.rankBound s * Parameters.delta n s

private theorem clog_two_succ {t : ℕ} (ht : 0 < t) : Nat.clog 2 (t + 1) = Nat.log 2 t + 1 := by
  apply le_antisymm
  · rw [Nat.clog_le_iff_le_pow (by norm_num)]
    exact Nat.lt_pow_succ_log_self (by norm_num) t
  · apply Nat.succ_le_of_lt
    rw [Nat.lt_clog_iff_pow_lt (by norm_num)]
    exact Nat.lt_succ_of_le (Nat.pow_log_le_self 2 ht.ne')

/-- The ambient dimension is two to the ceiling logarithm of the threshold plus one. -/
theorem ambientDimension_eq (n s : ℕ) :
    Parameters.ambientDimension n s = 2 ^ Nat.clog 2 (threshold n s + 1) := by
  rw [Parameters.ambientDimension, Parameters.exponent, threshold,
    clog_two_succ (Parameters.threshold_pos n s)]

/-- The cyclotomic degree is half of the ambient dimension. -/
theorem degree_eq (n s : ℕ) :
    CyclotomicRing.degree (Parameters.exponent n s) = Parameters.ambientDimension n s / 2 := by
  rw [CyclotomicRing.degree, Parameters.ambientDimension, pow_succ, Nat.mul_div_cancel _ two_pos]

/-- The common dimension of the hitting list is the generator's matrix dimension. -/
theorem hittingList_dimension (n s : ℕ) :
    (hittingList n s).dimension = Generator.matrixDimension (Parameters.exponent n s) := rfl

/-- The parameters `(N, e, M, Dg, H, d)` of the hitting-list generator: the truncation, the
exponent, the ambient dimension, the cyclotomic degree, the grid size and the matrix dimension. -/
def parameters (n s : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  (Parameters.truncation n s, Parameters.exponent n s, Parameters.ambientDimension n s,
    CyclotomicRing.degree (Parameters.exponent n s), Parameters.gridSize n s,
    Generator.matrixDimension (Parameters.exponent n s))

variable {α : Type} {input : α ↪ List Bool} {n s : α → ℕ}

/-- The number of matrices in a lifted tuple, in unary. -/
@[fun_prop]
theorem w_polytime (hn : ComputableTidilyInPolyTime n input encUnary) :
    ComputableTidilyInPolyTime (fun a => Parameters.w (n a)) input encUnary := by
  unfold Parameters.w
  fun_prop

/-- The rank bound, in unary. -/
@[fun_prop]
theorem rankBound_polytime (hs : ComputableTidilyInPolyTime s input encUnary) :
    ComputableTidilyInPolyTime (fun a => Parameters.rankBound (s a)) input encUnary := by
  unfold Parameters.rankBound
  fun_prop

/-- The dimension allowance, in unary. -/
@[fun_prop]
theorem delta_polytime (hn : ComputableTidilyInPolyTime n input encUnary)
    (hs : ComputableTidilyInPolyTime s input encUnary) :
    ComputableTidilyInPolyTime (fun a => Parameters.delta (n a) (s a)) input encUnary := by
  unfold Parameters.delta
  fun_prop

/-- The rank expansion threshold, in unary. -/
@[fun_prop]
theorem threshold_polytime (hn : ComputableTidilyInPolyTime n input encUnary)
    (hs : ComputableTidilyInPolyTime s input encUnary) :
    ComputableTidilyInPolyTime (fun a => threshold (n a) (s a)) input encUnary := by
  unfold threshold
  fun_prop

/-- The exponent, the binary logarithm of the threshold, in unary. -/
@[fun_prop]
theorem exponent_polytime (hn : ComputableTidilyInPolyTime n input encUnary)
    (hs : ComputableTidilyInPolyTime s input encUnary) :
    ComputableTidilyInPolyTime (fun a => Parameters.exponent (n a) (s a)) input encUnary := by
  change ComputableTidilyInPolyTime (fun a => Nat.log 2 (threshold (n a) (s a))) input encUnary
  fun_prop

/-- The ambient dimension, in unary, by repeated doubling up to the ceiling logarithm. -/
@[fun_prop]
theorem ambientDimension_polytime (hn : ComputableTidilyInPolyTime n input encUnary)
    (hs : ComputableTidilyInPolyTime s input encUnary) :
    ComputableTidilyInPolyTime (fun a => Parameters.ambientDimension (n a) (s a))
      input encUnary := by
  simp only [ambientDimension_eq]
  exact unary_pow_clog_const (by fun_prop) 2 2

/-- The cyclotomic degree, in unary. -/
@[fun_prop]
theorem degree_polytime (hn : ComputableTidilyInPolyTime n input encUnary)
    (hs : ComputableTidilyInPolyTime s input encUnary) :
    ComputableTidilyInPolyTime (fun a => CyclotomicRing.degree (Parameters.exponent (n a) (s a)))
      input encUnary := by
  simp only [degree_eq]
  fun_prop

/-- The number of retained columns, in unary. -/
@[fun_prop]
theorem truncation_polytime (hn : ComputableTidilyInPolyTime n input encUnary)
    (hs : ComputableTidilyInPolyTime s input encUnary) :
    ComputableTidilyInPolyTime (fun a => Parameters.truncation (n a) (s a)) input encUnary := by
  unfold Parameters.truncation
  fun_prop

/-- The grid side length, in unary. -/
@[fun_prop]
theorem gridSize_polytime (hn : ComputableTidilyInPolyTime n input encUnary)
    (hs : ComputableTidilyInPolyTime s input encUnary) :
    ComputableTidilyInPolyTime (fun a => Parameters.gridSize (n a) (s a)) input encUnary := by
  unfold Parameters.gridSize
  fun_prop

/-- The matrix dimension of the generator, in unary. -/
@[fun_prop]
theorem matrixDimension_polytime (hn : ComputableTidilyInPolyTime n input encUnary)
    (hs : ComputableTidilyInPolyTime s input encUnary) :
    ComputableTidilyInPolyTime
      (fun a => Generator.matrixDimension (Parameters.exponent (n a) (s a))) input encUnary := by
  change ComputableTidilyInPolyTime (fun a => Parameters.ambientDimension (n a) (s a) *
    CyclotomicRing.degree (Parameters.exponent (n a) (s a))) input encUnary
  fun_prop

/-- All generator parameters, in unary, from `n` and `s` in unary. -/
theorem parameters_polytime :
    ComputableTidilyInPolyTime (fun p : ℕ × ℕ => parameters p.1 p.2) (encPair encUnary encUnary)
      (encPair encUnary (encPair encUnary (encPair encUnary (encPair encUnary
        (encPair encUnary encUnary))))) := by
  have hn := fst encUnary encUnary
  have hs := snd encUnary encUnary
  unfold parameters
  fun_prop

/-- The common dimension of the hitting list, in unary, from `n` and `s` in unary. -/
theorem hittingList_dimension_polytime :
    ComputableTidilyInPolyTime (fun p : ℕ × ℕ => (hittingList p.1 p.2).dimension)
      (encPair encUnary encUnary) encUnary :=
  matrixDimension_polytime (fst encUnary encUnary) (snd encUnary encUnary)

/-- The common dimension of the hitting list, in binary, from `n` and `s` in unary. -/
theorem hittingList_dimension_polytime_binary :
    ComputableTidilyInPolyTime (fun p : ℕ × ℕ => (hittingList p.1 p.2).dimension)
      (encPair encUnary encUnary) encNat :=
  unary_to_binary.comp hittingList_dimension_polytime

end Cslib.Circuits.Rational.Runtime
