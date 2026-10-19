/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.LMN
public import Complexity.Computability.Learning.LowDegree
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Learning constant-depth circuits from random examples

By the Linial–Mansour–Nisan theorem (`Unbounded.sum_fourierCoeff_sq_le_of_computes`), a function
computed by a circuit of negations and unbounded fan-in conjunctions and disjunctions of depth at
most `d` with at most `g` gates has Fourier weight at most `2 g / 2 ^ s` above degree `t`, for
every `s ≥ 2` and `t + 1 ≥ 2 max 8 (2 s) (16 s + 1) ^ d`
(`Unbounded.sum_fourierCoeff_sq_le_of_computes_of_depth_le`). Taking `2 ^ s ≥ 4 g / ε`, the
weight is at most `ε / 2`, so the low-degree algorithm learns these circuits from uniform random
examples [LinialMansourNisan1993] [O'Donnell, Section 4.5][ODonnell2014]
(`Unbounded.lowDegreeLearner_learns_of_depth_le`). With `s = max 2 ⌈log₂ ⌈4 g / ε⌉⌉` the degree
is `t = Unbounded.lmnDegree d g ε = O (log (g / ε)) ^ (d + 1)` for fixed `d`
(`Unbounded.lowDegreeLearner_learns_lmnDegree`), and the algorithm uses
`m ≥ (4 N / ε) log (2 N / δ)` examples, where `N ≤ (n + 1) ^ t` is the number of sets of at most
`t` coordinates (`Learning.card_filter_card_le_le`). Read asymptotically (this reading is not
itself formalized), for `g` polynomial in `n` and constant `d`, `ε` and `δ` this is
`n ^ O (log n) ^ (d + 1)` examples: quasi-polynomially many.

The exponent `d + 1` is inherited from the Fourier bound used here
(`Unbounded.sum_fourierCoeff_sq_le_of_computes`), in which depth counts every gate on a path,
negations included, and each restriction stage keeps a `1 / (16 s + 1)` fraction of the free bits.
It is weaker than the degree `O (log (g / ε)) ^ d` of Linial, Mansour and Nisan, and than the
degree `O (log (g / ε)) ^ (d - 1) log (1 / ε)` of the sharper form presented by O'Donnell
[O'Donnell, Section 4.5][ODonnell2014].

The learner computes `N` empirical coefficients from `m` examples, `O (N m t)` arithmetic
operations; this running time is an informal count, not certified by a machine model.

## Main definitions

* `Cslib.Circuits.Boolean.Unbounded.lmnDegree`: the degree used for circuits of depth `d` with
  `g` gates and error `ε`.

## Main results

* `Cslib.Circuits.Boolean.Unbounded.sum_fourierCoeff_sq_le_of_computes_of_depth_le`: the
  Linial–Mansour–Nisan bound above an explicit degree, for every number of inputs.
* `Cslib.Circuits.Boolean.Unbounded.lowDegreeLearner_learns_of_depth_le`,
  `Cslib.Circuits.Boolean.Unbounded.lowDegreeLearner_learns_lmnDegree`: the low-degree algorithm
  learns circuits of constant depth from uniform random examples.

## References

* [N. Linial, Y. Mansour, N. Nisan, *Constant depth circuits, Fourier transform, and
  learnability*][LinialMansourNisan1993]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Unbounded

open BitString Finset

variable {n : ℕ}

/-- **The Linial–Mansour–Nisan theorem above an explicit degree.** Let `f` be computed by a
circuit of negations and unbounded fan-in conjunctions and disjunctions of depth at most `d`, and
let `s ≥ 2`. Then the Fourier weight of `f`, read as signs, on the sets of more than `t`
coordinates is at most `2 g / 2 ^ s`, where `g` is the number of gates, whenever
`2 max 8 (2 s) (16 s + 1) ^ d ≤ t + 1`. -/
theorem sum_fourierCoeff_sq_le_of_computes_of_depth_le {f : BooleanFunction n}
    {C : Circuit signature n 1} (hC : C.Computes interpretation (single f)) {s d t : ℕ}
    (hs : 2 ≤ s) (hd : C.depth ≤ d) (ht : 2 * max 8 (2 * s) * (16 * s + 1) ^ d ≤ t + 1) :
    ∑ U with t < #U, fourierCoeff (fun x => signVal (f x)) U ^ 2 ≤ 2 * C.size / 2 ^ s := by
  set q := (16 * s + 1) ^ C.depth
  set M := max 8 (2 * s)
  have hq : 0 < q := by positivity
  have hqd : q ≤ (16 * s + 1) ^ d := Nat.pow_le_pow_right (by omega) hd
  have hMq : 2 * M * q ≤ t + 1 := (Nat.mul_le_mul_left _ hqd).trans ht
  have hM : 8 ≤ M := le_max_left _ _
  rcases Nat.lt_or_ge n q with hnq | hqn
  · -- every set has at most `n ≤ t` coordinates
    have htn : n ≤ t := by nlinarith
    rw [sum_eq_zero fun U hU => absurd ((mem_filter.1 hU).2.trans_le
      ((card_le_univ U).trans (by simpa using htn))) (lt_irrefl t)]
    positivity
  · have hr : 1 ≤ n / q := Nat.div_pos hqn hq
    have hk : M * n ≤ (t + 1) * (n / q) :=
      calc M * n ≤ M * (q * (n / q + 1)) :=
            Nat.mul_le_mul_left _ (Nat.lt_mul_div_succ n hq).le
        _ ≤ M * (q * (2 * (n / q))) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
        _ = 2 * M * q * (n / q) := by ring
        _ ≤ (t + 1) * (n / q) := Nat.mul_le_mul_right _ hMq
    simpa only [Nat.add_one_le_iff] using
      sum_fourierCoeff_sq_le_of_computes hC hs (hq.trans_le hqn) hk

/-- **The low-degree algorithm learns constant-depth circuits** [LinialMansourNisan1993]
[O'Donnell, Section 4.5][ODonnell2014]. Let `s ≥ 2` with `4 g ≤ ε 2 ^ s`, let
`t + 1 ≥ 2 max 8 (2 s) (16 s + 1) ^ d`, and let `N` be the number of sets of at most `t` of the `n`
coordinates. Then the low-degree algorithm of degree `t` from `m ≥ (4 N / ε) log (2 N / δ)`
uniform random examples learns the functions computed by circuits of negations and unbounded
fan-in conjunctions and disjunctions of depth at most `d` with at most `g` gates, with error `ε`
and confidence `1 - δ`. -/
theorem lowDegreeLearner_learns_of_depth_le {d g s t m : ℕ} {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hs : 2 ≤ s) (hsg : 4 * (g : ℝ) ≤ ε * 2 ^ s)
    (ht : 2 * max 8 (2 * s) * (16 * s + 1) ^ d ≤ t + 1)
    (hm : 4 * #{S : Finset (Fin n) | #S ≤ t} / ε *
      Real.log (2 * #{S : Finset (Fin n) | #S ≤ t} / δ) ≤ m) :
    (Learning.lowDegreeLearner (Fin n) t m).Learns
      {f | ∃ C : Circuit signature n 1,
        C.Computes interpretation (single f) ∧ C.depth ≤ d ∧ C.size ≤ g} ε δ := by
  refine Learning.lowDegreeLearner_learns hε hδ hm fun f ⟨C, hC, hd, hg⟩ => ?_
  refine (sum_fourierCoeff_sq_le_of_computes_of_depth_le hC hs hd ht).trans ?_
  have hgR : (C.size : ℝ) ≤ g := by exact_mod_cast hg
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- The degree of the low-degree algorithm for circuits of depth `d` with `g` gates and error
`ε`: `2 max 8 (2 s) (16 s + 1) ^ d - 1` for `s = max 2 ⌈log₂ ⌈4 g / ε⌉⌉`, which is
`O (log (g / ε)) ^ (d + 1)` for fixed `d`. -/
noncomputable def lmnDegree (d g : ℕ) (ε : ℝ) : ℕ :=
  let s := max 2 (Nat.clog 2 ⌈4 * g / ε⌉₊)
  2 * max 8 (2 * s) * (16 * s + 1) ^ d - 1

/-- **The low-degree algorithm learns constant-depth circuits**, with the explicit degree
`t = lmnDegree d g ε = O (log (g / ε)) ^ (d + 1)` [LinialMansourNisan1993]
[O'Donnell, Section 4.5][ODonnell2014]: from `m ≥ (4 N / ε) log (2 N / δ)` uniform random
examples, where `N ≤ (n + 1) ^ t` is the number of sets of at most `t` of the `n` coordinates, it
learns the functions computed by circuits of negations and unbounded fan-in conjunctions and
disjunctions of depth at most `d` with at most `g` gates, with error `ε` and confidence
`1 - δ`. -/
theorem lowDegreeLearner_learns_lmnDegree {d g m : ℕ} {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hm : 4 * #{S : Finset (Fin n) | #S ≤ lmnDegree d g ε} / ε *
      Real.log (2 * #{S : Finset (Fin n) | #S ≤ lmnDegree d g ε} / δ) ≤ m) :
    (Learning.lowDegreeLearner (Fin n) (lmnDegree d g ε) m).Learns
      {f | ∃ C : Circuit signature n 1,
        C.Computes interpretation (single f) ∧ C.depth ≤ d ∧ C.size ≤ g} ε δ := by
  set s := max 2 (Nat.clog 2 ⌈4 * g / ε⌉₊)
  have hs : 2 ≤ s := le_max_left _ _
  have hsg : 4 * (g : ℝ) ≤ ε * 2 ^ s := by
    have h₁ : 4 * (g : ℝ) / ε ≤ 2 ^ s :=
      calc 4 * (g : ℝ) / ε ≤ ⌈4 * g / ε⌉₊ := Nat.le_ceil _
        _ ≤ ((2 ^ Nat.clog 2 ⌈4 * g / ε⌉₊ : ℕ) : ℝ) :=
            Nat.cast_le.2 (Nat.le_pow_clog (by norm_num) _)
        _ ≤ 2 ^ s := by
            rw [Nat.cast_pow, Nat.cast_ofNat]
            exact pow_le_pow_right₀ (by norm_num) (le_max_right _ _)
    rw [div_le_iff₀ hε] at h₁
    linarith
  have hpos : 0 < 2 * max 8 (2 * s) * (16 * s + 1) ^ d := by positivity
  have ht : 2 * max 8 (2 * s) * (16 * s + 1) ^ d ≤ lmnDegree d g ε + 1 := by
    change _ ≤ 2 * max 8 (2 * s) * (16 * s + 1) ^ d - 1 + 1
    omega
  exact lowDegreeLearner_learns_of_depth_le hε hδ hs hsg ht hm

end Cslib.Circuits.Boolean.Unbounded
