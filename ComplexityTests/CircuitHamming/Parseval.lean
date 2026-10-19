/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.BooleanAnalysis.HammingFourier
import Mathlib.Tactic.NormNum

/-! The noise distance between two distinct parities, which damps their disagreement by the size
of their sets; the relative Hamming distance of the constants; separation failing at `ρ = 0`; and
the metric `√D_ρ` at `ρ = 1`. -/

namespace ComplexityTests.CircuitHamming.Parseval

open Cslib Cslib.BitString Finset

/-! ### Parities -/

/-- Without noise, two distinct parities are at relative Hamming distance one half. -/
example : noiseDist 1 (parityOn ({0} : Finset (Fin 3))) (parityOn {1, 2}) = 1 / 2 := by
  rw [noiseDist_parityOn 1 (by decide)]
  norm_num

/-- At `ρ = 1 / 2`, a parity on one coordinate and one on two are at noise distance
`(1 / 4 + 1 / 16) / 4`: the larger set is damped more. -/
example : noiseDist (1 / 2) (parityOn ({0} : Finset (Fin 3))) (parityOn {1, 2}) = 5 / 64 := by
  rw [noiseDist_parityOn _ (by decide)]
  norm_num

/-- The relative Hamming distance between the parities, through the Fourier coefficients. -/
example : (hammingDist (parityOn ({0} : Finset (Fin 3))) (parityOn {1, 2}) : ℝ) / 2 ^ 3 =
    1 / 2 := by
  have h := noiseDist_one (parityOn ({0} : Finset (Fin 3))) (parityOn {1, 2})
  rw [noiseDist_parityOn 1 (by decide), Fintype.card_fin] at h
  rw [← h]
  norm_num

/-! ### The constants -/

/-- The two constants are at relative Hamming distance one, read off their Fourier
coefficients. -/
example : 1 / 4 * ∑ S : Finset (Fin 2), (fourierCoeff (fun _ => signVal false) S -
    fourierCoeff (fun _ => signVal true) S) ^ 2 = 1 := by
  rw [← hammingDist_div_eq_sum_fourierCoeff_sub_sq (fun _ : Fin 2 → Bool => false) fun _ => true]
  simp [hammingDist]
  norm_num

/-! ### Separation and the metric -/

/-- **Separation needs `ρ ≠ 0`.** At `ρ = 0` only the means are compared, and two distinct
parities on nonempty sets both have mean zero. -/
example : noiseDist 0 (parityOn ({0} : Finset (Fin 2))) (parityOn {1}) = 0 ∧
    parityOn ({0} : Finset (Fin 2)) ≠ parityOn {1} := by
  refine ⟨?_, ?_⟩
  · rw [noiseDist_parityOn 0 (by decide)]
    norm_num
  · intro h
    exact absurd (congrFun h ![true, false]) (by decide)

/-- For `ρ ≠ 0`, the same parities are at positive noise distance. -/
example : 0 < noiseDist (1 / 3) (parityOn ({0} : Finset (Fin 2))) (parityOn {1}) := by
  rw [noiseDist_parityOn _ (by decide)]
  norm_num

/-- The metric `√D_1` on Boolean functions of two bits: the two constants are at distance one. -/
example :
    (noiseMetricSpace (ι := Fin 2) one_ne_zero).dist (fun _ => false) (fun _ => true) = 1 := by
  have h : (hammingDist (fun _ : Fin 2 → Bool => false) fun _ => true : ℝ) / 2 ^ 2 = 1 := by
    simp [hammingDist]
    norm_num
  rw [noiseMetricSpace_dist, noiseDist_one, Fintype.card_fin, h, Real.sqrt_one]

/-- The triangle inequality for `√D_ρ`, at a concrete triple. -/
example (ρ : ℝ) :
    √(noiseDist ρ (parityOn ({0} : Finset (Fin 2))) (parityOn {1})) ≤
      √(noiseDist ρ (parityOn ({0} : Finset (Fin 2))) (parityOn {0, 1})) +
        √(noiseDist ρ (parityOn ({0, 1} : Finset (Fin 2))) (parityOn {1})) :=
  sqrt_noiseDist_triangle ρ _ _ _

/-! ### Axioms -/

/--
info: 'Cslib.BitString.hammingDist_div_eq_sum_fourierCoeff_sub_sq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms hammingDist_div_eq_sum_fourierCoeff_sub_sq

/--
info: 'Cslib.BitString.noiseDist_eq_sum' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms noiseDist_eq_sum

/--
info: 'Cslib.BitString.noiseDist_one' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms noiseDist_one

/--
info: 'Cslib.BitString.noiseDist_le_hammingDist_div' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms noiseDist_le_hammingDist_div

/--
info: 'Cslib.BitString.dist_noiseEmbedding' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms dist_noiseEmbedding

/--
info: 'Cslib.BitString.sqrt_noiseDist_triangle' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sqrt_noiseDist_triangle

/--
info: 'Cslib.BitString.noiseDist_eq_zero_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms noiseDist_eq_zero_iff

/--
info: 'Cslib.BitString.noiseDist_parityOn' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms noiseDist_parityOn

end ComplexityTests.CircuitHamming.Parseval
