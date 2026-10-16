/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.GoldreichLevin.Decoding
import Complexity.Probability.PMF.Expect

/-! Decoder checks with imperfect and perfect predictors, overlapping masks, and boundary cases. -/

namespace ComplexityTests.GoldreichLevin

open Cslib Cslib.Crypto.GoldreichLevin Cslib.Probability
open Finset
open scoped ENNReal

-- Ties, including the empty vote, are false in the shared majority operation.
example : BitString.strictMajorityOn (∅ : Finset (Fin 2)) (fun _ => true) = false := by decide
example : BitString.strictMajorityOn Finset.univ (fun i : Fin 2 => decide (i = 0)) = false := by
  decide

-- The two subsets overlap; their sums are still independent and uniform.
example (n : ℕ) :
    (PMF.uniformOfFintype (Fin 2 → BitString n)).map (fun masks => (masks 0, masks 0 + masks 1)) =
      PMF.uniformOfFintype (BitString n × BitString n) := by
  simpa using PMF.uniformOfFintype_map_sum_pair (G := BitString n)
    ({0} : Finset (Fin 2)) {0, 1} (by simp) (by simp) (by decide)

private def noisy (r : BitString 2) : Bool := r 0 && r 1
private def target : BitString 2 := ![true, false]

-- A genuinely imperfect predictor agrees with a parity on three of the four queries.
private theorem noisy_agreement : agreement noisy target = 3 / 4 := by
  rw [agreement_eq_probability, PMF.toReal_uniformOfFintype_map_apply_true]
  have hcount : #{r : BitString 2 | (noisy r == target ⬝ᵥ r) = true} = 3 := by decide
  rw [Finset.dens_eq_card_div_card, hcount]
  norm_num [BitString]

-- The concentration hypotheses are instantiated without assuming a perfect predictor.
example : (decode noisy 5).toOuterMeasure {list | target ∉ list} ≤ 1 / 2 := by
  apply decode_failure_le_half noisy target (1 / 4) (by norm_num) (by decide)
  · rw [noisy_agreement]
    norm_num
  · norm_num

-- Perfect prediction works for arbitrary masks, including all-zero and repeated masks.
example {n k : ℕ} (x : BitString n) (masks : Fin k → BitString n) (hk : 0 < k) :
    x ∈ candidates (fun r => x ⬝ᵥ r) masks := mem_candidates_parity x masks hk

-- Zero target length is valid; positive mask count is still an explicit theorem hypothesis.
example : (decode (fun _ : BitString 0 => false) 1).toOuterMeasure {list | 0 ∉ list} ≤ 1 / 2 := by
  apply decode_failure_le_half _ 0 (1 / 2) (by norm_num) (by decide)
  · norm_num [agreement, score, dotProduct, Bool.zero_eq_false]
    rfl
  · norm_num

end ComplexityTests.GoldreichLevin
