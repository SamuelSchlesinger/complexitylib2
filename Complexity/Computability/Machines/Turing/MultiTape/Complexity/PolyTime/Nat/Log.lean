/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import Mathlib.Data.Nat.Log
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Mathlib.Data.Nat.Size

/-!
# Polynomial-time binary logarithms

The base-two logarithm is the binary representation's length minus one, with truncated
subtraction handling zero. Unary input first uses the certified unary-to-binary conversion.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_log_two`: compute the logarithm of a
  binary natural, returning its unary value.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_log_two`: the unary-input version.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- The base-two logarithm is polynomial-time on binary naturals, with its result in unary. -/
@[fun_prop]
theorem binary_log_two : ComputableTidilyInPolyTime (Nat.log 2) encNat encUnary := by
  have heq (n : ℕ) : (encNat n).length - 1 = Nat.log 2 n := by
    rw [encNat_apply, Nat.size_eq_bits_len]
    rcases n.eq_zero_or_pos with rfl | hn
    · simp
    · have hs := Nat.size_pos.mpr hn
      symm
      apply Nat.log_eq_of_pow_le_of_lt_pow
      · exact Nat.lt_size.mp (by lia)
      · simpa only [Nat.sub_add_cancel hs] using Nat.lt_size_self n
  simpa only [Function.comp_def, heq] using
    unary_sub.comp ((encoding_length encNat).prod (const 1))

/-- The base-two logarithm is polynomial-time with both input and output in unary. -/
@[fun_prop]
theorem unary_log_two : ComputableTidilyInPolyTime (Nat.log 2) encUnary encUnary :=
  binary_log_two.comp unary_to_binary

end Turing.MultiTapeTM.ComputableTidilyInPolyTime
