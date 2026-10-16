/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.UniformNat
public import Complexity.Computability.Probabilistic.Sampling
import Complexity.Tactic.PPT

/-!
# Sampling bounded indices in strict polynomial time

Each sampler uses a fixed number of fair bits. Binary decoding saturates at a computed cap,
so both its intermediate states and its unary output remain polynomially bounded. The dyadic
range is at most `2 * (bound + 1)`, including zero. No unbounded rejection loop is used.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_dyadicSize`: efficient unary range size.
* `Cslib.Probability.isPPTOn_sampleDyadicIndex`: exact uniform sampling in the dyadic range.
* `Cslib.Probability.isPPTOn_sampleBoundedIndex`: capped sampling with a rejection sentinel.
* `Cslib.Probability.isPPTOn_sampleDyadicCoin`: exact capped dyadic probabilities.

## References

Adapted from `Computability/Probabilistic/UniformNat.lean` on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the tidy machine calculus and shared bit folds.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- Compute the dyadic range in unary via capped binary decoding. Its exponential expression
does not authorize exponential output: the proved linear cap supplies the implementation. -/
@[fun_prop]
theorem unary_dyadicSize : ComputableTidilyInPolyTime Cslib.Probability.dyadicSize
    encUnary encUnary := by
  change ComputableTidilyInPolyTime (fun n => Cslib.Probability.dyadicSize n) encUnary encUnary
  simp only [Cslib.Probability.dyadicSize_eq_boundedBinaryValue]
  fun_prop

end Turing.MultiTapeTM.ComputableTidilyInPolyTime

namespace Cslib.Probability

open Turing.MultiTapeTM

/-- An efficiently supplied unary bound gives a strict PPT exact dyadic sampler. -/
@[program_certificate]
theorem isPPTOn_sampleDyadicIndex {α : Type} {input : α ↪ List Bool} {bound : α → ℕ}
    (hbound : ComputableTidilyInPolyTime bound input encUnary) :
    IsPPTOn input encUnary (fun a => sampleDyadicIndex (bound a)) := by
  unfold sampleDyadicIndex
  ppt

/-- Efficient unary parameters give a strict PPT coin with the specified dyadic law. -/
@[program_certificate]
theorem isPPTOn_sampleDyadicCoin {α : Type} {input : α ↪ List Bool}
    {bound numerator : α → ℕ}
    (hbound : ComputableTidilyInPolyTime bound input encUnary)
    (hnumerator : ComputableTidilyInPolyTime numerator input encUnary) :
    IsPPTOn input encBool (fun a => sampleDyadicCoin (bound a) (numerator a)) := by
  unfold sampleDyadicCoin
  ppt

/-- An efficiently supplied unary bound gives a strict PPT capped index sampler. -/
@[program_certificate]
theorem isPPTOn_sampleBoundedIndex {α : Type} {input : α ↪ List Bool} {bound : α → ℕ}
    (hbound : ComputableTidilyInPolyTime bound input encUnary) :
    IsPPTOn input encUnary (fun a => sampleBoundedIndex (bound a)) := by
  unfold sampleBoundedIndex
  ppt

end Cslib.Probability
