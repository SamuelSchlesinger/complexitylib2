/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Basic
public import Complexity.Probability.BitString

/-!
# Sampling bit strings one fair bit at a time

`BitString.sampleList n` is an ordinary recursive program drawing `n` independent Boolean values.
Its distribution is the uniform law on lists of exactly that length. Computational efficiency is
certified separately in `Computability.Probabilistic.Sampling`.

## Main definitions

* `Cslib.BitString.sampleList`: sample a word using only fair Boolean choices.

## Main results

* `Cslib.BitString.eval_sampleList`: agreement with the finite uniform distribution.

## References

Adapted from `Cslib/Languages/Probabilistic/BitString.lean` on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the typed `PFunctor.FreeM` program interface.
-/

@[expose] public section

namespace Cslib.BitString

/-- Sample `n` independent fair bits, returned in sampling order. -/
noncomputable def sampleList : ℕ → ProbComp (List Bool)
  | 0 => pure []
  | n + 1 => do
    let bit ← ProbComp.uniform Bool
    return bit :: (← sampleList n)

/-- The operational fair-bit sampler has the finite uniform word distribution. -/
@[simp] theorem eval_sampleList (n : ℕ) : ProbComp.eval (sampleList n) = uniformList n := by
  induction n with
  | zero => simp [sampleList]
  | succ n ih => simp [sampleList, uniformList_succ, ih]

end Cslib.BitString
