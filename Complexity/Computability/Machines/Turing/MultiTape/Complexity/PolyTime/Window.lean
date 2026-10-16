/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Feature
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Polynomial-time enumeration of tape windows

The existing `Turing.windowList` enumerates `-T, …, T` from left to right. With the bound in
unary and the positions in signed unary, the same list is computable in polynomial time.

## Main results

* `Turing.computableTidilyInPolyTime_windowList`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Turing

open MultiTapeTM ComputableTidilyInPolyTime

/-- Enumerate all tape positions within a unary distance of the origin, in signed unary. -/
@[fun_prop]
theorem computableTidilyInPolyTime_windowList :
    ComputableTidilyInPolyTime windowList encUnary (encList encInt) := by
  unfold windowList
  have hf : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => (p.2 : ℤ) - p.1)
      (encPair encUnary encUnary) encInt :=
    int_natCast_sub.comp ((snd encUnary encUnary).prod (fst encUnary encUnary))
  exact mapWith hf id' (by fun_prop)

end Turing
