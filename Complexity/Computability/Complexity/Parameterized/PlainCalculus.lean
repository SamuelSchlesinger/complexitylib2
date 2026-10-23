/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public meta import Complexity.Tactic.PlainMirror
public import Complexity.Computability.Complexity.Parameterized

/-!
# Plain generic fixed-parameter computation rules

The existing PolyTime-to-FPT, conditional and composition rules are transported mechanically
across the proved plain/tidy equivalences. Uniform-machine and arbitrary parameter-bound
conventions are exactly those of `Parameterized`; the transformation adds no computability
assumption on a parameter-bound function and removes none of the original bounds.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.computableInFPTTime`: polynomial time is FPT time.
* `Cslib.Complexity.ComputableInFPTTime.ite`: conditional closure with the same parameter.
* `Cslib.Complexity.ComputableInFPTTime.comp`: composition with the original parameter bound.
-/

public section

attribute [plain_mirror]
  Turing.MultiTapeTM.ComputableTidilyInPolyTime.computableTidilyInFPTTime
  Cslib.Complexity.ComputableTidilyInFPTTime.ite
  Cslib.Complexity.ComputableTidilyInFPTTime.comp
