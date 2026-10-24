/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity
import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Id
import Cslib.Foundations.Data.PFunctor.Free

/-!
# Smoke test

Checks the upstream APIs this library builds on and inference under its complete public imports.
-/

namespace ComplexityTests

/-- The upstream time-and-space computability predicate. -/
example := @Turing.MultiTapeTM.ComputableInTimeAndSpace

/-- The upstream complexity of the identity function. -/
example := @Turing.MultiTapeTM.computableInTimeAndSpace_id

/-- The free monad the program layer is built on. -/
example := @PFunctor.FreeM

end ComplexityTests

-- The direct API remains callable, but no later annotation may restore its premature search path.
run_meta do
  let rules ← Mathlib.Meta.FunProp.getTheoremsForFunction `Prod.fst
    `Turing.MultiTapeTM.ComputableInPolyTime
  if rules.any (·.thmOrigin.name == `Turing.MultiTapeTM.ComputableInPolyTime.fst') then
    throwError "the direct fst' helper must remain outside automatic function search"

-- This is the captured arithmetic shape inside SAT's circuit-block certificate, under the same
-- complete import closure that exposed the encoding-inference regression.
section PlainInference

open _root_.Turing.MultiTapeTM

set_option maxHeartbeats 20000 in
-- Retain the unchanged inventory budget: the direct projection search formerly exhausted it.
example (c : ℕ) : ComputableInPolyTime
    (fun q : ((ℕ × ℕ) × Bool) × Bool => q.1.1.1 + c)
    (encPair (encPair (encPair encUnary encUnary) encBool) encBool) encNat := by
  fun_prop

end PlainInference
