/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.GGM.Evaluation
import Complexity.Tactic.PolyTime

/-! GGM's functional evaluator and its machine certificate, including short expansions and empty
seeds. These examples assert evaluation and efficiency, not cryptographic security. -/

namespace ComplexityTests.GGM

open Turing.MultiTapeTM Cslib.Crypto

example : GGM.eval (fun seed => seed ++ seed.reverse ++ [true]) [false, true] [true, false] =
    [true, false] := by decide

example (query : List Bool) : GGM.eval (fun _ => [true]) [] query = [] := by
  exact List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero (GGM.length_eval_le _ [] query))

-- Duplicating the seed is a concrete efficient generator, though it is not pseudorandom.
example : ComputableTidilyInPolyTime
    (fun p : List Bool × List Bool => GGM.eval (fun seed => seed ++ seed) p.1 p.2)
    (encPair encBits encBits) encBits := by fun_prop

-- A shrinking expansion is allowed: efficiency does not require a PRG or a length hypothesis.
example : ComputableTidilyInPolyTime
    (fun p : List Bool × List Bool => GGM.eval List.tail p.1 p.2)
    (encPair encBits encBits) encBits := by fun_prop

example (generator : List Bool → List Bool)
    (hgenerator : ComputableTidilyInPolyTime generator encBits encBits) :
    ComputableTidilyInPolyTime
      (fun p : List Bool × List Bool => GGM.eval generator p.1 (p.2 ++ p.2))
      (encPair encBits encBits) encBits := by fun_prop

end ComplexityTests.GGM
