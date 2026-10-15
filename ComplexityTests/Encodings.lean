/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Encoding

/-!
# Tests for the framed encodings
-/

namespace ComplexityTests.Encodings

open Turing.MultiTapeTM

example : frame [true, false] = [true, true, true, false, false] := rfl

example : encPair encNat encBool (2, true) = [true, false, true, true, false, true] := by
  decide

example : encList encBool [true, false] = [true, true, false, true, false, false] := rfl

example (w u : List Bool) : unframe (frame w ++ u) = w := unframe_frame_append w u

end ComplexityTests.Encodings
