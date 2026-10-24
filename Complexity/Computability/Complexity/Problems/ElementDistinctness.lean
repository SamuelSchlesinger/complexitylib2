/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (spike for #739, not for merge)

public import Complexity.Computability.Complexity.Classes.P.WordRAM
public import Complexity.Algorithms.WordRAM.ElementDistinctness
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Lists

/-!
# Element distinctness is in `P`, through the word RAM (spike pilot, #739)

The instances are lists of naturals whose entries are below their length, encoded as framed lists
of binary naturals. Membership in `P` follows from the existing linear-time word-RAM decider
`ElementDistinctness.deciderAdditive` (`decidesInTime_nodup_additive`) and the RAM ⇒ TM
simulation, with no Turing-machine construction specific to this problem.

## Main definitions

* `Cslib.Algorithms.WordRAM.ElementDistinctness.inputEncoding`: the bit-string encoding.

## Main results

* `Cslib.Algorithms.WordRAM.ElementDistinctness.nodup_mem_P`: element distinctness is in `P`.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ElementDistinctness

open Cslib.WordRAM Turing.MultiTapeTM

/-- Instances as framed lists of binary naturals. -/
def inputEncoding : Input ↪ List Bool :=
  (Function.Embedding.subtype _).trans (encList encNat)

/-- **Element distinctness is in `P`**, for lists whose entries are below their length. The
decider is the word-RAM program `deciderAdditive`, simulated by a multi-tape machine. -/
theorem nodup_mem_P : {l : Input | l.1.Nodup} ∈ Cslib.Complexity.P inputEncoding :=
  Program.DecidesInTime.mem_P Basis.polyTimeOps_additive (encode := Subtype.val)
    (T := fun n => 16 * (n + 1)) (size := fun l => l.1.length) (k := 2)
    (Cslib.polynomiallyBounded_iff_le.mpr ⟨16, 1, fun n => by simp⟩)
    (PolyBounded.self.mono fun l => length_le_length_encList encNat l.1)
    (.of_eq fun _ => rfl) decidesInTime_nodup_additive

end Cslib.Algorithms.WordRAM.ElementDistinctness
