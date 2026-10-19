/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.BPP.KarpLipton

/-! Structural corollaries of the class theorems: clients of the collapses on concrete encodings,
and axiom guards. -/

namespace ComplexityTests.ClassCorollaries

open Cslib Cslib.Complexity Turing.MultiTapeTM

/-! ### `NP ⊆ BPP ⇒ PH = Σ₂` -/

/-- The collapse applies to languages over `Bool`, with words encoded as themselves. -/
example (h : ∀ {β : Type} (encB : β ↪ List Bool), NP encB ⊆ BPP encB) :
    PH encBits = SigmaP 2 encBits :=
  PH_eq_SigmaP_two_of_NP_subset_BPP h

/-! ### Axiom guards -/

/--
info: 'Cslib.Complexity.PH_eq_SigmaP_two_of_NP_subset_BPP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PH_eq_SigmaP_two_of_NP_subset_BPP

end ComplexityTests.ClassCorollaries
