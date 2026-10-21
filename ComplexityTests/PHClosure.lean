/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.PH.Closure
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# Tests for Boolean closure of polynomial-hierarchy levels

Unequal and zero-length blocks check the concrete splitter; alternating predicates check both
quantifier polarities. Concrete polynomial-time languages instantiate closure at levels zero and
two, and the headline theorems have named axiom guards.
-/

namespace ComplexityTests.PHClosure

open Cslib.Complexity Turing.MultiTapeTM

example : splitAlternatingBlocks [(1, 2), (0, 1), (2, 0)]
    [true, false, true, false, false, true] =
    ([true, false, true], [false, true, false]) := by decide

example : splitAlternatingBlocks [(0, 0), (0, 0)] [true] = ([], []) := by decide

example (q : Bool) (P Q : List Bool → Prop) :
    Alternation q [3, 1, 2]
      (fun w => P (splitAlternatingBlocks [(1, 2), (0, 1), (2, 0)] w).1 ∧
        Q (splitAlternatingBlocks [(1, 2), (0, 1), (2, 0)] w).2) ↔
      Alternation q [1, 0, 2] P ∧ Alternation q [2, 1, 0] Q :=
  alternation_splitAlternatingBlocks [(1, 2), (0, 1), (2, 0)] q P Q

private theorem true_in_P : ({true} : Set Bool) ∈ P encBool :=
  ⟨id, ComputableTidilyInPolyTime.id', fun _ => Iff.rfl⟩

private theorem false_in_P : ({false} : Set Bool) ∈ P encBool :=
  ⟨Bool.not, ComputableTidilyInPolyTime.bool_not, fun b => by cases b <;> simp⟩

example : ({true} ∪ {false} : Set Bool) ∈ SigmaP 0 encBool :=
  union_mem_SigmaP (P_subset_SigmaP_zero true_in_P) (P_subset_SigmaP_zero false_in_P)

example : ({true} ∩ {false} : Set Bool) ∈ PiP 2 encBool :=
  inter_mem_PiP (SigmaP_subset_PiP_succ 1
    (SigmaP_subset_SigmaP_succ 0 (P_subset_SigmaP_zero true_in_P)))
    (SigmaP_subset_PiP_succ 1
      (SigmaP_subset_SigmaP_succ 0 (P_subset_SigmaP_zero false_in_P)))

/-- info: 'Cslib.Complexity.alternation_splitAlternatingBlocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms alternation_splitAlternatingBlocks
/-- info: 'Cslib.Complexity.inter_mem_SigmaP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inter_mem_SigmaP
/-- info: 'Cslib.Complexity.union_mem_SigmaP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms union_mem_SigmaP
/-- info: 'Cslib.Complexity.inter_mem_PiP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inter_mem_PiP
/-- info: 'Cslib.Complexity.union_mem_PiP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms union_mem_PiP

end ComplexityTests.PHClosure
