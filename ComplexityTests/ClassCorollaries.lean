/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.BPP.KarpLipton
import Complexity.Computability.Complexity.Classes.Oracle.PolyTime
import Complexity.Computability.Complexity.Classes.ValiantVazirani.Collapse

/-! Structural corollaries of the class theorems: clients of the collapses on concrete encodings,
and axiom guards. -/

namespace ComplexityTests.ClassCorollaries

open Cslib Cslib.Complexity Turing.MultiTapeTM

/-! ### `NP ⊆ BPP ⇒ PH = Σ₂` -/

/-- The collapse applies to languages over `Bool`, with words encoded as themselves. -/
example (h : ∀ {β : Type} (encB : β ↪ List Bool), NP encB ⊆ BPP encB) :
    PH encBits = SigmaP 2 encBits :=
  PH_eq_SigmaP_two_of_NP_subset_BPP h

/-! ### Oracles in `P` -/

/-- Every word: decided by the constant `true`. -/
theorem univ_mem_P : (Set.univ : Set (List Bool)) ∈ P encBits :=
  ⟨fun _ => true, .const true, fun _ => by simp⟩

example {α : Type} (enc : α ↪ List Bool) : PWithOracle Set.univ enc = P enc :=
  PWithOracle_eq_P univ_mem_P enc

example {α : Type} (enc : α ↪ List Bool) : NPWithOracle Set.univ enc = NP enc :=
  NPWithOracle_eq_NP univ_mem_P enc

example {α : Type} (enc : α ↪ List Bool) : RPWithOracle Set.univ enc = RP enc :=
  RPWithOracle_eq_RP univ_mem_P enc

open Classical in
/-- The decision problem of all numbers, as a promise problem in `PromiseP` under the binary
encoding, is solved by an oracle language in `P`. -/
example : ∃ A ∈ P encBits,
    (PromiseProblem.ofSet (Set.univ : Set ℕ)).SolvedBy fun n => decide (encNat n ∈ A) :=
  exists_mem_P_solvedBy_of_mem_PromiseP Decoder.nat
    (ofSet_mem_PromiseP.2 ⟨fun _ => true, .const true, fun _ => by simp⟩)

/-! ### Valiant–Vazirani collapses -/

example (h : PromiseUSAT ∈ PromiseP encCNF) : NP encBits = RP encBits :=
  NP_eq_RP_of_PromiseUSAT_mem_PromiseP h encBits

example (h : USAT ∈ P encCNF) : NP encCNF = RP encCNF :=
  NP_eq_RP_of_USAT_mem_P h encCNF

/-! ### Axiom guards -/

/--
info: 'Cslib.Complexity.PH_eq_SigmaP_two_of_NP_subset_BPP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PH_eq_SigmaP_two_of_NP_subset_BPP

/--
info: 'Cslib.Complexity.ComputableInPolyTimeWithOracle.computableTidilyInPolyTime' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.ComputableInPolyTimeWithOracle.computableTidilyInPolyTime

/--
info: 'Cslib.Complexity.PWithOracle_eq_P' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PWithOracle_eq_P

/--
info: 'Cslib.Complexity.NPWithOracle_eq_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.NPWithOracle_eq_NP

/--
info: 'Cslib.Complexity.RPWithOracle_eq_RP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.RPWithOracle_eq_RP

/--
info: 'Cslib.Complexity.NP_eq_RP_of_PromiseUSAT_mem_PromiseP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.NP_eq_RP_of_PromiseUSAT_mem_PromiseP

/--
info: 'Cslib.Complexity.NP_eq_RP_of_USAT_mem_P' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.NP_eq_RP_of_USAT_mem_P

end ComplexityTests.ClassCorollaries
