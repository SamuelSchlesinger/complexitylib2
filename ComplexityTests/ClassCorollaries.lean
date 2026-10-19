/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.BPP.KarpLipton
import Complexity.Computability.Complexity.Classes.Oracle.PolyTime
import Complexity.Computability.Complexity.Classes.Oracle.PP
import Complexity.Computability.Complexity.Classes.SPP.FewP
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

/-! ### `P^PP` and Toda's theorem -/

example : (Set.univ : Set (List Bool)) ∈ PWithPPOracle encBits :=
  P_subset_PWithPPOracle univ_mem_P

/-- Binary search for the constant `1 ∈ #P` reads its bit `0`. -/
example : (Set.univ : Set (List Bool)) ∈ PWithPPOracle encBits :=
  mem_PWithPPOracle_of_testBit SharpP.one_mem (p := 0) fun _ => by simp

/-- Binary search terminates on the value. -/
example : (BinarySearch.step 5)^[3] (0, 3) = (5, 0) := by decide

example {α : Type} (enc : α ↪ List Bool) : PH enc ⊆ PWithPPOracle enc :=
  PH_subset_PWithPPOracle

example {α : Type} (enc : α ↪ List Bool) : PWithSharpPOracle enc ⊆ PWithPPOracle enc :=
  PWithSharpPOracle_subset_PWithPPOracle

open Classical in
/-- Binary search against the oracle of `k ≤ 5`, on codes `(u, k)`, finds `5` in three rounds. -/
example (u : List Bool) :
    OracleComp.interpret (m := Id) (languageOracle {w | ∃ k ≤ 5, w = encPair encBits encNat (u, k)})
      (search u 3) = 5 :=
  interpret_id_search (fun k => ⟨fun ⟨j, hj, h⟩ =>
    (Prod.mk.inj ((encPair encBits encNat).injective h)).2 ▸ hj, fun hk => ⟨k, hk, rfl⟩⟩)
    (by norm_num)

/-! ### `FewP ⊆ SPP` -/

/-- A problem in `P`, hence in `UP` and `FewP`, is in `SPP`. -/
example : (Set.univ : Set (List Bool)) ∈ SPP encBits :=
  FewP_subset_SPP (UP_subset_FewP (P_subset_UP univ_mem_P))

/-! ### Axiom guards -/

/--
info: 'Cslib.Complexity.PH_eq_SigmaP_two_of_NP_subset_BPP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PH_eq_SigmaP_two_of_NP_subset_BPP

/--
info: 'Cslib.Complexity.ComputableInPolyTimeWithOracle.computableTidilyInPolyTime' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.ComputableInPolyTimeWithOracle.computableTidilyInPolyTime

/--
info: 'Cslib.Complexity.PWithOracle_eq_P' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PWithOracle_eq_P

/--
info: 'Cslib.Complexity.NPWithOracle_eq_NP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.NPWithOracle_eq_NP

/--
info: 'Cslib.Complexity.RPWithOracle_eq_RP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
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

/--
info: 'Cslib.Complexity.FewP_subset_SPP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.FewP_subset_SPP

/--
info: 'Cslib.Complexity.setOf_le_mem_PP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.setOf_le_mem_PP

/--
info: 'Cslib.Complexity.mem_PWithPPOracle_of_testBit' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_PWithPPOracle_of_testBit

/--
info: 'Cslib.Complexity.PWithSharpPOracle_subset_PWithPPOracle' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PWithSharpPOracle_subset_PWithPPOracle

/--
info: 'Cslib.Complexity.PH_subset_PWithPPOracle' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PH_subset_PWithPPOracle

end ComplexityTests.ClassCorollaries
