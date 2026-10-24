/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Computability.Complexity.Classes.SharpP.Lowness
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

@[expose] public section

namespace Cslib.Complexity.SharpPLownessTests

open Turing.MultiTapeTM

/-! ### Nonvacuous concrete oracle in `UP ∩ coUP`, `FewP`, and `SPP` -/

/-- A nontrivial oracle language accepting bit strings whose first bit is `true`. -/
def headTrue : Set (List Bool) := {w | w.headD false = true}

theorem true_singleton_mem_headTrue : [true] ∈ headTrue := rfl

theorem nil_not_mem_headTrue : [] ∉ headTrue := by simp [headTrue]

theorem headTrue_mem_P : headTrue ∈ P encBits :=
  ⟨fun w => w.headD false, .of_tidy (by fun_prop), fun _ => Iff.rfl⟩

theorem headTrue_mem_UP : headTrue ∈ UP encBits :=
  P_subset_UP headTrue_mem_P

theorem headTrue_mem_coUP : headTrue ∈ coUP encBits :=
  P_subset_coUP headTrue_mem_P

theorem headTrue_mem_FewP : headTrue ∈ FewP encBits :=
  UP_subset_FewP headTrue_mem_UP

theorem headTrue_mem_SPP : headTrue ∈ SPP encBits :=
  UP_subset_SPP headTrue_mem_UP

/-! ### Concrete `#P` and `GapP` precomposition with `FP^(UP ∩ coUP)` -/

theorem oracleId_computableInPolyTimeWithOracle :
    ComputableInPolyTimeWithOracle headTrue (fun w : List Bool => w) encBits encBits :=
  (ComputableTidilyInPolyTime.id').computableInPolyTimeWithOracle headTrue

example : ((fun _ : List Bool => (1 : ℕ)) ∘ fun w : List Bool => w) ∈ SharpP encBits :=
  SharpP.comp_mem_of_computableInPolyTimeWithOracle headTrue_mem_UP headTrue_mem_coUP
    oracleId_computableInPolyTimeWithOracle SharpP.one_mem

example : ((fun _ : List Bool => (1 : ℤ)) ∘ fun w : List Bool => w) ∈ GapP encBits :=
  GapP.comp_mem_of_computableInPolyTimeWithOracle headTrue_mem_UP headTrue_mem_coUP
    oracleId_computableInPolyTimeWithOracle GapP.one_mem

/-! ### Concrete `#P`, `UP`, `FewP`, `US`, `SBP`, `SPP`, and `ModP` lowness checks -/

example : SharpPWithOracle headTrue encBits = SharpP encBits :=
  SharpPWithOracle_eq_SharpP_of_mem_UP_of_mem_coUP headTrue_mem_UP headTrue_mem_coUP encBits

example : SharpPWithOracle headTrue encBits = SharpP encBits :=
  SharpPWithOracle_eq_SharpP_iff.mpr ⟨headTrue_mem_UP, headTrue_mem_coUP⟩

example : UPWithOracle headTrue encBits = UP encBits :=
  UPWithOracle_eq_UP_of_mem_UP_of_mem_coUP headTrue_mem_UP headTrue_mem_coUP encBits

example : coUPWithOracle headTrue encBits = coUP encBits :=
  coUPWithOracle_eq_coUP_of_mem_UP_of_mem_coUP headTrue_mem_UP headTrue_mem_coUP encBits

example : UPWithOracle headTrue encBits ∩ coUPWithOracle headTrue encBits =
    UP encBits ∩ coUP encBits :=
  UPWithOracle_inter_coUPWithOracle_eq_iff.mpr ⟨headTrue_mem_UP, headTrue_mem_coUP⟩

example : FewPWithOracle headTrue encBits = FewP encBits :=
  FewPWithOracle_eq_FewP_of_mem_UP_of_mem_coUP headTrue_mem_UP headTrue_mem_coUP encBits

example : USWithOracle headTrue encBits = US encBits :=
  USWithOracle_eq_US_of_mem_UP_of_mem_coUP headTrue_mem_UP headTrue_mem_coUP encBits

example : SBPWithFixedTarget headTrue encBits = SBP encBits :=
  SBPWithFixedTarget_eq_SBP_of_mem_UP_of_mem_coUP headTrue_mem_UP headTrue_mem_coUP encBits

example : GapPWithOracle headTrue encBits = GapP encBits :=
  GapPWithOracle_eq_GapP_iff.mpr headTrue_mem_SPP

example : SPPWithOracle headTrue encBits = SPP encBits :=
  SPPWithOracle_eq_SPP_iff.mpr headTrue_mem_SPP

example : ModPWithOracle 3 headTrue encBits = ModP 3 encBits :=
  ModPWithOracle_eq_ModP_of_mem_SPP (by decide) headTrue_mem_SPP encBits

example : coModPWithOracle 3 headTrue encBits = coModP 3 encBits :=
  coModPWithOracle_eq_coModP_of_mem_SPP (by decide) headTrue_mem_SPP encBits

example : ParityPWithOracle headTrue encBits = ParityP encBits :=
  ParityPWithOracle_eq_ParityP_of_mem_SPP headTrue_mem_SPP encBits

example : ModPWithOracle 5 headTrue encBits = ModP 5 encBits :=
  ModPWithOracle_eq_ModP_of_mem_FewP (by decide) headTrue_mem_FewP encBits

example : ParityPWithOracle headTrue encBits = ParityP encBits :=
  ParityPWithOracle_eq_ParityP_of_mem_FewP headTrue_mem_FewP encBits

/-! ### Axiom guards for headline theorems -/

/--
info: 'Cslib.Complexity.SharpP.encoded_comp_mem_of_computableInPolyTimeWithOracle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.SharpP.encoded_comp_mem_of_computableInPolyTimeWithOracle

/--
info: 'Cslib.Complexity.SharpPWithOracle_eq_SharpP_of_mem_UP_of_mem_coUP' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.SharpPWithOracle_eq_SharpP_of_mem_UP_of_mem_coUP

/-- info: 'Cslib.Complexity.SharpPWithOracle_eq_SharpP_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Complexity.SharpPWithOracle_eq_SharpP_iff

/--
info: 'Cslib.Complexity.UPWithOracle_eq_UP_and_coUPWithOracle_eq_coUP_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.UPWithOracle_eq_UP_and_coUPWithOracle_eq_coUP_iff

/-- info: 'Cslib.Complexity.UPWithOracle_inter_coUPWithOracle_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Complexity.UPWithOracle_inter_coUPWithOracle_eq_iff

/--
info: 'Cslib.Complexity.FewPWithOracle_eq_FewP_of_mem_UP_of_mem_coUP' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.FewPWithOracle_eq_FewP_of_mem_UP_of_mem_coUP

/-- info: 'Cslib.Complexity.USWithOracle_eq_US_of_mem_UP_of_mem_coUP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Complexity.USWithOracle_eq_US_of_mem_UP_of_mem_coUP

/--
info: 'Cslib.Complexity.SBPWithFixedTarget_eq_SBP_of_mem_UP_of_mem_coUP' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.SBPWithFixedTarget_eq_SBP_of_mem_UP_of_mem_coUP

/-- info: 'Cslib.Complexity.GapPWithOracle_eq_GapP_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Complexity.GapPWithOracle_eq_GapP_iff

/-- info: 'Cslib.Complexity.SPPWithOracle_eq_SPP_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Complexity.SPPWithOracle_eq_SPP_iff

/-- info: 'Cslib.Complexity.ModPWithOracle_eq_ModP_of_mem_SPP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Complexity.ModPWithOracle_eq_ModP_of_mem_SPP

/-- info: 'Cslib.Complexity.ParityPWithOracle_eq_ParityP_of_mem_SPP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Complexity.ParityPWithOracle_eq_ParityP_of_mem_SPP

end Cslib.Complexity.SharpPLownessTests
