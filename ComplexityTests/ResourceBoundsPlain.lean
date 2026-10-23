/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.Inclusions
import Complexity.Computability.Complexity.Classes.Space.TQBF.Membership
import Complexity.Computability.Complexity.Parameterized
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain
import Complexity.Tactic.PolyTime
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Id

/-! Plain computability within bounds up to constants, within a space bound, within polynomial
space and in fpt time, against the tidy notions in both directions: upstream machines that are not
tidy satisfy the plain notions and give tidy certificates, and library certificates, including
the deciders for `TQBF` and `SAT`, give plain ones. -/

namespace ComplexityTests.ResourceBoundsPlain

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM

/-! ### From upstream machines to tidy certificates -/

/-- Upstream's copy machine, which is not tidy and has no work tape, computes the identity within
linear time and space. -/
theorem id_computableInO :
    ComputableInO (id : List Bool → List Bool) encBits encBits (·.length) (·.length) :=
  ⟨1, computableInTimeAndSpace_id.mono (fun w => by simp [encBits]) fun _ => Nat.zero_le _,
    fun w => by simp [encBits]⟩

/-- The tidy normal form keeps the bounds up to constants. -/
example : ComputableTidilyInO (id : List Bool → List Bool) encBits encBits (·.length) (·.length) :=
  id_computableInO.tidy

/-- The copy machine computes the identity within linear space, in some time. -/
theorem id_computableInSpace :
    ComputableInSpace (id : List Bool → List Bool) encBits encBits (·.length) :=
  ⟨_, 1, computableInTimeAndSpace_id.mono (fun _ => le_rfl) fun _ => Nat.zero_le _,
    fun w => by simp [encBits]⟩

example : ComputableTidilyInSpace (id : List Bool → List Bool) encBits encBits (·.length) :=
  id_computableInSpace.tidy

/-- The value must fit in the space bound: although the copy machine uses no work space, the
identity is not computable within constant space in this sense. -/
example : ¬ComputableInSpace (id : List Bool → List Bool) encBits encBits fun _ => 0 := by
  rintro ⟨t, c, -, hl⟩
  simpa [encBits] using hl (List.replicate (c + 1) true)

/-- The copy machine computes the identity within polynomial space. -/
theorem id_computableInPolySpace :
    ComputableInPolySpace (id : List Bool → List Bool) encBits encBits :=
  ⟨_, fun n => n, by fun_prop,
    computableInTimeAndSpace_id.mono (fun _ => le_rfl) fun _ => Nat.zero_le _,
    fun w => by simp [encBits]⟩

example : ComputableTidilyInPolySpace (id : List Bool → List Bool) encBits encBits :=
  id_computableInPolySpace.tidy

/-- The copy machine computes the identity in fpt time, for every parameter. -/
theorem id_computableInFPTTime (κ : List Bool → ℕ) :
    ComputableInFPTTime (id : List Bool → List Bool) encBits encBits κ :=
  ⟨fun _ => 1, 1, computableInTimeAndSpace_id.mono (fun w => by simp [encBits])
    fun _ => Nat.zero_le _⟩

example (κ : List Bool → ℕ) :
    ComputableTidilyInFPTTime (id : List Bool → List Bool) encBits encBits κ :=
  (id_computableInFPTTime κ).tidy

/-! ### Classes through plain deciders -/

/-- The words equal to `[true]`, a problem on an infinite type. -/
private def single : Set (List Bool) := {[true]}

/-- Upstream's almost-constant machine decides `single` within constant time and zero space. -/
private theorem exists_computableInTimeAndSpace_single : ∃ c,
    ComputableInTimeAndSpace (fun w : List Bool => decide (w = [true])) encBits encBool
      (fun _ => c) fun _ => 0 :=
  computableInTimeAndSpace_of_exists_finite_ne
    ⟨false, (Set.finite_singleton [true]).subset fun w hw => by simpa using hw⟩

/-- A plain polynomial-space decider gives membership in `PSPACE`. -/
example : single ∈ PSPACE encBits := by
  obtain ⟨c, h⟩ := exists_computableInTimeAndSpace_single
  have hf : ComputableInPolySpace (fun w : List Bool => decide (w = [true])) encBits encBool :=
    ⟨_, fun _ => 1, by fun_prop, h.mono (fun _ => le_rfl) fun _ => Nat.zero_le _,
      fun _ => by simp⟩
  exact mem_PSPACE_iff_computableTidilyInPolySpace.mpr
    ⟨_, hf.tidy, fun w => by simp [single]⟩

/-- A plain fpt-time decider gives membership in `FPT`, for every parameter. -/
example (κ : List Bool → ℕ) : single ∈ FPT encBits κ := by
  obtain ⟨c, h⟩ := exists_computableInTimeAndSpace_single
  have hf : ComputableInFPTTime (fun w : List Bool => decide (w = [true])) encBits encBool κ :=
    ⟨fun _ => c, 0, h.mono (fun _ => by simp) fun _ => Nat.zero_le _⟩
  exact mem_FPT_iff_computableTidilyInFPTTime.mpr
    ⟨_, hf.tidy, fun w => by simp [single]⟩

/-! ### From library certificates to plain ones -/

/-- The first projection, from its tidy certificate. -/
example : ComputableInO Prod.fst (encPair encBits encBits) encBits
    (fun p => (encPair encBits encBits p).length) fun p => (encPair encBits encBits p).length :=
  .of_tidy (ComputableTidilyInO.fst encBits encBits)

/-- The first projection within linear space, from its tidy certificate. -/
example : ComputableInSpace Prod.fst (encPair encBits encBits) encBits
    fun p => (encPair encBits encBits p).length :=
  (ComputableTidilyInSpace.fst encBits encBits).computableInSpace

/-- A list program certified by `polytime` is computable within polynomial space. -/
example : ComputableInPolySpace
    (fun word : List Bool => word.foldl (fun reversed bit => bit :: reversed) [])
    encBits encBits :=
  computableInPolySpace_iff_computableTidilyInPolySpace.mpr (.of_polyTime (by polytime))

/-- `TQBF` has a plain polynomial-space decider. -/
example : ∃ f, ComputableInPolySpace f encQBF encBool ∧ ∀ φ, φ ∈ TQBF ↔ f φ = true := by
  obtain ⟨f, hf, hA⟩ := mem_PSPACE_iff_computableTidilyInPolySpace.mp TQBF_mem_PSPACE
  exact ⟨f, .of_tidy hf, hA⟩

/-- `SAT` has a plain fpt-time decider in the number of variables. -/
example : ∃ g, ComputableInFPTTime g encCNF encBool Logic.PL.CNF.numVars ∧
    ∀ φ, φ ∈ SAT ↔ g φ = true := by
  obtain ⟨g, hg, hA⟩ := mem_FPT_iff_computableTidilyInFPTTime.mp SAT_mem_FPT
  exact ⟨g, hg.computableInFPTTime, hA⟩

/-! ### Axioms -/

/--
info: 'Turing.MultiTapeTM.ComputableInTimeAndSpace.computableTidilyInO' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComputableInTimeAndSpace.computableTidilyInO

/--
info: 'Turing.MultiTapeTM.computableInO_iff_computableTidilyInO' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms computableInO_iff_computableTidilyInO

/--
info: 'Turing.MultiTapeTM.computableInSpace_iff_computableTidilyInSpace' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms computableInSpace_iff_computableTidilyInSpace

/--
info: 'Turing.MultiTapeTM.computableInPolySpace_iff_computableTidilyInPolySpace' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms computableInPolySpace_iff_computableTidilyInPolySpace

/--
info: 'Cslib.Complexity.computableInFPTTime_iff_computableTidilyInFPTTime' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms computableInFPTTime_iff_computableTidilyInFPTTime

end ComplexityTests.ResourceBoundsPlain
