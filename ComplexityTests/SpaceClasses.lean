/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.Constructible
import Complexity.Computability.Complexity.Classes.LogSpace
import Complexity.Computability.Complexity.Classes.Space.Time
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant

/-! Generic space-class and constructibility clients, without hierarchy imports.
The concrete zero-space instance and constructible bounds exercise satisfiable hypotheses. -/

namespace ComplexityTests.SpaceClasses

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM

/-! ### A problem in constant space -/

/-- Every word is accepted in zero space. -/
private theorem univ_mem_DSPACE : (Set.univ : Set (List Bool)) ∈ DSPACE encBits fun _ => 0 := by
  obtain ⟨c, h⟩ := computableInTimeAndSpace_of_const (α := List Bool) (encIn := encBits)
    (encOut := encBool) true
  exact mem_DSPACE_iff.mpr ⟨0, 0, _, decidableInTimeAndSpace_iff.mpr
    ⟨_, h.mono (fun _ => le_rfl) fun _ => le_rfl, fun _ => by simp⟩⟩

/-- It is decided within time `O((n + 2) * 2 ^ (c * 0))`, by counting configurations. -/
example : ∃ c, (Set.univ : Set (List Bool)) ∈ DTIME encBits fun n => (n + 2) * 2 ^ (c * 0) :=
  exists_mem_DTIME_of_mem_DSPACE univ_mem_DSPACE

/-! ### Space-constructible bounds -/

example : SpaceConstructible fun n => n := spaceConstructible_id

example : SpaceConstructible fun n => n + 1 := spaceConstructible_succ

example : SpaceConstructible fun n => (n + 1) ^ 3 := spaceConstructible_succ_pow 3

example : SpaceConstructible fun _ => 5 := spaceConstructible_const 5

example : SpaceConstructible (2 ^ ·) := spaceConstructible_two_pow

/-- `L` and `PSPACE` through `DSPACE`, as in cslib pull request #767. -/
example (A : Set (List Bool)) : A ∈ L encBits ↔ A ∈ DSPACE encBits Nat.log2 := mem_L_iff_mem_DSPACE

example (A : Set (List Bool)) : A ∈ PSPACE encBits ↔ ∃ k, A ∈ DSPACE encBits (· ^ k) :=
  mem_PSPACE_iff_exists_mem_DSPACE

/-! ### Axioms -/

/--
info: 'Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_time_two_pow' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_time_two_pow

/--
info: 'Cslib.Complexity.mem_DSPACE_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_DSPACE_iff

/--
info: 'Cslib.Complexity.exists_mem_DTIME_of_mem_DSPACE' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.exists_mem_DTIME_of_mem_DSPACE

/--
info: 'Cslib.Complexity.mem_L_iff_mem_DSPACE' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_L_iff_mem_DSPACE

/--
info: 'Cslib.Complexity.mem_PSPACE_iff_exists_mem_DSPACE' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_PSPACE_iff_exists_mem_DSPACE

end ComplexityTests.SpaceClasses
