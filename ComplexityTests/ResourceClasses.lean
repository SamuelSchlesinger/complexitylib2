/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.Inclusions
import Complexity.Computability.Complexity.Classes.Ladner
import Complexity.Computability.Complexity.Classes.ZPP

/-! The parametric time classes and their polynomial unions, exponential time, `ZPP`, and the
inclusions between the standard classes, with concrete members witnessing that the classes are
not vacuous. -/

namespace ComplexityTests.ResourceClasses

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM

/-- Everything is decided by the constant `true`. -/
theorem univ_mem_P : (Set.univ : Set (List Bool)) ∈ P encBits :=
  ⟨fun _ => true, .const true, fun _ => by simp⟩

/-! ### Time classes -/

example {α : Type} (enc : α ↪ List Bool) (A : Set α) :
    A ∈ NP enc ↔ ∃ k, A ∈ NTIME enc (· ^ k) :=
  mem_NP_iff_exists_mem_NTIME

example {α : Type} (enc : α ↪ List Bool) (A : Set α) :
    A ∈ BPP enc ↔ ∃ k, A ∈ BPTIME enc (· ^ k) :=
  mem_BPP_iff_exists_mem_BPTIME

example {α : Type} (enc : α ↪ List Bool) (t : ℕ → ℕ) : DTIME enc t ⊆ NTIME enc t :=
  DTIME_subset_NTIME

/-- A fair-coin machine decides everything with bounded error in polynomial time: the
bounded-error condition on fair-coin machines is satisfiable. -/
example : ∃ k, (Set.univ : Set (List Bool)) ∈ BPTIME encBits (· ^ k) :=
  mem_BPP_iff_exists_mem_BPTIME.mp (P_subset_BPP univ_mem_P)

/-- A nondeterministic machine decides everything in polynomial time. -/
example : ∃ k, (Set.univ : Set (List Bool)) ∈ NTIME encBits (· ^ k) :=
  mem_NP_iff_exists_mem_NTIME.mp (P_subset_NP univ_mem_P)

/-- The diagonal problem, outside `P`, is in nondeterministic exponential time. -/
example : {x | diagonal x = true} ∈ NEXP encBits ∧ {x | diagonal x = true} ∉ P encBits :=
  ⟨EXP_subset_NEXP setOf_diagonal_mem_EXP, diagonal_notMem_P⟩

/-! ### Exponential time -/

example {α : Type} (enc : α ↪ List Bool) : P enc ⊆ E enc ∧ E enc ⊆ EXP enc :=
  ⟨P_subset_E, E_subset_EXP⟩

example {α : Type} (enc : α ↪ List Bool) : NP enc ⊆ NE enc ∧ NE enc ⊆ NEXP enc :=
  ⟨NP_subset_NE, NE_subset_NEXP⟩

example {α : Type} (enc : α ↪ List Bool) : E enc ⊆ NE enc ∧ EXP enc ⊆ NEXP enc :=
  ⟨E_subset_NE, EXP_subset_NEXP⟩

/-! ### `ZPP` -/

example {α : Type} (enc : α ↪ List Bool) : ZPP enc = RP enc ∩ coRP enc := ZPP_eq_RP_inter_coRP

/-- Answering `some true` on every random string decides everything with zero error: the
zero-error condition is satisfiable. -/
theorem univ_mem_ZPP : (Set.univ : Set (List Bool)) ∈ ZPP encBits :=
  ⟨0, fun _ => some true, .const _, fun a => ⟨fun _ _ hb => by simp_all, by
    simp only [Option.isSome_some, Finset.filter_true, Polynomial.eval_zero, pow_zero]
    refine le_trans (by norm_num) (Nat.mul_le_mul_left 2 (Finset.card_pos.mpr ?_))
    exact Finset.univ_nonempty⟩⟩

/-- Its complement is in `ZPP` too, so `ZPP` has a member outside `RP`'s trivial witnesses. -/
example : (∅ : Set (List Bool)) ∈ ZPP encBits := by
  simpa using compl_mem_ZPP univ_mem_ZPP

example : (Set.univ : Set (List Bool)) ∈ RP encBits ∩ coRP encBits :=
  ZPP_eq_RP_inter_coRP ▸ univ_mem_ZPP

/-! ### Probabilistic inclusions -/

example {α : Type} (enc : α ↪ List Bool) : P enc ⊆ BPP enc := P_subset_BPP

example {α : Type} (enc : α ↪ List Bool) : NP enc ⊆ PP enc := NP_subset_PP

example {α : Type} (enc : α ↪ List Bool) (A : Set α) (hA : A ∈ PP enc) : Aᶜ ∈ PP enc :=
  compl_mem_PP hA

/-- `coNP ⊆ PP`, by closure under complement. -/
example {α : Type} (enc : α ↪ List Bool) : coNP enc ⊆ PP enc := fun A hA => by
  simpa using compl_mem_PP (NP_subset_PP hA)

/-! ### Space and exponential time -/

/-- The chain `P ⊆ NP ⊆ PSPACE ⊆ EXP`. -/
example {α : Type} (enc : α ↪ List Bool) :
    P enc ⊆ NP enc ∧ NP enc ⊆ PSPACE enc ∧ PSPACE enc ⊆ EXP enc :=
  ⟨P_subset_NP, NP_subset_PSPACE, PSPACE_subset_EXP⟩

example {α : Type} (enc : α ↪ List Bool) : PH enc ⊆ PSPACE enc := PH_subset_PSPACE

/-- `coNP ⊆ PSPACE`, by closure under complement. -/
example {α : Type} (enc : α ↪ List Bool) : coNP enc ⊆ PSPACE enc := fun A hA => by
  simpa using compl_mem_PSPACE (NP_subset_PSPACE hA)

/-- The bounded existential over a problem in `PSPACE`: the words with an extension of their own
length in a `PSPACE` problem. -/
example {B : Set (List Bool × List Bool)} (hB : B ∈ PSPACE (encPair encBits encBits)) :
    {x | ∃ w : List Bool, w.length = x.length ∧ (x, w) ∈ B} ∈ PSPACE encBits :=
  setOf_exists_mem_PSPACE hB (ComputableTidilyInPolyTime.encoding_length encBits)

/-! ### Axioms -/

/--
info: 'Cslib.Complexity.mem_NP_iff_exists_mem_NTIME' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_NP_iff_exists_mem_NTIME

/--
info: 'Cslib.Complexity.mem_BPP_iff_exists_mem_BPTIME' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_BPP_iff_exists_mem_BPTIME

/--
info: 'Cslib.Complexity.DTIME_subset_NTIME' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.DTIME_subset_NTIME

/--
info: 'Cslib.Complexity.NP_subset_NEXP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.NP_subset_NEXP

/--
info: 'Cslib.Complexity.ZPP_eq_RP_inter_coRP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.ZPP_eq_RP_inter_coRP

/--
info: 'Cslib.Complexity.compl_mem_PP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.compl_mem_PP

/--
info: 'Cslib.Complexity.NP_subset_PP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.NP_subset_PP

/--
info: 'Cslib.Complexity.P_subset_BPP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.P_subset_BPP

/--
info: 'Cslib.Complexity.NP_subset_PSPACE' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.NP_subset_PSPACE

/--
info: 'Cslib.Complexity.PSPACE_subset_EXP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PSPACE_subset_EXP

/--
info: 'Cslib.Complexity.setOf_exists_mem_PSPACE' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.setOf_exists_mem_PSPACE

/--
info: 'Cslib.Complexity.PH_subset_PSPACE' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PH_subset_PSPACE

end ComplexityTests.ResourceClasses
