/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.BPP.Collapse
import Complexity.Computability.Complexity.Classes.P.Complement
import Complexity.Computability.Complexity.Classes.PCP.ZeroRandomness
import Complexity.Computability.Complexity.Classes.PP.Characterization
import Complexity.Computability.Complexity.Classes.RP.Closure
import Complexity.Computability.Complexity.Classes.SharpP.Closure
import Complexity.Computability.Complexity.Classes.SharpP.Combinators
import Complexity.Computability.Complexity.Problems.ExactThreeSAT

/-! Verifier combinators on concrete verifiers, closure properties of `#P`, `GapP`, `PP`, `RP`,
`coRP` and `ZPP` applied to concrete problems, non-vacuity witnesses for the new conditions, and
axiom guards. -/

namespace ComplexityTests.ClassClosure

open Cslib Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Verifier combinators -/

/-- Reading the first bit and ignoring two more: `1 * 2 ^ 2` accepted strings of length `3`. -/
example : acceptCount (andVerifier (fun _ : Unit => 1) (fun x => x.2.headD false) fun _ => true)
    () (1 + 2) = 4 := by
  rw [acceptCount_andVerifier_true]
  decide

/-- Two strings of length `2` start with `true`, one is all `false`: three choices in total. -/
example : acceptCount (selectVerifier (allFalseVerifier : Unit × List Bool → Bool)
    fun x => x.2.headD false) () (2 + 1) = 3 := by
  rw [acceptCount_selectVerifier, acceptCount_allFalseVerifier]
  decide

/-- With no bits, a verifier accepts the empty string or nothing. -/
example : acceptCount (fun x : Unit × List Bool => x.2.isEmpty) () 0 = 1 := by
  rw [acceptCount_zero]
  rfl

/-! ### `#P` and `GapP` -/

example : (1 : List Bool → ℕ) + 1 ∈ SharpP encBits :=
  SharpP.add_one_mem SharpP.one_mem

example : (fun w : List Bool => 2 ^ Polynomial.X.eval (encBits w).length) *
    (fun w => 2 ^ Polynomial.X.eval (encBits w).length) ∈ SharpP encBits :=
  SharpP.mul_mem (SharpP.two_pow_mem _) (SharpP.two_pow_mem _)

example : (fun _ : List Bool => (1 : ℤ)) * (fun _ => (1 : ℤ)) - (fun _ => (1 : ℤ)) ∈
    GapP encBits := by
  have h : (fun _ : List Bool => (1 : ℤ)) ∈ GapP encBits := by
    simpa using SharpP.natCast_mem_GapP (SharpP.one_mem (enc := encBits))
  exact GapP.sub (GapP.mul h h) h

/-! ### `PP` -/

/-- The non-strict majority condition is satisfiable: the constant verifier `true` accepts all of
the single random string of length `0`. -/
example : Set.univ ∈ PP encBits :=
  mem_PP_iff_decidesByNonstrictMajority.2 ⟨0, fun _ => true, .const true, fun _ => by simp⟩

example : ∃ g ∈ GapP encBits, ∀ w, w ∈ (Set.univ : Set (List Bool)) ↔ 0 < g w :=
  mem_PP_iff_exists_GapP.1 (mem_PP_iff_decidesByNonstrictMajority.2
    ⟨0, fun _ => true, .const true, fun _ => by simp⟩)

/-! ### `P`, `RP`, `coRP` and `ZPP` -/

/-- The words starting with `true`. -/
theorem headD_mem_P : {w : List Bool | w.headD false = true} ∈ P encBits :=
  ⟨fun w => w.headD false, by fun_prop, fun _ => Iff.rfl⟩

example : {w : List Bool | w.headD false = true}ᶜ ∈ coNP encBits :=
  P_subset_coNP (compl_mem_P headD_mem_P)

example : {w : List Bool | w.headD false = true} ∪ {w | w.headD false = true}ᶜ ∈ RP encBits :=
  union_mem_RP (P_subset_RP headD_mem_P) (P_subset_RP (compl_mem_P headD_mem_P))

example : {w : List Bool | w.headD false = true} ∩ {w | w.headD false = true}ᶜ ∈ ZPP encBits :=
  inter_mem_ZPP (P_subset_ZPP headD_mem_P) (P_subset_ZPP (compl_mem_P headD_mem_P))

example : {w : List Bool | w.headD false = true} ∈ PCP (fun _ => 0) (fun _ => 0) encBits :=
  PCP_zero_zero.symm ▸ headD_mem_P

/-! ### Exact 3SAT -/

example : ExactThreeSAT.padClause [(0, true)] = [(0, true), (0, true), (0, true)] := by decide

example : ExactThreeSAT.padClause [(0, true), (1, false)] = [(0, true), (1, false), (0, true)] := by
  decide

/-- A satisfiable formula with one clause of three literals. -/
example : [[(0, true), (1, false), (0, true)]] ∈ ExactThreeSAT :=
  ⟨by decide, fun _ => true, by decide⟩

/-! ### Axiom guards -/

/--
info: 'Cslib.Complexity.SharpP.add_mem' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.SharpP.add_mem

/--
info: 'Cslib.Complexity.SharpP.mul_mem' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.SharpP.mul_mem

/--
info: 'Cslib.Complexity.GapP.mul' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.GapP.mul

/--
info: 'Cslib.Complexity.mem_PP_iff_decidesByNonstrictMajority' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_PP_iff_decidesByNonstrictMajority

/--
info: 'Cslib.Complexity.PolyTimeReducible.mem_PP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PolyTimeReducible.mem_PP

/--
info: 'Cslib.Complexity.mem_PP_iff_exists_SharpP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_PP_iff_exists_SharpP

/--
info: 'Cslib.Complexity.mem_PP_iff_exists_GapP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_PP_iff_exists_GapP

/--
info: 'Cslib.Complexity.union_mem_RP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.union_mem_RP

/--
info: 'Cslib.Complexity.inter_mem_RP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.inter_mem_RP

/--
info: 'Cslib.Complexity.PCP_zero_zero' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PCP_zero_zero

/--
info: 'Cslib.Complexity.mem_NP_iff_exists_PCP_zero' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_NP_iff_exists_PCP_zero

/--
info: 'Cslib.Complexity.ExactThreeSAT_npComplete' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.ExactThreeSAT_npComplete

/--
info: 'Cslib.Complexity.BPP_eq_P_of_NP_subset_P' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.BPP_eq_P_of_NP_subset_P

end ComplexityTests.ClassClosure
