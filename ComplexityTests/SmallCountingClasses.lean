/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.SPP
import Complexity.Computability.Complexity.Classes.FewP
import Complexity.Computability.Complexity.Classes.ModP
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! Concrete clients for small counting classes, including nonconstant characteristic functions,
multiple witnesses, prime and composite moduli, and degenerate moduli. -/

namespace ComplexityTests.SmallCountingClasses

open Cslib Cslib.Complexity Turing.MultiTapeTM

private theorem head_mem_P : {w : List Bool | w.headD false = true} ∈ P encBits :=
  ⟨fun w => w.headD false, by fun_prop, fun _ => Iff.rfl⟩

private theorem head_mem_SPP : {w : List Bool | w.headD false = true} ∈ SPP encBits :=
  UP_subset_SPP (P_subset_UP head_mem_P)

example : {w : List Bool | w.headD false = true}ᶜ ∈ SPP encBits :=
  compl_mem_SPP head_mem_SPP

example : {w : List Bool | w.headD false = true} ∪ {w | w.headD false = true}ᶜ ∈ SPP encBits :=
  union_mem_SPP head_mem_SPP (compl_mem_SPP head_mem_SPP)

example : {w : List Bool | w.headD false = true} ∩ {w | w.headD false = true}ᶜ ∈ SPP encBits :=
  inter_mem_SPP head_mem_SPP (compl_mem_SPP head_mem_SPP)

example : Set.univ ∈ SPP encBits :=
  ⟨1, GapP.one_mem, fun _ => Or.inr rfl, fun _ => by simp⟩

example : (∅ : Set (List Bool)) ∈ SPP encBits :=
  ⟨0, GapP.zero_mem, fun _ => Or.inl rfl, fun _ => by simp⟩

example : {w : List Bool | w.headD false = true} ∈ CeqP encBits ∩ coCeqP encBits :=
  ⟨SPP_subset_CeqP head_mem_SPP, SPP_subset_coCeqP head_mem_SPP⟩

/-- A verifier with two accepting certificates satisfies FewP's bound; no uniqueness is assumed. -/
private theorem univ_mem_FewP : Set.univ ∈ FewP encBits := by
  refine mem_FewP.mpr ⟨1, 2, fun _ => true, .const true, ?_, ?_⟩ <;> intro a <;> simp

example : (∅ : Set (List Bool)) ∈ FewP encBits :=
  ⟨0, SharpP.zero_mem, 0, fun _ => by simp, fun _ => by simp⟩

example : {w : List Bool | w.headD false = true} ∪ Set.univ ∈ FewP encBits :=
  union_mem_FewP (UP_subset_FewP (P_subset_UP head_mem_P)) univ_mem_FewP

example : {w : List Bool | w.headD false = true} ∩ Set.univ ∈ FewP encBits :=
  inter_mem_FewP (UP_subset_FewP (P_subset_UP head_mem_P)) univ_mem_FewP

private theorem tail_reduces_head : PolyTimeReducible encBits encBits
    {w : List Bool | w.tail.headD false = true} {w | w.headD false = true} :=
  ⟨List.tail, by fun_prop, fun _ => Iff.rfl⟩

example : {w : List Bool | w.tail.headD false = true} ∈ FewP encBits :=
  tail_reduces_head.mem_FewP (UP_subset_FewP (P_subset_UP head_mem_P))

example : {w : List Bool | w.tail.headD false = true} ∈ SPP encBits :=
  tail_reduces_head.mem_SPP head_mem_SPP

example : {w : List Bool | w.headD false = true}ᶜ ∈ coUP encBits :=
  compl_mem_coUP.mpr (P_subset_UP head_mem_P)

example : SAT ∈ coCeqP encCNF := NP_subset_coCeqP SAT.mem_NP
example : SAT ∈ PP encCNF := coCeqP_subset_PP (NP_subset_coCeqP SAT.mem_NP)

/-- Count two has a nonzero residue mod three, although it is even. -/
example : Set.univ ∈ ModP 3 encBits := ⟨2, SharpP.natCast_mem 2, fun _ => by norm_num⟩

/-- Composite moduli are permitted in the definition and basic containments. -/
example : {w : List Bool | w.headD false = true} ∈ ModP 6 encBits :=
  P_subset_ModP (by decide) head_mem_P

example : {w : List Bool | w.tail.headD false = true} ∈ ModP 6 encBits :=
  tail_reduces_head.mem_ModP (P_subset_ModP (by decide) head_mem_P)

example : ModP 2 encBits = ParityP encBits := ModP_two
example : ModP 0 encBits = NP encBits := ModP_zero
example : (∅ : Set (List Bool)) ∈ ModP 1 encBits := mem_ModP_one.mpr rfl
example : Set.univ ∉ ModP 1 encBits := by simp [mem_ModP_one]

example : {w : List Bool | w.headD false = true}ᶜ ∈ ModP 3 encBits :=
  compl_mem_ModP (by decide) (P_subset_ModP (by decide) head_mem_P)

example : {w : List Bool | w.headD false = true} ∩ {w | w.headD false = true}ᶜ ∈
    ModP 3 encBits := inter_mem_ModP (by decide) (P_subset_ModP (by decide) head_mem_P)
      (compl_mem_ModP (by decide) (P_subset_ModP (by decide) head_mem_P))

example : {w : List Bool | w.headD false = true} ∪ {w | w.headD false = true}ᶜ ∈
    ModP 3 encBits := union_mem_ModP (by decide) (P_subset_ModP (by decide) head_mem_P)
      (compl_mem_ModP (by decide) (P_subset_ModP (by decide) head_mem_P))

/-- Why the product argument needs primality: two nonzero residues can multiply to zero. -/
example : 2 % 6 ≠ 0 ∧ 3 % 6 ≠ 0 ∧ (2 * 3) % 6 = 0 := by decide

/-! Headline axiom guards. -/

/--
info: 'Cslib.Complexity.UP_subset_SPP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.UP_subset_SPP

/--
info: 'Cslib.Complexity.compl_mem_SPP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.compl_mem_SPP

/--
info: 'Cslib.Complexity.inter_mem_SPP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.inter_mem_SPP

/--
info: 'Cslib.Complexity.SPP_subset_CeqP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.SPP_subset_CeqP

/--
info: 'Cslib.Complexity.SPP_subset_coCeqP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.SPP_subset_coCeqP

/--
info: 'Cslib.Complexity.PolyTimeReducible.mem_SPP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PolyTimeReducible.mem_SPP

/--
info: 'Cslib.Complexity.UP_subset_FewP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.UP_subset_FewP

/--
info: 'Cslib.Complexity.FewP_subset_NP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.FewP_subset_NP

/--
info: 'Cslib.Complexity.union_mem_FewP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.union_mem_FewP

/--
info: 'Cslib.Complexity.inter_mem_FewP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.inter_mem_FewP

/--
info: 'Cslib.Complexity.PolyTimeReducible.mem_FewP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PolyTimeReducible.mem_FewP

/--
info: 'Cslib.Complexity.ModP_two' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.ModP_two

/--
info: 'Cslib.Complexity.P_subset_ModP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.P_subset_ModP

/--
info: 'Cslib.Complexity.compl_mem_ModP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.compl_mem_ModP

/--
info: 'Cslib.Complexity.inter_mem_ModP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.inter_mem_ModP

/--
info: 'Cslib.Complexity.union_mem_ModP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.union_mem_ModP

/--
info: 'Cslib.Complexity.PolyTimeReducible.mem_ModP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PolyTimeReducible.mem_ModP

/--
info: 'Cslib.Complexity.P_subset_coUP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.P_subset_coUP

/--
info: 'Cslib.Complexity.coUP_subset_coNP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.coUP_subset_coNP

/--
info: 'Cslib.Complexity.NP_subset_coCeqP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.NP_subset_coCeqP

/--
info: 'Cslib.Complexity.coCeqP_subset_PP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.coCeqP_subset_PP

end ComplexityTests.SmallCountingClasses
