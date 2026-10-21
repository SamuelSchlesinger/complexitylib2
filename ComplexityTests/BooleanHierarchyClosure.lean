/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import Complexity.Computability.Complexity.Classes.BooleanHierarchy.Closure

/-! Regression tests for Boolean-hierarchy closure and its level bounds. -/

open Cslib.Complexity

-- The generic intersection/difference bounds do not require the base class to contain ∅.
example : (∅ : Set Bool) ∩ ∅ ∈ differenceHierarchy ∅ (0 * 0) :=
  inter_mem_differenceHierarchy (by simp) (by simp) rfl rfl

example : (∅ : Set Bool) \ ∅ ∈ differenceHierarchy ∅ (0 * (0 + 1)) :=
  diff_mem_differenceHierarchy (by simp) (by simp) rfl rfl

-- All sets form a concrete non-vacuous base lattice; its first level contains any language.
example (A B : Set Bool) : A ∩ B ∈ differenceHierarchy Set.univ (1 * 1) :=
  inter_mem_differenceHierarchy (by simp) (by simp)
    (by simp) (by simp)

example (A B : Set Bool) : A \ B ∈ differenceHierarchy Set.univ (1 * (1 + 1)) :=
  diff_mem_differenceHierarchy (by simp) (by simp)
    (by simp) (by simp)

example (A B : Set Bool) : A ∪ B ∈ differenceHierarchy Set.univ ((1 + 1) * (1 + 1) + 1) :=
  union_mem_differenceHierarchy (by simp) (by simp) (by simp)
    (by simp) (by simp)

-- NP languages occur at level one, so the bounds can be used without unfolding the hierarchy.
example {α : Type} {enc : α ↪ List Bool} {A B : Set α}
    (hA : A ∈ NP enc) (hB : B ∈ NP enc) : A ∩ B ∈ BH enc 1 :=
  inter_mem_BH (n := 1) (m := 1) (BH_one.symm ▸ hA) (BH_one.symm ▸ hB)

example {α : Type} {enc : α ↪ List Bool} {A B : Set α}
    (hA : A ∈ NP enc) (hB : B ∈ NP enc) : A \ B ∈ BH enc 2 :=
  diff_mem_BH (n := 1) (m := 1) (BH_one.symm ▸ hA) (BH_one.symm ▸ hB)

/--
info: 'Cslib.Complexity.inter_mem_differenceHierarchy' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms inter_mem_differenceHierarchy

/--
info: 'Cslib.Complexity.diff_mem_differenceHierarchy' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms diff_mem_differenceHierarchy

/--
info: 'Cslib.Complexity.union_mem_differenceHierarchy' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms union_mem_differenceHierarchy

/--
info: 'Cslib.Complexity.inter_mem_BH' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms inter_mem_BH

/--
info: 'Cslib.Complexity.diff_mem_BH' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms diff_mem_BH

/--
info: 'Cslib.Complexity.union_mem_BH' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms union_mem_BH

/--
info: 'Cslib.Complexity.inter_mem_BooleanHierarchy' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms inter_mem_BooleanHierarchy

/--
info: 'Cslib.Complexity.diff_mem_BooleanHierarchy' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms diff_mem_BooleanHierarchy

/--
info: 'Cslib.Complexity.union_mem_BooleanHierarchy' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms union_mem_BooleanHierarchy

/--
info: 'Cslib.Complexity.symmDiff_mem_BooleanHierarchy' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms symmDiff_mem_BooleanHierarchy
