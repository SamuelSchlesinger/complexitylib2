/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.PH.Collapse

/-! Collapses of the polynomial hierarchy, with concrete instances of cutting blocks of
certificates. -/

namespace ComplexityTests.ResourceClasses2

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM

/-! ### Collapses of the polynomial hierarchy -/

/-- Cutting blocks of lengths `X + 1` and `2` at `2`, namely `3` and `2`, to their lengths at `1`,
namely `2` and `2`. -/
example : truncateBlocks [.X + 1, 2] 1 2 [true, false, true, false, true] =
    [true, false, false, true] := by
  simp [truncateBlocks]

/-- Cutting at equal lengths keeps the concatenated blocks. -/
example : truncateBlocks [.X, .X] 2 2 [true, false, true, true] = [true, false, true, true] := by
  simp [truncateBlocks]

/-- The quantifiers over longer blocks, cut, are the quantifiers over shorter blocks. -/
example (P : List Bool → Prop) :
    Alternation true ([Polynomial.X, 1].map fun p => p.eval 3)
        (fun w => P (truncateBlocks [.X, 1] 1 3 w)) ↔
      Alternation true ([Polynomial.X, 1].map fun p => p.eval 1) P :=
  alternation_truncateBlocks (by norm_num)

example {α : Type} (enc : α ↪ List Bool) {k : ℕ} (hk : 1 ≤ k)
    (h : ∀ {β : Type} (encB : β ↪ List Bool), PiP k encB ⊆ SigmaP k encB) :
    PH enc = SigmaP k enc :=
  PH_eq_SigmaP_of_PiP_subset_SigmaP hk h

/-- `Σₖ = Πₖ` collapses `PH` to `Σₖ`, the textbook form. -/
example {α : Type} (enc : α ↪ List Bool) {k : ℕ} (hk : 1 ≤ k)
    (h : ∀ {β : Type} (encB : β ↪ List Bool), SigmaP k encB = PiP k encB) :
    PH enc = SigmaP k enc :=
  PH_eq_SigmaP_of_PiP_subset_SigmaP hk fun encB => (h encB).ge

/-- `NP = coNP` collapses `PH` to `NP`. -/
example {α : Type} (enc : α ↪ List Bool)
    (h : ∀ {β : Type} (encB : β ↪ List Bool), NP encB = coNP encB) :
    PH enc = NP enc :=
  PH_eq_NP_of_coNP_subset_NP fun encB => (h encB).ge

/-- `P = NP` collapses `PH` to `P`, and then `PH = NP` too. -/
example {α : Type} (enc : α ↪ List Bool)
    (h : ∀ {β : Type} (encB : β ↪ List Bool), P encB = NP encB) :
    PH enc = P enc ∧ PH enc = NP enc :=
  ⟨PH_eq_P_of_NP_subset_P fun encB => (h encB).ge,
    (PH_eq_P_of_NP_subset_P fun encB => (h encB).ge).trans (h enc)⟩

/-- The collapse at the second level, as used by the Karp–Lipton theorem. -/
example {α : Type} (enc : α ↪ List Bool)
    (h : ∀ {β : Type} (encB : β ↪ List Bool), SigmaP 3 encB ⊆ SigmaP 2 encB) :
    PH enc = SigmaP 2 enc :=
  PH_eq_SigmaP_of_SigmaP_succ_subset_SigmaP h

/-- At `k = 0` the hypothesis `Π₀ ⊆ Σ₀` holds outright, both levels being `P`, which is why the
collapse from `Πₖ ⊆ Σₖ` needs `1 ≤ k`. -/
example {β : Type} (encB : β ↪ List Bool) : PiP 0 encB ⊆ SigmaP 0 encB := by
  rw [PiP_zero, SigmaP_zero]

/-- At `k = 0`, `Σ₁ ⊆ Σ₀` is `NP ⊆ P`, which collapses `PH` to `Σ₀ = P`. -/
example {α : Type} (enc : α ↪ List Bool)
    (h : ∀ {β : Type} (encB : β ↪ List Bool), NP encB ⊆ P encB) : PH enc = SigmaP 0 enc :=
  PH_eq_SigmaP_of_SigmaP_succ_subset_SigmaP fun encB => by
    simpa only [zero_add, SigmaP_one, SigmaP_zero] using h encB

/-! ### Axioms -/

/--
info: 'Cslib.Complexity.SigmaP_succ_subset_SigmaP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.SigmaP_succ_subset_SigmaP

/--
info: 'Cslib.Complexity.PH_eq_SigmaP_of_PiP_subset_SigmaP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PH_eq_SigmaP_of_PiP_subset_SigmaP

/--
info: 'Cslib.Complexity.PH_eq_NP_of_coNP_subset_NP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PH_eq_NP_of_coNP_subset_NP

/--
info: 'Cslib.Complexity.PH_eq_P_of_NP_subset_P' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PH_eq_P_of_NP_subset_P

/--
info: 'Cslib.Complexity.PH_eq_SigmaP_of_SigmaP_succ_subset_SigmaP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PH_eq_SigmaP_of_SigmaP_succ_subset_SigmaP

end ComplexityTests.ResourceClasses2
