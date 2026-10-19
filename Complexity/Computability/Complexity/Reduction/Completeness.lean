/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Reduction

/-!
# Hardness and completeness for a class

A class of problems is given, as `NP`, `PP` or `ModP k`, by a set of problems for every type of
instances and every encoding of them. A problem `B` is hard for such a class `C` under
polynomial-time many-one reductions when every problem in `C`, with any encoding of its
instances, reduces to `B` (`PolyTimeHard C encB B`), and complete when it also belongs to `C`
(`PolyTimeComplete C encB B`) [Arora and Barak, Definition 2.7][AroraBarak09]. `NPHard` and
`NPComplete` are the instances for `NP` (`polyTimeHard_NP_iff`, `polyTimeComplete_NP_iff`).

When the problems of a class `D` are the complements of those of `C`, as `coNP` and `NP`, the
complement of a `C`-complete problem is `D`-complete (`PolyTimeComplete.compl`).

## Main definitions

* `Cslib.Complexity.PolyTimeHard`, `Cslib.Complexity.PolyTimeComplete`.

## Main results

* `Cslib.Complexity.PolyTimeHard.trans`: hardness transfers along polynomial-time reductions.
* `Cslib.Complexity.PolyTimeHard.compl`, `Cslib.Complexity.PolyTimeComplete.compl`: complements
  of hard and complete problems.
* `Cslib.Complexity.polyTimeHard_NP_iff`, `Cslib.Complexity.polyTimeComplete_NP_iff`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

variable {β γ : Type}

/-- `B` is hard for the class `C` under polynomial-time many-one reductions: every problem in `C`,
with any encoding of its instances, reduces to `B`. -/
def PolyTimeHard (C : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)) (encB : β ↪ List Bool)
    (B : Set β) : Prop :=
  ∀ {α : Type} (enc : α ↪ List Bool) (A : Set α), A ∈ C enc → PolyTimeReducible enc encB A B

/-- `B` is complete for the class `C` under polynomial-time many-one reductions: it is in `C` and
every problem in `C` reduces to it. -/
def PolyTimeComplete (C : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)) (encB : β ↪ List Bool)
    (B : Set β) : Prop :=
  B ∈ C encB ∧ PolyTimeHard C encB B

variable {C D : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)} {encB : β ↪ List Bool}
  {encC : γ ↪ List Bool} {B : Set β} {B' : Set γ}

/-- Hardness transfers along a polynomial-time reduction. -/
theorem PolyTimeHard.trans (hB : PolyTimeHard C encB B) (hBB' : PolyTimeReducible encB encC B B') :
    PolyTimeHard C encC B' :=
  fun enc A hA => (hB enc A hA).trans hBB'

/-- If the complement of every problem in `D` is in `C`, the complement of a `C`-hard problem is
`D`-hard. -/
theorem PolyTimeHard.compl (hDC : ∀ {α : Type} (enc : α ↪ List Bool) (A : Set α), A ∈ D enc →
    Aᶜ ∈ C enc) (hB : PolyTimeHard C encB B) : PolyTimeHard D encB Bᶜ :=
  fun enc A hA => by simpa using (hB enc Aᶜ (hDC enc A hA)).compl

/-- If the problems in `D` are exactly the complements of the problems in `C`, the complement of
a `C`-complete problem is `D`-complete. -/
theorem PolyTimeComplete.compl (hDC : ∀ {α : Type} (enc : α ↪ List Bool) (A : Set α),
    A ∈ D enc ↔ Aᶜ ∈ C enc) (hB : PolyTimeComplete C encB B) : PolyTimeComplete D encB Bᶜ :=
  ⟨(hDC encB Bᶜ).2 (by simpa using hB.1),
    PolyTimeHard.compl (fun enc A hA => (hDC enc A).1 hA) hB.2⟩

theorem polyTimeHard_NP_iff : PolyTimeHard NP encB B ↔ NPHard encB B := Iff.rfl

theorem polyTimeComplete_NP_iff : PolyTimeComplete NP encB B ↔ NPComplete encB B := Iff.rfl

end Cslib.Complexity
