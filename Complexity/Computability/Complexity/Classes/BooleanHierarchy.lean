/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.DP
import Complexity.Computability.Complexity.Classes.NP.Witness

/-!
# The Boolean hierarchy over NP

The difference hierarchy iterates `A ∖ B`, with `A` in a base class and `B` at the previous
level. Level zero is the singleton class containing the empty language. Over NP, level one is
NP and level two is DP. This is the difference-hierarchy presentation of the Boolean hierarchy
[Cai et al.][CaiEtAl1988]. The generic construction and inverse-image theorem apply to any
base class; the elementary results below do not establish strictness or collapse theorems.

## Main definitions

* `differenceHierarchy`: finite nested differences over an arbitrary class of sets.
* `BH`, `BooleanHierarchy`: the levels over NP and their union.

## Main results

* `BH_one`, `BH_two`: the first levels are NP and DP.
* `BH_mono`, `compl_mem_BH_succ`: increasing levels and complement at the next level.
* `PolyTimeReducible.mem_BH`: level-preserving many-one reduction closure.

## References

* [J.-Y. Cai et al., *The Boolean Hierarchy I: Structural Properties*][CaiEtAl1988]
-/

@[expose] public section

namespace Cslib.Complexity

variable {α β : Type*}

/-- Nested differences over `C`, starting with just the empty set. -/
def differenceHierarchy (C : Set (Set α)) : ℕ → Set (Set α)
  | 0 => {∅}
  | n + 1 => {A | ∃ B ∈ C, ∃ D ∈ differenceHierarchy C n, A = B \ D}

/-- At level one, taking a difference with the empty set recovers the base class. -/
@[simp]
theorem differenceHierarchy_one (C : Set (Set α)) : differenceHierarchy C 1 = C := by
  ext A
  simp [differenceHierarchy]

/-- Inverse images preserve every level whenever they preserve the base classes. -/
theorem preimage_mem_differenceHierarchy {C : Set (Set α)} {D : Set (Set β)}
    {f : α → β} (hf : ∀ B ∈ D, f ⁻¹' B ∈ C) {n : ℕ} {A : Set β}
    (hA : A ∈ differenceHierarchy D n) : f ⁻¹' A ∈ differenceHierarchy C n := by
  induction n generalizing A with
  | zero =>
    have h : A = ∅ := hA
    subst h
    exact Set.preimage_empty
  | succ n ih =>
    obtain ⟨B, hB, E, hE, rfl⟩ := hA
    exact ⟨f ⁻¹' B, hf B hB, f ⁻¹' E, ih hE, rfl⟩

/-- Empty membership makes the levels increasing. -/
theorem differenceHierarchy_subset_succ {C : Set (Set α)} (hC : ∅ ∈ C) (n : ℕ) :
    differenceHierarchy C n ⊆ differenceHierarchy C (n + 1) := by
  induction n with
  | zero =>
    intro A hA
    have h : A = ∅ := hA
    subst h
    exact ⟨∅, hC, ∅, rfl, by simp⟩
  | succ n ih =>
    rintro A ⟨B, hB, D, hD, rfl⟩
    exact ⟨B, hB, D, ih hD, rfl⟩

/-- If the universe belongs to the base class, complementation costs one level. -/
theorem compl_mem_differenceHierarchy_succ {C : Set (Set α)} (hC : Set.univ ∈ C)
    {n : ℕ} {A : Set α} (hA : A ∈ differenceHierarchy C n) :
    Aᶜ ∈ differenceHierarchy C (n + 1) :=
  ⟨Set.univ, hC, A, hA, by ext a; simp⟩

variable {α β : Type} {enc : α ↪ List Bool} {A : Set α}

/-- The `n`th level of the Boolean hierarchy over NP, with level zero containing only `∅`. -/
def BH (enc : α ↪ List Bool) (n : ℕ) : Set (Set α) := differenceHierarchy (NP enc) n

/-- The union of all finite levels of the Boolean hierarchy over NP. -/
def BooleanHierarchy (enc : α ↪ List Bool) : Set (Set α) := ⋃ n, BH enc n

@[simp]
theorem BH_one : BH enc 1 = NP enc := differenceHierarchy_one _

/-- The second level is precisely DP. -/
theorem BH_two : BH enc 2 = DP enc := by
  ext A
  change (∃ B ∈ NP enc, ∃ D ∈ differenceHierarchy (NP enc) 1, A = B \ D) ↔ _
  rw [differenceHierarchy_one, mem_DP_iff_diff]

/-- The levels of the Boolean hierarchy are increasing. -/
theorem BH_mono : Monotone (BH enc) := by
  apply monotone_nat_of_le_succ
  exact differenceHierarchy_subset_succ (show ∅ ∈ NP enc from
    ⟨0, fun _ => false, .const _, by simp [IsVerifier]⟩)

/-- Complementation moves a language at most one level up. -/
theorem compl_mem_BH_succ {n : ℕ} (hA : A ∈ BH enc n) : Aᶜ ∈ BH enc (n + 1) :=
  compl_mem_differenceHierarchy_succ (show Set.univ ∈ NP enc from
    ⟨0, fun _ => true, .const _, by simp [IsVerifier]⟩) hA

/-- The union of the finite levels is closed under complement. -/
theorem compl_mem_BooleanHierarchy (hA : A ∈ BooleanHierarchy enc) :
    Aᶜ ∈ BooleanHierarchy enc := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hA
  exact Set.mem_iUnion.mpr ⟨n + 1, compl_mem_BH_succ hn⟩

/-- Many-one reductions preserve each finite level. -/
theorem PolyTimeReducible.mem_BH {encB : β ↪ List Bool} {B : Set β} {n : ℕ}
    (h : PolyTimeReducible enc encB A B) (hB : B ∈ BH encB n) : A ∈ BH enc n := by
  obtain ⟨f, hf, hAB⟩ := h
  have h := preimage_mem_differenceHierarchy
    (fun D hD => PolyTimeReducible.mem_NP ⟨f, hf, fun _ => Iff.rfl⟩ hD) hB
  rwa [show f ⁻¹' B = A from Set.ext fun a => (hAB a).symm] at h

end Cslib.Complexity
