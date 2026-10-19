/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.ParityP
public import Complexity.Computability.Complexity.Reduction
public import Complexity.Computability.Complexity.Classes.SharpP.Closure
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# Unambiguous polynomial time

`UP` is defined using polynomial-time verifiers with at most one accepting certificate of the
specified polynomial length on every input. This file uses the verifier formulation; it does not
assert an unambiguous nondeterministic-machine characterization.

## Main definitions

* `Cslib.Complexity.UP`: languages whose characteristic function belongs to `#P`.

## Main results

* `Cslib.Complexity.mem_UP`: the at-most-one-witness characterization.
* `Cslib.Complexity.P_subset_UP`, `Cslib.Complexity.UP_subset_NP`,
  `Cslib.Complexity.UP_subset_ParityP`.
* `Cslib.Complexity.PolyTimeReducible.mem_UP`: closure under polynomial-time reductions.

## References

* [C. H. Papadimitriou, *Computational Complexity*][Papadimitriou94]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- Unambiguous polynomial time: some `#P` function is bounded by one everywhere and is one
exactly on the language. -/
def UP (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ f ∈ SharpP enc, (∀ a, f a ≤ 1) ∧ ∀ a, a ∈ A ↔ f a = 1}

/-- `UP` through verifiers: at most one certificate of the specified length accepts on each input,
and exactly one accepts on members. -/
theorem mem_UP : A ∈ UP enc ↔ ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableTidilyInPolyTime V (encPair enc encBits) encBool ∧
    (∀ a, acceptCount V a (p.eval (enc a).length) ≤ 1) ∧
    ∀ a, a ∈ A ↔ acceptCount V a (p.eval (enc a).length) = 1 := by
  constructor
  · rintro ⟨f, ⟨p, V, hV, hf⟩, hle, hA⟩
    exact ⟨p, V, hV, fun a => hf a ▸ hle a, fun a => (hA a).trans (by rw [hf a])⟩
  · rintro ⟨p, V, hV, hle, hA⟩
    exact ⟨_, ⟨p, V, hV, fun _ => rfl⟩, hle, hA⟩

/-- A deterministic decider uses only the empty certificate. -/
theorem P_subset_UP : P enc ⊆ UP enc := by
  rintro A ⟨f, hf, hA⟩
  refine mem_UP.mpr ⟨0, fun x => f x.1, hf.comp (.fst enc encBits), ?_, ?_⟩
  · intro a
    simp only [Polynomial.eval_zero, acceptCount_zero]
    split <;> omega
  · intro a
    simp [Polynomial.eval_zero, acceptCount_zero, hA a]

/-- An unambiguous verifier is an NP verifier. -/
theorem UP_subset_NP : UP enc ⊆ NP enc := by
  rintro A ⟨f, hf, hle, hA⟩
  refine mem_NP_iff_exists_SharpP.mpr ⟨f, hf, fun a => ?_⟩
  rw [hA a]
  have := hle a
  omega

/-- An accepting count bounded by one is odd exactly when it is one. -/
theorem UP_subset_ParityP : UP enc ⊆ ParityP enc := by
  rintro A ⟨f, hf, hle, hA⟩
  refine mem_ParityP_iff_exists_SharpP.mpr ⟨f, hf, fun a => ?_⟩
  rw [hA a, Nat.odd_iff]
  have := hle a
  omega

/-- `UP` is closed under polynomial-time many-one reductions. -/
theorem PolyTimeReducible.mem_UP {β : Type} {encB : β ↪ List Bool} {B : Set β}
    (h : PolyTimeReducible enc encB A B) (hB : B ∈ UP encB) : A ∈ UP enc := by
  obtain ⟨g, hg, hAB⟩ := h
  obtain ⟨f, hf, hle, hB⟩ := hB
  exact ⟨f ∘ g, SharpP.comp_mem hf hg, fun a => hle (g a),
    fun a => (hAB a).trans (hB (g a))⟩

end Cslib.Complexity
