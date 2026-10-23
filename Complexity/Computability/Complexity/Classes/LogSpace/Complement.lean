/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.LogSpace
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.InductiveCounting

/-!
# Complementary nondeterministic logarithmic space

`coNL enc` consists of the complements of problems in the native machine class `NL enc`.
It uses exactly the same encoding, every-prefix work-space measure and all-branches halting
convention as `NL`.

The Immerman–Szelepcsényi construction proves complement closure of this native class. Its
source machine may even be a recognizer with nonterminating branches; the constructed machine
halts on every branch.

## Main definitions

* `Cslib.Complexity.coNL`: complements of nondeterministic logarithmic-space problems.

## Main results

* `Cslib.Complexity.mem_coNL`: membership is membership of the complement in `NL`.
* `Cslib.Complexity.compl_mem_coNL_iff`: the corresponding double-complement equivalence.
* `Cslib.Complexity.compl_mem_NL`: native nondeterministic logarithmic-space complement closure.
* `Cslib.Complexity.NL_eq_coNL`: the Immerman–Szelepcsényi theorem.
* `Cslib.Complexity.mem_NL_of_recognizesInSpace`: recognizers and deciders give the same class.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.6][Sipser2013]
* [N. Immerman, *Nondeterministic Space Is Closed under Complementation*][Immerman1988]
* [R. Szelepcsényi, *The Method of Forcing for Nondeterministic Automata*][Szelepcsenyi1987]
-/

@[expose] public section

namespace Cslib.Complexity

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- The problems whose complements belong to native nondeterministic logarithmic space. -/
def coNL (enc : α ↪ List Bool) : Set (Set α) := {A | Aᶜ ∈ NL enc}

/-- A problem belongs to `coNL` exactly when its complement belongs to `NL`. -/
theorem mem_coNL : A ∈ coNL enc ↔ Aᶜ ∈ NL enc := Iff.rfl

/-- Complementing a problem in `NL` gives a problem in `coNL`, and conversely. -/
theorem compl_mem_coNL_iff : Aᶜ ∈ coNL enc ↔ A ∈ NL enc := by
  rw [mem_coNL, compl_compl]

/-- **Native nondeterministic logarithmic space is closed under complement.** The constructed
machine halts on every branch and obeys the same input/output space convention. -/
theorem compl_mem_NL (h : A ∈ NL enc) : Aᶜ ∈ NL enc := by
  obtain ⟨k, State, _, ntm, c, hA⟩ := h
  exact Turing.MultiTapeNTM.exists_decidesInLogSpace_compl hA.recognizesInSpace

/-- Complementation preserves membership in native nondeterministic logarithmic space. -/
theorem compl_mem_NL_iff : Aᶜ ∈ NL enc ↔ A ∈ NL enc := by
  constructor
  · intro h
    simpa only [compl_compl] using compl_mem_NL h
  · exact compl_mem_NL

/-- **`NL = coNL`**, the Immerman–Szelepcsényi theorem for the library's native machines and
arbitrary injective instance encodings. -/
theorem NL_eq_coNL : NL enc = coNL enc := by
  ext A
  exact compl_mem_NL_iff.symm

/-- A logarithmic-space recognizer, even with nonterminating branches, recognizes a problem
decidable within logarithmic space with every branch halting. -/
theorem mem_NL_of_recognizesInSpace {k c : ℕ} {State : Type} [Finite State]
    {ntm : Turing.MultiTapeNTM k Bool State}
    (h : ntm.RecognizesInSpace enc A fun a => c * (Nat.log2 (enc a).length + 1)) :
    A ∈ NL enc := by
  have hc : Aᶜ ∈ NL enc := Turing.MultiTapeNTM.exists_decidesInLogSpace_compl h
  exact compl_mem_NL_iff.mp hc

end Cslib.Complexity
