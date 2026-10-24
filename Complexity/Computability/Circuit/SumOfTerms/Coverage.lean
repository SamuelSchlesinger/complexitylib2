/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.SumOfTerms.Basic
public import Complexity.Computability.Circuit.Fusion.Counting

/-!
# Support coverage by dictionary circuits

Interpret addition as finite-set union and a dictionary term as its prescribed support.
Nonmembership of a target element is preserved by addition, so every covered target element
must first appear at a dictionary gate. A local coverage bound therefore gives a weighted
dictionary-cost lower bound. Shared gates are counted once; free supplied inputs must be
disjoint from the target. The ambient support type may be infinite.

These are circuits of supports, with union as the operation. Applying the result to polynomial
supports requires a separate semantic bridge; cancellation is not silently treated as union.

## Main definitions

* `Cslib.Circuits.SumOfTerms.supportInterpretation`: dictionary supports with union gates.

## Main results

* `Cslib.Circuits.SumOfTerms.card_le_mul_dictionaryCost`: weighted coverage bound for any wire.
* `Cslib.Circuits.SumOfTerms.ceilDiv_card_le_termCost`: term-count bound for any selected output.
* `Cslib.Circuits.SumOfTerms.card_le_termCost_of_separated`: one term per target element when
  each dictionary support meets the target in at most one element.

## References

* Adapted from LowerBound/Fusion/SumOfTerms/Coverage.lean in
  [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*][Schlesinger2026Algebraic].
-/

@[expose] public section

namespace Cslib.Circuits.SumOfTerms

universe u v

variable {T : Type u} {M : Type v} [DecidableEq M] {n g m : ℕ}

/-- Interpret dictionary terms by finite supports and addition by union. -/
def supportInterpretation (support : T → Finset M) : Interpretation (signature T) (Finset M)
  | .add, args => args 0 ∪ args 1
  | .term t, _ => support t

/-- Union cannot introduce an element absent from both arguments. -/
@[simp] theorem failures_support_add (support : T → Finset M) (target : Finset M)
    (args : Fin 2 → Finset M) :
    (⟨.add, args⟩ : Fusion.Atom (signature T) (Finset M)).failures
      (supportInterpretation support) (fun t s => t ∉ s) target = ∅ := by
  ext t
  simp [Fusion.Atom.mem_failures, Fusion.Atom.Preserves, supportInterpretation,
    Fin.forall_fin_two, not_or]

/-- A nullary dictionary gate fails exactly at the target elements in its support. -/
@[simp] theorem failures_support_term (support : T → Finset M) (target : Finset M)
    (t : T) (args : Fin 0 → Finset M) :
    (⟨.term t, args⟩ : Fusion.Atom (signature T) (Finset M)).failures
      (supportInterpretation support) (fun t s => t ∉ s) target = target ∩ support t := by
  ext x
  simp [Fusion.Atom.mem_failures, Fusion.Atom.Preserves, supportInterpretation]

/-- Covering a target disjoint from the supplied inputs costs enough to pay for its elements.
Capacity zero is allowed: it forces the covered target to be empty. -/
theorem card_le_mul_dictionaryCost (p : Program (signature T) n g)
    (support : T → Finset M) (input : Fin n → Finset M) (target : Finset M)
    (hin : ∀ i, Disjoint target (input i)) (w : Wire n g)
    (hout : target ⊆ p.trace (supportInterpretation support) input w)
    (weight : T → ℕ) (capacity : ℕ)
    (hbound : ∀ t, (target ∩ support t).card ≤ capacity * weight t) :
    target.card ≤ capacity * p.cost (dictionaryCost weight) := by
  refine Fusion.card_le_mul_program_cost p (supportInterpretation support)
    (fun t s => t ∉ s) target input (fun t ht i => Finset.disjoint_left.mp (hin i) ht)
    (fun t ht => ⟨w, fun h => h (hout ht)⟩) (dictionaryCost weight) capacity ?_
  intro k
  change _ ≤ capacity * dictionaryCost weight
    (Fusion.programAtoms p (supportInterpretation support) input k).op
  rcases Fusion.programAtoms p (supportInterpretation support) input k with ⟨op, args⟩
  cases op with
  | add => simp
  | term t => simpa using hbound t

/-- If each dictionary support covers at most `capacity` target elements, divide the target
size by that positive capacity and round up. Other circuit outputs are unrestricted. -/
theorem ceilDiv_card_le_termCost (c : Circuit (signature T) n m)
    (support : T → Finset M) (input : Fin n → Finset M) (target : Finset M)
    (hin : ∀ i, Disjoint target (input i)) (o : Fin m)
    (hout : target ⊆ c.eval (supportInterpretation support) input o)
    {capacity : ℕ} (hpos : 0 < capacity)
    (hbound : ∀ t, (target ∩ support t).card ≤ capacity) :
    target.card ⌈/⌉ capacity ≤ c.program.cost termCost := by
  apply (ceilDiv_le_iff_le_mul hpos).mpr
  exact card_le_mul_dictionaryCost c.program support input target hin (c.outputs o) hout
    (fun _ => 1) capacity (fun t => by simpa only [Nat.mul_one] using hbound t)

/-- A dictionary whose terms cover at most one target element needs at least `target.card`
terms, even when terms are shared by several additions. -/
theorem card_le_termCost_of_separated (c : Circuit (signature T) n m)
    (support : T → Finset M) (input : Fin n → Finset M) (target : Finset M)
    (hin : ∀ i, Disjoint target (input i)) (o : Fin m)
    (hout : target ⊆ c.eval (supportInterpretation support) input o)
    (hbound : ∀ t, (target ∩ support t).card ≤ 1) :
    target.card ≤ c.program.cost termCost := by
  simpa using ceilDiv_card_le_termCost c support input target hin o hout Nat.zero_lt_one hbound

end Cslib.Circuits.SumOfTerms
