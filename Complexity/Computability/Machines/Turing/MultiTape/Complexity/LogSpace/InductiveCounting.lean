/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.InductiveCounting.Bounds
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.InductiveCounting.Callbacks
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.Compiler

/-!
# Native nondeterministic logarithmic-space complementation

Inductive counting constructs a new finite-state nondeterministic multi-tape machine for the
complement of the language recognized by a logarithmic-space machine. The construction first
counts the input length, then scans the compact configuration graph with the small-register
controller, and compiles its binary choices and read-only input queries to native instructions.

The output machine halts on every branch and obeys an every-prefix work-space bound. The
source need only recognize its language: its branches may run forever. Input and write-only
output are uncharged, exactly as in the existing native `RunsInSpace` convention.

## Main results

* `Turing.MultiTapeNTM.exists_decidesInLogSpace_compl`: a native logarithmic-space recognizer
  has an all-branches-halting native logarithmic-space complement decider.

## References

* [N. Immerman, *Nondeterministic Space Is Closed under Complementation*][Immerman1988]
* [R. Szelepcsényi, *The Method of Forcing for Nondeterministic Automata*][Szelepcsenyi1987]
* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.6][Sipser2013]
-/

@[expose] public section

namespace Turing.MultiTapeNTM

variable {α State : Type} {k c : ℕ} [Finite State]
  {ntm : MultiTapeNTM k Bool State} {enc : α ↪ List Bool} {A : Set α}

/-- **Immerman–Szelepcsényi, with native machines.** Every language recognized in logarithmic
space has a logarithmic-space complement decider whose every branch halts. Both the input
encoding and the original all-prefix work-space convention are preserved. -/
theorem exists_decidesInLogSpace_compl
    (hA : ntm.RecognizesInSpace enc A fun a => c * (Nat.log2 (enc a).length + 1)) :
    ∃ (k' : ℕ) (State' : Type) (_ : Finite State')
      (ntm' : MultiTapeNTM k' Bool State') (c' : ℕ),
      ntm'.DecidesInSpace enc Aᶜ fun a => c' * (Nat.log2 (enc a).length + 1) := by
  classical
  let : Fintype State := Fintype.ofFinite State
  let D := ConfigurationGraph.radixExponent State c
  let M := Turing.InductiveCounting.queryMachine ntm D
  apply M.exists_decidesInSpace
    (Turing.InductiveCounting.query_inSpace D)
    (Turing.InductiveCounting.next_inSpace ntm D)
    Turing.InductiveCounting.halted_inSpace
    Turing.InductiveCounting.accept_inSpace
    (fun a => Turing.InductiveCounting.abstractTime ntm D (enc a).length)
    (fun a => Turing.InductiveCounting.queryMachine_haltsWithin ntm D (enc a))
    (A := Aᶜ) ?_
    (fun a => Nat.log2 (enc a).length + 1) (fun _ => le_rfl)
    ⟨Turing.InductiveCounting.storageConstant k D,
      fun a choices => Turing.InductiveCounting.length_run_le ntm D (enc a) choices⟩
  intro a
  have hnot : a ∈ Aᶜ ↔ ¬ ntm.Accepts (enc a) := not_congr (hA a).2
  exact hnot.trans (Turing.InductiveCounting.queryMachine_accepts_iff_not_accepts
    ntm (enc a) c (hA a).1).symm

end Turing.MultiTapeNTM
