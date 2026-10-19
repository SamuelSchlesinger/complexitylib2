/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Space.GeneralizedGeography.Membership
public import Complexity.Computability.Complexity.Classes.Space.GeneralizedGeography.Reduction

/-!
# Generalized Geography is `PSPACE`-complete

Generalized Geography (`Cslib.Complexity.GeneralizedGeography`: a directed graph with a start
vertex, on which two players alternately move a token along arcs to unvisited vertices, the first
player unable to move losing, and the instance is in the set when the first player has a winning
strategy) is `PSPACE`-complete [Schaefer][Schaefer1978] [Sipser, Theorem 8.11][Sipser2013]:

* it is in `PSPACE` (`Cslib.Complexity.GeneralizedGeography_mem_PSPACE`): it is a game of
  polynomially many moves with a polynomial-time winning condition, decided in polynomial space by
  the characterization of `PSPACE` through such games;
* it is `PSPACE`-hard (`Cslib.Complexity.GeneralizedGeography_pspaceHard`): true quantified Boolean
  formulas in alternating prenex conjunctive normal form (`Cslib.Complexity.TQBFCNF`), which are
  `PSPACE`-hard, reduce to it by Schaefer's diamond construction.

Both are relative to the encoding `encPair encGraph encNat` of a graph, as lists of binary vertices
and arcs, with a binary start vertex.

## Main results

* `Cslib.Complexity.GeneralizedGeography_pspaceComplete`: Generalized Geography is
  `PSPACE`-complete.

## References

* [T. J. Schaefer, *On the complexity of some two-person perfect-information games*][Schaefer1978]
* [M. Sipser, *Introduction to the Theory of Computation*, Theorem 8.11][Sipser2013]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- **Generalized Geography is `PSPACE`-complete** [Schaefer][Schaefer1978]
[Sipser, Theorem 8.11][Sipser2013]. -/
theorem GeneralizedGeography_pspaceComplete :
    PSPACEComplete (encPair encGraph encNat) GeneralizedGeography :=
  ⟨GeneralizedGeography_mem_PSPACE, GeneralizedGeography_pspaceHard⟩

end Cslib.Complexity
