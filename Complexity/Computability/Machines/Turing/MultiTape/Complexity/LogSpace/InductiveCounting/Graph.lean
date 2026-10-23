/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Reachability.InductiveCounting.Semantics
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph

/-!
# Feeding the compact native graph to inductive counting

The local configuration edge test already rejects vertices beyond the fixed polynomial bound.
Consequently restricting the graph to this bound changes no edge. The counting controller's
safety property is exactly nonacceptance by the original nondeterministic machine.

## Main results

* `Turing.InductiveCounting.safe_iff_not_accepts`: native nonacceptance as graph safety.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.6][Sipser2013]
-/

@[expose] public section

namespace Turing.InductiveCounting

open MultiTapeNTM.ConfigurationGraph

variable {k : ℕ} {State : Type} [Fintype State]
  (ntm : MultiTapeNTM k Bool State) (D : ℕ) (input : List Bool)

/-- The Boolean edge test obtained by supplying the one actual input symbol requested by the
compact graph. The operational query machine supplies this symbol without storing `input`. -/
noncomputable def graphEdge (u v : ℕ) : Bool :=
  edgeWithSymbol ntm D input.length u v input[queryIndex (k := k) D input.length u]?

/-- Both endpoints of every accepted local edge are below the polynomial graph bound. -/
theorem graphEdge_bounds {u v : ℕ} (h : graphEdge ntm D input u v = true) :
    u < vertexBound (k := k) D input.length ∧
      v < vertexBound (k := k) D input.length := by
  simp only [graphEdge, edgeWithSymbol, Bool.and_eq_true] at h
  have hu := h.1.1
  have hv := h.1.2
  simp only [valid, Bool.and_eq_true, decide_eq_true_eq] at hu hv
  constructor
  · exact hu.1.1.1.1
  · exact hv.1.1.1.1

/-- The controller's explicit vertex guards remove no compact configuration edge. -/
theorem boundedGraph_eq :
    Cslib.InductiveCounting.Graph (vertexBound (k := k) D input.length)
      (graphEdge ntm D input) = Edge ntm D input := by
  funext u v
  apply propext
  constructor
  · exact fun h => h.2.2
  · intro h
    exact ⟨(graphEdge_bounds ntm D input h).1, (graphEdge_bounds ntm D input h).2, h⟩

/-- Under the source logarithmic-space bound, the controller's safety property is exactly the
absence of an accepting native computation path. No source running-time assumption is used. -/
theorem safe_iff_not_accepts (c : ℕ)
    (hspace : ntm.RunsInSpace input (c * (Nat.log2 input.length + 1))) :
    Cslib.InductiveCounting.Safe
      (vertexBound (k := k) (radixExponent State c) input.length)
      (startID ntm (radixExponent State c) input.length)
      (graphEdge ntm (radixExponent State c) input)
      (bad (k := k) (State := State) (radixExponent State c) input.length) ↔
      ¬ ntm.Accepts input := by
  rw [Cslib.InductiveCounting.Safe, boundedGraph_eq,
    accepts_iff_reachable_bad_of_runsInSpace c hspace]
  constructor
  · intro h ⟨u, hu, hb⟩
    rw [h u hu] at hb
    exact Bool.false_ne_true hb
  · intro h u hu
    apply Bool.eq_false_iff.mpr
    exact fun hb => h ⟨u, hu, hb⟩

end Turing.InductiveCounting
