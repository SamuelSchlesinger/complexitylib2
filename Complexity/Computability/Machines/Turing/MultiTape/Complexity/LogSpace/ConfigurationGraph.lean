/-
Copyright (c) 2026 Bolton Bailey, Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Bounds
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Routines

/-!
# Executable compact configuration graphs

A fixed finite-state binary nondeterministic multi-tape machine using logarithmic work space has
an exact configuration graph with polynomially many natural-number vertices. Each vertex stores
an input position, control tag, output summary and two ternary stacks plus a head per work tape.
The original input word is omitted.

The local edge routine uses one supplied input symbol, forces blank at the native boundary cells,
and otherwise performs deterministic arithmetic in linear workspace in the binary length and
vertex IDs. Its `ComputableTidilyInSpace` certificate is for an actual native tidy multi-tape
machine. The graph-to-source correctness theorem applies without a source halting assumption.

## Main definitions

* `Turing.MultiTapeNTM.ConfigurationGraph.startID`: initial vertex from the input length.
* `Turing.MultiTapeNTM.ConfigurationGraph.queryIndex`: the sole requested input-bit position.
* `Turing.MultiTapeNTM.ConfigurationGraph.edgeWithSymbol`: local guarded edge query.
* `Turing.MultiTapeNTM.ConfigurationGraph.bad`: accepting halted vertices.

## Main results

* `Turing.MultiTapeNTM.ConfigurationGraph.accepts_iff_reachable_bad_of_runsInSpace`: exact graph.
* `Turing.MultiTapeNTM.ConfigurationGraph.vertexID_lt_pow_of_runsInSpace`: polynomial ID bound.
* `Turing.MultiTapeNTM.ConfigurationGraph.edgeWithSymbol_inSpace`: native local edge routine.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.4][Sipser2013]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 4.1][AroraBarak09]
-/
