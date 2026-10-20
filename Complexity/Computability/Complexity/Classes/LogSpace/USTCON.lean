/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.LogSpace
public import Complexity.Computability.USTCON.Space

/-!
# Undirected connectivity is in deterministic logarithmic space

**Reingold's theorem** [Reingold, Theorem 4.1][Reingold2008]
[Arora and Barak, Section 21.4][AroraBarak09]: undirected `s`–`t` connectivity, on simple graphs
given by their adjacency matrices (`Cslib.Complexity.encUSTCON`), is in `L`
(`Cslib.Complexity.USTCON_mem_L`).

The decider is the read machine `Cslib.USTCON.Reader.machine`, which walks in Reingold's graph of
the input along all label sequences of length `O(log n)` and evaluates its rotation map in place
with a constant number of labels per level; its simulation on multi-tape machines runs in space
`O(log n)` (`Cslib.USTCON.computableInLogSpace_decide`).

The class `SL` of symmetric logarithmic space is not defined in the library, so the corollary
`SL = L` of [Reingold, Theorem 4.2][Reingold2008] is not stated.

## Main results

* `Cslib.Complexity.USTCON_mem_L`: undirected connectivity is in `L`.

## References

* [O. Reingold, *Undirected connectivity in log-space*][Reingold2008]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

/-- **Reingold's theorem**: undirected `s`–`t` connectivity is in deterministic logarithmic
space. -/
theorem USTCON_mem_L : USTCON ∈ L encUSTCON :=
  ⟨_, USTCON.computableInLogSpace_decide, fun _ ↦ by simp⟩

end Cslib.Complexity
