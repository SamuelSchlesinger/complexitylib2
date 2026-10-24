/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain.Calculus
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Tape
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Option
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Pi
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Fold
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Fold
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Arith
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Lists
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BinaryCompare
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Streaming
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Translate
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Bit

/-!
# Plain resource-bounded structural calculus

Supported plain/tidy equivalences transport whole generic resource statements without changing
independent time and space bounds. Exact machine-budget or degree predicates without such an
equivalence are not weakened or silently published as a partially plain statement.

This sidecar extends the polynomial-time calculus using an explicit list of generic machine
sources. The registry identifies retained originals for later internalization; it is not a
permanent surface-policy exemption.
-/

public section

plain_mirror_sources [
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Tape,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Option,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Pi,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Fold,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.Fold,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.Arith,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.Lists,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.Binary,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.BinaryCompare,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.Streaming,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.Translate,
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Bit]
