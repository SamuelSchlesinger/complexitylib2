/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger, lean-canny contributors
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain.Calculus
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Tape
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Matrix.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.RotationMap.Walk
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
# Resource-calculus provider imports

Canonical plain rules live in their original topic modules. This compatibility import module
reexports those providers without adding declarations or proof-search registrations.
-/
