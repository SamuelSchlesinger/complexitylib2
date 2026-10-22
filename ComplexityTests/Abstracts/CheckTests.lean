/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract tests)

import ComplexityTests.Abstracts.Check
import ComplexityTests.Abstracts.CookLevinBridge
import Complexity.Computability.Complexity.Problems.SAT
import Complexity.Computability.Complexity.Reduction

/-!
# Regression tests for `#check_abstract`

Each test places a deliberate leak in its own namespace and pins the audit's error message with
`#guard_msgs`; the positive tests pin the success report.
-/

namespace ComplexityTests.Abstracts.CheckTests

/-! ### Rejected leaks -/

/- 1. Direct leak in a public definition body. -/
namespace DirectDefLeak
def leakedDef : Set (List (List (ℕ × Bool))) := Cslib.Complexity.SAT
end DirectDefLeak

/--
error: abstract audit:
`ComplexityTests.Abstracts.CheckTests.DirectDefLeak.leakedDef` depends on
implementation declaration `Cslib.Complexity.SAT` from
`Complexity.Computability.Complexity.Problems.SAT`
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.CheckTests.DirectDefLeak

/- 2. Transitive leak through a `private` pattern-matching helper inside the namespace. -/
namespace PrivateMatcherLeak
private def helper : Bool → Set (List (List (ℕ × Bool)))
  | true => Cslib.Complexity.SAT
  | false => ∅
def publicWrapper : Set (List (List (ℕ × Bool))) := helper true
end PrivateMatcherLeak

/--
error: abstract audit:
`ComplexityTests.Abstracts.CheckTests.PrivateMatcherLeak.publicWrapper` depends on
implementation declaration `Cslib.Complexity.SAT` from
`Complexity.Computability.Complexity.Problems.SAT`
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.CheckTests.PrivateMatcherLeak

/- 3. Leak in a `theorem` statement (even when the proof is `rfl`). -/
namespace TheoremTypeLeak
theorem leakedStmt : Cslib.Complexity.SAT = Cslib.Complexity.SAT := rfl
end TheoremTypeLeak

/--
error: abstract audit:
`ComplexityTests.Abstracts.CheckTests.TheoremTypeLeak.leakedStmt` depends on
implementation declaration `Cslib.Logic.PL.CNF` from `Complexity.Logics.Propositional.CNF`
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.CheckTests.TheoremTypeLeak

/- 4. Leak to a declaration in the same file outside the audited namespace. -/
def outsideHelper : Nat := 42
namespace OutsideNamespaceLeak
def usesOutside : Nat := outsideHelper
end OutsideNamespaceLeak

/--
error: abstract audit:
`ComplexityTests.Abstracts.CheckTests.OutsideNamespaceLeak.usesOutside` depends on
declaration `ComplexityTests.Abstracts.CheckTests.outsideHelper` outside
`ComplexityTests.Abstracts.CheckTests.OutsideNamespaceLeak`
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.CheckTests.OutsideNamespaceLeak

/- 5. Leak inside the constructor of a `private inductive` referenced only by type. -/
namespace PrivateInductiveCtorLeak
private inductive Hidden where
  | mk (h : Cslib.Complexity.SAT = Cslib.Complexity.SAT)
def usesHiddenType : Prop := Nonempty Hidden
end PrivateInductiveCtorLeak

/--
error: abstract audit:
`ComplexityTests.Abstracts.CheckTests.PrivateInductiveCtorLeak.usesHiddenType`
depends on implementation declaration `Cslib.Complexity.SAT` from
`Complexity.Computability.Complexity.Problems.SAT`
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.CheckTests.PrivateInductiveCtorLeak

/- 6. Rejection of `opaque` / `partial` definitions in an abstract namespace. -/
namespace OpaqueDefLeak
opaque hiddenVal : Nat
end OpaqueDefLeak

/--
error: abstract audit:
`ComplexityTests.Abstracts.CheckTests.OpaqueDefLeak.hiddenVal` is `opaque`,
`partial`, or `unsafe`
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.CheckTests.OpaqueDefLeak

/- 7. The allowlist is transitive: `Cslib.Complexity.NPComplete` lives in the allowlisted
`Reduction` module, but its definition reaches declarations from modules that are not
allowlisted. -/
namespace AllowlistTransitiveLeak
def usesNPComplete : Set (List (List (ℕ × Bool))) → Prop :=
  Cslib.Complexity.NPComplete Cslib.Complexity.encCNF
end AllowlistTransitiveLeak

/--
error: abstract audit:
`ComplexityTests.Abstracts.CheckTests.AllowlistTransitiveLeak.usesNPComplete` depends on
implementation declaration `Cslib.Complexity.NP` from
`Complexity.Computability.Complexity.Classes.NP`
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.CheckTests.AllowlistTransitiveLeak allowing [
  Complexity.Computability.Complexity.Reduction
]

end ComplexityTests.Abstracts.CheckTests

/- 8. Declarations that an imported module (here the Cook–Levin bridge) places in the audited
namespace are rejected, even if this file adds its own declarations there. -/
namespace ComplexityTests.Abstracts.CookLevinBridge
def localAddition : Nat := 0
end ComplexityTests.Abstracts.CookLevinBridge

/--
error: abstract audit: `ComplexityTests.Abstracts.CookLevinBridge.ComputableInPolyTime` lies in
`ComplexityTests.Abstracts.CookLevinBridge` but is defined in imported module
`ComplexityTests.Abstracts.CookLevinBridge`, not in the current file
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.CookLevinBridge

namespace ComplexityTests.Abstracts.CheckTests

/-! ### Accepted abstracts -/

/- 9. An allowlisted module is accepted when the allowlist covers its dependencies. -/
namespace AllowlistAccepted
def usesEncNat : ℕ ↪ List Bool := Turing.MultiTapeTM.encNat
end AllowlistAccepted

/--
info: abstract audit passed for `ComplexityTests.Abstracts.CheckTests.AllowlistAccepted`: 1 root
declarations, 9 dependencies checked
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.CheckTests.AllowlistAccepted allowing [
  Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat
]

end ComplexityTests.Abstracts.CheckTests
