/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.OneWay.NP

/-! One-way functions against structural hypotheses: the preimage-prefix problem, the
search-to-decision inverter and `OWF ⇒ P ≠ NP`. The hypotheses of the inverter lemmas are
discharged for concrete functions; one-wayness itself is a conjecture and is not instantiated. -/

namespace ComplexityTests.OneWayMetacomplexity

open Turing.MultiTapeTM Cslib Cslib.Crypto Cslib.Complexity

-- The preimage-prefix problem of a concrete polynomial-time function is in `NP`.
example : preimagePrefix (fun x => x ++ x) ∈ NP encPreimagePrefix :=
  preimagePrefix_mem_NP (by fun_prop)

-- The search hypothesis is satisfiable: with an exact (classical) decision procedure, the search
-- recovers the input of an injective function.
open Classical in
example (x : List Bool) :
    preimageSearch (fun p => decide (p ∈ preimagePrefix List.reverse)) (x.length, x.reverse) =
      x := by
  simpa using apply_preimageSearch (f := List.reverse)
    (D := fun p => decide (p ∈ preimagePrefix List.reverse)) (fun _ => decide_eq_true_iff.symm) x

-- The search runs on a concrete instance with a decision procedure that is correct for the
-- identity: a prefix extends to a preimage of `y` of length `n` exactly when it is a prefix of
-- `y` and `y` has length `n`.
example : preimageSearch (fun p => decide (p.2.2 <+: p.2.1 ∧ p.2.1.length = p.1))
    (3, [true, false, true]) = [true, false, true] := by decide

-- The inverter lemma applies: the identity is not one-way, by its own inverse.
example : ¬ OneWay id :=
  not_oneWay_of_lengthInverse Prod.snd (ComputableTidilyInPolyTime.snd _ _) fun _ => rfl

/--
info: 'Cslib.Crypto.preimagePrefix_mem_NP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.preimagePrefix_mem_NP

/--
info: 'Cslib.Crypto.exists_inverse_of_preimagePrefix_mem_P' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.exists_inverse_of_preimagePrefix_mem_P

/--
info: 'Cslib.Crypto.OneWay.preimagePrefix_notMem_P' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.OneWay.preimagePrefix_notMem_P

/--
info: 'Cslib.Crypto.OneWay.P_ne_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.OneWay.P_ne_NP

/--
info: 'Cslib.Crypto.OneWay.SAT_notMem_P' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.OneWay.SAT_notMem_P

end ComplexityTests.OneWayMetacomplexity
