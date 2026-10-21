/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Combinatorics.FiniteCover
import Complexity.Foundations.Combinatorics.MajorityVote

/-!
# Exact finite-cover budgets

The original finite-cover import still supplies the exact bound. Empty obligations need no tests;
half-density families retain the sharp `n + 1` test count, including at `n = 0`.
-/

namespace ComplexityTests.FiniteCover

open Cslib

example : ∃ samples : Fin 0 → Bool, ∀ _ : Fin 0, ∃ i, samples i = true :=
  exists_cover_of_scaled_card_lt (fun bit (_ : Fin 0) => bit = true) 1 1 0
    (by decide) (by decide)

example : ∃ samples : Fin 1 → Bool, ∀ _ : Unit, ∃ i, samples i = true := by
  simpa only [Finset.mem_singleton] using
    (exists_forall_exists_apply_mem (Ω := Bool) (X := Unit) (n := 0)
      (by decide) (fun _ => {true}) (by decide))

example : ∃ samples : Fin 2 → Bool, ∀ bit : Bool, ∃ i, samples i = bit := by
  simpa only [Finset.mem_singleton] using
    (exists_forall_exists_apply_mem (Ω := Bool) (X := Bool) (n := 1)
      (by decide) (fun bit => {bit}) (by decide))

/-- info: 'Cslib.exists_cover_of_scaled_card_lt' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.exists_cover_of_scaled_card_lt

/-- info: 'Cslib.exists_forall_exists_apply_mem' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.exists_forall_exists_apply_mem

end ComplexityTests.FiniteCover
