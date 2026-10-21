/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Logics.Propositional.Resolution.Pigeonhole

/-!
# Tests: pigeonhole formulas and Haken's resolution lower bound

Satisfiability and unsatisfiability of small pigeonhole formulas; a concrete resolution refutation
of `PHP^2_1` and its monotone translation pairs; instances of the recurrence and exponential lower
bounds; and the axioms of the headline theorems.
-/

namespace ComplexityTests.ProofComplexity.Pigeonhole

open Cslib Cslib.Logic.PL Finset

/-! ### Satisfiability and size of small pigeonhole formulas -/

example : (CNF.pigeonhole 2 2).Satisfiable :=
  CNF.satisfiable_pigeonhole_iff.2 (by decide)

example : ¬ (CNF.pigeonhole 2 1).Satisfiable :=
  CNF.not_satisfiable_pigeonhole (by decide)

example : ¬ (CNF.pigeonhole 3 2).Satisfiable :=
  CNF.not_satisfiable_pigeonhole (by decide)

example : (CNF.pigeonhole 3 2).length ≤ 3 + 2 * 3 ^ 2 :=
  CNF.length_pigeonhole_le 3 2

example : (CNF.pigeonhole 3 2).vars.toFinset.card ≤ 3 * 2 :=
  CNF.card_toFinset_vars_pigeonhole_le 3 2

/-! ### A concrete resolution refutation of `PHP^2_1` -/

example : CNF.pigeonhole 2 1 =
    [[((0, 0), true)], [((1, 0), true)], [((0, 0), false), ((1, 0), false)]] := by
  decide

/-- Refute `PHP^2_1` in five lines by resolving the two pigeon clauses against the hole clause. -/
private def php21Proof : List (Clause (Fin 2 × Fin 1)) :=
  [[],
   [((1, 0), false)],
   [((0, 0), false), ((1, 0), false)],
   [((1, 0), true)],
   [((0, 0), true)]]

private theorem isProof_php21 : (CNF.pigeonhole 2 1).IsProof php21Proof := by
  have h₁ : (CNF.pigeonhole 2 1).IsProof
      [[((0, 0), false), ((1, 0), false)], [((1, 0), true)], [((0, 0), true)]] :=
    ((CNF.IsProof.nil.mem (by decide)).mem (by decide)).mem (by decide)
  have h₂ := h₁.resolvent (c₁ := [((0, 0), true)])
    (c₂ := [((0, 0), false), ((1, 0), false)]) (0, 0)
    (by decide) (by decide) (by decide) (by decide)
  have h₃ := h₂.resolvent (c₁ := [((1, 0), true)]) (c₂ := [((1, 0), false)]) (1, 0)
    (by decide) (by decide) (by decide) (by decide)
  exact h₃

example : (CNF.pigeonhole 2 1).RefutableInSize 5 :=
  ⟨php21Proof, isProof_php21, by decide, le_rfl⟩

/-- Both pairs `(0, 0)` and `(1, 0)` satisfy the hole clause `¬x_{0,0} ∨ ¬x_{1,0}` under
`matchPair`. -/
example : #(Pigeonhole.satPairs (univ : Finset (Fin 2)) (univ : Finset (Fin 1))
    (CNF.holeClause 0 1 0)) = 2 := by
  decide

/-! ### Lower-bound instances -/

/-- For `n = 8`, the recurrence bound `12 ^ 2 ≤ 11 ^ 2 · s` forces `2 ≤ s`. -/
example {s : ℕ} (hs : (CNF.pigeonhole 9 8).RefutableInSize s) : 2 ≤ s := by
  have := CNF.pow_le_mul_of_refutableInSize_pigeonhole (n := 8) (by decide) hs
  omega

/-- For `n = 24`, no resolution refutation of `PHP^{25}_{24}` has fewer than `2` lines. -/
example : ¬ (CNF.pigeonhole 25 24).RefutableInSize 1 :=
  CNF.not_refutableInSize_pigeonhole (n := 24) (by decide)

/-- For `n = 48`, no resolution refutation of `PHP^{49}_{48}` has at most `3` lines. -/
example : ¬ (CNF.pigeonhole 49 48).RefutableInSize 3 :=
  CNF.not_refutableInSize_pigeonhole (n := 48) (by decide)

/-! ### Axioms -/

/--
info: 'Cslib.Logic.PL.CNF.satisfiable_pigeonhole_iff' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.satisfiable_pigeonhole_iff

/--
info: 'Cslib.Logic.PL.CNF.not_satisfiable_pigeonhole' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.not_satisfiable_pigeonhole

/--
info: 'Cslib.Logic.PL.Pigeonhole.exists_le_card_satPairs' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.Pigeonhole.exists_le_card_satPairs

/--
info: 'Cslib.Logic.PL.CNF.exists_le_card_satPairs_pigeonhole' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.exists_le_card_satPairs_pigeonhole

/--
info: 'Cslib.Logic.PL.CNF.pow_le_mul_of_refutableInSize_pigeonhole' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.pow_le_mul_of_refutableInSize_pigeonhole

/--
info: 'Cslib.Logic.PL.CNF.two_pow_le_of_refutableInSize_pigeonhole' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.two_pow_le_of_refutableInSize_pigeonhole

/--
info: 'Cslib.Logic.PL.CNF.not_refutableInSize_pigeonhole' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.not_refutableInSize_pigeonhole

/--
info: 'Cslib.Logic.PL.CNF.Derivation.two_pow_le_size_pigeonhole' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.Derivation.two_pow_le_size_pigeonhole

end ComplexityTests.ProofComplexity.Pigeonhole
