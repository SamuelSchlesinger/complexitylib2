/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PCP.LocalTest

/-! Concrete regression clients for query padding and rejection of a random test family. -/

namespace ComplexityTests.PCPLocalTest

open Cslib.PCP
open Finset

private def firstBitTest : LocalTest (Fin 2) Unit (Fin 1) Bool where
  query _ _ := 0
  Accepts _ answers := answers 0 = true

private def honestProof : Fin 2 → Bool := fun _ => true

private def paddedTest := firstBitTest.padQueries (n := 0) (m := 3) (by decide)

-- Padding preserves acceptance on the honest proof and rejects a proof with a false checked bit.
example : paddedTest.Passes honestProof () := by
  simp [paddedTest, LocalTest.Passes, LocalTest.padQueries, LocalTest.reindexQueries,
    firstBitTest, honestProof]

example : ¬ paddedTest.Passes (fun _ => false) () := by
  simp [paddedTest, LocalTest.Passes, LocalTest.padQueries, LocalTest.reindexQueries,
    firstBitTest]

-- The extra answer slots do not affect the predicate: changing them leaves acceptance unchanged.
example : paddedTest.Accepts () (fun i : Fin 3 => if i = 0 then true else false) := by
  simp [paddedTest, LocalTest.padQueries, LocalTest.reindexQueries, firstBitTest]

example : paddedTest.Accepts () (fun _ : Fin 3 => true) := by
  simp [paddedTest, LocalTest.padQueries, LocalTest.reindexQueries, firstBitTest]

example : ¬ paddedTest.Accepts () (fun i : Fin 3 => if i = 0 then false else true) := by
  simp [paddedTest, LocalTest.padQueries, LocalTest.reindexQueries, firstBitTest]

-- The third query repeats the original position.
example : paddedTest.query () 2 = 0 := by decide

private def bothBitsTest : LocalTest (Fin 2) Unit (Fin 2) Bool where
  query _ i := i
  Accepts _ answers := answers 0 = true ∧ answers 1 = true

private def selectedBitTest (e : Bool) : LocalTest (Fin 2) Unit (Fin 1) Bool where
  query _ _ := if e then 0 else 1
  Accepts _ answers := answers 0 = true

private def counterexampleProof : Fin 2 → Bool := fun i => if i = 0 then true else false

private theorem trueBranchCard :
    #{r : Bool × Unit | r.1 = true} = 1 := by
  rw [show ({r : Bool × Unit | r.1 = true} : Finset (Bool × Unit)) = {(true, ())} by
    ext ⟨b, u⟩
    cases b <;> simp]
  simp

-- For π = [true, false], the conjunction rejects with probability 1, while a uniformly
-- selected coordinate rejects with probability 1/2, attaining the factor-two bound.
example : bothBitsTest.acceptProb counterexampleProof = 0 := by
  norm_num [LocalTest.acceptProb_eq_card_div, LocalTest.Passes, bothBitsTest,
    counterexampleProof, trueBranchCard]

example : (LocalTest.mix selectedBitTest).acceptProb counterexampleProof = 1 / 2 := by
  norm_num [LocalTest.acceptProb_eq_card_div, LocalTest.Passes, LocalTest.mix,
    selectedBitTest, counterexampleProof, trueBranchCard]

example :
    1 - bothBitsTest.acceptProb counterexampleProof =
      (2 : ℝ) * (1 - (LocalTest.mix selectedBitTest).acceptProb counterexampleProof) := by
  rw [show bothBitsTest.acceptProb counterexampleProof = 0 by
    norm_num [LocalTest.acceptProb_eq_card_div, LocalTest.Passes, bothBitsTest,
      counterexampleProof, trueBranchCard]]
  rw [show (LocalTest.mix selectedBitTest).acceptProb counterexampleProof = 1 / 2 by
    norm_num [LocalTest.acceptProb_eq_card_div, LocalTest.Passes, LocalTest.mix,
      selectedBitTest, counterexampleProof, trueBranchCard]]
  norm_num

-- Passing both selected checks implies that both bits pass the conjunction.
example :
    1 - bothBitsTest.acceptProb counterexampleProof ≤
      (2 : ℝ) * (1 - (LocalTest.mix selectedBitTest).acceptProb counterexampleProof) := by
  have h := LocalTest.one_sub_acceptProb_le_card_mul_one_sub_acceptProb_mix
    (S := bothBitsTest) (T := selectedBitTest) counterexampleProof (by
      intro r hall
      exact ⟨hall true, hall false⟩)
  simpa using h

end ComplexityTests.PCPLocalTest
