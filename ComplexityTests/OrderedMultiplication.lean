/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Ordered.Multiplication

/-! # Native TIMES, overflow rejection, and packed-decoder boundaries -/

@[expose] public section

namespace Cslib.Tests.OrderedMultiplication

open FirstOrder Language Structure Cslib.Logic.FO.Ordered

abbrev L : Language := Language.empty

instance {n : ℕ} : L.Structure (Fin n) := Language.emptyStructure
instance : Fact (2 ≤ 2) := ⟨by decide⟩
instance : Fact (2 ≤ 3) := ⟨by decide⟩
instance : Fact (2 ≤ 5) := ⟨by decide⟩
instance : Fact (2 ≤ 256) := ⟨by decide⟩
instance : Fact (2 ≤ 257) := ⟨by decide⟩
instance : Fact (2 ≤ 1000) := ⟨by decide⟩
instance : Fact (2 ≤ 262145) := ⟨by decide⟩

/-- Zero and one work in the minimum canonical universe. -/
example : (multiplication L).Realize (![0, 1, 0] : Fin 3 → Fin 2) := by
  rw [realize_multiplication]
  decide

example : (multiplication L).Realize (![1, 0, 0] : Fin 3 → Fin 2) := by
  rw [realize_multiplication]
  decide

example : (multiplication L).Realize (![1, 1, 1] : Fin 3 → Fin 2) := by
  rw [realize_multiplication]
  decide

example : ¬(multiplication L).Realize (![1, 1, 0] : Fin 3 → Fin 2) := by
  rw [realize_multiplication]
  decide

/-- The ordinary product can exist in an odd-sized universe. -/
example : (multiplication L).Realize (![2, 2, 4] : Fin 3 → Fin 5) := by
  rw [realize_multiplication]
  decide

/-- Every candidate is rejected if the product exceeds an odd-sized universe. -/
example (z : Fin 3) : ¬(multiplication L).Realize ![2, 2, z] :=
  not_realize_multiplication_of_le _ (by change 3 ≤ 4; decide)

/-- The final input covered by the fixed finite branch. -/
example : (multiplication L).Realize (![255, 1, 255] : Fin 3 → Fin 256) := by
  rw [realize_multiplication]
  decide

/-- The first input requiring packed witnesses, at the first large universe. -/
example : (multiplication L).Realize (![256, 1, 256] : Fin 3 → Fin 257) := by
  rw [realize_multiplication]
  decide

example : (multiplication L).Realize (![256, 0, 0] : Fin 3 → Fin 257) := by
  rw [realize_multiplication]
  decide

example (z : Fin 257) : ¬(multiplication L).Realize ![256, 2, z] :=
  not_realize_multiplication_of_le _ (by change 257 ≤ 512; decide)

/-- Packed multiplication in a universe strictly between consecutive powers of two. -/
example : (multiplication L).Realize (![300, 3, 900] : Fin 3 → Fin 1000) := by
  rw [realize_multiplication]
  decide

example (z : Fin 1000) : ¬(multiplication L).Realize ![300, 4, z] :=
  not_realize_multiplication_of_le _ (by change 1000 ≤ 1200; decide)

/-- Dense inputs require nonzero carries spanning several blocks. -/
example : (multiplication L).Realize (![511, 511, 261121] : Fin 3 → Fin 262145) := by
  rw [realize_multiplication]
  decide

/-- The uniqueness theorem has an explicit, nonvacuous bounded-product client. -/
example : ∃! z : Fin 1000, (multiplication L).Realize ![300, 3, z] :=
  existsUnique_multiplication 300 3 (by decide)

/-- The formula composes with ordinary variable relabeling. -/
example (v : Fin 4 → Fin 1000) :
    ((multiplication L).relabel (fun i => i.succ)).Realize v ↔
      (v 1).val * (v 2).val = (v 3).val := by
  rw [Formula.realize_relabel, realize_multiplication]
  rfl

/-- A one-bit field rejects a high set bit even for arbitrary packed words. -/
example (w : Fin 8 → Fin 257) :
    ¬(packedField L (.var (.inl 0)) (fun r => .var (.inr r)) (.var (.inl 1))
      (.var (.inl 2)) (.var (.inl 3))).Realize (Sum.elim (![8, 0, 1, 2] : Fin 4 → Fin 257) w) := by
  rw [realize_packedField _ _ _ _ _ _ (by change 8 * 8 < 257; decide)]
  intro he
  have hb := BitString.readPackedField_lt 8 (fun r => (w r).val) 0 1
  change 2 = BitString.readPackedField 8 (fun r => (w r).val) 0 1 at he
  rw [← he] at hb
  contradiction

/-- info: 'Cslib.Logic.FO.Ordered.realize_multiplication' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Logic.FO.Ordered.realize_multiplication

/-- info: 'Cslib.Logic.FO.Ordered.not_realize_multiplication_of_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Logic.FO.Ordered.not_realize_multiplication_of_le

/-- info: 'Cslib.Logic.FO.Ordered.existsUnique_multiplication' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Logic.FO.Ordered.existsUnique_multiplication

end Cslib.Tests.OrderedMultiplication
