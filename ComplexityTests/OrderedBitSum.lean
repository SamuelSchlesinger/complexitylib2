/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Ordered.BitSum

/-! # Native Bit Sum and exact-shift boundaries -/

@[expose] public section

namespace Cslib.Tests.OrderedBitSum

open FirstOrder Language Structure Cslib.Logic.FO.Ordered

abbrev L : Language := Language.empty

instance {n : ℕ} : L.Structure (Fin n) := Language.emptyStructure
instance : Fact (2 ≤ 2) := ⟨by decide⟩
instance : Fact (2 ≤ 3) := ⟨by decide⟩
instance : Fact (2 ≤ 5) := ⟨by decide⟩
instance : Fact (2 ≤ 8) := ⟨by decide⟩
instance : Fact (2 ≤ 9) := ⟨by decide⟩
instance : Fact (2 ≤ 256) := ⟨by decide⟩
instance : Fact (2 ≤ 257) := ⟨by decide⟩
instance : Fact (2 ≤ 512) := ⟨by decide⟩
instance : Fact (2 ≤ 513) := ⟨by decide⟩

/-- Both values of the minimum universe have their actual counts. -/
example : (bitSum L).Realize (![0, 0] : Fin 2 → Fin 2) := by
  rw [realize_bitSum]
  decide

example : (bitSum L).Realize (![1, 1] : Fin 2 → Fin 2) := by
  rw [realize_bitSum]
  decide

example : ¬(bitSum L).Realize (![1, 0] : Fin 2 → Fin 2) := by
  rw [realize_bitSum]
  decide

/-- Non-power-of-two universes use the ordinary binary representation. -/
example : (bitSum L).Realize (![2, 1] : Fin 2 → Fin 3) := by
  rw [realize_bitSum]
  decide

example : (bitSum L).Realize (![7, 3] : Fin 2 → Fin 9) := by
  rw [realize_bitSum]
  decide

example : (bitSum L).Realize (![8, 1] : Fin 2 → Fin 9) := by
  rw [realize_bitSum]
  decide

/-- The last input handled by the fixed small-input disjunction. -/
example : (bitSum L).Realize (![255, 8] : Fin 2 → Fin 256) := by
  rw [realize_bitSum]
  decide

/-- The first input requiring the packed-tree branch, in an odd-sized universe. -/
example : (bitSum L).Realize (![256, 1] : Fin 2 → Fin 257) := by
  rw [realize_bitSum]
  decide

/-- A large all-one input, followed by a single high bit in a non-power-of-two universe. -/
example : (bitSum L).Realize (![511, 9] : Fin 2 → Fin 512) := by
  rw [realize_bitSum]
  decide

example : (bitSum L).Realize (![512, 1] : Fin 2 → Fin 513) := by
  rw [realize_bitSum]
  decide

example : ¬(bitSum L).Realize (![511, 8] : Fin 2 → Fin 512) := by
  rw [realize_bitSum]
  decide

/-- Composition with arbitrary free-variable assignments uses the same native formula. -/
example (v : Fin 3 → Fin 257) :
    ((bitSum L).relabel (fun i => i.succ)).Realize v ↔
      (v 2).val = (v 1).val.bitIndices.length := by
  rw [Formula.realize_relabel, realize_bitSum]
  rfl

/-- Fixed syntactic numerals do not assume that the universe contains them. -/
example (x : Fin 2) : ¬(natEq L 256 (.var ())).Realize (fun _ => x) := by
  rw [realize_natEq]
  have := x.isLt
  change ¬x.val = 256
  lia

/-- A positive shift that leaves the universe has no output. -/
example (z : Fin 5) :
    ¬(shiftLeft L (.var 0) (.var 1) (.var 2)).Realize (![3, 1, z] : Fin 3 → Fin 5) := by
  rw [realize_shiftLeft]
  have := z.isLt
  change ¬6 = z.val
  lia

/-- A shifted bit beyond every representable bit index cannot silently disappear. -/
example :
    ¬(shiftLeft L (.var 0) (.var 1) (.var 2)).Realize (![4, 7, 0] : Fin 3 → Fin 8) := by
  rw [realize_shiftLeft]
  decide

/-- The same large shift remains defined on zero. -/
example :
    (shiftLeft L (.var 0) (.var 1) (.var 2)).Realize (![0, 7, 0] : Fin 3 → Fin 8) := by
  rw [realize_shiftLeft]
  decide

/-- A leaf decoder constrains high bits even when its packed words are arbitrary. -/
example (w : Fin 8 → ℕ) : ¬BitSum.EncodesNode 1 8 w 0 0 3 := by
  intro h
  have := ((h 1).mp (by decide)).1
  lia

/-- info: 'Cslib.Logic.FO.Ordered.realize_bitSum' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Logic.FO.Ordered.realize_bitSum

/-- info: 'Cslib.Logic.FO.Ordered.existsUnique_bitSum' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Logic.FO.Ordered.existsUnique_bitSum

/-- info: 'Cslib.Logic.FO.Ordered.realize_shiftLeft' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Logic.FO.Ordered.realize_shiftLeft

end Cslib.Tests.OrderedBitSum
