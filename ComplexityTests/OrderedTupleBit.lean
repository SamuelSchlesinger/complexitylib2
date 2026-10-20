/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Ordered.TupleBit

/-! # Arbitrary-base tuple BIT and its bounded radix arithmetic -/

@[expose] public section

namespace Cslib.Tests.OrderedTupleBit

open FirstOrder Language Structure Cslib.Logic.FO.Ordered

abbrev L : Language := Language.empty

instance {n : ℕ} : L.Structure (Fin n) := Language.emptyStructure
instance : Fact (2 ≤ 2) := ⟨by decide⟩
instance : Fact (2 ≤ 8) := ⟨by decide⟩
instance : Fact (2 ≤ 9) := ⟨by decide⟩
instance : Fact (2 ≤ 64) := ⟨by decide⟩

/-- The valid binary computation `2*3+3=9` needs an intermediate carry equal to the radix. -/
example :
    (Radix.affine L (.var (.inl 0)) (.var (.inl 1))
      (fun i => .var (.inr (0, i))) (fun i => .var (.inr (1, i)))
      (fun i => .var (.inr (2, i)))).Realize
    (Sum.elim (![2, 2] : Fin 2 → Fin 9)
      (fun p : Fin 3 × Fin 4 => (![![1, 1, 0, 0], ![1, 1, 0, 0], ![1, 0, 0, 1] ] p.1) p.2)) := by
  rw [Radix.realize_affine _ _ _ _ _ _ (by change 1 < 2; decide)
    (by change 2 ^ 3 < 9; decide)]
  decide

/-- A three-digit word has no output for `2*4=8`, including noncanonical output digits. -/
example (z : Fin 3 → Fin 9) :
    ¬(Radix.affine L (.var (.inl 0)) (.var (.inl 1))
      (fun i => .var (.inr (0, i))) (fun i => .var (.inr (1, i)))
      (fun i => .var (.inr (2, i)))).Realize
    (Sum.elim (![2, 2] : Fin 2 → Fin 9)
      (fun p : Fin 3 × Fin 3 => (![![0, 0, 1], ![0, 0, 0], z] p.1) p.2)) := by
  rw [Radix.realize_affine _ _ _ _ _ _ (by change 1 < 2; decide)
    (by change 2 ^ 3 < 9; decide)]
  rintro ⟨_, _, _, hz, he⟩
  change ∀ i, (z i).val < 2 at hz
  change 8 = Nat.ofDigits 2 (List.ofFn fun i => (z i).val) at he
  have := Nat.ofDigits_ofFn_lt (by decide : 1 < 2) (fun i => (z i).val) hz
  lia

/-- A scalar decoder cannot silently discard its final nonzero quotient. -/
example :
    ¬(Radix.decode L (.var (.inl 0)) (.var (.inl 1))
      (fun i => .var (.inr i))).Realize
    (Sum.elim (![2, 8] : Fin 2 → Fin 9) (![0, 0, 0] : Fin 3 → Fin 9)) := by
  rw [Radix.realize_decode _ _ _ _ (by decide)]
  decide

/-- Empty-word arithmetic has its ordinary zero semantics. -/
example :
    (Radix.affine L (.var 0) (.var 1) (fun i : Fin 0 => i.elim0)
      (fun i : Fin 0 => i.elim0) (fun i : Fin 0 => i.elim0)).Realize
      (![2, 2] : Fin 2 → Fin 9) := by
  rw [Radix.realize_affine _ _ _ _ _ _ (by decide) (by decide)]
  decide

/-- The minimum universe has its ordinary scalar bit relation. -/
example : (tupleBit L 1).Realize
    (fun p : Fin 2 × Fin 1 => (![![1], ![0] ] p.1) p.2 : _ → Fin 2) := by
  rw [realize_tupleBit]
  decide

example : ¬(tupleBit L 1).Realize
    (fun p : Fin 2 × Fin 1 => (![![1], ![1] ] p.1) p.2 : _ → Fin 2) := by
  rw [realize_tupleBit]
  decide

/-- The last small universe still uses first-coordinate-most-significant numbering. -/
example : (tupleBit L 2).Realize
    (fun p : Fin 2 × Fin 2 => (![![1, 0], ![0, 3] ] p.1) p.2 : _ → Fin 8) := by
  rw [realize_tupleBit]
  decide

/-- In the first large universe, ranks 512 and 9 give a true bit with index outside `Fin 9`. -/
example : (tupleBit L 3).Realize
    (fun p : Fin 2 × Fin 3 => (![![6, 2, 8], ![0, 1, 0] ] p.1) p.2 : _ → Fin 9) := by
  rw [realize_tupleBit]
  decide

/-- Reversing the source digits would turn the rank 11 into 19 and lose this bit. -/
example : (tupleBit L 2).Realize
    (fun p : Fin 2 × Fin 2 => (![![1, 2], ![0, 3] ] p.1) p.2 : _ → Fin 9) := by
  rw [realize_tupleBit]
  decide

/-- At size 64 the canonical binary radix needs all seven cardinality digits. -/
example : (Radix.cardinality L (.var (.inl ()))
    (fun i => .var (.inr i))).Realize
    (Sum.elim (fun _ : Unit => (2 : Fin 64)) (![0, 0, 0, 0, 0, 0, 1] : Fin 7 → Fin 64)) := by
  rw [Radix.realize_cardinality _ _ _ (by decide) (by decide)]
  decide

example : (tupleBit L 2).Realize
    (fun p : Fin 2 × Fin 2 => (![![1, 0], ![0, 6] ] p.1) p.2 : _ → Fin 64) := by
  rw [realize_tupleBit]
  decide

/-- Leading zero digits and multiplication by zero are valid throughout conversion. -/
example : ¬(tupleBit L 3).Realize
    (fun p : Fin 2 × Fin 3 => (![![0, 0, 0], ![0, 0, 0] ] p.1) p.2 : _ → Fin 9) := by
  rw [realize_tupleBit]
  decide

/-- Maximum tuple indices are rejected rather than reduced modulo the source size. -/
example (x : Fin 2 → Fin 9) :
    ¬(tupleBit L 2).Realize (fun p => (![x, ![8, 8] ] p.1) p.2) := by
  apply not_realize_tupleBit_of_lt
  have hx := lexRank_lt x
  change lexRank x < 2 ^ 80
  exact lt_trans hx (by decide)

/-- Zero dimension has an explicitly false formula, despite its singleton tuple set. -/
example (v : Fin 2 × Fin 0 → Fin 9) : ¬(tupleBit L 0).Realize v := by
  simp [lexRank_apply]

/-- Formula relabeling retains the full rank semantics. -/
example (v : Fin 3 × Fin 2 → Fin 9) :
    ((tupleBit L 2).relabel (fun p => (p.1.succ, p.2))).Realize v ↔
      (lexRank (fun i => v (1, i))).testBit (lexRank (fun i => v (2, i))) = true := by
  rw [Formula.realize_relabel, realize_tupleBit]
  rfl

/-- info: 'Cslib.Logic.FO.Ordered.realize_tupleBit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Logic.FO.Ordered.realize_tupleBit

/-- info: 'Cslib.Logic.FO.Ordered.Radix.realize_affine' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Logic.FO.Ordered.Radix.realize_affine

end Cslib.Tests.OrderedTupleBit
