/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Ordered.Radix.Decode

/-! # Arbitrary-base tuple BIT and its bounded radix arithmetic -/

@[expose] public section

namespace Cslib.Tests.OrderedTupleBit

open FirstOrder Language Structure Cslib.Logic.FO.Ordered

abbrev L : Language := Language.empty

instance {n : ℕ} : L.Structure (Fin n) := Language.emptyStructure
instance : Fact (2 ≤ 9) := ⟨by decide⟩

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

/-- info: 'Cslib.Logic.FO.Ordered.Radix.realize_affine' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Logic.FO.Ordered.Radix.realize_affine

end Cslib.Tests.OrderedTupleBit
