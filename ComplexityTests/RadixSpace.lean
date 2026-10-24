/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Radix

/-! Binary radix arguments and unbounded tuple values share their encoded-input space budget. -/
namespace ComplexityTests.RadixSpace
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInSpace
open Turing.MultiTapeNTM.ConfigurationGraph

private abbrev inputCode : ℕ × ℕ ↪ List Bool := encPair encNat encNat

-- The digit position is fixed while both operands are computed from the runtime input.
example (i : ℕ) : ComputableInSpace
    (fun p : ℕ × ℕ => Cslib.Radix.digit (p.1 + 1) (p.2 + 1) i)
    inputCode encNat (fun p => (inputCode p).length) :=
  budget_comp_linear (digit_inSpace i)
    (budget_prod (budget_natSucc (fst _ _)) (budget_natSucc (snd _ _)))

example (i : Bool) : ComputableInSpace
    (fun p : ℕ × ℕ => Cslib.Radix.component (p.1 + 1) p.2 i)
    inputCode encNat (fun p => (inputCode p).length) :=
  budget_comp_linear (component_inSpace i)
    (budget_prod (budget_natSucc (fst _ _)) (snd _ _))

-- Packing is total even when component values exceed the runtime radix.
example : ComputableInSpace
    (fun p : ℕ × ℕ => Cslib.Radix.pack p.1
      (fun i : Bool => if i then p.1 + p.2 else p.2))
    inputCode encNat (fun p => (inputCode p).length) := by
  apply pack_inSpace (fst _ _) ?_ (BigOLe.refl _)
  intro i
  cases i
  · exact snd _ _
  · exact budget_natAdd (fst _ _) (snd _ _)

-- The empty tuple works for every binary radix, including zero and one.
example : ComputableInSpace
    (fun b : ℕ => Cslib.Radix.pack b (fun i : Fin 0 => i.elim0))
    encNat encNat (fun b => (encNat b).length) :=
  pack_inSpace (B := fun b : ℕ => b) (of_inO (.of_linear (.of_eq fun _ => rfl)))
    (fun i => i.elim0) (BigOLe.refl _)

end ComplexityTests.RadixSpace
