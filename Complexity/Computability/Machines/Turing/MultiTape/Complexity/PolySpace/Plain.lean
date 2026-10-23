/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (after crei/tidy-universal lands)

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace
public import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain

/-!
# Polynomial space on plain machines

`Turing.MultiTapeTM.ComputableInPolySpace`, computability within polynomial space by any machine,
agrees with its tidy counterpart `Turing.MultiTapeTM.ComputableTidilyInPolySpace`: the tidy normal
form changes the bounds by constant factors
(`Turing.MultiTapeTM.ComputableInTimeAndSpace.computableTidilyInO`). Proofs switch between the
notions with `Turing.MultiTapeTM.ComputableInPolySpace.tidy` and
`Turing.MultiTapeTM.ComputableInPolySpace.of_tidy`.

## Main results

* `Turing.MultiTapeTM.computableInPolySpace_iff_computableTidilyInPolySpace`: the plain and tidy
  notions agree, with the shortcuts `Turing.MultiTapeTM.ComputableInPolySpace.tidy`,
  `Turing.MultiTapeTM.ComputableInPolySpace.of_tidy` and
  `Turing.MultiTapeTM.ComputableTidilyInPolySpace.computableInPolySpace`.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {α β : Type} {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}

/-- A function computable within polynomial space is tidily computable within polynomial space. -/
theorem ComputableInPolySpace.tidy (h : ComputableInPolySpace f encIn encOut) :
    ComputableTidilyInPolySpace f encIn encOut :=
  let ⟨_, _, hs, hc, hl⟩ := h
  ⟨_, _, .of_polynomiallyBounded _ hs, hc.computableTidilyInO hl⟩

/-- A function tidily computable within polynomial space is computable within polynomial space, by
the same machine. -/
theorem ComputableInPolySpace.of_tidy (h : ComputableTidilyInPolySpace f encIn encOut) :
    ComputableInPolySpace f encIn encOut := by
  obtain ⟨T, S, ⟨b, hb, hS⟩, c, hc, hl⟩ := h
  have hcS (a : α) : c * (S a + 1) ≤ c * (b (encIn a).length + 1) :=
    Nat.mul_le_mul_left c (Nat.add_le_add_right (hS a) 1)
  exact ⟨_, fun n => c * (b n + 1), by fun_prop,
    hc.computableInTimeAndSpace.mono (fun _ => le_rfl) hcS, fun a => (hl a).trans (hcS a)⟩

/-- `Turing.MultiTapeTM.ComputableInPolySpace.of_tidy` for dot notation on a tidy hypothesis. -/
theorem ComputableTidilyInPolySpace.computableInPolySpace
    (h : ComputableTidilyInPolySpace f encIn encOut) : ComputableInPolySpace f encIn encOut :=
  .of_tidy h

/-- **Plain and tidy computability within polynomial space agree.** -/
theorem computableInPolySpace_iff_computableTidilyInPolySpace :
    ComputableInPolySpace f encIn encOut ↔ ComputableTidilyInPolySpace f encIn encOut :=
  ⟨ComputableInPolySpace.tidy, ComputableInPolySpace.of_tidy⟩

end Turing.MultiTapeTM
