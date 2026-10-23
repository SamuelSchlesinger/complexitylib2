/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (after crei/tidy-universal lands)

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace
public import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain

/-!
# Space bounds on plain machines

`Turing.MultiTapeTM.ComputableInSpace`, computability within space `O(S a)` by any machine,
agrees with its tidy counterpart `Turing.MultiTapeTM.ComputableTidilyInSpace`, with the same bound:
the tidy normal form changes the bounds by constant factors
(`Turing.MultiTapeTM.ComputableInTimeAndSpace.computableTidilyInO`). Proofs switch between the
notions with `Turing.MultiTapeTM.ComputableInSpace.tidy` and
`Turing.MultiTapeTM.ComputableInSpace.of_tidy`.

## Main results

* `Turing.MultiTapeTM.computableInSpace_iff_computableTidilyInSpace`: the plain and tidy notions
  agree, with the shortcuts `Turing.MultiTapeTM.ComputableInSpace.tidy`,
  `Turing.MultiTapeTM.ComputableInSpace.of_tidy` and
  `Turing.MultiTapeTM.ComputableTidilyInSpace.computableInSpace`.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {α β : Type*} {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
  {S : α → ℕ}

/-- A function computable within space `O(S)` is tidily computable within it. -/
theorem ComputableInSpace.tidy (h : ComputableInSpace f encIn encOut S) :
    ComputableTidilyInSpace f encIn encOut S := by
  obtain ⟨t, c, hc, hl⟩ := h
  obtain ⟨d, hd, hdl⟩ := hc.computableTidilyInO hl
  refine ⟨t, d * (c + 1), hd.mono (fun a => ?_) (fun a => ?_), fun a => (hdl a).trans ?_⟩
  · nlinarith [Nat.zero_le (d * c * t a)]
  all_goals nlinarith

/-- A function tidily computable within space `O(S)` is computable within it, by the same
machine. -/
theorem ComputableInSpace.of_tidy (h : ComputableTidilyInSpace f encIn encOut S) :
    ComputableInSpace f encIn encOut S :=
  let ⟨_, c, hc, hl⟩ := h
  ⟨_, c, hc.computableInTimeAndSpace, hl⟩

/-- `Turing.MultiTapeTM.ComputableInSpace.of_tidy` for dot notation on a tidy hypothesis. -/
theorem ComputableTidilyInSpace.computableInSpace (h : ComputableTidilyInSpace f encIn encOut S) :
    ComputableInSpace f encIn encOut S :=
  .of_tidy h

/-- **Plain and tidy computability within a space bound agree.** -/
theorem computableInSpace_iff_computableTidilyInSpace :
    ComputableInSpace f encIn encOut S ↔ ComputableTidilyInSpace f encIn encOut S :=
  ⟨ComputableInSpace.tidy, ComputableInSpace.of_tidy⟩

end Turing.MultiTapeTM
