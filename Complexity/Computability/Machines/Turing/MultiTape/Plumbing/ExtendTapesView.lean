/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Plumbing/ExtendTapes.lean`)

public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes

/-!
# The view of a configuration through a tape embedding

For an embedding `e : Fin k ↪ Fin k'` of work tapes, `viewCfg e cfg` is the configuration of a
machine with `k` work tapes that sees the tapes `e j` of `cfg`. Placing it back with
`Turing.MultiTapeTM.embed` gives `cfg` (`embed_viewCfg`), so the run of `tm.extendTapes e` from
any configuration is the run of `tm` on the view, placed back (`runFrom_extendTapes`). This
generalises `Turing.MultiTapeTM.oneTapeCfg` and `Turing.MultiTapeTM.runFrom_tapeEmb` from one tape
to any embedding.

## Main definitions

* `Turing.MultiTapeTM.viewCfg`: the view of a configuration through a tape embedding.

## Main results

* `Turing.MultiTapeTM.runFrom_extendTapes`, `Turing.MultiTapeTM.space_extendTapes_le`: the run
  and the space of a machine run on the tapes selected by an embedding.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k k' : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- The configuration of a machine with `k` work tapes seeing the tapes `e j` of `cfg`. -/
def viewCfg (e : Fin k ↪ Fin k') (cfg : Cfg k' Symbol State input) : Cfg k Symbol State input :=
  ⟨cfg.state, cfg.inputPos, fun j => cfg.workTapes (e j), fun j => cfg.workTapePos (e j),
    cfg.output⟩

/-- A configuration is its view through `e`, placed back on the tapes `e j`. -/
theorem embed_viewCfg (e : Fin k ↪ Fin k') (cfg : Cfg k' Symbol State input) :
    embed e (viewCfg e cfg) cfg.workTapes cfg.workTapePos = cfg := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> simp only [embed, viewCfg] <;>
    · cases h : partialInv e l with
      | none => rfl
      | some j => rw [← partialInv_eq_some e h]

/-- **Running a machine on the tapes selected by an embedding.** The run is the run on the view of
the configuration, placed back on the selected tapes; every other tape and head keeps its starting
value. -/
theorem runFrom_extendTapes (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k')
    (cfg : Cfg k' Symbol State input) (n : ℕ) :
    (tm.extendTapes e).runFrom cfg n =
      embed e (tm.runFrom (viewCfg e cfg) n) cfg.workTapes cfg.workTapePos := by
  rw [← embedHom_apply tm, ← runFrom_map, embedHom_apply, embed_viewCfg]

/-- **Space of a machine run on the tapes selected by an embedding:** the space of the run on the
view, plus one cell for each tape the machine does not use. -/
theorem space_extendTapes_le (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k')
    (cfg : Cfg k' Symbol State input) (n : ℕ) :
    (tm.extendTapes e).space cfg n ≤ tm.space (viewCfg e cfg) n + (k' - k) := by
  conv_lhs => rw [← embed_viewCfg e cfg]
  exact space_embed_le _ _ _ _ _ _

end Turing.MultiTapeTM
