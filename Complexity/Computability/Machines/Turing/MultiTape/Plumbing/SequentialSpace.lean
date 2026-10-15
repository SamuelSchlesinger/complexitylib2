/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Plumbing/Sequential.lean`)

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential

/-!
# Space of a sequential run

Two run paths to halted configurations, the second started where the first halted, join to a run
path of `tm₀.seq tm₁` that visits at most the cells of the two paths together
(`exists_runPath_seq_space`). This is `Turing.MultiTapeTM.exists_runPath_seq` with the space bound
that `Turing.MultiTapeTM.transformsTapes_seq` proves inline, for paths between arbitrary
configurations.

## Main results

* `Turing.MultiTapeTM.exists_runPath_seq_space`: the time and space of a sequential run path.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State₀ State₁ : Type*} {input : List Symbol}
  {tm₀ : MultiTapeTM k Symbol State₀} {tm₁ : MultiTapeTM k Symbol State₁}

open Sequential in
/-- **The space of a sequential run.** A run path of `tm₀` to a halted configuration, followed by a
run path of `tm₁` to a halted configuration started where `tm₀` halted, gives a run path of `seq`
taking at most the steps and visiting at most the cells of the two paths together. -/
theorem exists_runPath_seq_space {p₀ : tm₀.RunPath input} (h₀ : p₀.last.Halted)
    {p₁ : tm₁.RunPath input} (h₁ : p₁.head = p₀.last.withState (some tm₁.q₀))
    (hp₁ : p₁.last.Halted) :
    ∃ p : (tm₀.seq tm₁).RunPath input, p.head = leftCfg tm₁ p₀.head ∧
      p.last = rightCfg p₁.last ∧ p.time ≤ p₀.time + p₁.time ∧
      p.space ≤ p₀.space + p₁.space := by
  obtain ⟨p, hh, hl, ht, hmem⟩ := exists_runPath_seq h₀ h₁ hp₁
  refine ⟨p, hh, hl, ht, ?_⟩
  -- every head position of the composed path is one of the first path or one of the second
  refine (p.space_le_sum_card
    (S := fun i => p₀.visitedByTapeHead i ∪ p₁.visitedByTapeHead i) fun c hc i => ?_).trans
    ((Finset.sum_le_sum fun i _ => Finset.card_union_le _ _).trans_eq Finset.sum_add_distrib)
  rcases hmem c hc with ⟨_, ⟨n, rfl⟩, he⟩ | ⟨_, ⟨n, rfl⟩, he⟩ <;>
    rw [show c.workTapePos i = _ from congrArg (·.workTapePos i) he]
  · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ n))
  · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ n))

end Turing.MultiTapeTM
