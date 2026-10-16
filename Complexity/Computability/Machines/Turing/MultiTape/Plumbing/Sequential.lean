/-
Copyright (c) 2026 Christian Reitwiessner and Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: submitted #1111 @3441fa81

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
public import Complexity.Computability.Machines.Turing.MultiTape.TapeLemmas

/-!
# Space of a sequential run

The additions of cslib PR #1111 to
`Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential`.

## Main results

* `Turing.MultiTapeTM.exists_runPath_seq_space_le`: the composed path visits at most the cells of
  the two paths combined.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State₀ State₁ : Type*} {input : List Symbol}

variable {tm₀ : MultiTapeTM k Symbol State₀} {tm₁ : MultiTapeTM k Symbol State₁}

open Sequential in
/-- **Space of a sequential run.** The run path of `seq` composed from two run paths visits at most
the cells of the two paths combined. -/
theorem exists_runPath_seq_space_le {p₀ : tm₀.RunPath input} (h₀ : p₀.last.Halted)
    {p₁ : tm₁.RunPath input} (h₁ : p₁.head = p₀.last.withState (some tm₁.q₀))
    (hp₁ : p₁.last.Halted) :
    ∃ p : (tm₀.seq tm₁).RunPath input, p.head = leftCfg tm₁ p₀.head ∧
      p.last = rightCfg p₁.last ∧ p.length ≤ p₀.length + p₁.length ∧
      p.space ≤ p₀.space + p₁.space := by
  obtain ⟨p, hh, hl, ht, hmem⟩ := exists_runPath_seq h₀ h₁ hp₁
  refine ⟨p, hh, hl, ht, ?_⟩
  -- every head position of the composed run is one of the first path or one of the second
  refine (p.space_le_sum_card
    (S := fun i => p₀.visitedByTapeHead i ∪ p₁.visitedByTapeHead i) fun c hc i => ?_).trans
    ((Finset.sum_le_sum fun i _ => Finset.card_union_le _ _).trans_eq Finset.sum_add_distrib)
  rcases hmem c hc with ⟨_, ⟨n, rfl⟩, he⟩ | ⟨_, ⟨n, rfl⟩, he⟩ <;>
    rw [show c.workTapePos i = _ from congrArg (·.workTapePos i) he]
  · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ n))
  · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ n))

end Turing.MultiTapeTM
