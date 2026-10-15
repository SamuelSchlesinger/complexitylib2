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

The space used by a run of `tm₀.seq tm₁` is at most the space of the run of `tm₀` plus the space
of the run of `tm₁` started where `tm₀` halted (`spaceUsed_seq_le`), for arbitrary configurations.
This is the space half of `Turing.MultiTapeTM.runFrom_seq`; the corresponding bound for tape
transformations is part of `Turing.MultiTapeTM.transformsTapes_seq`.

## Main results

* `Turing.MultiTapeTM.spaceUsed_seq_le`: the space of a sequential run.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State₀ State₁ : Type*} {input : List Symbol}
  {tm₀ : MultiTapeTM k Symbol State₀} {tm₁ : MultiTapeTM k Symbol State₁}

open Sequential in
/-- If `tm₀` halts at step `u`, the first `u + n` steps of `seq` use at most the space of the run
of `tm₀` plus the space of the first `n` steps of `tm₁`, started where `tm₀` halted. -/
theorem HaltsAt.spaceUsed_seq_le {cfg : Cfg k Symbol State₀ input} {u : ℕ}
    (h : tm₀.HaltsAt cfg u) (n : ℕ) :
    (tm₀.seq tm₁).spaceUsed (leftCfg tm₁ cfg) (u + n) ≤
      tm₀.spaceUsed cfg u + tm₁.spaceUsed ((tm₀.runFrom cfg u).withState (some tm₁.q₀)) n := by
  refine (spaceUsed_add_le _ _ _).trans (Nat.add_le_add (le_of_eq ?_) (le_of_eq ?_))
  · -- the first phase visits what `tm₀` visits, including the cell of the handoff
    refine (spaceUsed_eq_of_workTapePos _ _ u fun m hm => ?_).symm
    rcases Nat.lt_or_ge m u with hm' | hm'
    · rw [runFrom_leftCfg cfg m fun _ hr => h.not_halted (by omega), workTapePos_leftCfg]
    · obtain rfl : m = u := le_antisymm hm hm'
      rw [← add_zero m, h.runFrom_seq, workTapePos_rightCfg]
      rfl
  · -- the second phase visits what `tm₁` visits
    rw [show (tm₀.seq tm₁).runFrom (leftCfg tm₁ cfg) u = _ from by
      simpa using h.runFrom_seq (tm₁ := tm₁) 0]
    refine spaceUsed_eq_of_workTapePos _ _ n fun m _ => ?_
    rw [runFrom_rightCfg, workTapePos_rightCfg]
    rfl

/-- **The space of a sequential run.** If `tm₀` has halted in `mid` by step `t₀`, and `tm₁`, started
where `tm₀` halted, has halted by step `t₁`, then the first `t₀ + t₁` steps of `seq` use at most
the space of the two runs together. -/
theorem spaceUsed_seq_le {cfg mid : Cfg k Symbol State₀ input} {t₀ t₁ : ℕ}
    (h₀ : tm₀.runFrom cfg t₀ = mid) (hmid : mid.Halted)
    (h₁ : (tm₁.runFrom (mid.withState (some tm₁.q₀)) t₁).Halted) :
    (tm₀.seq tm₁).spaceUsed (Sequential.leftCfg tm₁ cfg) (t₀ + t₁) ≤
      tm₀.spaceUsed cfg t₀ + tm₁.spaceUsed (mid.withState (some tm₁.q₀)) t₁ := by
  obtain ⟨u, hu, hhaltsAt⟩ := exists_haltsAt (tm := tm₀) (cfg := cfg) (h₀ ▸ hmid)
  have hmid' : tm₀.runFrom cfg u = mid := (hhaltsAt.runFrom_eq hu).symm.trans h₀
  -- the composed machine has halted by step `u + t₁`
  have hhalt : ((tm₀.seq tm₁).runFrom (Sequential.leftCfg tm₁ cfg) (u + t₁)).Halted := by
    rw [hhaltsAt.runFrom_seq, hmid']
    simp only [Cfg.Halted] at h₁ ⊢
    simp [Sequential.rightCfg, h₁]
  rw [spaceUsed_eq_of_halt _ (by omega : u + t₁ ≤ t₀ + t₁) hhalt]
  refine (hhaltsAt.spaceUsed_seq_le t₁).trans (Nat.add_le_add (spaceUsed_mono tm₀ _ hu) ?_)
  rw [hmid']

end Turing.MultiTapeTM
