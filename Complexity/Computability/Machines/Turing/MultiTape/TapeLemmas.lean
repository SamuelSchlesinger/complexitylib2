/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: submitted #1111 @3441fa81

public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas
public import Complexity.Computability.Machines.Turing.MultiTape.Deterministic
public import Complexity.Computability.Machines.Turing.MultiTape.Nondeterministic

/-!
# Space of run paths and of halted runs

The additions of cslib PR #1111 to `Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas`.

`MultiTapeNTM.RunPath.space_le_mul_time_add_one` bounds the space of any run path by its length.

`MultiTapeTM.runsInSpace_of_runPath` turns the space of a single run path to a halted configuration
into a space bound for every computation path, since a deterministic machine stays where it is
after halting.

## Main results

* `Turing.MultiTapeNTM.RunPath.space_le_mul_time_add_one`.
* `Turing.MultiTapeTM.mem_of_last_halted`, `Turing.MultiTapeTM.runsInSpace_of_runPath`.
-/

@[expose] public section

namespace Turing.MultiTapeNTM

variable {k : ℕ} {State Symbol : Type*} {input : List Symbol}
variable {ntm : MultiTapeNTM k Symbol State}

namespace RunPath

/-- Each head visits at most one cell per configuration, so a path visits at most `k * (time + 1)`
cells. -/
lemma space_le_mul_time_add_one (p : ntm.RunPath input) : p.space ≤ k * (p.time + 1) :=
  calc p.space ≤ ∑ _ : Fin k, (p.time + 1) :=
        Finset.sum_le_sum fun _ _ => Finset.card_image_le.trans_eq (Finset.card_fin _)
    _ = k * (p.time + 1) := by simp

end RunPath

end Turing.MultiTapeNTM

namespace Turing.MultiTapeTM

variable {k : ℕ}
variable {State Symbol : Type*}
variable {input : List Symbol}
variable {tm : MultiTapeTM k Symbol State}

/-! ### Space of halted runs -/

/-- Every configuration on a path from the head of a path that ends halted lies on that path: after
halting, a deterministic machine stays where it is. -/
lemma mem_of_last_halted {p q : tm.RunPath input} (hp : p.last.Halted) (hq : q.head = p.head) :
    ∀ c ∈ q, c ∈ p := by
  rintro _ ⟨n, rfl⟩
  have hlast : tm.runFrom p.head p.length = p.last := (runPath_apply_eq_runFrom p (.last _)).symm
  rw [runPath_apply_eq_runFrom, hq]
  rcases le_or_gt n.val p.length with h | h
  · exact ⟨⟨n, Nat.lt_succ_of_le h⟩, runPath_apply_eq_runFrom p _⟩
  · rw [runFrom_eq_of_halt tm _ h.le (hlast ▸ hp), hlast]
    exact ⟨.last _, rfl⟩

/-- A run path from the initial configuration to a halted configuration, using at most `s` cells,
bounds the space of every computation path by `s`. -/
lemma runsInSpace_of_runPath {s : ℕ} {p : tm.RunPath input} (hhead : p.head = tm.initCfg input)
    (hp : p.last.Halted) (hs : p.space ≤ s) : tm.RunsInSpace input s :=
  fun q => (MultiTapeNTM.RunPath.space_le_of_subset
    (mem_of_last_halted hp (q.head_eq.trans hhead.symm))).trans hs

end Turing.MultiTapeTM
