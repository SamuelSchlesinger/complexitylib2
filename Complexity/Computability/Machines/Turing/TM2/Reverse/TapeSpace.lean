/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.TM2.Reverse.Tape
public import Complexity.Computability.Machines.Turing.MultiTape.Deterministic
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas

/-!
# Raw tape storage equals native visited space

The raw two-stack representation retains every visited blank, but stores no unvisited cell.
Its absolute window grows by inserting the new head position. Consequently its size is exactly
native visited space, even during arbitrarily long computations that revisit old cells.

## Main definitions

* `Turing.MultiTapeTM.ToTM2.Tape.window`: the stored interval at an absolute head position.
* `Turing.MultiTapeTM.ToTM2.Tape.nativeAction`: the work-tape action, including halted stuttering.
* `Turing.MultiTapeTM.ToTM2.Tape.run`: raw work tapes along a native machine run.

## Main results

* `Turing.MultiTapeTM.ToTM2.Tape.window_run`: stored cells are exactly visited cells.
* `Turing.MultiTapeTM.ToTM2.Tape.span_run_eq_spaceUsedByTape`: exact per-tape space.
* `Turing.MultiTapeTM.ToTM2.Tape.sum_span_run_le`: a native space bound bounds all raw storage.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ToTM2.Tape

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- Absolute positions stored by a raw tape with its head at `pos`. -/
def window (t : Tape Symbol) (pos : ℤ) : Finset ℤ :=
  Finset.Icc (pos - t.left.length) (pos + t.right.length)

@[simp] theorem card_window (t : Tape Symbol) (pos : ℤ) :
    (t.window pos).card = t.span := by
  rw [window, Int.card_Icc]
  unfold span
  omega

/-- A tape step stores precisely its previous window and its new head position. -/
theorem window_step (t : Tape Symbol) (a : Option (Option Symbol) × SignType) (pos : ℤ) :
    (t.step a).window (pos + a.2) = insert (pos + a.2) (t.window pos) := by
  ext z
  simp only [window, Finset.mem_Icc, Finset.mem_insert]
  rcases a with ⟨w, d⟩
  cases d <;>
    simp only [length_left_step, length_right_step, SignType.cast, add_zero]
  all_goals omega

/-- The action on work tape `i`; a halted machine neither writes nor moves. -/
noncomputable def nativeAction (tm : MultiTapeTM k Symbol State)
    (c : Cfg k Symbol State input) (i : Fin k) : Option (Option Symbol) × SignType :=
  match c.state with
  | none => (none, .zero)
  | some q => (tm.tr q c.inputSymbol c.workTapeSymbols).workTapes i

/-- The effective action gives the exact new head position, including after halting. -/
theorem nativeAction_pos (tm : MultiTapeTM k Symbol State)
    (c : Cfg k Symbol State input) (i : Fin k) :
    (tm.step c).workTapePos i = c.workTapePos i + (nativeAction tm c i).2 := by
  cases hs : c.state with
  | none => simp [nativeAction, hs, SignType.cast]
  | some q => rw [tm.step_of_state hs]; simp [nativeAction, hs, Action.apply]

/-- Raw tape semantics follows the native step, also at halted configurations. -/
theorem Represents.nativeStep {t : Tape Symbol} {tm : MultiTapeTM k Symbol State}
    {c : Cfg k Symbol State input} {i : Fin k}
    (h : t.Represents (c.workTapes i) (c.workTapePos i)) :
    (t.step (nativeAction tm c i)).Represents
      ((tm.step c).workTapes i) ((tm.step c).workTapePos i) := by
  cases hs : c.state with
  | none => simpa [nativeAction, hs, Tape.step, Tape.write, tm.step_of_halt hs] using h
  | some q =>
    rw [nativeAction, hs, tm.step_of_state hs]
    exact h.step ((tm.tr q c.inputSymbol c.workTapeSymbols).workTapes i)

/-- Raw work-tape states after `n` native steps from blank work tapes. -/
noncomputable def run (tm : MultiTapeTM k Symbol State) (input : List Symbol) :
    ℕ → Fin k → Tape Symbol
  | 0, _ => init
  | n + 1, i => (run tm input n i).step
      (nativeAction tm (tm.runFrom (tm.initCfg input) n) i)

@[simp] theorem run_zero (tm : MultiTapeTM k Symbol State) (input : List Symbol) (i : Fin k) :
    run tm input 0 i = init := rfl

/-- The raw tape along a native run represents the complete native tape and its head. -/
theorem represents_run (tm : MultiTapeTM k Symbol State) (input : List Symbol) (n : ℕ)
    (i : Fin k) :
    (run tm input n i).Represents ((tm.runFrom (tm.initCfg input) n).workTapes i)
      ((tm.runFrom (tm.initCfg input) n).workTapePos i) := by
  induction n with
  | zero => exact Represents.init
  | succ n ih => rw [run, runFrom_succ]; exact ih.nativeStep

private theorem visited_succ (tm : MultiTapeTM k Symbol State)
    (c : Cfg k Symbol State input) (n : ℕ) (i : Fin k) :
    tm.visitedByTapeHead c (n + 1) i =
      insert ((tm.runFrom c (n + 1)).workTapePos i) (tm.visitedByTapeHead c n i) := by
  ext z
  simp only [tm.mem_visitedByTapeHead, Finset.mem_insert]
  constructor
  · rintro ⟨m, hm, hz⟩
    by_cases h : m = n + 1
    · exact .inl (h ▸ hz).symm
    · exact .inr ⟨m, by omega, hz⟩
  · rintro (hz | ⟨m, hm, hz⟩)
    · exact ⟨n + 1, by omega, hz.symm⟩
    · exact ⟨m, by omega, hz⟩

/-- Every stored cell has been visited, and every visited cell remains stored. -/
theorem window_run (tm : MultiTapeTM k Symbol State) (input : List Symbol) (n : ℕ)
    (i : Fin k) :
    (run tm input n i).window ((tm.runFrom (tm.initCfg input) n).workTapePos i) =
      tm.visitedByTapeHead (tm.initCfg input) n i := by
  induction n with
  | zero => simp [run, window, init, MultiTapeTM.visitedByTapeHead, runFrom, MultiTapeNTM.initCfg]
  | succ n ih =>
    rw [run, runFrom_succ, nativeAction_pos, window_step, ih, visited_succ, runFrom_succ,
      nativeAction_pos]

/-- Raw tape storage is exactly the number of native visited cells on that tape. -/
theorem span_run_eq_spaceUsedByTape (tm : MultiTapeTM k Symbol State) (input : List Symbol)
    (n : ℕ) (i : Fin k) :
    (run tm input n i).span = tm.spaceUsedByTape (tm.initCfg input) n i := by
  rw [← card_window _ ((tm.runFrom (tm.initCfg input) n).workTapePos i), window_run]
  rfl

/-- Summed raw storage equals native space, with no runtime term. -/
theorem sum_span_run_eq_space (tm : MultiTapeTM k Symbol State) (input : List Symbol) (n : ℕ) :
    ∑ i, (run tm input n i).span = tm.space (tm.initCfg input) n := by
  simp only [span_run_eq_spaceUsedByTape]
  rfl

/-- A native space certificate bounds raw storage at every time, including after halting. -/
theorem sum_span_run_le {tm : MultiTapeTM k Symbol State} {input : List Symbol} {s : ℕ}
    (hs : tm.RunsInSpace input s) (n : ℕ) : ∑ i, (run tm input n i).span ≤ s := by
  rw [sum_span_run_eq_space]
  exact hs (.ofDeterministic tm input n)

/-- Each individual raw tape also fits the native total space bound. -/
theorem span_run_le {tm : MultiTapeTM k Symbol State} {input : List Symbol} {s : ℕ}
    (hs : tm.RunsInSpace input s) (n : ℕ) (i : Fin k) : (run tm input n i).span ≤ s :=
  (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans
    (sum_span_run_le hs n)

end Turing.MultiTapeTM.ToTM2.Tape
