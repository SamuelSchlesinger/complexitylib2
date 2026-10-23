/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Reachability.InductiveCounting.Completeness
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.InductiveCounting.Encoding
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.InductiveCounting.Graph
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine

/-!
# The input-scanning query machine for inductive counting

The machine first counts the read-only input in binary. It then runs the streaming counting
controller on the compact configuration graph. Neither the input nor a sequence of choices is
stored in its state. Each edge-query phase requests exactly the source configuration's input
symbol; all other phases ignore the supplied input symbol.

## Main definitions

* `Turing.InductiveCounting.Runtime`: the binary input counter and optional counting state.
* `Turing.InductiveCounting.queryMachine`: the complete binary-choice query machine.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.6][Sipser2013]
-/

@[expose] public section

namespace Turing.InductiveCounting

open MultiTapeTM MultiTapeNTM.ConfigurationGraph

/-- Before counting, `counting = none` and `length` is the next input position to inspect.
Afterward `length` is the full input length and `counting` is the bounded controller state. -/
structure Runtime where
  /-- A binary input-length counter. -/
  length : ℕ
  /-- The controller is installed only after the end of the input has been read. -/
  counting : Option Cslib.InductiveCounting.State

/-- The state encoding omits the input and every proof-level choice history. -/
def encRuntime : Runtime ↪ List Bool :=
  ⟨fun s => encPair encNat (encOption encState) (s.length, s.counting), by
    intro s t h
    have h' := (encPair encNat (encOption encState)).injective h
    cases s
    cases t
    cases h'
    rfl⟩

variable {k : ℕ} {State : Type} [Fintype State]
  (ntm : MultiTapeNTM k Bool State) (D : ℕ)

/-- Enough binary choices to guess every graph identifier, without retrying invalid guesses. -/
def guessWidth (n : ℕ) : ℕ := (vertexBound (k := k) D n).size

/-- Answer a pending graph request using at most the one supplied input symbol. -/
noncomputable def localAnswer (n : ℕ) (s : Cslib.InductiveCounting.State)
    (symbol : Option Bool) : Bool :=
  match Cslib.InductiveCounting.query s with
  | some (.edge u v) => edgeWithSymbol ntm D n u v symbol
  | some (.bad u) => bad (k := k) (State := State) D n u
  | none => false

/-- Input lookup for the length scan or the controller's pending edge request. -/
noncomputable def runtimeQuery (s : Runtime) : ℕ :=
  match s.counting with
  | none => s.length
  | some c =>
    match Cslib.InductiveCounting.query c with
    | some (.edge u _) => queryIndex (k := k) D s.length u
    | _ => 0

/-- The first phase increments a binary input counter. The second executes one checked
controller instruction. There is no unbounded search for a valid random guess. -/
noncomputable def runtimeNext (s : Runtime) (symbol : Option Bool) (choice : Bool) : Runtime :=
  match s.counting with
  | none =>
    if symbol.isSome then ⟨s.length + 1, none⟩ else
      ⟨s.length, some (Cslib.InductiveCounting.initial
        (vertexBound (k := k) D s.length) (startID ntm D s.length))⟩
  | some c =>
    ⟨s.length, some (Cslib.InductiveCounting.advance
      (vertexBound (k := k) D s.length) (guessWidth (k := k) D s.length)
      (startID ntm D s.length) c (localAnswer ntm D s.length c symbol) choice)⟩

/-- No state halts during the initial input scan. -/
def runtimeHalted (s : Runtime) : Bool :=
  s.counting.any Cslib.InductiveCounting.halted

/-- Acceptance is precisely the controller's accepting finite phase. -/
def runtimeAccept (s : Runtime) : Bool :=
  s.counting.any fun c => c.phase == .accept

/-- The full uniform query machine. The original native machine and radix exponent are fixed
when its program is selected; the runtime input does not supply code or advice. -/
noncomputable def queryMachine : NondeterministicQueryMachine Runtime where
  init := ⟨0, none⟩
  query := runtimeQuery (k := k) D
  next p := runtimeNext ntm D p.1 p.2.1 p.2.2
  halted := runtimeHalted
  accept := runtimeAccept

/-- Every compact graph identifier can be expressed by the chosen number of choice bits. -/
theorem vertexBound_lt_two_pow_guessWidth (n : ℕ) :
    vertexBound (k := k) D n < 2 ^ guessWidth (k := k) D n := Nat.lt_size_self _

/-- An edge request reads the same original input symbol as the compact configuration graph. -/
theorem localAnswer_eq (input : List Bool) (s : Cslib.InductiveCounting.State) :
    localAnswer ntm D input.length s
      input[runtimeQuery (k := k) D ⟨input.length, some s⟩]? =
    Cslib.InductiveCounting.answer (graphEdge ntm D input)
      (bad (k := k) (State := State) D input.length) s := by
  unfold localAnswer Cslib.InductiveCounting.answer
  cases h : Cslib.InductiveCounting.query s with
  | none => rfl
  | some q => cases q <;> simp [runtimeQuery, h, graphEdge]

/-- After the length scan, one query-machine instruction is exactly one checked controller
instruction, including on rejecting and already halted branches. -/
theorem step_counting (input : List Bool) (s : Cslib.InductiveCounting.State) (choice : Bool) :
    (queryMachine ntm D).step input ⟨input.length, some s⟩ choice =
      ⟨input.length, some (Cslib.InductiveCounting.step
        (vertexBound (k := k) D input.length) (guessWidth (k := k) D input.length)
        (startID ntm D input.length) (graphEdge ntm D input)
        (bad (k := k) (State := State) D input.length) s choice)⟩ := by
  simp only [NondeterministicQueryMachine.step, queryMachine, runtimeHalted, Option.any_some,
    NondeterministicQueryMachine.read]
  by_cases h : Cslib.InductiveCounting.halted s = true
  · simp only [h, ↓reduceIte, Cslib.InductiveCounting.step,
      Cslib.InductiveCounting.advance_halted _ _ h]
  · have h' : Cslib.InductiveCounting.halted s = false := Bool.eq_false_iff.mpr h
    simp only [h', Bool.false_eq_true, ↓reduceIte, runtimeNext,
      Cslib.InductiveCounting.step, localAnswer_eq]

/-- Choice replays after bootstrap agree exactly with the controller's replays. -/
theorem replay_counting (input : List Bool) (s : Cslib.InductiveCounting.State)
    (choices : List Bool) :
    (queryMachine ntm D).replay input choices ⟨input.length, some s⟩ =
      ⟨input.length, some (Cslib.InductiveCounting.replay
        (vertexBound (k := k) D input.length) (guessWidth (k := k) D input.length)
        (startID ntm D input.length) (graphEdge ntm D input)
        (bad (k := k) (State := State) D input.length) s choices)⟩ := by
  induction choices generalizing s with
  | nil => rfl
  | cons choice choices ih =>
    rw [NondeterministicQueryMachine.replay_cons, step_counting, ih]
    rfl

/-- The input scan ignores the choice bit and advances exactly one input position. -/
theorem step_scan (input : List Bool) {j : ℕ} (hj : j < input.length) (choice : Bool) :
    (queryMachine ntm D).step input ⟨j, none⟩ choice = ⟨j + 1, none⟩ := by
  simp [NondeterministicQueryMachine.step, NondeterministicQueryMachine.read, queryMachine,
    runtimeHalted, runtimeQuery, runtimeNext, List.getElem?_eq_getElem hj]

/-- Reading the first absent input bit installs the controller, without retaining the input. -/
theorem step_scan_end (input : List Bool) (choice : Bool) :
    (queryMachine ntm D).step input ⟨input.length, none⟩ choice =
      ⟨input.length, some (Cslib.InductiveCounting.initial
        (vertexBound (k := k) D input.length) (startID ntm D input.length))⟩ := by
  simp [NondeterministicQueryMachine.step, NondeterministicQueryMachine.read, queryMachine,
    runtimeHalted, runtimeQuery, runtimeNext]

/-- Every prefix of the input scan has the same binary counter, independently of its choices. -/
theorem replay_scan (input : List Bool) (choices : List Bool) {j : ℕ}
    (hj : j + choices.length ≤ input.length) :
    (queryMachine ntm D).replay input choices ⟨j, none⟩ = ⟨j + choices.length, none⟩ := by
  induction choices generalizing j with
  | nil => simp [NondeterministicQueryMachine.replay]
  | cons choice choices ih =>
    rw [NondeterministicQueryMachine.replay_cons, step_scan ntm D input (by
      simp only [List.length_cons] at hj; omega), ih (by
      simp only [List.length_cons] at hj; omega)]
    simp only [List.length_cons]
    congr 1
    omega

/-- Every choice sequence of bootstrap length reaches exactly the initialized controller. -/
theorem run_bootstrap (input : List Bool) (choices : List Bool)
    (hlen : choices.length = input.length + 1) :
    (queryMachine ntm D).run input choices =
      ⟨input.length, some (Cslib.InductiveCounting.initial
        (vertexBound (k := k) D input.length) (startID ntm D input.length))⟩ := by
  have ht : (choices.take input.length).length = input.length := by
    simp only [List.length_take, hlen, Nat.min_eq_left (Nat.le_succ input.length)]
  have hd : (choices.drop input.length).length = 1 := by simp [hlen]
  obtain ⟨choice, hd⟩ := List.length_eq_one_iff.mp hd
  unfold NondeterministicQueryMachine.run
  conv_lhs => rw [← List.take_append_drop input.length choices]
  rw [NondeterministicQueryMachine.replay_append]
  change (queryMachine ntm D).replay input (choices.drop input.length)
    ((queryMachine ntm D).replay input (choices.take input.length) ⟨0, none⟩) = _
  rw [replay_scan ntm D input _ (by omega), ht, Nat.zero_add, hd,
    NondeterministicQueryMachine.replay_cons, NondeterministicQueryMachine.replay_nil]
  exact step_scan_end ntm D input choice

/-- After bootstrap, all remaining choices are exactly a controller replay. -/
theorem run_after_bootstrap (input : List Bool) (choices : List Bool)
    (hlen : input.length + 1 ≤ choices.length) :
    (queryMachine ntm D).run input choices =
      ⟨input.length, some (Cslib.InductiveCounting.replay
        (vertexBound (k := k) D input.length) (guessWidth (k := k) D input.length)
        (startID ntm D input.length) (graphEdge ntm D input)
        (bad (k := k) (State := State) D input.length)
        (Cslib.InductiveCounting.initial
          (vertexBound (k := k) D input.length) (startID ntm D input.length))
        (choices.drop (input.length + 1)))⟩ := by
  conv_lhs => rw [← List.take_append_drop (input.length + 1) choices]
  rw [NondeterministicQueryMachine.run_append, run_bootstrap ntm D input _ (by
    simp only [List.length_take, Nat.min_eq_left hlen]), replay_counting]

/-- An explicit finite clock for every abstract branch, including dishonest guesses. -/
noncomputable def abstractTime (n : ℕ) : ℕ :=
  n + 1 + Cslib.InductiveCounting.rank
    (vertexBound (k := k) D n) (guessWidth (k := k) D n)
    (Cslib.InductiveCounting.initial (vertexBound (k := k) D n) (startID ntm D n))

/-- Every branch of the complete query machine halts within the same input-dependent clock. -/
theorem queryMachine_haltsWithin (input : List Bool) :
    (queryMachine ntm D).HaltsWithin input (abstractTime ntm D input.length) := by
  intro choices hlen
  have hlong : input.length + 1 ≤ choices.length := by rw [hlen]; exact Nat.le_add_right _ _
  rw [run_after_bootstrap ntm D input choices hlong]
  change Cslib.InductiveCounting.halted _ = true
  apply Cslib.InductiveCounting.halted_replay_of_rank_le
  simp only [List.length_drop, hlen, abstractTime]
  omega

/-- Bootstrap adds no accepting branches and removes no controller choices. -/
theorem queryMachine_accepts_iff (input : List Bool) :
    (queryMachine ntm D).Accepts input ↔
      Cslib.InductiveCounting.Accepts
        (vertexBound (k := k) D input.length) (guessWidth (k := k) D input.length)
        (startID ntm D input.length) (graphEdge ntm D input)
        (bad (k := k) (State := State) D input.length) := by
  constructor
  · rintro ⟨choices, _, ha⟩
    by_cases hshort : choices.length ≤ input.length
    · have hr : (queryMachine ntm D).run input choices = ⟨choices.length, none⟩ := by
        simpa only [NondeterministicQueryMachine.run, queryMachine, Nat.zero_add] using
          replay_scan ntm D input choices (j := 0) (by omega)
      rw [hr] at ha
      simp [queryMachine, runtimeAccept] at ha
    · rw [run_after_bootstrap ntm D input choices (by omega)] at ha
      exact ⟨choices.drop (input.length + 1), by
        simpa only [queryMachine, runtimeAccept, Option.any_some, beq_iff_eq] using ha⟩
  · rintro ⟨choices, ha⟩
    refine ⟨List.replicate (input.length + 1) false ++ choices, ?_, ?_⟩
    all_goals
      rw [NondeterministicQueryMachine.run_append,
        run_bootstrap ntm D input _ (List.length_replicate ..), replay_counting]
    · simp [queryMachine, runtimeHalted, Cslib.InductiveCounting.halted, ha]
    · simp [queryMachine, runtimeAccept, ha]

/-- The compact start vertex is in the counting domain under the source space bound. -/
theorem startID_lt_of_runsInSpace (input : List Bool) (c : ℕ)
    (hspace : ntm.RunsInSpace input (c * (Nat.log2 input.length + 1))) :
    startID ntm (radixExponent State c) input.length <
      vertexBound (k := k) (radixExponent State c) input.length := by
  have h := vertexID_lt (fits_of_runsInSpace c hspace (Relation.ReflTransGen.refl))
  rw [vertexID_init] at h
  exact h

/-- Every accepting branch of the complete query machine certifies native nonacceptance. -/
theorem queryMachine_accepts_sound (input : List Bool) (c : ℕ)
    (hspace : ntm.RunsInSpace input (c * (Nat.log2 input.length + 1)))
    (h : (queryMachine ntm (radixExponent State c)).Accepts input) :
    ¬ ntm.Accepts input :=
  (safe_iff_not_accepts ntm input c hspace).mp
    (Cslib.InductiveCounting.accepts_sound (startID_lt_of_runsInSpace ntm input c hspace)
      ((queryMachine_accepts_iff ntm (radixExponent State c) input).mp h))

/-- The complete query machine accepts exactly the complement of native acceptance, using the
actual guarded counting controller and compact configuration graph. -/
theorem queryMachine_accepts_iff_not_accepts (input : List Bool) (c : ℕ)
    (hspace : ntm.RunsInSpace input (c * (Nat.log2 input.length + 1))) :
    (queryMachine ntm (radixExponent State c)).Accepts input ↔ ¬ ntm.Accepts input := by
  rw [queryMachine_accepts_iff,
    Cslib.InductiveCounting.accepts_iff (startID_lt_of_runsInSpace ntm input c hspace)
      (vertexBound_lt_two_pow_guessWidth (k := k) (radixExponent State c) input.length).le]
  exact safe_iff_not_accepts ntm input c hspace

end Turing.InductiveCounting
