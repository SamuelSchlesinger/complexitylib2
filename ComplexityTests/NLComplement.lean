/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.InductiveCounting.Bounds
import Complexity.Computability.Complexity.Classes.LogSpace.Complement

/-! Integration tests for input bootstrap, finite binary choices and looping native sources. -/

namespace ComplexityTests.NLComplement

open Turing Turing.MultiTapeTM Turing.InductiveCounting

/-- Concrete finite query models instantiate every hypothesis of the new native compiler. -/
private theorem finite_query_native {σ : Type} [Finite σ]
    (M : NondeterministicQueryMachine σ) (time : ℕ)
    (hhalt : ∀ input, M.HaltsWithin input time) {A : Set (List Bool)}
    (hcorrect : ∀ input, input ∈ A ↔ M.Accepts input) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (ntm : MultiTapeNTM k Bool State) (c : ℕ),
      ntm.DecidesInSpace encBits A fun input => c * (Nat.log2 input.length + 1) := by
  apply M.exists_decidesInSpace (enc := encBits) (encS := encFinite σ)
    (ComputableTidilyInSpace.of_finite _)
    (ComputableTidilyInSpace.of_finite _)
    (ComputableTidilyInSpace.of_finite _)
    (ComputableTidilyInSpace.of_finite _)
    (fun _ => time) hhalt hcorrect
    (fun input : List Bool => Nat.log2 input.length + 1) (fun _ => le_rfl)
  refine ⟨Nat.card σ, fun input choices => ?_⟩
  exact (length_encFinite_lt (M.run input choices)).le.trans
    (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))

/-- One accepting and one rejecting branch, with the input answer deliberately ignored. -/
private def branching : NondeterministicQueryMachine (Fin 3) where
  init := 0
  query _ := 0
  next p := if p.2.2 then 1 else 2
  halted q := q != 0
  accept q := q == 1

example (input : List Bool) : branching.run input [true] = 1 := rfl
example (input : List Bool) : branching.run input [false] = 2 := rfl

example (input : List Bool) : branching.Accepts input := ⟨[true], rfl, rfl⟩

private theorem branching_halts (input : List Bool) : branching.HaltsWithin input 1 := by
  intro choices hlen
  obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp hlen
  cases b <;> rfl

/-- Native existential acceptance must preserve an accepting branch in the presence of a
rejecting branch. This applies the constructed compiler rather than postulating a simulator. -/
example : ∃ (k : ℕ) (State : Type) (_ : Finite State) (ntm : MultiTapeNTM k Bool State) (c : ℕ),
    ntm.DecidesInSpace encBits Set.univ fun input => c * (Nat.log2 input.length + 1) :=
  finite_query_native branching 1 branching_halts fun _ =>
    ⟨fun _ => ⟨[true], rfl, rfl⟩, fun _ => trivial⟩

/-- The native compiler must also handle zero abstract steps before halting. -/
private def initiallyHalted : NondeterministicQueryMachine Unit where
  init := ()
  query _ := 0
  next _ := ()
  halted _ := true
  accept _ := true

example (input : List Bool) : initiallyHalted.Accepts input := ⟨[], rfl, rfl⟩

private theorem initiallyHalted_halts (input : List Bool) :
    initiallyHalted.HaltsWithin input 0 := by
  intro choices hlen
  have : choices = [] := List.length_eq_zero_iff.mp hlen
  subst choices
  rfl

/-- Zero abstract steps need not mean zero native instructions: the compiler still initializes
and emits the initially halted state's verdict, within a finite native all-branches clock. -/
example : ∃ (k : ℕ) (State : Type) (_ : Finite State) (ntm : MultiTapeNTM k Bool State) (c : ℕ),
    ntm.DecidesInSpace encBits Set.univ fun input => c * (Nat.log2 input.length + 1) :=
  finite_query_native initiallyHalted 0 initiallyHalted_halts fun _ =>
    ⟨fun _ => ⟨[], rfl, rfl⟩, fun _ => trivial⟩

/-- A native source that loops forever without using a work tape or emitting a bit. -/
private def loopAction : Action 0 Bool Unit :=
  { inputTape := 0, workTapes := Fin.elim0, output := none, state := some () }

private def loopSource : MultiTapeNTM 0 Bool Unit where
  q₀ := ()
  Tr _ _ _ action := action = loopAction

private theorem not_accepts_loopSource (input : List Bool) : ¬ loopSource.Accepts input := by
  have only_initial {v : FiniteCfg 0 Bool Unit}
      (h : Relation.ReflTransGen loopSource.ViewStep (loopSource.initView input) v) :
      v = loopSource.initView input := by
    induction h with
    | refl => rfl
    | @tail a b h hstep ih =>
      rw [ih] at hstep
      obtain ⟨action, ha, rfl⟩ := hstep
      change action = loopAction at ha
      subst action
      have hwork : (fun tape : Fin 0 => (Cslib.Turing.BiTape.nil : Cslib.Turing.BiTape Bool).step
          (Fin.elim0 tape)) = fun _ => Cslib.Turing.BiTape.nil :=
        funext fun tape => Fin.elim0 tape
      simpa [FiniteCfg.summarizeOutput, FiniteCfg.step, MultiTapeNTM.initView,
        FiniteCfg.init, loopAction, MultiTapeNTM.outputClass] using hwork
  intro h
  obtain ⟨v, hv, hhalt, _⟩ := MultiTapeNTM.accepts_iff_reflTransGen_viewStep.mp h
  rw [only_initial hv] at hhalt
  contradiction

/-- Complement correctness applies even though the source has no halting computation. -/
example (input : List Bool) :
    (queryMachine loopSource (MultiTapeNTM.ConfigurationGraph.radixExponent Unit 0)).Accepts
      input :=
  (queryMachine_accepts_iff_not_accepts loopSource input 0
    (MultiTapeNTM.runsInSpace_zero_tapes _ _ _)).mpr (not_accepts_loopSource input)

/-- Startup counts exactly all input bits and one end marker, for arbitrary choices. -/
example (choices : List Bool) (hlen : choices.length = 4) :
    (queryMachine loopSource 5).run [true, false, true] choices =
      ⟨3, some (Cslib.InductiveCounting.initial
        (MultiTapeNTM.ConfigurationGraph.vertexBound (k := 0) 5 3)
        (MultiTapeNTM.ConfigurationGraph.startID loopSource 5 3))⟩ :=
  run_bootstrap loopSource 5 [true, false, true] choices hlen

/-- The empty input still executes its end-marker bootstrap step. -/
example : (queryMachine loopSource 5).run [] [false] =
    ⟨0, some (Cslib.InductiveCounting.initial
      (MultiTapeNTM.ConfigurationGraph.vertexBound (k := 0) 5 0)
      (MultiTapeNTM.ConfigurationGraph.startID loopSource 5 0))⟩ :=
  run_bootstrap loopSource 5 [] [false] rfl

/-- All branches, including dishonest choices, have bounded storage and a common clock. -/
example (input choices : List Bool) :
    (encRuntime ((queryMachine loopSource 5).run input choices)).length ≤
      storageConstant 0 5 * (Nat.log2 input.length + 1) :=
  length_run_le loopSource 5 input choices

example (input : List Bool) :
    (queryMachine loopSource 5).HaltsWithin input (abstractTime loopSource 5 input.length) :=
  queryMachine_haltsWithin loopSource 5 input

/-- A genuinely looping recognizer supplies the source hypotheses of the native theorem. -/
private theorem recognizes_loopSource : loopSource.RecognizesInSpace encBits ∅
    (fun input => 0 * (Nat.log2 input.length + 1)) := fun input =>
  ⟨MultiTapeNTM.runsInSpace_zero_tapes _ _ _, by simp [not_accepts_loopSource input]⟩

/-- The output of the actual native construction is an all-branches-halting decider. -/
example : ∃ (k : ℕ) (State : Type) (_ : Finite State) (ntm : MultiTapeNTM k Bool State) (c : ℕ),
    ntm.DecidesInSpace encBits (∅ : Set (List Bool))ᶜ
      fun input => c * (Nat.log2 input.length + 1) :=
  MultiTapeNTM.exists_decidesInLogSpace_compl recognizes_loopSource

/--
info: 'Cslib.Complexity.NL_eq_coNL' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.NL_eq_coNL

/--
info: 'Cslib.Complexity.compl_mem_NL' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.compl_mem_NL

/--
info: 'Turing.MultiTapeNTM.exists_decidesInLogSpace_compl' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeNTM.exists_decidesInLogSpace_compl

/--
info: 'Turing.NondeterministicQueryMachine.exists_decidesInSpace' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.NondeterministicQueryMachine.exists_decidesInSpace

end ComplexityTests.NLComplement
