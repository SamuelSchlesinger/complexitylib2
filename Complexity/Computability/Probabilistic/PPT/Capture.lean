/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.PPT.Composition
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.OutputPrefix
import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Run
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# Captured inputs in efficient probabilistic programs

Ordinary monadic continuations and callbacks may use both the caller's input and a sampled
result. A tidy deterministic routine writes the retained data before the sampler runs; the
existing pair encoding makes this a typed value for the next computation. The machine proof
charges all copying, framing and preparation, without exposing those details to clients.

## Main results

* `Cslib.Probability.IsPPTOn.pair`: retain efficiently computed data alongside a sampled result.
* `Cslib.Probability.IsPPTOn.bind_with`: a monadic continuation may capture the original input.
* `Cslib.Probability.IsPPTOn.map_with`: a deterministic callback may capture the original input.
* `Cslib.Probability.IsPPTOn.cond`, `Cslib.Probability.IsPPTOn.ite`: efficient branch selection.

## References

Adapted from `Computability/Probabilistic/{Realization/Composition,Composition}.lean` on the cslib
`crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the existing tidy calculus
and framed pair encoding.
-/

@[expose] public section

namespace Cslib.Probability

open Turing Turing.MultiTapeTM Turing.MultiTapePTM Turing.MultiTapeMachine

/-- Write efficiently computed input data before a probabilistic output, charging preparation. -/
theorem IsPPTOn.prefix {α : Type} {input : α ↪ List Bool} {pre : α → List Bool}
    {program : α → ProbComp (List Bool)} (hprogram : IsPPTOn input encBits program)
    (hprefix : ComputableTidilyInPolyTime pre input encBits) :
    IsPPTOn input encBits (fun a => (pre a ++ ·) <$> program a) := by
  obtain ⟨t, s, ⟨ci, di, ht⟩, _, ki, InitState, hfinite, initializer, hi⟩ := hprefix
  obtain ⟨ks, State, hfinite', source, cs, ds, hsource, hhalt⟩ := hprogram.exists_halting_machine
  let prep := initializer.extendTapes (Fin.castAddEmb ks)
  let runner := source.extendTapes (Fin.natAddEmb ki)
  let compiled := (ofDeterministic prep).seq runner
  let prepareTime := fun length => ci * (length + 1) ^ di
  let runTime := fun length => cs * (length + 1) ^ ds
  have hpoly : PolynomiallyBounded (fun length => prepareTime length + runTime length) := by
    fun_prop
  obtain ⟨coefficient, degree, htime⟩ := polynomiallyBounded_iff_le.mp hpoly
  have hprep (a : α) : prep.runFrom (prep.initCfg (input a)) (prepareTime (input a).length) =
      wordsCfg (input a) none (fun _ => []) (pre a) :=
    (((hi a).mono (ht a) le_rfl).extendTapes (Fin.castAddEmb ks)).runFrom_initCfg_eq
  have hrunner (a : α) : ∀ final ∈ (ProbComp.eval
      (runner.runClosedConfigFrom (runTime (input a).length)
        (runner.initialConfig (input a)))).support,
      final.tapes.state = none := by
    intro final hfinal
    simp only [runner, runClosedConfigFrom, initialConfig_extendTapes,
      MultiTapePTM.runConfigFrom_embed, ProbComp.eval_map] at hfinal
    obtain ⟨original, horiginal, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
    exact hhalt (input a) original horiginal
  refine ⟨ki + ks, InitState ⊕ State, inferInstance, compiled, coefficient, degree, fun a => ?_⟩
  rw [eval_runClosed_eq_of_halted compiled _ (htime (input a).length)
    (seq_prependOutput_halted prep runner (input a) (pre a) _ _ (hprep a) (hrunner a)),
    eval_seq_prependOutput prep runner (input a) (pre a) _ _ (hprep a) (hrunner a),
    runClosed_extendTapes, ← hsource a]
  simp only [ProbComp.eval_map, encBits, Function.Embedding.coe_refl, PMF.map_id]

variable {α β γ : Type} {input : α ↪ List Bool} {left : β ↪ List Bool}
  {right : γ ↪ List Bool}

/-- Retain efficiently computed input data beside a sampled result, using the existing encoding. -/
@[fun_prop]
theorem IsPPTOn.pair {program : α → ProbComp γ} {f : α → β}
    (hprogram : IsPPTOn input right program) (hf : ComputableTidilyInPolyTime f input left) :
    IsPPTOn input (encPair left right) (fun a => (fun b => (f a, b)) <$> program a) := by
  apply isPPTOn_iff_encoded.mpr
  have hframe : ComputableTidilyInPolyTime (fun b => frame (left b)) left encBits :=
    .of_linear (.of_frame fun _ => rfl)
  refine ((isPPTOn_iff_encoded.mp hprogram).prefix (hframe.comp hf)).congr ?_
  intro a
  simp only [ProbComp.eval_map, PMF.map_comp]
  rfl

/-- Keep the original argument available to a later computation, charging its encoded copy. -/
theorem IsPPTOn.keep_input {program : α → ProbComp β}
    (hprogram : IsPPTOn input left program) :
    IsPPTOn input (encPair input left) (fun a => (fun b => (a, b)) <$> program a) :=
  hprogram.pair ComputableTidilyInPolyTime.id'

/-- A monadic continuation may use both the caller's input and the sampled result. -/
@[fun_prop]
theorem IsPPTOn.bind_with {first : α → ProbComp β} {second : α → β → ProbComp γ}
    (hfirst : IsPPTOn input left first)
    (hsecond : IsPPTOn (encPair input left) right (fun pair => second pair.1 pair.2)) :
    IsPPTOn input right (fun a => do
      let b ← first a
      second a b) := by
  simpa only [bind_map_left] using hfirst.keep_input.bind hsecond

/-- A deterministic callback may capture the original argument. -/
@[fun_prop]
theorem IsPPTOn.map_with {program : α → ProbComp β} {f : α → β → γ}
    (hprogram : IsPPTOn input left program)
    (hf : ComputableTidilyInPolyTime (fun pair => f pair.1 pair.2) (encPair input left) right) :
    IsPPTOn input right (fun a => f a <$> program a) := by
  simpa only [bind_pure_comp] using
    hprogram.bind_with (right := right) (second := fun a b => pure (f a b)) hf.isPPTOn

/-- Select a closed probabilistic branch with an efficient Boolean condition. A witness may
run both total branches and discard one result; the sum of their clocks is still polynomial. -/
@[fun_prop]
theorem IsPPTOn.cond {condition : α → Bool} {yes no : α → ProbComp β}
    (hcondition : ComputableTidilyInPolyTime condition input encBool)
    (hyes : IsPPTOn input left yes) (hno : IsPPTOn input left no) :
    IsPPTOn input left (fun a => if condition a then yes a else no a) := by
  have hcombined : IsPPTOn input left (fun a => do
      let b ← yes a
      let c ← no a
      pure (if condition a then b else c)) := by
    fun_prop
  apply hcombined.congr
  intro a
  cases condition a <;> simp [ProbComp.eval_bind, PMF.map, Function.comp_def]

/-- Select a closed probabilistic branch with an efficiently decidable condition. -/
@[fun_prop]
theorem IsPPTOn.ite {condition : α → Prop} [∀ a, Decidable (condition a)]
    {yes no : α → ProbComp β}
    (hcondition : ComputableTidilyInPolyTime (fun a => decide (condition a)) input encBool)
    (hyes : IsPPTOn input left yes) (hno : IsPPTOn input left no) :
    IsPPTOn input left (fun a => if condition a then yes a else no a) := by
  simpa only [decide_eq_true_eq] using hyes.cond hcondition hno

end Cslib.Probability
