/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.PPT.Clock
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Composition
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure

/-!
# Composing uniformly efficient probabilistic programs

Encoded probabilistic programs compose through ordinary monadic `bind`. Each certificate gives
one finite machine for every input. The output-length bound controls the continuation's clock,
and the machine compiler charges every instruction needed to prepare its fresh input.

This module also registers deterministic preprocessing and postprocessing with `fun_prop`.
Continuations here consume the sampled result; `PPT.Capture` supplies the copying construction
for retaining the caller's input.

## Main results

* `Cslib.Probability.IsPPTOn.bind`: monadic composition preserves uniform strict PPT.
* `Cslib.Probability.IsPPTOn.map`: polynomial-time deterministic postprocessing preserves PPT.
* `Cslib.Probability.IsPPTOn.preprocess`: efficiently prepare a probabilistic program's input.

## References

Adapted from `Computability/Probabilistic/Realization/Composition.lean` and
`Computability/Probabilistic/Composition.lean` on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, reusing the common machine and tidy deterministic
calculus.
-/

@[expose] public section

namespace Cslib.Probability

open Turing.MultiTapePTM
open Turing.MultiTapeTM (ComputableTidilyInPolyTime)

variable {α β γ : Type} {input : α ↪ List Bool} {middle : β ↪ List Bool}
  {output : γ ↪ List Bool}

/-- Sequence two uniformly efficient encoded programs. The intermediate output length bounds
the continuation's time, and input preparation is included in the compiled polynomial clock. -/
@[fun_prop]
theorem IsPPTOn.bind {first : α → ProbComp β} {second : β → ProbComp γ}
    (hfirst : IsPPTOn input middle first) (hsecond : IsPPTOn middle output second) :
    IsPPTOn input output (fun a => do
      let b ← first a
      second b) := by
  obtain ⟨k₀, State₀, hfinite₀, source, c₀, d₀, hsource, hsourceHalt⟩ :=
    hfirst.exists_halting_machine
  obtain ⟨k₁, State₁, hfinite₁, target, c₁, d₁, htarget, htargetHalt⟩ :=
    hsecond.exists_halting_machine
  let firstTime := fun length => c₀ * (length + 1) ^ d₀
  let secondTime := fun length => c₁ * (firstTime length + 1) ^ d₁
  have hpoly : PolynomiallyBounded
      (fun length => firstTime length + (firstTime length + 4 + secondTime length)) := by
    fun_prop
  obtain ⟨coefficient, degree, htime⟩ := polynomiallyBounded_iff_le.mp hpoly
  refine ⟨k₁ + k₀ + 2,
    State₀ ⊕ ((Turing.MultiTapeTM.MarkWorkState ⊕ Turing.MultiTapeTM.RewindWorkState) ⊕ State₁),
    inferInstance, target.comp source true, coefficient, degree, fun a => ?_⟩
  let encoded := input a
  have hbound (word : List Bool)
      (hword : word ∈
        (ProbComp.eval (source.runClosed (firstTime encoded.length) encoded)).support) :
      c₁ * (word.length + 1) ^ d₁ ≤ secondTime encoded.length :=
    Nat.mul_le_mul_left c₁ (Nat.pow_le_pow_left
      (Nat.add_le_add_right (source.length_output_eval_runClosed_le _ _ _ hword) 1) d₁)
  have htargetBound (word : List Bool)
      (hword : word ∈
        (ProbComp.eval (source.runClosed (firstTime encoded.length) encoded)).support) :
      ∀ final ∈ (ProbComp.eval
        (target.runClosedConfigFrom (secondTime encoded.length)
          (target.initialConfig word))).support,
        final.tapes.state = none := by
    intro final hfinal
    rw [eval_runClosedConfigFrom_eq_of_halted target _ (hbound word hword) (htargetHalt word)]
      at hfinal
    exact htargetHalt word final hfinal
  have hhalt := comp_halted source target true encoded (firstTime encoded.length)
    (secondTime encoded.length) (hsourceHalt encoded) htargetBound
  rw [eval_runClosed_eq_of_halted _ _ (htime encoded.length) hhalt,
    eval_comp source target true encoded _ _ (hsourceHalt encoded) htargetBound,
    ← hsource a, PMF.bind_map, ProbComp.eval_bind, PMF.map_bind]
  apply PMF.bind_congr_on_support
  intro result hresult
  have hword : middle result ∈
      (ProbComp.eval (source.runClosed (firstTime encoded.length) encoded)).support := by
    rw [← hsource a]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, hresult, rfl⟩
  exact (htarget result).trans
    (eval_runClosed_eq_of_halted target _ (hbound _ hword) (htargetHalt _)).symm

/-- Prepare the encoded argument of a uniformly efficient probabilistic program. -/
@[fun_prop]
theorem IsPPTOn.preprocess {program : β → ProbComp γ} {prepare : α → β}
    (hprogram : IsPPTOn middle output program)
    (hprepare : ComputableTidilyInPolyTime prepare input middle) :
    IsPPTOn input output (fun a => program (prepare a)) := by
  simpa only [pure_bind] using hprepare.isPPTOn.bind hprogram

/-- Polynomial-time deterministic processing of each sampled result preserves PPT. -/
@[fun_prop]
theorem IsPPTOn.map {program : α → ProbComp β} {f : β → γ}
    (hprogram : IsPPTOn input middle program) (hf : ComputableTidilyInPolyTime f middle output) :
    IsPPTOn input output (fun a => f <$> program a) := by
  simpa only [bind_pure_comp] using hprogram.bind hf.isPPTOn

end Cslib.Probability
