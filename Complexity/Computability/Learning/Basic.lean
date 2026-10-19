/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.Product
public import Mathlib.InformationTheory.Hamming
public import Cslib.Probability.PMF

/-!
# Learning from uniform random examples

A *concept* is a Boolean function `f` on the cube `ι → Bool`, and a *concept class* is a set of
concepts. A learner receives labelled examples `(x, f x)` of an unknown target `f` from the class,
at independent uniformly random points `x` (`Learning.uniformExamples`), and outputs a hypothesis
`h`, possibly using its own random choices (`Learning.Learner`). Its *error* is the fraction of
the points where `h` differs from `f` (`Learning.error`): the probability that `h` misclassifies
a fresh uniform point. A learner *learns* the class with error `ε` and confidence `1 - δ`
(`Learning.Learner.Learns`) if, for every target in the class, the hypothesis has error above `ε`
with probability at most `δ`, over the examples and the learner's own random choices. This is
learning from random examples under the uniform distribution, the setting of the low-degree
algorithm of Linial, Mansour and Nisan [LinialMansourNisan1993]
[O'Donnell, Section 3.4][ODonnell2014]; Valiant's model of probably approximately correct learning
asks the same for every distribution of the points [Valiant1984].

A deterministic learner computes its hypothesis from the examples (`Learning.Learner.ofHypothesis`);
it learns exactly when, for every target, few uniform samples of points lead to a bad hypothesis
(`Learning.Learner.learns_ofHypothesis_iff`). The examples are independent
(`Learning.uniformExamples_eq_pi`).

The definitions here are information-theoretic: they bound the number of examples, not the running
time of the learner.

## Main definitions

* `Cslib.Learning.examples`, `Cslib.Learning.uniformExamples`: the examples of a concept at given
  points, and at independent uniform points.
* `Cslib.Learning.error`: the error of a hypothesis under the uniform distribution.
* `Cslib.Learning.Learner`: a randomized learner from a fixed number of examples.
* `Cslib.Learning.Learner.Learns`: learning a concept class from uniform random examples.
* `Cslib.Learning.Learner.ofHypothesis`: a deterministic learner.

## Main results

* `Cslib.Learning.uniformExamples_eq_pi`: the examples are independent.
* `Cslib.Learning.Learner.learns_ofHypothesis_iff`: learning by a deterministic learner, in terms
  of uniform samples of points.
* `Cslib.Learning.Learner.Learns.mono`: learning is monotone in the class, the error and the
  confidence.

## References

* [L. G. Valiant, *A theory of the learnable*][Valiant1984]
* [N. Linial, Y. Mansour, N. Nisan, *Constant depth circuits, Fourier transform, and
  learnability*][LinialMansourNisan1993]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.Learning

open Cslib.Probability
open scoped ENNReal

variable {ι : Type*} {m : ℕ}

/-- The examples of `f` at the points `x j`: the labelled pairs `(x j, f (x j))`. -/
def examples (f : (ι → Bool) → Bool) (x : Fin m → ι → Bool) : Fin m → (ι → Bool) × Bool :=
  fun j => (x j, f (x j))

@[simp] theorem examples_apply (f : (ι → Bool) → Bool) (x : Fin m → ι → Bool) (j : Fin m) :
    examples f x j = (x j, f (x j)) :=
  rfl

variable [Fintype ι] [DecidableEq ι]

/-- `m` labelled examples of `f` at independent uniformly random points. -/
noncomputable def uniformExamples (f : (ι → Bool) → Bool) (m : ℕ) :
    PMF (Fin m → (ι → Bool) × Bool) :=
  (PMF.uniformOfFintype (Fin m → ι → Bool)).map (examples f)

/-- The examples are independent, each a uniform point labelled by `f`. -/
theorem uniformExamples_eq_pi (f : (ι → Bool) → Bool) (m : ℕ) :
    uniformExamples f m =
      PMF.pi fun _ : Fin m => (PMF.uniformOfFintype (ι → Bool)).map fun x => (x, f x) := by
  rw [PMF.pi_map, PMF.pi_uniformOfFintype]
  rfl

/-- The error of a hypothesis `h` for the target `f` under the uniform distribution: the fraction
of the points where `h` and `f` differ. -/
noncomputable def error (f h : (ι → Bool) → Bool) : ℝ :=
  hammingDist h f / 2 ^ Fintype.card ι

theorem error_nonneg (f h : (ι → Bool) → Bool) : 0 ≤ error f h := by
  unfold error
  positivity

@[simp] theorem error_self (f : (ι → Bool) → Bool) : error f f = 0 := by
  simp [error]

variable (ι m) in
/-- A learner from `m` labelled examples on the cube `ι → Bool`: it maps the examples to a
distribution of hypotheses, the outcome of its own random choices. -/
abbrev Learner : Type _ :=
  (Fin m → (ι → Bool) × Bool) → PMF ((ι → Bool) → Bool)

namespace Learner

/-- The learner `A` *learns* the concept class `C` from `m` uniform random examples with error
`ε` and confidence `1 - δ`: for every target `f ∈ C`, the hypothesis output by `A` on `m` examples
of `f` at independent uniform points has error above `ε` with probability at most `δ`. -/
def Learns (A : Learner ι m) (C : Set ((ι → Bool) → Bool)) (ε δ : ℝ) : Prop :=
  ∀ f ∈ C, ((uniformExamples f m).bind A).toOuterMeasure {h | ε < error f h} ≤ ENNReal.ofReal δ

/-- Learning is monotone: a smaller class, a larger error and a smaller confidence. -/
theorem Learns.mono {A : Learner ι m} {C C' : Set ((ι → Bool) → Bool)} {ε ε' δ δ' : ℝ}
    (hA : A.Learns C ε δ) (hC : C' ⊆ C) (hε : ε ≤ ε') (hδ : δ ≤ δ') : A.Learns C' ε' δ' :=
  fun f hf => (((uniformExamples f m).bind A).toOuterMeasure.mono fun _ hh =>
    hε.trans_lt hh).trans ((hA f (hC hf)).trans (ENNReal.ofReal_le_ofReal hδ))

/-- The deterministic learner computing the hypothesis `hyp e` from the examples `e`. -/
noncomputable def ofHypothesis (hyp : (Fin m → (ι → Bool) × Bool) → (ι → Bool) → Bool) :
    Learner ι m :=
  fun e => PMF.pure (hyp e)

/-- A deterministic learner learns `C` exactly when, for every target `f ∈ C`, the uniform samples
of `m` points whose examples lead to a hypothesis of error above `ε` have probability at most
`δ`. -/
theorem learns_ofHypothesis_iff {hyp : (Fin m → (ι → Bool) × Bool) → (ι → Bool) → Bool}
    {C : Set ((ι → Bool) → Bool)} {ε δ : ℝ} :
    (ofHypothesis hyp).Learns C ε δ ↔ ∀ f ∈ C,
      (PMF.uniformOfFintype (Fin m → ι → Bool)).toOuterMeasure
        {x | ε < error f (hyp (examples f x))} ≤ ENNReal.ofReal δ := by
  refine forall₂_congr fun f _ => ?_
  change ((uniformExamples f m).bind (PMF.pure ∘ hyp)).toOuterMeasure _ ≤ _ ↔ _
  rw [PMF.bind_pure_comp, uniformExamples, PMF.map_comp, PMF.toOuterMeasure_map_apply]
  rfl

end Learner

end Cslib.Learning
