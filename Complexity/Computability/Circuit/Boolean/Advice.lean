/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.PolynomialTime
public import Complexity.Computability.Circuit.Boolean.Substitution

/-!
# Polynomial advice

A machine *takes advice* when, on an input `x` of length `n`, it also reads a string `α n` that
depends only on `n` [Arora and Barak, Definition 6.10][AroraBarak09]. With the advice placed in
front of the input as the pair `(α |x|, x)`, encoded as `frame (α |x|) ++ x`, a language is in
`PAdvice` when it consists of the inputs whose pair lies in a problem decidable in polynomial time,
for advice of polynomial length. This is the class `⋃ DTIME(n ^ c) / n ^ d` of
[Arora and Barak, Theorem 6.11][AroraBarak09], the original definition of `P/poly`
[Karp and Lipton][KarpLipton1980].

Hardwiring the advice into circuits for the pairs gives circuits for the language: at each length
`n` the first `2 |α n| + 1` inputs are fixed to the bits of `frame (α n)`, which costs two gates for
the constants (`PPoly.of_advice`). With `P ⊆ P/poly` (`PPoly.exists_of_mem_P`), every language in
`PAdvice` is in `PPoly` (`PAdvice_subset_PPoly`). The machine enters only through the hypothesis
that the problem of pairs is in `Complexity.P`. The converse inclusion needs a machine evaluating
circuits in polynomial time, which is not proved here.

## Main definitions

* `Cslib.Circuits.Boolean.PAdvice`: polynomial time with polynomial advice.

## Main results

* `Cslib.Circuits.Boolean.PPoly.of_advice`: hardwiring advice of polynomial length into circuits
  of polynomial size.
* `Cslib.Circuits.Boolean.PAdvice_subset_PPoly`: `P/advice ⊆ P/poly`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.3][AroraBarak09]
* [R. M. Karp, R. J. Lipton, *Some connections between nonuniform and uniform complexity
  classes*][KarpLipton1980]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Turing.MultiTapeTM

/-- **Hardwiring advice.** If `x ∈ L` exactly when `frame (α |x|) ++ x ∈ M`, with `M` in `P/poly`
and advice `α` of polynomial length, then `L` is in `P/poly`: fixing the first inputs of the
circuits for `M` to the bits of `frame (α n)` costs two gates. -/
theorem PPoly.of_advice {L M : Language Bool} (hM : M ∈ PPoly) (α : ℕ → List Bool)
    (hα : PolynomiallyBounded fun n => (α n).length)
    (h : ∀ x, x ∈ L ↔ frame (α x.length) ++ x ∈ M) : L ∈ PPoly := by
  set q := fun N => complexity interpretation (single (M.slice N))
  have hq : PolynomiallyBounded q := hM
  refine PolynomiallyBounded.mono_of_le (g := fun n => q (2 * (α n).length + 1 + n) + 2)
    (by fun_prop) fun n => ?_
  let a : Fin (frame (α n)).length → Bool := fun j => (frame (α n))[j]
  have ha : List.ofFn a = frame (α n) := List.ofFn_getElem
  have hslice : L.slice n = fun x => M.slice ((frame (α n)).length + n)
      (substitute (prependInputs a) x) := by
    funext x
    rw [Bool.eq_iff_iff, Language.slice_eq_true_iff, Language.slice_eq_true_iff,
      substitute_prependInputs, List.ofFn_fin_append, h, List.length_ofFn, ha]
  have hc := complexity_substitute_le (prependInputs a) (M.slice ((frame (α n)).length + n))
  rwa [← hslice, length_frame] at hc

/-- **Polynomial time with polynomial advice** [Arora and Barak, Definition 6.10][AroraBarak09]:
the languages `L` with advice `α` of polynomial length and a problem `A` of pairs, decidable in
polynomial time for the encoding `frame u ++ x` of `(u, x)`, such that `x ∈ L` exactly when
`(α |x|, x) ∈ A`. -/
def PAdvice : Set (Language Bool) :=
  {L | ∃ α : ℕ → List Bool, PolynomiallyBounded (fun n => (α n).length) ∧
    ∃ A ∈ Complexity.P (encPair encBits encBits), ∀ x, x ∈ L ↔ (α x.length, x) ∈ A}

/-- **P/advice ⊆ P/poly** [Arora and Barak, Theorem 6.11][AroraBarak09]: a language decided in
polynomial time with polynomial advice has circuits of polynomial size. -/
theorem PAdvice_subset_PPoly : PAdvice ⊆ PPoly := by
  rintro L ⟨α, hα, A, hA, hL⟩
  obtain ⟨M, hM, hAM⟩ := PPoly.exists_of_mem_P hA
  exact PPoly.of_advice hM α hα fun x => (hL x).trans (hAM _)

end Cslib.Circuits.Boolean
