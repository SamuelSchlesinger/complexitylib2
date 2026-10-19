/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Interpretation
public import Mathlib.ModelTheory.Complexity

/-!
# Quantifier-free interpretations

An interpretation is quantifier-free when its domain and relation formulas are quantifier-free.
Such interpretations preserve quantifier-free formulas under pullback and compose. This is a
syntactic property, distinct from the single-input-literal restriction of a projection.

## Main definitions

* `Cslib.Logic.FO.Interpretation.IsQF`: quantifier-free domain and relation definitions.

## Main results

* `Cslib.Logic.FO.Interpretation.IsQF.onFormula`: pullback preserves quantifier-freeness.
* `Cslib.Logic.FO.Interpretation.IsQF.comp`: quantifier-free interpretations compose.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999]
-/

@[expose] public section

namespace FirstOrder.Language.BoundedFormula.IsQF

variable {L L' : Language} {α β : Type*} {n : ℕ}

/-- A finite conjunction of quantifier-free formulas is quantifier-free. -/
theorem iInf [Finite β] (f : β → L.BoundedFormula α n) (h : ∀ b, (f b).IsQF) :
    (BoundedFormula.iInf f).IsQF := by
  suffices ∀ s : List β, ((s.map f).foldr (· ⊓ ·) ⊤).IsQF from this _
  intro s
  induction s with
  | nil => exact .top
  | cons b _ ih => exact (h b).inf ih

/-- Mapping relation and function symbols preserves quantifier-freeness. -/
theorem onBoundedFormula {φ : L.BoundedFormula α n} (h : φ.IsQF) (f : L →ᴸ L') :
    (f.onBoundedFormula φ).IsQF := by
  induction h with
  | falsum => exact .falsum
  | of_isAtomic h =>
    cases h with
    | equal => exact (IsAtomic.equal _ _).isQF
    | rel => exact (IsAtomic.rel _ _).isQF
  | imp _ _ ih₁ ih₂ => exact ih₁.imp ih₂

end FirstOrder.Language.BoundedFormula.IsQF

namespace Cslib.Logic.FO.Interpretation

open FirstOrder Language

variable {L L' L'' : Language} {ι κ α : Type*}

/-- Quantifier-free interpretations have both a quantifier-free domain and quantifier-free
relation definitions. This permits arbitrary Boolean combinations of input relations. -/
structure IsQF (I : Interpretation L L' ι) : Prop where
  /-- The domain introduces no quantifiers. -/
  domain : I.domain.IsQF
  /-- No relation definition introduces quantifiers. -/
  rel : ∀ {n} (R : L'.Relations n), (I.rel R).IsQF

theorem IsQF.onBoundedFormula [Finite ι] [L'.IsRelational] {I : Interpretation L L' ι}
    (hI : I.IsQF) {n : ℕ} {φ : L'.BoundedFormula α n} (hφ : φ.IsQF) :
    (I.onBoundedFormula φ).IsQF := by
  induction hφ with
  | falsum => exact .falsum
  | of_isAtomic h =>
    cases h with
    | equal => exact BoundedFormula.IsQF.iInf _ fun _ => (BoundedFormula.IsAtomic.equal _ _).isQF
    | rel R ts => exact (hI.rel R).relabel _
  | imp _ _ ih₁ ih₂ => exact ih₁.imp ih₂

/-- Quantifier-free interpretations preserve quantifier-free formulas under pullback. -/
theorem IsQF.onFormula [Finite ι] [L'.IsRelational] {I : Interpretation L L' ι}
    (hI : I.IsQF) {φ : L'.Formula α} (hφ : φ.IsQF) : (I.onFormula φ).IsQF :=
  (hI.onBoundedFormula hφ).relabel _

theorem isQF_id (L : Language) : (Interpretation.id L).IsQF :=
  ⟨.top, fun _ => (BoundedFormula.IsAtomic.rel _ _).isQF⟩

/-- Quantifier-free interpretations compose, including their relativized domains. -/
theorem IsQF.comp [Finite ι] [Finite κ] [L'.IsRelational]
    {J : Interpretation L' L'' κ} {I : Interpretation L L' ι} (hJ : J.IsQF) (hI : I.IsQF) :
    (J.comp I).IsQF :=
  ⟨(BoundedFormula.IsQF.iInf _ fun _ => hI.domain.relabel _).inf (hI.onFormula hJ.domain),
    fun R => (hI.onFormula (hJ.rel R)).relabel _⟩

end Cslib.Logic.FO.Interpretation
