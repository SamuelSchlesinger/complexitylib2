/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Interpretation.Tagged

/-!
# First-order reductions on structures with two elements

First-order reductions (`Cslib.Logic.FO.Reduces`) are asked to be correct on every finite
structure, including the empty one and those with one element. On these, an interpretation of the
unordered structures of this library has little room: an interpretation of positive dimension
maps the empty structure to the empty structure, and a structure with one element to a structure
with at most one element. Whether a reduction to a class exists then depends on how the class
treats its smallest members. Every structure with at most one element is an independent set
instance with a solution, for example, while the empty clause on one element is an unsatisfiable
CNF structure, so SAT is not first-order reducible to independent set in this sense.

Immerman's structures are ordered and have at least one element, and his reductions may test the
constants `0` and `max` of the ordering, so that small structures are definable cases
[Immerman, Chapters 1 and 3][Immerman1999]. The closest unordered convention asks for
correctness on the structures with two distinct elements only: `K` is **first-order reducible to
`K'` on nontrivial structures** (`Cslib.Logic.FO.ReducesNontrivial K K'`) when some interpretation
maps each finite structure with two distinct elements inside `K'` exactly when it is in `K`. Every
first-order reduction is one. Such reductions compose when the first maps nontrivial structures to
nontrivial ones (`Cslib.Logic.FO.ReducesNontrivial.trans_of_nontrivial`), as compiled tagged
interpretations do (`Cslib.Logic.FO.ReducesNontrivial.of_tagged`), and when the second is a
first-order reduction (`Cslib.Logic.FO.ReducesNontrivial.trans_reduces`).

## Main definitions

* `Cslib.Logic.FO.ReducesNontrivial`: first-order reducibility on structures with two distinct
  elements.

## Main results

* `Cslib.Logic.FO.Reduces.reducesNontrivial`: first-order reductions are reductions on nontrivial
  structures.
* `Cslib.Logic.FO.ReducesNontrivial.refl`, `Cslib.Logic.FO.ReducesNontrivial.trans_reduces`,
  `Cslib.Logic.FO.ReducesNontrivial.trans_of_nontrivial`: reflexivity and composition.
* `Cslib.Logic.FO.ReducesNontrivial.of_tagged`: reductions on nontrivial structures by tagged
  interpretations, whose compiled interpretations keep structures nontrivial.
* `Cslib.Logic.FO.Reduces.of_reducesNontrivial`: between classes containing every structure with
  at most one element, reductions on nontrivial structures are first-order reductions.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999]
-/

@[expose] public section

universe u v u' v' u'' v'' w

open FirstOrder Language Structure CategoryTheory

namespace Cslib.Logic.FO

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {L'' : Language.{u'', v''}}
  [L'.IsRelational] [L''.IsRelational]

/-- A class `K` of `L`-structures is **first-order reducible on nontrivial structures** to a class
`K'` of `L'`-structures when some first-order interpretation of `L'` in `L` maps every finite
`L`-structure with two distinct elements inside `K'` exactly when it is in `K`. -/
def ReducesNontrivial (K : Set (Bundled.{w} L.Structure)) (K' : Set (Bundled.{w} L'.Structure)) :
    Prop :=
  ∃ (ι : Type) (_ : Finite ι) (I : Interpretation L L' ι),
    ∀ (M : Bundled.{w} L.Structure) [Finite M], Nontrivial M →
      (M ∈ K ↔ Bundled.of (c := L'.Structure) (I.Model M) ∈ K')

variable {K : Set (Bundled.{w} L.Structure)} {K' : Set (Bundled.{w} L'.Structure)}
  {K'' : Set (Bundled.{w} L''.Structure)}

/-- A first-order reduction is a reduction on nontrivial structures. -/
theorem Reduces.reducesNontrivial (h : Reduces K K') : ReducesNontrivial K K' :=
  let ⟨ι, hι, I, hI⟩ := h
  ⟨ι, hι, I, fun M _ _ => hI M⟩

namespace ReducesNontrivial

/-- Reducibility on nontrivial structures is reflexive on classes closed under isomorphism. -/
theorem refl [L.IsRelational] (hK : IsoClosed K) : ReducesNontrivial K K :=
  (Reduces.refl hK).reducesNontrivial

/-- A reduction on nontrivial structures followed by a first-order reduction. -/
theorem trans_reduces (h : ReducesNontrivial K K') (h' : Reduces K' K'') (hK'' : IsoClosed K'') :
    ReducesNontrivial K K'' := by
  obtain ⟨ι, _, I, hI⟩ := h
  obtain ⟨κ, _, J, hJ⟩ := h'
  refine ⟨κ × ι, inferInstance, J.comp I, fun M _ hM => ?_⟩
  rw [hI M hM, hJ (Bundled.of (I.Model M))]
  exact hK'' (Interpretation.compEquiv J I)

/-- A reduction on nontrivial structures through an interpretation that keeps them nontrivial,
followed by a reduction on nontrivial structures. -/
theorem trans_of_nontrivial {ι : Type} [Finite ι] (I : Interpretation L L' ι)
    (hI : ∀ (M : Bundled.{w} L.Structure) [Finite M], Nontrivial M →
      Nontrivial (I.Model M) ∧ (M ∈ K ↔ Bundled.of (c := L'.Structure) (I.Model M) ∈ K'))
    (h' : ReducesNontrivial K' K'') (hK'' : IsoClosed K'') : ReducesNontrivial K K'' := by
  obtain ⟨κ, _, J, hJ⟩ := h'
  refine ⟨κ × ι, inferInstance, J.comp I, fun M _ hM => ?_⟩
  obtain ⟨hnt, hiff⟩ := hI M hM
  rw [hiff, hJ (Bundled.of (I.Model M)) hnt]
  exact hK'' (Interpretation.compEquiv J I)

end ReducesNontrivial

/-- A reduction on nontrivial structures between classes containing every finite structure with
at most one element is a first-order reduction: an interpretation maps a structure with at most one
element to a structure with at most one element. -/
theorem Reduces.of_reducesNontrivial (h : ReducesNontrivial K K')
    (hK : ∀ (M : Bundled.{w} L.Structure) [Finite M], Subsingleton M → M ∈ K)
    (hK' : ∀ (N : Bundled.{w} L'.Structure) [Finite N], Subsingleton N → N ∈ K') :
    Reduces K K' := by
  obtain ⟨ι, _, I, hI⟩ := h
  refine .of_interpretation I fun M _ => ?_
  rcases subsingleton_or_nontrivial M with hM | hM
  · have : Subsingleton (I.Model M) :=
      ⟨fun x y => Interpretation.Model.ext (Subsingleton.elim _ _)⟩
    exact iff_of_true (hK M hM) (hK' _ this)
  · exact hI M hM

variable (L L') in
/-- The interpretation of dimension one with an empty domain. -/
def Interpretation.empty : Interpretation L L' Unit where
  domain := ⊥
  rel _ := ⊥

omit [L'.IsRelational] in
/-- On a structure with two distinct elements, the compiled interpretation of a tagged
interpretation whose structures are nonempty is nontrivial: there are at least two copies. -/
theorem TaggedInterpretation.nontrivial_toInterpretation_model {T : Type} [Finite T]
    {ι : T → Type} [∀ t, Finite (ι t)] (I : TaggedInterpretation L L' T ι)
    (S : Interpretation L L' Unit) {M : Type w} [L.Structure M] [Nontrivial M]
    [Nonempty (I.Model M)] : Nontrivial ((I.toInterpretation S).Model M) := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne M
  obtain ⟨e⟩ := ‹Nonempty (I.Model M)›
  refine ⟨⟨TaggedInterpretation.ofCopies S ⟨⟨(x, y), hxy⟩, e⟩,
    TaggedInterpretation.ofCopies S ⟨⟨(y, x), hxy.symm⟩, e⟩, fun h => hxy ?_⟩⟩
  have := (TaggedInterpretation.ofCopies_bijective S).1 h
  exact congrArg (fun c : Copies (TaggedInterpretation.Pairs M) (I.Model M) => c.idx.1.1) this

/-- **Tagged interpretations give reductions on nontrivial structures** to classes closed under
isomorphism and copies, when their structures on nontrivial inputs are nonempty; the compiled
interpretation keeps structures nontrivial. -/
theorem ReducesNontrivial.of_tagged_nontrivial {K : Set (Bundled.{w} L.Structure)}
    {K' : Set (Bundled.{w} L'.Structure)} (hK' : IsoClosed K') (hcopy : CopyInvariant K')
    {T : Type} [Finite T] {ι : T → Type} [∀ t, Finite (ι t)]
    (I : TaggedInterpretation L L' T ι)
    (hne : ∀ (M : Type w) [L.Structure M] [Finite M], Nontrivial M → Nonempty (I.Model M))
    (hlarge : ∀ (M : Bundled.{w} L.Structure) [Finite M], Nontrivial M →
      (M ∈ K ↔ (Bundled.of (I.Model M) : Bundled.{w} L'.Structure) ∈ K'))
    (M : Bundled.{w} L.Structure) [Finite M] (hM : Nontrivial M) :
    Nontrivial ((I.toInterpretation (Interpretation.empty L L')).Model M) ∧
      (M ∈ K ↔ Bundled.of (c := L'.Structure)
        ((I.toInterpretation (Interpretation.empty L L')).Model M) ∈ K') := by
  have := hne M hM
  refine ⟨I.nontrivial_toInterpretation_model _, ?_⟩
  have : Finite (Bundled.of (c := L'.Structure)
      (Copies (TaggedInterpretation.Pairs M) (I.Model M))) :=
    inferInstanceAs (Finite (Copies _ _))
  rw [hlarge M hM, ← hcopy (TaggedInterpretation.Pairs M)]
  exact hK' (TaggedInterpretation.copiesEquiv _)

/-- **Tagged interpretations give reductions on nontrivial structures** to classes closed under
isomorphism and copies. -/
theorem ReducesNontrivial.of_tagged {K : Set (Bundled.{w} L.Structure)}
    {K' : Set (Bundled.{w} L'.Structure)} (hK' : IsoClosed K') (hcopy : CopyInvariant K')
    {T : Type} [Finite T] {ι : T → Type} [∀ t, Finite (ι t)]
    (I : TaggedInterpretation L L' T ι)
    (hne : ∀ (M : Type w) [L.Structure M] [Finite M], Nontrivial M → Nonempty (I.Model M))
    (hlarge : ∀ (M : Bundled.{w} L.Structure) [Finite M], Nontrivial M →
      (M ∈ K ↔ (Bundled.of (I.Model M) : Bundled.{w} L'.Structure) ∈ K')) :
    ReducesNontrivial K K' :=
  ⟨_, inferInstance, I.toInterpretation (Interpretation.empty L L'), fun M _ hM =>
    (ReducesNontrivial.of_tagged_nontrivial hK' hcopy I hne hlarge M hM).2⟩

end Cslib.Logic.FO
