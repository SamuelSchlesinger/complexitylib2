/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Interpretation
public import Mathlib.ModelTheory.Bundled

/-!
# First-order definability and first-order reductions

Descriptive complexity studies classes of finite structures. As in Mathlib's model theory, a class
of `L`-structures is a set of bundled structures, `Set (Bundled L.Structure)`; the notions below
only look at its finite members.

A class `K` is first-order definable (`FO.Definable K`) when some first-order sentence holds in
exactly the finite structures of `K`. Such a class is closed under isomorphism of finite
structures, and the definable classes are closed under complement, intersection and union.

A class `K` of `L`-structures is first-order reducible to a class `K'` of `L'`-structures
(`FO.Reduces K K'`) when some first-order interpretation `I` of `L'` in `L` satisfies
`M ∈ K ↔ I.Model M ∈ K'` for every finite `M` [Immerman, Chapter 3][Immerman1999].
Reducibility is reflexive and transitive on classes closed under isomorphism, and first-order
definability is closed under it: if `K'` is defined by `φ`, then `K` is defined by the pullback of
`φ` [Immerman, Definition 3.9 and Framework 3.12][Immerman1999].

## Main definitions

* `Cslib.Logic.FO.Definable`: first-order definability of a class of finite structures.
* `Cslib.Logic.FO.Reduces`: first-order reducibility between classes of finite structures.

## Main results

* `Cslib.Logic.FO.Definable.mem_iff_of_equiv`: definable classes are closed under isomorphism.
* `Cslib.Logic.FO.Definable.compl`, `Cslib.Logic.FO.Definable.inter`,
  `Cslib.Logic.FO.Definable.union`: Boolean operations.
* `Cslib.Logic.FO.Reduces.refl`, `Cslib.Logic.FO.Reduces.trans`: reducibility is a preorder on
  classes closed under isomorphism.
* `Cslib.Logic.FO.Reduces.mem_iff_of_equiv`: a class reducible to a class closed under isomorphism
  is closed under isomorphism of finite structures.
* `Cslib.Logic.FO.Definable.of_reduces`: definability is closed under first-order reductions.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999]
-/

@[expose] public section

universe u v u' v' u'' v'' w

namespace Cslib.Logic.FO

open FirstOrder Language Structure CategoryTheory

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {L'' : Language.{u'', v''}}

/-! ### First-order definability -/

/-- A class of structures is **first-order definable** when some first-order sentence holds in
exactly its finite members, among all finite structures. -/
def Definable (K : Set (Bundled.{w} L.Structure)) : Prop :=
  ∃ φ : L.Sentence, ∀ (M : Bundled.{w} L.Structure) [Finite M], M ∈ K ↔ M ⊨ φ

namespace Definable

variable {K K₁ K₂ : Set (Bundled.{w} L.Structure)}

/-- A first-order definable class is closed under isomorphism of finite structures. -/
theorem mem_iff_of_equiv (hK : Definable K) {M N : Bundled.{w} L.Structure} [Finite M]
    (e : M ≃[L] N) : M ∈ K ↔ N ∈ K := by
  obtain ⟨φ, hφ⟩ := hK
  have : Finite N := Finite.of_equiv _ e.toEquiv
  rw [hφ M, hφ N]
  exact StrongHomClass.realize_sentence e φ

/-- The complement of a first-order definable class is first-order definable. -/
theorem compl (hK : Definable K) : Definable Kᶜ := by
  obtain ⟨φ, hφ⟩ := hK
  exact ⟨φ.not, fun M _ => by rw [Set.mem_compl_iff, hφ M, Sentence.realize_not]⟩

/-- The intersection of two first-order definable classes is first-order definable. -/
theorem inter (h₁ : Definable K₁) (h₂ : Definable K₂) : Definable (K₁ ∩ K₂) := by
  obtain ⟨φ₁, hφ₁⟩ := h₁
  obtain ⟨φ₂, hφ₂⟩ := h₂
  exact ⟨φ₁ ⊓ φ₂, fun M _ => by rw [Set.mem_inter_iff, hφ₁ M, hφ₂ M, Sentence.realize_inf]⟩

/-- The union of two first-order definable classes is first-order definable. -/
theorem union (h₁ : Definable K₁) (h₂ : Definable K₂) : Definable (K₁ ∪ K₂) := by
  obtain ⟨φ₁, hφ₁⟩ := h₁
  obtain ⟨φ₂, hφ₂⟩ := h₂
  exact ⟨φ₁ ⊔ φ₂, fun M _ => by rw [Set.mem_union, hφ₁ M, hφ₂ M, Sentence.realize_sup]⟩

end Definable

/-! ### First-order reductions -/

variable [L'.IsRelational]

/-- A class `K` of `L`-structures is **first-order reducible** to a class `K'` of `L'`-structures
when some first-order interpretation of `L'` in `L` maps the finite members of `K` into `K'` and
the other finite `L`-structures outside `K'` [Immerman, Chapter 3][Immerman1999]. -/
def Reduces (K : Set (Bundled.{w} L.Structure)) (K' : Set (Bundled.{w} L'.Structure)) : Prop :=
  ∃ (ι : Type) (_ : Finite ι) (I : Interpretation L L' ι),
    ∀ (M : Bundled.{w} L.Structure) [Finite M],
      M ∈ K ↔ Bundled.of (c := L'.Structure) (I.Model M) ∈ K'

namespace Reduces

/-- **First-order reducibility is reflexive** on classes closed under isomorphism, through the
identity interpretation. -/
theorem refl [L.IsRelational] {K : Set (Bundled.{w} L.Structure)}
    (hK : ∀ M N : Bundled.{w} L.Structure, Nonempty (M ≃[L] N) → (M ∈ K ↔ N ∈ K)) :
    Reduces K K :=
  ⟨Unit, inferInstance, Interpretation.id L, fun _ _ => hK _ _ ⟨Interpretation.idEquiv.symm⟩⟩

/-- **First-order reducibility is transitive** when the last class is closed under isomorphism,
through the composite interpretation. -/
theorem trans [L''.IsRelational] {K : Set (Bundled.{w} L.Structure)}
    {K' : Set (Bundled.{w} L'.Structure)} {K'' : Set (Bundled.{w} L''.Structure)}
    (h : Reduces K K') (h' : Reduces K' K'')
    (hK'' : ∀ M N : Bundled.{w} L''.Structure, Nonempty (M ≃[L''] N) → (M ∈ K'' ↔ N ∈ K'')) :
    Reduces K K'' := by
  obtain ⟨ι, _, I, hI⟩ := h
  obtain ⟨κ, _, J, hJ⟩ := h'
  refine ⟨κ × ι, inferInstance, J.comp I, fun M _ => ?_⟩
  rw [hI M, @hJ (Bundled.of (I.Model M)) (inferInstanceAs (Finite (I.Model M)))]
  exact hK'' _ _ ⟨Interpretation.compEquiv J I⟩

/-- A class reducible to a class closed under isomorphism is closed under isomorphism of finite
structures: isomorphic structures interpret isomorphic structures. -/
theorem mem_iff_of_equiv {K : Set (Bundled.{w} L.Structure)} {K' : Set (Bundled.{w} L'.Structure)}
    (h : Reduces K K')
    (hK' : ∀ M N : Bundled.{w} L'.Structure, Nonempty (M ≃[L'] N) → (M ∈ K' ↔ N ∈ K'))
    {M N : Bundled.{w} L.Structure} [Finite M] (e : M ≃[L] N) : M ∈ K ↔ N ∈ K := by
  obtain ⟨ι, _, I, hI⟩ := h
  have : Finite N := Finite.of_equiv _ e.toEquiv
  rw [hI M, hI N]
  exact hK' _ _ ⟨I.mapEquiv e⟩

end Reduces

/-- **First-order definability is closed under first-order reductions**: if `K` reduces to a
class `K'` defined by `φ`, then `K` is defined by the pullback of `φ`
[Immerman, Framework 3.12][Immerman1999]. -/
theorem Definable.of_reduces {K : Set (Bundled.{w} L.Structure)}
    {K' : Set (Bundled.{w} L'.Structure)} (hK' : Definable K') (h : Reduces K K') :
    Definable K := by
  obtain ⟨ι, _, I, hI⟩ := h
  obtain ⟨φ, hφ⟩ := hK'
  exact ⟨I.onSentence φ, fun M _ => by
    rw [hI M, @hφ _ (inferInstanceAs (Finite (I.Model M))), Interpretation.realize_onSentence]
    rfl⟩

end Cslib.Logic.FO
