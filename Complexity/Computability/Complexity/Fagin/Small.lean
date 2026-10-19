/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Encoding
public import Complexity.Logics.SecondOrder.Projection
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Small structures and cardinality splitting

In Fagin's theorem, the Cook–Levin tableau of a verifier is encoded by `k`-tuples over the domain
`M`. When `Nat.card M ≥ 2`, `n ^ k` grows large enough to index the tableau's time steps and tape
positions; when `Nat.card M ≤ 1`, `n ^ k ≤ 1` cannot.

Over a fixed finite relational vocabulary `v : Vocabulary L`, however, there are only finitely many
isomorphism classes of structures of cardinality `0` or `1`: every relation table has length
`n ^ a ≤ 1`, so an isomorphism-closed class `K` restricted to `Nat.card M ≤ 1` is determined by a
finite Boolean table of first-order sentences and is therefore first-order definable
(`FO.Definable.inter_card_le_one`). Combining this with the first-order sentence `cardGeTwoSentence`
(`∃ x y, x ≠ y`) reduces existential second-order definability of any isomorphism-closed class `K`
to agreeing with `K` on finite structures of cardinality at least `2`
(`ESO.Definable.of_card_ge_two`).

## Main definitions

* `Cslib.Logic.FO.cardZeroSentence`, `Cslib.Logic.FO.cardOneSentence`,
  `Cslib.Logic.FO.cardGeTwoSentence`: first-order sentences for `Nat.card M = 0`, `Nat.card M = 1`,
  and `2 ≤ Nat.card M`.
* `Cslib.Logic.FO.truthTableSentence`: the first-order sentence expressing a predicate `P` on the
  truth values of a finite family of sentences `φ : Fin m → L.Sentence`.

## Main results

* `Cslib.Logic.FO.Definable.inter_card_le_one`: for any isomorphism-closed class `K` over a finite
  relational vocabulary, `{M ∈ K | Nat.card M ≤ 1}` is first-order definable.
* `Cslib.Logic.ESO.Definable.of_card_ge_two`: to show `ESO.Definable K` for an isomorphism-closed
  class `K`, it suffices to exhibit an `ESO.Sentence` that agrees with `K` on finite structures with
  `2 ≤ Nat.card M`.
-/

@[expose] public section

universe u v w

open FirstOrder Language Structure CategoryTheory BoundedFormula

namespace Cslib.Logic.FO

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

/-! ### Cardinality sentences -/

/-- The first-order sentence `∀ x, x ≠ x`, which holds in `M` iff `M` is empty. -/
def cardZeroSentence : L.Sentence :=
  ∀' ∼(&0 =' &0)

/-- The first-order sentence `(∃ x, x = x) ∧ ∀ x y, x = y`, which holds in `M` iff `M` has a
unique element. -/
def cardOneSentence : L.Sentence :=
  (∃' (&0 =' &0)) ⊓ ∀' ∀' (&0 =' &1)

/-- The first-order sentence `∃ x y, x ≠ y`, which holds in `M` iff `M` has at least two distinct
elements. -/
def cardGeTwoSentence : L.Sentence :=
  ∃' ∃' ∼(&0 =' &1)

@[simp]
theorem realize_cardZeroSentence [Finite M] :
    M ⊨ (cardZeroSentence : L.Sentence) ↔ Nat.card M = 0 := by
  have h1 : M ⊨ (cardZeroSentence : L.Sentence) ↔ IsEmpty M := by
    simp [cardZeroSentence, Sentence.Realize, Formula.Realize, isEmpty_iff]
  rw [h1, Nat.card_eq_zero]
  exact ⟨Or.inl, fun h => h.resolve_right (not_infinite_iff_finite.2 inferInstance)⟩

@[simp]
theorem realize_cardOneSentence :
    M ⊨ (cardOneSentence : L.Sentence) ↔ Nat.card M = 1 := by
  have h1 : M ⊨ (cardOneSentence : L.Sentence) ↔ (∃ _ : M, True) ∧ ∀ a b : M, a = b := by
    simp [cardOneSentence, Sentence.Realize, Formula.Realize, Fin.snoc]
  rw [h1, Nat.card_eq_one_iff_exists]
  constructor
  · rintro ⟨⟨a, -⟩, hall⟩
    exact ⟨a, fun b => hall b a⟩
  · rintro ⟨a, ha⟩
    exact ⟨⟨a, trivial⟩, fun x y => (ha x).trans (ha y).symm⟩

@[simp]
theorem realize_cardGeTwoSentence [Finite M] :
    M ⊨ (cardGeTwoSentence : L.Sentence) ↔ 2 ≤ Nat.card M := by
  have h1 : M ⊨ (cardGeTwoSentence : L.Sentence) ↔ ∃ x y : M, x ≠ y := by
    simp [cardGeTwoSentence, Sentence.Realize, Formula.Realize, Fin.snoc]
  rw [h1, ← nontrivial_iff, ← Finite.one_lt_card_iff_nontrivial]
  omega

theorem Definable.card_ge_two :
    Definable {M : Bundled.{w} L.Structure | 2 ≤ Nat.card M} :=
  ⟨cardGeTwoSentence, fun _ _ => realize_cardGeTwoSentence.symm⟩

/-! ### Finite Boolean tables of sentences -/

/-- Given `m` sentences `φ` and a predicate `P` on bit vectors `Fin m → Bool`, the first-order
sentence asserting that the truth values `i ↦ (M ⊨ φ i)` satisfy `P`. -/
noncomputable def truthTableSentence {m : ℕ} (φ : Fin m → L.Sentence)
    (P : (Fin m → Bool) → Prop) : L.Sentence :=
  BoundedFormula.iSup fun s : {s : Fin m → Bool // P s} =>
    BoundedFormula.iInf fun i : Fin m => if s.1 i then φ i else ∼(φ i)

open scoped Classical in
@[simp]
theorem realize_truthTableSentence {m : ℕ} (φ : Fin m → L.Sentence)
    (P : (Fin m → Bool) → Prop) :
    M ⊨ truthTableSentence φ P ↔ P (fun i => decide (M ⊨ φ i)) := by
  simp only [truthTableSentence, Sentence.Realize, Formula.Realize, BoundedFormula.realize_iSup,
    BoundedFormula.realize_iInf, Subtype.exists]
  have hiff (s : Fin m → Bool) (i : Fin m) :
      BoundedFormula.Realize (if s i = true then φ i else ∼(φ i))
        (default : Empty → M) default ↔ s i = decide (M ⊨ φ i) := by
    cases s i
    · simpa [Sentence.Realize, Formula.Realize] using (@decide_eq_false_iff_not (M ⊨ φ i) _).symm
    · simpa [Sentence.Realize, Formula.Realize] using (@decide_eq_true_iff (M ⊨ φ i) _).symm
  simp only [hiff, ← funext_iff]
  exact ⟨fun ⟨s, hs, h⟩ => h ▸ hs, fun h => ⟨_, h, rfl⟩⟩

/-! ### Small structures over a finite vocabulary -/

section Vocabulary

variable [L.IsRelational] (v : Vocabulary L)

/-- The sentence testing whether a relation symbol `r` is nullary and holds on the empty tuple. -/
def nullaryRelSentence : (Σ n, L.Relations n) → L.Sentence
  | ⟨0, r⟩ => Relations.boundedFormula r finZeroElim
  | ⟨_ + 1, _⟩ => ⊥

/-- The sentence testing whether the `i`-th symbol of `v` is nullary and holds on the empty
tuple. -/
def nullarySymbolSentence (i : Fin v.count) : L.Sentence :=
  nullaryRelSentence (v.symbol i)

/-- The sentence testing whether a relation symbol `r` holds on every constant tuple
`fun _ => x`. -/
def constTupleRelSentence (r : Σ n, L.Relations n) : L.Sentence :=
  ∀' Relations.boundedFormula r.2 (fun _ => &0)

/-- The sentence testing whether the `i`-th symbol of `v` holds on every constant tuple
`fun _ => x`. In a singleton structure this is the single bit of the symbol's relation table. -/
def constTupleSentence (i : Fin v.count) : L.Sentence :=
  constTupleRelSentence (v.symbol i)

/-- The `EncodedStructure` of cardinality `0` whose nullary tables are given by `s`. -/
def encodeOfZero (s : Fin v.count → Bool) : EncodedStructure :=
  (0, List.ofFn fun i : Fin v.count => if (v.symbol i).1 = 0 then [s i] else [])

/-- The `EncodedStructure` of cardinality `1` whose singleton tables are given by `s`. -/
def encodeOfOne (s : Fin v.count → Bool) : EncodedStructure :=
  (1, List.ofFn fun i : Fin v.count => [s i])

open scoped Classical in
omit [L.IsRelational] in
theorem relTable_eq_of_equiv_fin_zero {N : Type} [L.Structure N] (e : N ≃ Fin 0)
    (r : Σ n, L.Relations n) :
    Vocabulary.relTable N e r =
      if r.1 = 0 then [decide (N ⊨ nullaryRelSentence r)] else [] := by
  rcases r with ⟨_ | k, r⟩
  · simp only [↓reduceIte, nullaryRelSentence]
    refine List.ext_getElem (by simp [Vocabulary.relTable]) fun j hj₁ hj₂ => ?_
    simp only [Vocabulary.relTable, List.getElem_ofFn, List.getElem_singleton]
    refine decide_eq_decide.2 ?_
    change RelMap r (e.symm ∘ finFunctionFinEquiv.symm ⟨j, _⟩) ↔
      RelMap r fun k : Fin 0 => _
    exact iff_of_eq (congrArg (RelMap r) (funext fun k => k.elim0))
  · simp [Vocabulary.relTable]

open scoped Classical in
omit [L.IsRelational] in
theorem encode_eq_encodeOfZero {N : Type} [L.Structure N] (e : N ≃ Fin 0) :
    v.encode N e = encodeOfZero v (fun i => decide (N ⊨ nullarySymbolSentence v i)) := by
  refine Prod.ext rfl (congrArg List.ofFn (funext fun i => ?_))
  exact relTable_eq_of_equiv_fin_zero e (v.symbol i)

open scoped Classical in
omit [L.IsRelational] in
theorem relTable_eq_of_equiv_fin_one {N : Type} [L.Structure N] (e : N ≃ Fin 1)
    (r : Σ n, L.Relations n) :
    Vocabulary.relTable N e r = [decide (N ⊨ constTupleRelSentence r)] := by
  refine List.ext_getElem (by simp [Vocabulary.relTable]) fun j hj₁ hj₂ => ?_
  have hj' : j < 1 ^ r.1 := by simpa [Vocabulary.relTable] using hj₁
  simp only [Vocabulary.relTable, List.getElem_ofFn, List.getElem_singleton]
  refine decide_eq_decide.2 ?_
  have hrel : (N ⊨ constTupleRelSentence r) ↔ ∀ x : N, RelMap r.2 (fun _ => x) := by
    simp [constTupleRelSentence, Sentence.Realize, Formula.Realize, Fin.snoc]
  rw [hrel]
  constructor
  · intro h x
    have hx : (fun _ : Fin r.1 => x) = e.symm ∘ finFunctionFinEquiv.symm ⟨j, hj'⟩ := by
      funext k
      exact e.injective (Subsingleton.elim _ _)
    rwa [hx]
  · intro h
    have hx : (e.symm ∘ finFunctionFinEquiv.symm ⟨j, hj'⟩) = fun _ : Fin r.1 => e.symm 0 := by
      funext k
      exact e.injective (Subsingleton.elim _ _)
    rw [hx]
    exact h (e.symm 0)

open scoped Classical in
omit [L.IsRelational] in
theorem encode_eq_encodeOfOne {N : Type} [L.Structure N] (e : N ≃ Fin 1) :
    v.encode N e = encodeOfOne v (fun i => decide (N ⊨ constTupleSentence v i)) := by
  refine Prod.ext rfl (congrArg List.ofFn (funext fun i => ?_))
  exact relTable_eq_of_equiv_fin_one e (v.symbol i)

include v in
/-- For any isomorphism-closed class `K` over a finite relational vocabulary, the restriction of
`K` to empty structures (`Nat.card M = 0`) is first-order definable. -/
theorem Definable.inter_card_eq_zero {K : Set (Bundled.{0} L.Structure)} (hK : IsoClosed K) :
    Definable {M : Bundled.{0} L.Structure | M ∈ K ∧ Nat.card M = 0} := by
  refine ⟨cardZeroSentence ⊓ truthTableSentence (nullarySymbolSentence v)
    (fun s => v.decoded (encodeOfZero v s) ∈ K), fun M _ => ?_⟩
  rw [Sentence.realize_inf, realize_cardZeroSentence, realize_truthTableSentence]
  constructor
  · rintro ⟨hM, h0⟩
    refine ⟨h0, ?_⟩
    have e : M ≃ Fin 0 := h0 ▸ Finite.equivFin M
    have heqv := v.decodeEncodeEquiv M e
    have hmem : v.decoded (v.encode M e) ∈ K := (hK heqv).1 hM
    rwa [encode_eq_encodeOfZero v e] at hmem
  · rintro ⟨h0, hdec⟩
    refine ⟨?_, h0⟩
    have e : M ≃ Fin 0 := h0 ▸ Finite.equivFin M
    have heqv := v.decodeEncodeEquiv M e
    rw [← encode_eq_encodeOfZero v e] at hdec
    exact (hK heqv).2 hdec

include v in
/-- For any isomorphism-closed class `K` over a finite relational vocabulary, the restriction of
`K` to singleton structures (`Nat.card M = 1`) is first-order definable. -/
theorem Definable.inter_card_eq_one {K : Set (Bundled.{0} L.Structure)} (hK : IsoClosed K) :
    Definable {M : Bundled.{0} L.Structure | M ∈ K ∧ Nat.card M = 1} := by
  refine ⟨cardOneSentence ⊓ truthTableSentence (constTupleSentence v)
    (fun s => v.decoded (encodeOfOne v s) ∈ K), fun M _ => ?_⟩
  rw [Sentence.realize_inf, realize_cardOneSentence, realize_truthTableSentence]
  constructor
  · rintro ⟨hM, h1⟩
    refine ⟨h1, ?_⟩
    have e : M ≃ Fin 1 := h1 ▸ Finite.equivFin M
    have heqv := v.decodeEncodeEquiv M e
    have hmem : v.decoded (v.encode M e) ∈ K := (hK heqv).1 hM
    rwa [encode_eq_encodeOfOne v e] at hmem
  · rintro ⟨h1, hdec⟩
    refine ⟨?_, h1⟩
    have e : M ≃ Fin 1 := h1 ▸ Finite.equivFin M
    have heqv := v.decodeEncodeEquiv M e
    rw [← encode_eq_encodeOfOne v e] at hdec
    exact (hK heqv).2 hdec

include v in
/-- For any isomorphism-closed class `K` over a finite relational vocabulary, the restriction of
`K` to structures of cardinality at most `1` is first-order definable. -/
theorem Definable.inter_card_le_one {K : Set (Bundled.{0} L.Structure)} (hK : IsoClosed K) :
    Definable {M : Bundled.{0} L.Structure | M ∈ K ∧ Nat.card M ≤ 1} := by
  have heq : {M : Bundled.{0} L.Structure | M ∈ K ∧ Nat.card M ≤ 1} =
      {M : Bundled.{0} L.Structure | M ∈ K ∧ Nat.card M = 0} ∪
        {M : Bundled.{0} L.Structure | M ∈ K ∧ Nat.card M = 1} := by
    ext M
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · rintro ⟨hM, hle⟩
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hle with h | h
      · exact Or.inl ⟨hM, h⟩
      · exact Or.inr ⟨hM, h⟩
    · rintro (⟨hM, h0⟩ | ⟨hM, h1⟩) <;> exact ⟨hM, by omega⟩
  rw [heq]
  exact (Definable.inter_card_eq_zero v hK).union (Definable.inter_card_eq_one v hK)

end Vocabulary

end Cslib.Logic.FO

namespace Cslib.Logic.ESO

variable {L : Language.{u, v}} [L.IsRelational]

/-- To prove that an isomorphism-closed class `K` over a finite relational vocabulary is
existential second-order definable, it suffices to exhibit an existential second-order sentence
`Φ` that agrees with `K` on finite structures of cardinality at least `2`. -/
theorem Definable.of_card_ge_two (v : Vocabulary L) {K : Set (Bundled.{0} L.Structure)}
    (hK : IsoClosed K) (Φ : Sentence L)
    (hΦ : ∀ (M : Bundled.{0} L.Structure) [Finite M], 2 ≤ Nat.card M → (M ∈ K ↔ Φ.Realize M)) :
    Definable K := by
  obtain ⟨φ_small, hsmall⟩ := FO.Definable.inter_card_le_one v hK
  refine ⟨Sentence.ofSentence φ_small ⊔ (Sentence.ofSentence FO.cardGeTwoSentence ⊓ Φ),
    fun M _ => ?_⟩
  rw [Sentence.realize_sup, Sentence.realize_ofSentence, Sentence.realize_inf,
    Sentence.realize_ofSentence, FO.realize_cardGeTwoSentence, ← hsmall M]
  change M ∈ K ↔ (M ∈ K ∧ Nat.card M ≤ 1) ∨ (2 ≤ Nat.card M ∧ Φ.Realize M)
  by_cases h2 : 2 ≤ Nat.card M
  · rw [hΦ M h2]
    exact ⟨fun h => Or.inr ⟨h2, h⟩, fun h => h.elim (fun ⟨_, hle⟩ => by omega) And.right⟩
  · have hle : Nat.card M ≤ 1 := by omega
    exact ⟨fun h => Or.inl ⟨h, hle⟩, fun h => h.elim And.left fun ⟨hge, _⟩ => by omega⟩

/-- To prove that an isomorphism-closed class `K` over a finite relational vocabulary is
existential second-order definable, it suffices to exhibit an existential second-order sentence
`Φ` over `L.sum orderLanguage` that agrees with `K` on finite structures of cardinality at least `2`
under every numbering `e : M ≃ Fin (Nat.card M)`. -/
theorem Definable.of_withLinearOrder_card_ge_two (v : Vocabulary L)
    {K : Set (Bundled.{0} L.Structure)} (hK : IsoClosed K)
    (Φ : Sentence (L.sum orderLanguage))
    (hΦ : ∀ (M : Bundled.{0} L.Structure) [Finite M] (e : M ≃ Fin (Nat.card M)),
      2 ≤ Nat.card M →
        (M ∈ K ↔
          letI := varLanguage.structure (arity := fun _ : Unit => 2) (orderRelOfEquiv e)
          Φ.Realize M)) :
    Definable K := by
  refine Definable.of_card_ge_two v hK Φ.withLinearOrder fun M _ h2 => ?_
  rw [Sentence.realize_withLinearOrder_iff]
  exact ⟨fun hM => ⟨Finite.equivFin M, (hΦ M (Finite.equivFin M) h2).1 hM⟩,
    fun ⟨e, h⟩ => (hΦ M e h2).2 h⟩

end Cslib.Logic.ESO
