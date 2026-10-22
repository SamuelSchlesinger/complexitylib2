/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Ordered.Query
public import Complexity.Logics.FirstOrder.Ordered.Tuple
public import Mathlib.Data.Finset.Sort

/-!
# Ordered interpretations with a domain formula

An ordered interpretation of dimension `k` supplies a domain formula and formulas for the target
input relations, all over the canonically ordered source language. In a source structure the
universe of the image is the set of `k`-tuples satisfying the domain formula, ordered
lexicographically with the first coordinate most significant. Up to the rank isomorphism, this is
the image of [Immerman1999, Definition 1.26]: here the domain tuples are renumbered by rank onto
`Fin m`, where `m` is their number, and the target relations are evaluated at the unranked tuples.

The canonical numerics of the image are those of `Fin m`; nothing about their definability is
assumed at this level. Without the assumption that the domain formula is `true`, target `BIT` need
not be first-order definable in the image [Immerman1999, the paragraph after Exercise 1.33], so
these semantic maps are more general than Immerman's first-order queries on ordered structures,
which define the target numerics [Immerman1999, Remark 1.32]. Those definitions are the numeric
certificates of `Ordered.Reduction`.

An ordered target structure needs at least two elements [Immerman1999, Proviso 1.15]. An
interpretation is *admissible* when its domain has at least two tuples in every source. This is the
library's convention, motivated by that proviso; Immerman's definition does not discuss smaller
domains.

## Main definitions

* `Cslib.Logic.FO.Ordered.DomainInterpretation`: a domain formula and target relation formulas.
* `Cslib.Logic.FO.Ordered.DomainInterpretation.card`: the number of domain tuples.
* `Cslib.Logic.FO.Ordered.DomainInterpretation.unrank`: the domain tuple of each rank.
* `Cslib.Logic.FO.Ordered.DomainInterpretation.rank`: the rank of each domain tuple.
* `Cslib.Logic.FO.Ordered.DomainInterpretation.inputStructure`: the target relations on ranks.
* `Cslib.Logic.FO.Ordered.DomainInterpretation.Admissible`: at least two domain tuples everywhere.
* `Cslib.Logic.FO.Ordered.DomainInterpretation.map`: the image of a source structure.

## Main results

* `Cslib.Logic.FO.Ordered.Structure.ext`: equality of ordered structures through a size cast.
* `Cslib.Logic.FO.Ordered.DomainInterpretation.lexRank_unrank_lt_lexRank_unrank_iff`: ranks
  number domain tuples in lexicographic order.
* `Cslib.Logic.FO.Ordered.DomainInterpretation.card_filter_lt_unrank`: the rank of a domain
  tuple counts the domain tuples before it.
* `Cslib.Logic.FO.Ordered.DomainInterpretation.unrank_eq_of_strictMono`: any increasing
  enumeration of the domain is `unrank`.
* `Cslib.Logic.FO.Ordered.DomainInterpretation.relMap_map`: target relations in the image.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Proviso 1.15, Definition 1.26,
  Remark 1.32, Exercise 1.33 and the paragraph after it.
-/

@[expose] public section

namespace Cslib.Logic.FO.Ordered

open FirstOrder Language Structure

/-- Ordered structures over a relational language are equal when their sizes are and the size
cast preserves every relation. -/
theorem Structure.ext {L : Language} [L.IsRelational] {M N : Structure L} (h : M.size = N.size)
    (hrel : ∀ {r} (R : L.Relations r) (x : Fin r → Fin M.size),
      RelMap R x ↔ RelMap R (Fin.cast h ∘ x)) : M = N := by
  obtain ⟨m, hm, s⟩ := M
  obtain ⟨n, hn, t⟩ := N
  change m = n at h
  subst h
  congr 1
  apply FirstOrder.Language.Structure.ext
  · funext r f
    exact isEmptyElim f
  · funext r R x
    exact propext (hrel R x)

/-- An ordered interpretation of dimension `k` of `L'` in `L`: a domain formula on `k`-tuples, and
for each relation symbol of `L'` a formula with a block of `k` variables per argument. All formulas
are over the canonically ordered source language. -/
structure DomainInterpretation (L L' : Language) (k : ℕ) where
  /-- The domain formula: the image consists of the tuples satisfying it. -/
  domain : (language L).Formula (Fin k)
  /-- The formula defining a target relation on blocks of `k` source variables. -/
  rel : ∀ {r}, L'.Relations r → (language L).Formula (Fin r × Fin k)

namespace DomainInterpretation

variable {L L' : Language} {k : ℕ} (I : DomainInterpretation L L' k) (M : Structure L)

open scoped Classical in
/-- The lexicographic ranks, among all `k`-tuples, of the domain tuples. -/
noncomputable def domainRanks : Finset (Fin (M.size ^ k)) :=
  Finset.univ.filter fun r => I.domain.Realize (lexEquiv.symm r)

/-- The number of domain tuples: the size of the image. -/
noncomputable def card : ℕ :=
  (I.domainRanks M).card

/-- The domain tuple of a given rank, in lexicographic order. -/
noncomputable def unrank (i : Fin (I.card M)) : Fin k → Fin M.size :=
  lexEquiv.symm ((I.domainRanks M).orderEmbOfFin (rfl : (I.domainRanks M).card = I.card M) i)

variable {I M}

theorem mem_domainRanks {r : Fin (M.size ^ k)} :
    r ∈ I.domainRanks M ↔ I.domain.Realize (lexEquiv.symm r) := by
  classical
  simp [domainRanks]

/-- The domain tuples are counted by `card`. -/
theorem card_eq_card_filter [DecidablePred fun x : Fin k → Fin M.size => I.domain.Realize x] :
    I.card M = (Finset.univ.filter fun x : Fin k → Fin M.size => I.domain.Realize x).card := by
  rw [card, ← Finset.card_map lexEquiv.symm.toEmbedding]
  congr 1
  ext x
  simp only [Finset.mem_map_equiv, Equiv.symm_symm, mem_domainRanks, Equiv.symm_apply_apply,
    Finset.mem_filter, Finset.mem_univ, true_and]

/-- The tuple of every rank satisfies the domain formula. -/
theorem realize_domain_unrank (i : Fin (I.card M)) : I.domain.Realize (I.unrank M i) :=
  mem_domainRanks.mp (Finset.orderEmbOfFin_mem _ rfl i)

theorem lexEquiv_unrank (i : Fin (I.card M)) :
    lexEquiv (I.unrank M i) =
      (I.domainRanks M).orderEmbOfFin (rfl : (I.domainRanks M).card = I.card M) i :=
  lexEquiv.apply_symm_apply _

/-- Ranks number the domain tuples in lexicographic order. -/
theorem lexRank_unrank_lt_lexRank_unrank_iff {i j : Fin (I.card M)} :
    lexRank (I.unrank M i) < lexRank (I.unrank M j) ↔ i < j := by
  change lexEquiv (I.unrank M i) < lexEquiv (I.unrank M j) ↔ i < j
  rw [lexEquiv_unrank, lexEquiv_unrank]
  exact ((I.domainRanks M).orderEmbOfFin (rfl : (I.domainRanks M).card = I.card M)).lt_iff_lt

theorem strictMono_lexRank_unrank : StrictMono fun i => lexRank (I.unrank M i) :=
  fun _ _ h => lexRank_unrank_lt_lexRank_unrank_iff.mpr h

theorem lexRank_unrank_le_lexRank_unrank_iff {i j : Fin (I.card M)} :
    lexRank (I.unrank M i) ≤ lexRank (I.unrank M j) ↔ i ≤ j :=
  strictMono_lexRank_unrank.le_iff_le

theorem unrank_injective : Function.Injective (I.unrank M) :=
  fun _ _ h => strictMono_lexRank_unrank.injective (congrArg lexRank h)

/-- Every domain tuple has a rank. -/
theorem exists_unrank_eq {x : Fin k → Fin M.size} (hx : I.domain.Realize x) :
    ∃ i, I.unrank M i = x := by
  have hr : lexEquiv x ∈ I.domainRanks M :=
    mem_domainRanks.mpr (by rwa [Equiv.symm_apply_apply])
  have hr' : lexEquiv x ∈ Set.range
      ((I.domainRanks M).orderEmbOfFin (rfl : (I.domainRanks M).card = I.card M)) := by
    rw [Finset.range_orderEmbOfFin]
    exact hr
  obtain ⟨i, hi⟩ := hr'
  exact ⟨i, lexEquiv.injective ((lexEquiv_unrank i).trans hi)⟩

variable (I M) in
/-- The rank of a domain tuple. -/
noncomputable def rank (x : Fin k → Fin M.size) (hx : I.domain.Realize x) : Fin (I.card M) :=
  (exists_unrank_eq hx).choose

@[simp] theorem unrank_rank {x : Fin k → Fin M.size} (hx : I.domain.Realize x) :
    I.unrank M (I.rank M x hx) = x :=
  (exists_unrank_eq hx).choose_spec

@[simp] theorem rank_unrank (i : Fin (I.card M)) :
    I.rank M (I.unrank M i) (realize_domain_unrank i) = i :=
  unrank_injective (unrank_rank _)

/-- The rank of a domain tuple counts the domain tuples before it in lexicographic order. -/
theorem card_filter_lt_unrank
    [DecidablePred fun x : Fin k → Fin M.size => I.domain.Realize x]
    (i : Fin (I.card M)) :
    (Finset.univ.filter fun y : Fin k → Fin M.size =>
      I.domain.Realize y ∧ lexRank y < lexRank (I.unrank M i)).card = i := by
  classical
  have h : (Finset.univ.filter fun y : Fin k → Fin M.size =>
      I.domain.Realize y ∧ lexRank y < lexRank (I.unrank M i)) =
      (Finset.univ.filter fun j => j < i).image (I.unrank M) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hy, hlt⟩
      obtain ⟨j, rfl⟩ := exists_unrank_eq hy
      exact ⟨j, lexRank_unrank_lt_lexRank_unrank_iff.mp hlt, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨realize_domain_unrank j, lexRank_unrank_lt_lexRank_unrank_iff.mpr hj⟩
  rw [h, Finset.card_image_of_injective _ unrank_injective]
  have hi : (Finset.univ.filter fun j => j < i) = Finset.Iio i := by
    ext j
    simp
  rw [hi, Fin.card_Iio]

/-- The rank of a domain tuple, as a count of the domain tuples before it. -/
theorem val_rank [DecidablePred fun x : Fin k → Fin M.size => I.domain.Realize x]
    {x : Fin k → Fin M.size} (hx : I.domain.Realize x) :
    (I.rank M x hx).val = (Finset.univ.filter fun y : Fin k → Fin M.size =>
      I.domain.Realize y ∧ lexRank y < lexRank x).card := by
  conv_rhs => rw [← unrank_rank hx]
  exact (card_filter_lt_unrank _).symm

/-- **Characterization of ranks.** An enumeration of exactly the domain tuples that increases in
lexicographic order is `unrank`, up to the size cast. -/
theorem unrank_eq_of_strictMono {m : ℕ} (g : Fin m → Fin k → Fin M.size)
    (hdom : ∀ i, I.domain.Realize (g i))
    (hsurj : ∀ x, I.domain.Realize x → ∃ i, g i = x)
    (hmono : StrictMono fun i => lexRank (g i)) :
    ∃ h : I.card M = m, ∀ i, I.unrank M i = g (Fin.cast h i) := by
  classical
  have hf : StrictMono fun i => lexEquiv (g i) := fun _ _ hij => Fin.lt_def.mpr (hmono hij)
  have hs : I.domainRanks M = Finset.univ.image fun i => lexEquiv (g i) := by
    ext r
    simp only [mem_domainRanks, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hr
      obtain ⟨i, hi⟩ := hsurj _ hr
      exact ⟨i, by rw [hi, Equiv.apply_symm_apply]⟩
    · rintro ⟨i, rfl⟩
      rw [Equiv.symm_apply_apply]
      exact hdom i
  have hcard : I.card M = m := by
    rw [card, hs, Finset.card_image_of_injective _ hf.injective, Finset.card_univ,
      Fintype.card_fin]
  refine ⟨hcard, fun i => ?_⟩
  have hu := Finset.orderEmbOfFin_unique (s := I.domainRanks M) (rfl : _ = I.card M)
    (f := fun i => lexEquiv (g (Fin.cast hcard i)))
    (fun i => by rw [hs]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _))
    (hf.comp (Fin.cast_strictMono hcard))
  exact lexEquiv.injective ((lexEquiv_unrank i).trans (congrFun hu i).symm)

/-! ### The image -/

variable (I) in
/-- An interpretation is admissible when every source has at least two domain tuples, so that its
image carries distinct canonical constants `0` and `1`. -/
def Admissible : Prop :=
  ∀ M : Structure L, 2 ≤ I.card M

variable [L'.IsRelational]

variable (I M) in
/-- The target input relations on the ranks of the domain tuples. Numeric symbols are the
canonical ones of `Fin (I.card M)`. -/
@[instance_reducible]
noncomputable def inputStructure : L'.Structure (Fin (I.card M)) where
  RelMap R x := (I.rel R).Realize fun p => I.unrank M (x p.1) p.2

variable (I) in
/-- The image of a source structure under an admissible interpretation. -/
noncomputable def map (hI : I.Admissible) (M : Structure L) : Structure L' where
  size := I.card M
  size_ge_two := hI M
  input := I.inputStructure M

@[simp] theorem size_map (hI : I.Admissible) : (I.map hI M).size = I.card M := rfl

/-- A target relation holds of some ranks when its formula holds of the unranked tuples. -/
theorem relMap_map (hI : I.Admissible) {r : ℕ} (R : L'.Relations r) (x : Fin r → I.map hI M) :
    RelMap R x ↔ (I.rel R).Realize fun p => I.unrank M (x p.1) p.2 :=
  Iff.rfl

end DomainInterpretation

end Cslib.Logic.FO.Ordered
