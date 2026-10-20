/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Interpretation
public import Complexity.Logics.FirstOrder.Encoding

/-!
# Numbering the elements of an interpreted structure

A first-order interpretation `I` of dimension `ι` interprets, in a structure on `Fin n`, a structure
whose elements are the tuples `ι → Fin n` satisfying the domain formula. Fixing an enumeration
`e : ι ≃ Fin d` of the coordinates, a tuple has an index below `n ^ d` (`Cslib.Logic.tupleIndex`),
and the elements of the interpreted structure are numbered by the rank of their index among the
indices of the domain (`Cslib.Logic.FO.Interpretation.rankEquiv`): the number of indices of the
domain below it. This is the numbering an algorithm computes by counting, as a logarithmic-space
transducer for the interpretation does.

## Main definitions

* `Cslib.Logic.FO.Interpretation.tupleAt`: the tuple with a given index.
* `Cslib.Logic.FO.Interpretation.InDomain`: the indices of the tuples of the domain.
* `Cslib.Logic.FO.Interpretation.domainRank`: the number of indices of the domain below a number.
* `Cslib.Logic.FO.Interpretation.rankEquiv`: the numbering of the interpreted structure by ranks.

## Main results

* `Cslib.Logic.FO.Interpretation.domainRank_succ`: ranks count the indices of the domain.
* `Cslib.Logic.FO.Interpretation.rankEquiv_symm_val`: the element of a given rank is the tuple
  whose index has that rank.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999]
-/

@[expose] public section

universe u v u' v'

open FirstOrder Language Structure

namespace Cslib.Logic.FO.Interpretation

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {ι : Type*} {d : ℕ}
  (I : Interpretation L L' ι) (e : ι ≃ Fin d)

/-- The tuple of elements of `Fin n` with index `u`, through the enumeration `e` of the
coordinates. -/
def tupleAt {n : ℕ} (u : Fin (n ^ d)) : ι → Fin n := finFunctionFinEquiv.symm u ∘ e

theorem tupleAt_val {n : ℕ} (u : Fin (n ^ d)) (i : ι) :
    (tupleAt e u i : ℕ) = u / n ^ (e i : ℕ) % n := by
  simp [tupleAt, finFunctionFinEquiv_symm_apply_val]

/-- The index of a tuple, through the enumeration `e` of the coordinates. -/
def indexOf {n : ℕ} (x : ι → Fin n) : ℕ := tupleIndex (x ∘ e.symm)

theorem indexOf_lt {n : ℕ} (x : ι → Fin n) : indexOf e x < n ^ d := tupleIndex_lt _

theorem tupleAt_indexOf {n : ℕ} (x : ι → Fin n) :
    tupleAt e ⟨indexOf e x, indexOf_lt e x⟩ = x := by
  funext i
  simp only [tupleAt, indexOf, tupleIndex, Function.comp_apply, Fin.eta, Equiv.symm_apply_apply]

theorem indexOf_tupleAt {n : ℕ} (u : Fin (n ^ d)) : indexOf e (tupleAt e u) = u := by
  simp [tupleAt, indexOf, tupleIndex, Function.comp_def]

theorem indexOf_injective {n : ℕ} : Function.Injective (indexOf e (n := n)) := fun x y h => by
  rw [← tupleAt_indexOf e x, ← tupleAt_indexOf e y]
  simp only [h]

variable (n : ℕ) [L.Structure (Fin n)]

/-- The number `u` is the index of a tuple of the domain of `I`. -/
def InDomain (u : ℕ) : Prop := ∃ h : u < n ^ d, I.domain.Realize (tupleAt e ⟨u, h⟩)

open scoped Classical in
/-- The number of indices of tuples of the domain below `u`. -/
noncomputable def domainRank (u : ℕ) : ℕ := ((Finset.range u).filter (I.InDomain e n)).card

variable {I e n}

theorem domainRank_zero : I.domainRank e n 0 = 0 := by simp [domainRank]

open scoped Classical in
theorem domainRank_succ (u : ℕ) :
    I.domainRank e n (u + 1) = I.domainRank e n u + if I.InDomain e n u then 1 else 0 := by
  unfold domainRank
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

theorem domainRank_mono {u u' : ℕ} (h : u ≤ u') : I.domainRank e n u ≤ I.domainRank e n u' := by
  classical
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.mpr h))

theorem domainRank_lt_of_inDomain {u u' : ℕ} (hu : I.InDomain e n u) (h : u < u') :
    I.domainRank e n u < I.domainRank e n u' := by
  classical
  calc I.domainRank e n u < I.domainRank e n (u + 1) := by
        rw [domainRank_succ, ite_eq_left hu]; omega
    _ ≤ I.domainRank e n u' := domainRank_mono h

theorem inDomain_indexOf (x : I.Model (Fin n)) : I.InDomain e n (indexOf e x.1) :=
  ⟨indexOf_lt e x.1, by rw [tupleAt_indexOf]; exact x.2⟩

variable (I e n) in
/-- The number of elements of the interpreted structure: the number of indices of the domain. -/
noncomputable abbrev modelCard : ℕ := I.domainRank e n (n ^ d)

theorem modelCard_le_pow : modelCard I e n ≤ n ^ d := by
  classical
  unfold modelCard domainRank
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- The rank of the index of an element of the interpreted structure. -/
noncomputable def rankOf (x : I.Model (Fin n)) : Fin (modelCard I e n) :=
  ⟨I.domainRank e n (indexOf e x.1), domainRank_lt_of_inDomain (inDomain_indexOf x)
    (indexOf_lt e x.1)⟩

theorem rankOf_injective : Function.Injective (rankOf (I := I) (e := e) (n := n)) := by
  intro x y h
  have h' : I.domainRank e n (indexOf e x.1) = I.domainRank e n (indexOf e y.1) :=
    congrArg Fin.val h
  apply Model.ext
  apply indexOf_injective e
  rcases lt_trichotomy (indexOf e x.1) (indexOf e y.1) with hlt | heq | hgt
  · exact absurd h' (domainRank_lt_of_inDomain (inDomain_indexOf x) hlt).ne
  · exact heq
  · exact absurd h' (domainRank_lt_of_inDomain (inDomain_indexOf y) hgt).ne'

/-- Every rank below the number of elements is the rank of an index of the domain. -/
theorem exists_inDomain_of_lt {r : ℕ} (hr : r < modelCard I e n) :
    ∃ u, I.InDomain e n u ∧ I.domainRank e n u = r := by
  classical
  have hex : ∃ u, r < I.domainRank e n u := ⟨_, hr⟩
  let u₀ := Nat.find hex
  have hu₀ : r < I.domainRank e n u₀ := Nat.find_spec hex
  have hpos : u₀ ≠ 0 := fun h => by
    rw [h, domainRank_zero] at hu₀
    omega
  obtain ⟨u, hu⟩ : ∃ u, u₀ = u + 1 := Nat.exists_eq_succ_of_ne_zero hpos
  have hle : I.domainRank e n u ≤ r := by
    by_contra h
    exact Nat.find_min hex (show u < u₀ by omega) (by omega)
  rw [hu, domainRank_succ] at hu₀
  by_cases hd : I.InDomain e n u
  · rw [ite_eq_left hd] at hu₀
    exact ⟨u, hd, by omega⟩
  · rw [ite_eq_right hd] at hu₀
    omega

theorem rankOf_surjective : Function.Surjective (rankOf (I := I) (e := e) (n := n)) := by
  intro r
  obtain ⟨u, ⟨hu, hdom⟩, hr⟩ := exists_inDomain_of_lt r.2
  refine ⟨⟨tupleAt e ⟨u, hu⟩, hdom⟩, Fin.ext ?_⟩
  simp only [rankOf, indexOf_tupleAt, hr]

variable (I e n) in
/-- **The numbering of the interpreted structure by ranks**: an element is numbered by the number
of indices of the domain below its index. -/
noncomputable def rankEquiv : I.Model (Fin n) ≃ Fin (modelCard I e n) :=
  Equiv.ofBijective rankOf ⟨rankOf_injective, rankOf_surjective⟩

/-- **The element of a given rank** is the tuple whose index is in the domain and has that rank. -/
theorem rankEquiv_symm_val {r : Fin (modelCard I e n)} {u : ℕ} (hu : I.InDomain e n u)
    (hr : I.domainRank e n u = r) : (rankEquiv I e n).symm r = ⟨tupleAt e ⟨u, hu.1⟩, hu.2⟩ := by
  apply (rankEquiv I e n).injective
  rw [Equiv.apply_symm_apply]
  refine Fin.ext ?_
  change r.val = I.domainRank e n (indexOf e (tupleAt e ⟨u, hu.1⟩))
  rw [indexOf_tupleAt, hr]

end Cslib.Logic.FO.Interpretation
