/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.DegreeReduction
public import Complexity.Foundations.Combinatorics.Expander.Family

/-!
# Preprocessing

Dinur's powering step needs a constraint graph that is regular, of constant degree, an expander,
and has a self-loop at every vertex. **Preprocessing** [Dinur, Section 3.1][Dinur2005] produces one
from an arbitrary constraint graph `G`, over the same alphabet, given a family `X` of `D`-regular
expanders of spectral expansion at most `μ` (`Cslib.RotationMap.ExpanderFamily`), in three steps:

1. **degree reduction** (`Cslib.PCP.ConstraintGraph.degreeReduce`), with the expanders of `X` on the
   clouds: a `(1 + |D|)`-regular constraint graph on the `2 |E|` half-edges of `G`;
2. **expanderization**: the edges of the expander of `X` on the half-edges added, with constraints
   that always hold (`Cslib.PCP.RegularConstraintGraph.addTrivial`), for degree `1 + 2 |D|`;
3. a **self-loop** added at every vertex, with a constraint that always holds
   (`Cslib.PCP.RegularConstraintGraph.addLoops`), for degree `2 + 2 |D|`.

The result `G.preprocess X` is `(2 |D| + 2)`-regular on `2 |E|` vertices, so its size is linear in
the number of edges of `G`; its spectral expansion is at most `1 - (1 - μ) |D| / (2 |D| + 2)`
(`spectralExpansion_preprocess_le`); for `μ < 1` it is satisfiable exactly when `G` is
(`satisfiable_preprocess_iff`); and its value is between `min 1 ((1 - μ) |D|) / (4 (1 + |D|))`
times `UNSAT(G)` and `UNSAT(G)` (`le_unsatVal_preprocess`, `unsatVal_preprocess_le`), whatever the
alphabet.

With the non-explicit family `Cslib.RotationMap.expanderFamily` of `120`-regular expanders of
spectral expansion at most `1 - 1 / 360000`, the preprocessed graph is `242`-regular, its spectral
expansion is at most `1 - 1 / 726000` (`spectralExpansion_preprocess_expanderFamily_le`) and its
value at least `UNSAT(G) / 1452000` (`le_unsatVal_preprocess_expanderFamily`).

## Main definitions

* `Cslib.PCP.ConstraintGraph.PreprocessLabel`: the labels of the darts of a preprocessed graph.
* `Cslib.PCP.ConstraintGraph.degreeReduceExpander`: degree reduction with the expanders of a family
  on the clouds.
* `Cslib.PCP.ConstraintGraph.preprocess`: the preprocessed regular constraint graph.

## Main results

* `Cslib.PCP.ConstraintGraph.spectralExpansion_preprocess_le`: it is an expander.
* `Cslib.PCP.ConstraintGraph.neighbor_preprocess_inr`: it has a self-loop at every vertex.
* `Cslib.PCP.ConstraintGraph.card_vertices_preprocess`,
  `Cslib.PCP.ConstraintGraph.card_label_preprocess`: it has `2 |E|` vertices and degree
  `2 |D| + 2`.
* `Cslib.PCP.ConstraintGraph.satisfiable_preprocess_iff`: it is satisfiable exactly when `G` is.
* `Cslib.PCP.ConstraintGraph.le_unsatVal_preprocess`,
  `Cslib.PCP.ConstraintGraph.unsatVal_preprocess_le`: its value is within a constant factor of
  that of `G`.
* `Cslib.PCP.ConstraintGraph.spectralExpansion_preprocess_expanderFamily_le`,
  `Cslib.PCP.ConstraintGraph.le_unsatVal_preprocess_expanderFamily`: the constants for the
  non-explicit family of expanders.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [I. Dinur, *The PCP theorem by gap amplification*, ECCC TR05-046, revision 1][Dinur2005]
-/

@[expose] public section

universe u

namespace Cslib.PCP

namespace ConstraintGraph

open RotationMap

/-- The labels of the darts of a constraint graph preprocessed with a family of `D`-regular
expanders: the edge-link and the cloud-links of degree reduction, the edges of the expander on the
half-edges, and a self-loop. -/
abbrev PreprocessLabel (D : Type*) : Type _ :=
  ((Unit ⊕ D) ⊕ D) ⊕ Unit

/- The instances on `PreprocessLabel D` are declared on it, rather than found on the sums it
unfolds to, so that the instances on the alphabet `WalkLabels (PreprocessLabel D) T → α` of a
powered graph stay below the size limit of instance synthesis. -/

instance PreprocessLabel.instDecidableEq {D : Type*} [DecidableEq D] :
    DecidableEq (PreprocessLabel D) :=
  inferInstanceAs (DecidableEq (((Unit ⊕ D) ⊕ D) ⊕ Unit))

instance PreprocessLabel.instFintype {D : Type*} [Fintype D] : Fintype (PreprocessLabel D) :=
  inferInstanceAs (Fintype (((Unit ⊕ D) ⊕ D) ⊕ Unit))

/-- A constraint graph preprocessed with a family of `D`-regular expanders has degree
`2 |D| + 2`. -/
theorem card_label_preprocess (D : Type*) [Fintype D] :
    Fintype.card (PreprocessLabel D) = 2 * Fintype.card D + 2 := by
  simp only [PreprocessLabel, Fintype.card_sum, Fintype.card_unit]
  ring

variable {V : Type*} {E : Type u} {α : Type*} [Fintype E] [DecidableEq V]
  (G : ConstraintGraph V E α) {D : Type*} [Fintype D] {μ : ℝ} (X : ExpanderFamily.{u} D μ)

/-- The degree reduction of `G` with the expanders of the family `X` on the clouds. -/
abbrev degreeReduceExpander : RegularConstraintGraph (E × Bool) (Unit ⊕ D) α :=
  G.degreeReduce fun v ↦ X.graph (G.Cloud v)

/-- **Preprocessing** [Dinur, Section 3.1][Dinur2005] with the family of expanders `X`: degree
reduction with expanders of `X` on the clouds, then the edges of the expander of `X` on the
half-edges and a self-loop at every vertex added, with constraints that always hold. The vertices
are the half-edges of `G`, and the degree is `2 |D| + 2`. -/
def preprocess : RegularConstraintGraph (E × Bool) (PreprocessLabel D) α :=
  ((G.degreeReduceExpander X).addTrivial (X.graph (E × Bool))).addLoops Unit

/-- Preprocessing is degree reduction, then expanderization, then self-loops. -/
theorem preprocess_eq :
    G.preprocess X =
      ((G.degreeReduceExpander X).addTrivial (X.graph (E × Bool))).addLoops Unit :=
  rfl

omit [DecidableEq V] in
/-- The preprocessed constraint graph has `2 |E|` vertices. -/
theorem card_vertices_preprocess : Fintype.card (E × Bool) = 2 * Fintype.card E := by
  rw [Fintype.card_prod, Fintype.card_bool, mul_comm]

/-- **The preprocessed constraint graph has a self-loop at every vertex.** -/
@[simp]
theorem neighbor_preprocess_inr (p : E × Bool) (i : Unit) :
    (G.preprocess X).graph.neighbor p (.inr i) = p :=
  rfl

/-- **The preprocessed constraint graph is an expander**: its spectral expansion is at most
`1 - (1 - μ) |D| / (2 |D| + 2)`. -/
theorem spectralExpansion_preprocess_le :
    (G.preprocess X).graph.spectralExpansion ≤
      1 - (1 - μ) * Fintype.card D / (2 * Fintype.card D + 2) := by
  set R := (G.degreeReduceExpander X).graph
  set Y := X.graph (E × Bool)
  have h₁ := R.spectralExpansion_le_one
  have h₂ := X.spectralExpansion_graph_le (E × Bool)
  have h₃ := R.spectralExpansion_union_le Y
  have h₄ := (R.union Y).spectralExpansion_addLoops_le (E := Unit)
  change ((R.union Y).addLoops Unit).spectralExpansion ≤ _
  generalize ((R.union Y).addLoops Unit).spectralExpansion = x₄ at h₄ ⊢
  generalize (R.union Y).spectralExpansion = x₃ at h₃ h₄
  generalize R.spectralExpansion = x₁ at h₁ h₃
  generalize Y.spectralExpansion = x₂ at h₂ h₃
  simp only [Fintype.card_sum, Fintype.card_unit] at h₃ h₄
  push_cast at h₃ h₄
  have hd : (0 : ℝ) ≤ Fintype.card D := Nat.cast_nonneg _
  generalize (Fintype.card D : ℝ) = d at hd h₃ h₄ ⊢
  rw [le_div_iff₀ (by positivity)] at h₃ h₄
  rw [show 1 - (1 - μ) * d / (2 * d + 2) = (2 + d + d * μ) / (2 * d + 2) by field_simp; ring,
    le_div_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left h₁ (by positivity : (0 : ℝ) ≤ 1 + d),
    mul_le_mul_of_nonneg_left h₂ hd]

/-- Expanderization and self-loops halve the value of the degree-reduced constraint graph. -/
theorem unsatVal_preprocess :
    (G.preprocess X).toConstraintGraph.unsatVal =
      (G.degreeReduceExpander X).toConstraintGraph.unsatVal / 2 := by
  rw [preprocess_eq, RegularConstraintGraph.unsatVal_addLoops,
    RegularConstraintGraph.unsatVal_addTrivial]
  simp only [Fintype.card_sum, Fintype.card_unit]
  have h₁ : (1 + Fintype.card D + Fintype.card D : ℝ) ≠ 0 := by positivity
  have h₂ : (1 + Fintype.card D + Fintype.card D + 1 : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

section Value

variable [Nonempty α]

/-- **Preprocessing preserves satisfiability**, with a family of expanders: their degree is positive
and their spectral expansions are at most some `μ < 1`. -/
theorem satisfiable_preprocess_iff [Nonempty D] (hμ : μ < 1) :
    (G.preprocess X).toConstraintGraph.Satisfiable ↔ G.Satisfiable := by
  rw [preprocess_eq, RegularConstraintGraph.satisfiable_addLoops_iff,
    RegularConstraintGraph.satisfiable_addTrivial_iff]
  exact satisfiable_degreeReduce_iff _ hμ fun v ↦ X.spectralExpansion_graph_le _

/-- **Soundness of preprocessing** [Dinur, Section 3.1][Dinur2005]: preprocessing with a family of
`D`-regular expanders of spectral expansion at most `μ` divides the value by at most
`4 (1 + |D|) / min 1 ((1 - μ) |D|)`, whatever the alphabet. -/
theorem le_unsatVal_preprocess :
    min 1 ((1 - μ) * Fintype.card D) / (4 * (1 + Fintype.card D)) * G.unsatVal ≤
      (G.preprocess X).toConstraintGraph.unsatVal := by
  have h := le_unsatVal_degreeReduce (G := G) _ fun v ↦ X.spectralExpansion_graph_le (G.Cloud v)
  rw [unsatVal_preprocess]
  calc min 1 ((1 - μ) * Fintype.card D) / (4 * (1 + Fintype.card D)) * G.unsatVal
      = min 1 ((1 - μ) * Fintype.card D) / (2 * (1 + Fintype.card D)) * G.unsatVal / 2 := by
        have : (0 : ℝ) < 1 + Fintype.card D := by positivity
        field_simp
        ring
    _ ≤ _ := by gcongr

/-- **Completeness of preprocessing** [Dinur, Section 3.1][Dinur2005]: preprocessing does not
increase the value. -/
theorem unsatVal_preprocess_le :
    (G.preprocess X).toConstraintGraph.unsatVal ≤ G.unsatVal := by
  have h := one_add_card_mul_unsatVal_degreeReduce_le (G := G) fun v ↦ X.graph (G.Cloud v)
  have h₀ := (G.degreeReduceExpander X).toConstraintGraph.unsatVal_nonneg
  have hD : (0 : ℝ) ≤ Fintype.card D := Nat.cast_nonneg _
  rw [unsatVal_preprocess]
  nlinarith

end Value

/-! ### The non-explicit family of expanders -/

/-- **The preprocessed constraint graph is an expander**: with the non-explicit family
`expanderFamily` of `120`-regular expanders, its spectral expansion is at most `1 - 1 / 726000`. -/
theorem spectralExpansion_preprocess_expanderFamily_le :
    (G.preprocess expanderFamily).graph.spectralExpansion ≤ 1 - 1 / 726000 := by
  refine (G.spectralExpansion_preprocess_le expanderFamily).trans_eq ?_
  rw [Fintype.card_fin]
  norm_num

/-- **Soundness of preprocessing** [Dinur, Section 3.1][Dinur2005]: with the non-explicit family
`expanderFamily` of `120`-regular expanders, preprocessing divides the value by at most `1452000`,
whatever the alphabet. -/
theorem le_unsatVal_preprocess_expanderFamily [Nonempty α] :
    G.unsatVal / 1452000 ≤ (G.preprocess expanderFamily).toConstraintGraph.unsatVal := by
  refine le_of_eq_of_le ?_ (G.le_unsatVal_preprocess expanderFamily)
  rw [Fintype.card_fin, min_eq_right (by norm_num)]
  ring

end ConstraintGraph

end Cslib.PCP
