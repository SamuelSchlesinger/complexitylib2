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
and has a self-loop at every vertex. **Preprocessing** [Dinur, Section 3.1][Dinur2007] produces one
from an arbitrary constraint graph `G`, over the same alphabet, in three steps:

1. **degree reduction** (`Cslib.PCP.ConstraintGraph.degreeReduce`), with the expanders
   `RotationMap.expander` of degree `120` on the clouds: a `121`-regular constraint graph on the
   `2 |E|` half-edges of `G`;
2. **expanderization**: the edges of the expander `RotationMap.expander` on the half-edges added,
   with constraints that always hold (`Cslib.PCP.RegularConstraintGraph.addTrivial`), for degree
   `241`;
3. a **self-loop** added at every vertex, with a constraint that always holds
   (`Cslib.PCP.RegularConstraintGraph.addLoops`), for degree `242`.

The result `G.preprocess` is `242`-regular on `2 |E|` vertices, so its size is linear in the number
of edges of `G`; its spectral expansion is at most `1 - 1 / 726000`
(`spectralExpansion_preprocess_le`); it is satisfiable exactly when `G` is
(`satisfiable_preprocess_iff`); and its value is between `UNSAT(G) / (1452000 |α|)` and
`UNSAT(G)` (`le_unsatVal_preprocess`, `unsatVal_preprocess_le`). The constants come from the
non-explicit expander family `RotationMap.expander`; any family of constant degree and spectral
expansion bounded away from `1` would do, with other constants.

## Main definitions

* `Cslib.PCP.ConstraintGraph.degreeReduceExpander`: degree reduction with the expanders
  `RotationMap.expander` on the clouds.
* `Cslib.PCP.ConstraintGraph.preprocess`: the preprocessed regular constraint graph.

## Main results

* `Cslib.PCP.ConstraintGraph.spectralExpansion_preprocess_le`: it is an expander.
* `Cslib.PCP.ConstraintGraph.neighbor_preprocess_inr`: it has a self-loop at every vertex.
* `Cslib.PCP.ConstraintGraph.card_vertices_preprocess`,
  `Cslib.PCP.ConstraintGraph.card_label_preprocess`: it has `2 |E|` vertices and degree `242`.
* `Cslib.PCP.ConstraintGraph.satisfiable_preprocess_iff`: it is satisfiable exactly when `G` is.
* `Cslib.PCP.ConstraintGraph.le_unsatVal_preprocess`,
  `Cslib.PCP.ConstraintGraph.unsatVal_preprocess_le`: its value is within a constant factor of
  that of `G`.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
-/

@[expose] public section

namespace Cslib.PCP

namespace ConstraintGraph

open RotationMap

variable {V E α : Type*} [Fintype E] [DecidableEq V] (G : ConstraintGraph V E α)

/-- The degree reduction of `G` with the expanders `RotationMap.expander` on the clouds. -/
noncomputable abbrev degreeReduceExpander :
    RegularConstraintGraph (E × Bool) (Unit ⊕ Fin 120) α :=
  G.degreeReduce fun v ↦ expander (G.Cloud v)

/-- **Preprocessing** [Dinur, Section 3.1][Dinur2007]: degree reduction with expanders on the
clouds, then the edges of an expander and a self-loop at every vertex added, with constraints that
always hold. The vertices are the half-edges of `G`, and the degree is `242`. -/
noncomputable def preprocess :
    RegularConstraintGraph (E × Bool) (((Unit ⊕ Fin 120) ⊕ Fin 120) ⊕ Unit) α :=
  (G.degreeReduceExpander.addTrivial (expander (E × Bool))).addLoops Unit

/-- Preprocessing is degree reduction, then expanderization, then self-loops. -/
theorem preprocess_eq :
    G.preprocess = (G.degreeReduceExpander.addTrivial (expander (E × Bool))).addLoops Unit :=
  rfl

/-- The preprocessed constraint graph has `2 |E|` vertices. -/
theorem card_vertices_preprocess : Fintype.card (E × Bool) = 2 * Fintype.card E := by
  rw [Fintype.card_prod, Fintype.card_bool, mul_comm]

/-- The preprocessed constraint graph has degree `242`. -/
theorem card_label_preprocess : Fintype.card (((Unit ⊕ Fin 120) ⊕ Fin 120) ⊕ Unit) = 242 := by
  simp

/-- **The preprocessed constraint graph has a self-loop at every vertex.** -/
@[simp]
theorem neighbor_preprocess_inr (p : E × Bool) (i : Unit) :
    G.preprocess.graph.neighbor p (.inr i) = p :=
  rfl

/-- **The preprocessed constraint graph is an expander**: its spectral expansion is at most
`1 - 1 / 726000`. -/
theorem spectralExpansion_preprocess_le :
    G.preprocess.graph.spectralExpansion ≤ 1 - 1 / 726000 := by
  set R := G.degreeReduceExpander.graph
  set X := expander (E × Bool)
  have h₁ := R.spectralExpansion_le_one
  have h₂ := spectralExpansion_expander_le (E × Bool)
  have h₃ := R.spectralExpansion_union_le X
  have h₄ := (R.union X).spectralExpansion_addLoops_le (E := Unit)
  change ((R.union X).addLoops Unit).spectralExpansion ≤ _
  generalize ((R.union X).addLoops Unit).spectralExpansion = x₄ at h₄ ⊢
  generalize (R.union X).spectralExpansion = x₃ at h₃ h₄
  generalize R.spectralExpansion = x₁ at h₁ h₃
  generalize X.spectralExpansion = x₂ at h₂ h₃
  simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin] at h₃ h₄
  norm_num at h₃ h₄ ⊢
  linarith

/-- Expanderization and self-loops halve the value of the degree-reduced constraint graph. -/
theorem unsatVal_preprocess :
    G.preprocess.toConstraintGraph.unsatVal =
      G.degreeReduceExpander.toConstraintGraph.unsatVal / 2 := by
  rw [preprocess_eq, RegularConstraintGraph.unsatVal_addLoops,
    RegularConstraintGraph.unsatVal_addTrivial]
  simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]
  push_cast
  ring

section Value

variable [Nonempty α]

/-- **Preprocessing preserves satisfiability.** -/
theorem satisfiable_preprocess_iff [Finite α] :
    G.preprocess.toConstraintGraph.Satisfiable ↔ G.Satisfiable := by
  rw [preprocess_eq, RegularConstraintGraph.satisfiable_addLoops_iff,
    RegularConstraintGraph.satisfiable_addTrivial_iff]
  exact satisfiable_degreeReduce_iff _ (μ := 1 - 1 / 360000) (by norm_num)
    fun v ↦ spectralExpansion_expander_le _

/-- **Soundness of preprocessing** [Dinur, Section 3.1][Dinur2007]: preprocessing divides the value
by at most `1452000 |α|`. -/
theorem le_unsatVal_preprocess [Fintype α] :
    G.unsatVal / (1452000 * Fintype.card α) ≤ G.preprocess.toConstraintGraph.unsatVal := by
  have h := le_unsatVal_degreeReduce (G := G) _ (μ := 1 - 1 / 360000)
    fun v ↦ spectralExpansion_expander_le _
  have hα : (1 : ℝ) ≤ Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [Fintype.card_fin, min_eq_right (by
    rw [div_le_one (by positivity)]
    norm_num
    linarith)] at h
  rw [unsatVal_preprocess]
  have hG := G.unsatVal_nonneg
  calc G.unsatVal / (1452000 * Fintype.card α)
      = (1 - (1 - 1 / 360000)) * (120 : ℕ) / Fintype.card α / (2 * (1 + (120 : ℕ))) *
          G.unsatVal / 2 := by
        field_simp
        ring
    _ ≤ _ := by gcongr

/-- **Completeness of preprocessing** [Dinur, Section 3.1][Dinur2007]: preprocessing does not
increase the value. -/
theorem unsatVal_preprocess_le :
    G.preprocess.toConstraintGraph.unsatVal ≤ G.unsatVal := by
  have h := one_add_card_mul_unsatVal_degreeReduce_le (G := G) fun v ↦ expander (G.Cloud v)
  have h₀ := G.degreeReduceExpander.toConstraintGraph.unsatVal_nonneg
  rw [Fintype.card_fin] at h
  rw [unsatVal_preprocess]
  push_cast at h
  linarith

end Value

end ConstraintGraph

end Cslib.PCP
