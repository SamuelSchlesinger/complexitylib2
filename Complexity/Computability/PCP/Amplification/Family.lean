/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Composition
public import Complexity.Computability.PCP.PoweringBound
public import Complexity.Computability.PCP.Preprocess
public import Complexity.Computability.PCP.Amplifier

/-!
# Amplification with specified expanders

Dinur's preprocessing, powering and composition argument applies to any fixed expander degree
and any fixed spectral bound below one. This file keeps those parameters in the interface, so
that changing the construction does not require rebuilding the argument around numerical
constants. The transformation is mathematical: an executable realization must additionally
implement the graph representation and certify each transformation.

## Main definitions

* `Cslib.PCP.ConstraintGraph.amplifyWith`: preprocessing with supplied rotations, followed by
  powering and composition.
* `Cslib.PCP.ConstraintGraph.Amplification.retention`: the value retained by preprocessing.
* `Cslib.PCP.ConstraintGraph.Amplification.denominator`: the denominator in the gain obtained by
  powering and composition.
* `Cslib.PCP.ConstraintGraph.Amplification.amplifier`: a gap amplifier with supplied rotations.

## Main results

* `Cslib.PCP.ConstraintGraph.satisfiable_amplifyWith_iff`: preservation of satisfiability.
* `Cslib.PCP.ConstraintGraph.le_unsatVal_amplifyWith`: quantitative soundness for arbitrary degree.
* `Cslib.PCP.ConstraintGraph.Amplification.card_vertices` and
  `Cslib.PCP.ConstraintGraph.Amplification.card_edges`: exact output sizes.
* `Cslib.PCP.ConstraintGraph.min_le_unsatVal_amplifyWith`: doubling up to a fixed threshold.
* `Cslib.PCP.ConstraintGraph.Amplification.exists_killRate`: suitable fixed parameters exist.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [I. Dinur, *The PCP theorem by gap amplification*, ECCC TR05-046, revision 1][Dinur2005]
-/

@[expose] public section

universe u

namespace Cslib.PCP.ConstraintGraph

open Finset HadamardTester RotationMap

namespace Amplification

/-- The darts after powering, for a preprocessing family with label type `D`. -/
abbrev Dart (D E : Type*) (T q : ℕ) : Type _ :=
  (E × Bool) × (Fin T → PreprocessLabel D) × (Fin T → Fin q)

/-- The vertices after composition. -/
abbrev Vertex (D E α : Type*) (T q : ℕ) : Type _ :=
  ComposePos (E × Bool) (Dart D E T q) (WalkLabels (PreprocessLabel D) T → α) ⊕
    Dart D E T q × Rand (WalkLabels (PreprocessLabel D) T → α)

/-- The edges after composition. -/
abbrev Edge (D E α : Type*) (T q : ℕ) : Type _ :=
  (Dart D E T q × Rand (WalkLabels (PreprocessLabel D) T → α)) × Query

instance {D E α : Type*} [Fintype D] [DecidableEq D] [Fintype E] [Fintype α] [DecidableEq α]
    {T q : ℕ} :
    Fintype (Vertex D E α T q) :=
  inferInstanceAs (Fintype (_ ⊕ _))

instance {D E α : Type*} [Fintype D] [DecidableEq D] [Fintype E] [Fintype α] [DecidableEq α]
    {T q : ℕ} :
    Fintype (Edge D E α T q) :=
  inferInstanceAs (Fintype (_ × _))

/-- The fraction of value retained by preprocessing with degree `d` and spectral bound `μ`. -/
noncomputable def retention (d : ℕ) (μ : ℝ) : ℝ :=
  min 1 ((1 - μ) * d) / (4 * (1 + d))

/-- The denominator of the gain from powering and composition, for an alphabet of size `K`. -/
noncomputable def denominator (K d : ℕ) (μ : ℝ) : ℝ :=
  476 * (4 * K ^ 2 + 16 * K ^ 4 + 128 * K ^ 5 / ((1 - μ) * d / (2 * d + 2)))

/-- A positive expander degree and a spectral bound below one give positive retention. -/
theorem retention_pos {d : ℕ} {μ : ℝ} (hd : 0 < d) (hμ : μ < 1) :
    0 < retention d μ := by
  unfold retention
  have : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  exact div_pos (lt_min zero_lt_one (mul_pos (sub_pos.mpr hμ) this)) (by positivity)

/-- Preprocessing retains at most the original value. -/
theorem retention_le_one (d : ℕ) (μ : ℝ) : retention d μ ≤ 1 := by
  unfold retention
  rw [div_le_one (by positivity)]
  exact (min_le_left _ _).trans (by have := Nat.cast_nonneg (α := ℝ) d; linarith)

/-- The gain denominator is positive for a nonempty alphabet and an expander family. -/
theorem denominator_pos {K d : ℕ} {μ : ℝ} (hK : 0 < K) (hd : 0 < d) (hμ : μ < 1) :
    0 < denominator K d μ := by
  unfold denominator
  have : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have : 0 < 1 - μ := sub_pos.mpr hμ
  positivity

/-- Every fixed positive degree and spectral gap admit a fixed killing rate sufficient to double
the value. This is a mathematical existence statement; clients may supply concrete parameters. -/
theorem exists_killRate {K d : ℕ} {μ : ℝ} (hK : 0 < K) (hd : 0 < d) (hμ : μ < 1) :
    ∃ q : ℕ, 2 ≤ q ∧
      2 / retention d μ ≤ ((q : ℝ) - 1) / denominator K d μ := by
  have hr := retention_pos hd hμ
  have hden := denominator_pos hK hd hμ
  obtain ⟨q, hq⟩ := exists_nat_gt (1 + 2 * denominator K d μ / retention d μ)
  have hq₁ : (1 : ℝ) < q := by
    have : 0 < 2 * denominator K d μ / retention d μ := by positivity
    linarith
  refine ⟨q, ?_, ?_⟩
  · have : 1 < q := by exact_mod_cast hq₁
    lia
  · rw [le_div_iff₀ hden]
    calc 2 / retention d μ * denominator K d μ
        = 2 * denominator K d μ / retention d μ := by ring
      _ ≤ q - 1 := by linarith

/-- The number of labels in the powered alphabet. -/
def alphabetCard (d K T : ℕ) : ℕ :=
  K ^ ∑ ℓ ∈ range (T + 1), (2 * d + 2) ^ ℓ

/-- The number of output vertices per input edge. -/
def vertexFactor (d K T q : ℕ) : ℕ :=
  2 ^ (alphabetCard d K T + 1) + 2 * (2 ^ (2 * alphabetCard d K T) +
    2 ^ (4 * alphabetCard d K T ^ 2) +
    2 ^ (20 * alphabetCard d K T ^ 2 + 15 * alphabetCard d K T + 3)) * ((2 * d + 2) * q) ^ T

/-- The number of output edges per input edge. -/
def edgeFactor (d K T q : ℕ) : ℕ :=
  34 * 2 ^ (20 * alphabetCard d K T ^ 2 + 15 * alphabetCard d K T + 3) *
    ((2 * d + 2) * q) ^ T

variable {D E α : Type*} [Fintype D] [DecidableEq D] [Fintype E] [Fintype α] (T q : ℕ)

/-- The powered alphabet depends only on the original alphabet, the degree and the walk length. -/
theorem card_walkLabels :
    Fintype.card (WalkLabels (PreprocessLabel D) T → α) =
      alphabetCard (Fintype.card D) (Fintype.card α) T := by
  rw [RegularConstraintGraph.card_alphabet_power, alphabetCard, card_label_preprocess]

omit [DecidableEq D] in
/-- The number of darts presented to composition. -/
theorem card_dart :
    Fintype.card (Dart D E T q) =
      2 * ((2 * Fintype.card D + 2) * q) ^ T * Fintype.card E := by
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fun, card_label_preprocess,
    Fintype.card_fin, mul_pow]
  ring

/-- Each input edge gives a fixed number of output vertices. -/
theorem card_vertices [DecidableEq α] :
    Fintype.card (Vertex D E α T q) =
      vertexFactor (Fintype.card D) (Fintype.card α) T q * Fintype.card E := by
  rw [card_vertices_compose, card_dart, card_walkLabels, Fintype.card_prod,
    Fintype.card_bool, vertexFactor]
  ring

/-- Each input edge gives a fixed number of output edges. -/
theorem card_edges [DecidableEq α] :
    Fintype.card (Edge D E α T q) =
      edgeFactor (Fintype.card D) (Fintype.card α) T q * Fintype.card E := by
  rw [card_edges_compose, card_dart, card_walkLabels, edgeFactor]
  ring

end Amplification

variable {V : Type*} {E : Type u} {α D : Type*} [Fintype E] [DecidableEq V]
  [Fintype D] [DecidableEq D] (G : ConstraintGraph V E α) {μ : ℝ}
  (X : G.PreprocessExpanders D μ)

/-- An amplification round with supplied cloud and half-edge rotations: preprocess, power,
compose. -/
noncomputable def amplifyWith (T q : ℕ) [NeZero q] [Fintype α] [DecidableEq α] :
    ConstraintGraph (Amplification.Vertex D E α T q) (Amplification.Edge D E α T q)
      (Bool × (Query → Bool)) :=
  ((G.preprocessWith X).power T q).toConstraintGraph.compose

variable [Fintype α] [DecidableEq α] [Nonempty α] [Nonempty D] {T q : ℕ} [NeZero q]

/-- An amplification round preserves satisfiability when the supplied family has a spectral gap. -/
theorem satisfiable_amplifyWith_iff (hμ : μ < 1) (hT : 1 ≤ T) (hq : 2 ≤ q) :
    (G.amplifyWith X T q).Satisfiable ↔ G.Satisfiable := by
  rw [amplifyWith, satisfiable_compose_iff,
    RegularConstraintGraph.satisfiable_power_iff _ _ _ hT hq,
    satisfiable_preprocessWith_iff _ _ hμ]

omit [DecidableEq D] [DecidableEq α] in
/-- Preprocessing and powering supply the quantitative gap used by composition. Dividing by the
assignment tester's fixed loss makes this bound reusable by any exact encoded realization. -/
theorem le_div_unsatVal_power_preprocessWith (hμ : μ < 1) (hq : 2 ≤ q)
    (hT : T = 4 * Fintype.card α * (q - 1)) :
    ((q : ℝ) - 1) / Amplification.denominator (Fintype.card α) (Fintype.card D) μ *
      min (Amplification.retention (Fintype.card D) μ * G.unsatVal) (1 / T ^ 2) ≤
        ((G.preprocessWith X).power T q).toConstraintGraph.unsatVal / 476 := by
  have hd : (0 : ℝ) < Fintype.card D := Nat.cast_pos.mpr Fintype.card_pos
  have hgap : 0 < (1 - μ) * Fintype.card D / (2 * Fintype.card D + 2) :=
    div_pos (mul_pos (sub_pos.mpr hμ) hd) (by positivity)
  have hpow := (G.preprocessWith X).le_unsatVal_power T q hq hT
    (G.spectralExpansion_preprocessWith_le X) (by linarith)
  rw [sub_sub_cancel] at hpow
  set K : ℝ := (Fintype.card α : ℝ)
  set B : ℝ := 4 * K ^ 2 + 16 * K ^ 4 +
    128 * K ^ 5 / ((1 - μ) * Fintype.card D / (2 * Fintype.card D + 2))
  have hs : 0 ≤ ((q : ℝ) - 1) / B := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    exact div_nonneg (by linarith) (by dsimp only [B]; positivity)
  calc ((q : ℝ) - 1) / Amplification.denominator (Fintype.card α) (Fintype.card D) μ *
        min (Amplification.retention (Fintype.card D) μ * G.unsatVal) (1 / T ^ 2)
      = (((q : ℝ) - 1) / B *
          min (Amplification.retention (Fintype.card D) μ * G.unsatVal) (1 / T ^ 2)) / 476 := by
        change (q - 1) / (476 * B) * _ = _
        rw [mul_comm 476, ← div_div]
        ring
    _ ≤ (((q : ℝ) - 1) / B *
          min (G.preprocessWith X).toConstraintGraph.unsatVal (1 / T ^ 2)) / 476 := by
        gcongr ?_ / _
        exact mul_le_mul_of_nonneg_left
          (min_le_min_right _ (G.le_unsatVal_preprocessWith X)) hs
    _ ≤ ((G.preprocessWith X).power T q).toConstraintGraph.unsatVal / 476 := by
        gcongr

/-- Quantitative amplification with arbitrary fixed degree and spectral gap. The loss from
preprocessing is `retention`; powering and composition supply the factor linear in `q`. -/
theorem le_unsatVal_amplifyWith (hμ : μ < 1) (hq : 2 ≤ q)
    (hT : T = 4 * Fintype.card α * (q - 1)) :
    ((q : ℝ) - 1) / Amplification.denominator (Fintype.card α) (Fintype.card D) μ *
      min (Amplification.retention (Fintype.card D) μ * G.unsatVal) (1 / T ^ 2) ≤
        (G.amplifyWith X T q).unsatVal :=
  (G.le_div_unsatVal_power_preprocessWith X hμ hq hT).trans
    ((G.preprocessWith X).power T q).toConstraintGraph.le_unsatVal_compose

/-- A sufficiently large fixed killing rate doubles the value up to `1 / T²`. The required
inequality is satisfiable for every nonempty alphabet, positive degree and positive spectral gap
by `Amplification.exists_killRate`. -/
theorem min_le_unsatVal_amplifyWith (hμ : μ < 1) (hq : 2 ≤ q)
    (hT : T = 4 * Fintype.card α * (q - 1))
    (hgain : 2 / Amplification.retention (Fintype.card D) μ ≤
      ((q : ℝ) - 1) / Amplification.denominator (Fintype.card α) (Fintype.card D) μ) :
    min (2 * G.unsatVal) (1 / T ^ 2) ≤ (G.amplifyWith X T q).unsatVal := by
  have hr := Amplification.retention_pos (d := Fintype.card D) Fintype.card_pos hμ
  have hr₁ := Amplification.retention_le_one (Fintype.card D) μ
  set c : ℝ := ((q : ℝ) - 1) /
    Amplification.denominator (Fintype.card α) (Fintype.card D) μ
  have hc : 1 ≤ c := (le_div_iff₀ hr).mpr (by linarith) |>.trans hgain
  have hcr : 2 ≤ c * Amplification.retention (Fintype.card D) μ :=
    (div_le_iff₀ hr).mp hgain
  refine le_trans ?_ (G.le_unsatVal_amplifyWith X hμ hq hT)
  rw [mul_min_of_nonneg _ _ (by linarith : 0 ≤ c)]
  refine min_le_min ?_ (le_mul_of_one_le_left (by positivity) hc)
  calc 2 * G.unsatVal ≤ (c * Amplification.retention (Fintype.card D) μ) * G.unsatVal :=
      mul_le_mul_of_nonneg_right hcr G.unsatVal_nonneg
    _ = c * (Amplification.retention (Fintype.card D) μ * G.unsatVal) := mul_assoc _ _ _

end Cslib.PCP.ConstraintGraph

namespace Cslib.PCP.ConstraintGraph.Amplification

open HadamardTester

variable {D : Type} [Fintype D] [DecidableEq D] {μ : ℝ}
  (X : (G : FinConstraintGraph.{u} (Bool × (Query → Bool))) →
    letI := Classical.decEq G.V
    G.graph.PreprocessExpanders D μ)

/-- The amplification round on bundled finite graphs. Supplying rotations separately for each
input permits executable clients to retain their own cloud and vertex numberings. -/
noncomputable def round (T q : ℕ) [NeZero q]
    (G : FinConstraintGraph.{u} (Bool × (Query → Bool))) :
    FinConstraintGraph.{u} (Bool × (Query → Bool)) :=
  letI := Classical.decEq G.V
  ⟨Vertex D G.E (Bool × (Query → Bool)) T q, Edge D G.E (Bool × (Query → Bool)) T q,
    G.graph.amplifyWith (X G) T q⟩

/-- A supplied expander construction and parameters with enough gain give an amplifier. The
result is mathematical; the encoded implementation and running time need separate certificates. -/
noncomputable def amplifier [Nonempty D] (T q : ℕ) [NeZero q] (hμ : μ < 1) (hq : 2 ≤ q)
    (hT : T = 4 * Fintype.card (Bool × (Query → Bool)) * (q - 1))
    (hgain : 2 / retention (Fintype.card D) μ ≤
      ((q : ℝ) - 1) / denominator (Fintype.card (Bool × (Query → Bool))) (Fintype.card D) μ) :
    Amplifier.{u} (Bool × (Query → Bool)) :=
  have hT₁ : 1 ≤ T := by
    rw [hT]
    exact Nat.mul_pos (Nat.mul_pos (by decide) Fintype.card_pos) (by lia)
  { toFun := round X T q
    factor := vertexFactor (Fintype.card D) (Fintype.card (Bool × (Query → Bool))) T q +
      edgeFactor (Fintype.card D) (Fintype.card (Bool × (Query → Bool))) T q
    gap := 1 / (T : ℝ) ^ 2
    gap_pos := by
      have : (0 : ℝ) < T := Nat.cast_pos.mpr hT₁
      positivity
    gap_le_one := by
      have : (1 : ℝ) ≤ T := by exact_mod_cast hT₁
      rw [div_le_one (by positivity)]
      exact one_le_pow₀ this
    card_vertices_le G :=
      (card_vertices (D := D) (E := G.E) (α := Bool × (Query → Bool)) T q).trans_le
        (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
    card_edges_le G :=
      (card_edges (D := D) (E := G.E) (α := Bool × (Query → Bool)) T q).trans_le
        (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))
    satisfiable_iff G :=
      letI := Classical.decEq G.V
      G.graph.satisfiable_amplifyWith_iff (X G) hμ hT₁ hq
    min_le_unsatVal G :=
      letI := Classical.decEq G.V
      G.graph.min_le_unsatVal_amplifyWith (X G) hμ hq hT hgain }

end Cslib.PCP.ConstraintGraph.Amplification
