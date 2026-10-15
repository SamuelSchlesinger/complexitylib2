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
import Mathlib.Tactic.IrreducibleDef

/-!
# An amplification round

The main theorem of Dinur's proof of the PCP theorem [Dinur, Theorem 4.1][Dinur2007] is a single
transformation of constraint graphs that keeps satisfiable graphs satisfiable, at least doubles the
value of unsatisfiable ones until it reaches a universal constant, multiplies the size by at most a
universal constant, and leaves the alphabet fixed. It is the composite of the three operations of
the proof:

1. **preprocessing** (`Cslib.PCP.ConstraintGraph.preprocess`) with the family of `120`-regular
   expanders `Cslib.RotationMap.expanderFamily`: a `242`-regular expander on the half-edges, losing
   a factor `1452000` of the value, whatever the alphabet;
2. **powering** (`Cslib.PCP.RegularConstraintGraph.power`) along killed walks truncated at `T`
   steps, killed with probability `1 / q`, which multiplies the value by a factor linear in `q`, at
   the cost of an alphabet of size `|α| ^ (∑ ℓ ≤ T, 242 ^ ℓ)`;
3. **composition** (`Cslib.PCP.ConstraintGraph.compose`), back to the fixed alphabet
   `Bool × (HadamardTester.Query → Bool)` of `2 ^ 18` symbols, losing a factor `476` of the value
   whatever the alphabet it starts from.

The round `G.amplify T q` is defined over any finite alphabet `α`. For `T = 4 |α| (q - 1)`, its
value is at least `(q - 1) / (476 (4 |α| ^ 2 + 16 |α| ^ 4 + 92928000 |α| ^ 5))` times
`min (UNSAT(G) / 1452000) (1 / T ^ 2)` (`le_unsatVal_amplify`), and its numbers of vertices
and edges are those of `G` times factors depending on `|α|`, `T` and `q` only
(`card_vertices_amplify`, `card_edges_amplify`): the vertices of a preprocessed graph are the
half-edges, so the result does not depend on the vertices of `G` at all.

Over the fixed alphabet `Σ₀ = Bool × (HadamardTester.Query → Bool)` (`Cslib.PCP.Dinur.Alphabet`),
with the killing rate `q = 2 ^ 165 + 1` and the walk length `T = 2 ^ 185` chosen once and for all,
the round maps `Σ₀` to itself and **doubles the value up to the threshold** `γ = 1 / T ^ 2`:
`min (2 UNSAT(G)) γ ≤ UNSAT(G.amplify T q)` (`Cslib.PCP.Dinur.min_le_unsatVal_amplify`). This is
Dinur's main theorem, in a non-explicit form: the expanders of preprocessing are chosen
non-constructively (`Cslib.RotationMap.expanderFamily`), and the round is a noncomputable
definition; its realization in polynomial time is not addressed here. The constants are
astronomically large, since nothing has been done to optimize them: the size factors are triply
exponential in `T`.

## Main definitions

* `Cslib.PCP.ConstraintGraph.amplify`: the amplification round, preprocessing, then powering, then
  composition.
* `Cslib.PCP.ConstraintGraph.amplifyVertexFactor`, `Cslib.PCP.ConstraintGraph.amplifyEdgeFactor`:
  the numbers of vertices and edges of the round per edge of the original graph.
* `Cslib.PCP.Dinur.Alphabet`, `Cslib.PCP.Dinur.killRate`, `Cslib.PCP.Dinur.walkLength`,
  `Cslib.PCP.Dinur.gap`: the fixed alphabet, the parameters of the round and its threshold.

## Main results

* `Cslib.PCP.ConstraintGraph.satisfiable_amplify_iff`: the round preserves satisfiability.
* `Cslib.PCP.ConstraintGraph.le_unsatVal_amplify`: the value of the round, for any alphabet.
* `Cslib.PCP.ConstraintGraph.card_vertices_amplify`, `Cslib.PCP.ConstraintGraph.card_edges_amplify`:
  its size.
* `Cslib.PCP.Dinur.min_le_unsatVal_amplify`: over the fixed alphabet, the round doubles the value
  up to the threshold `Cslib.PCP.Dinur.gap`.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
-/

@[expose] public section

namespace Cslib.PCP

open Finset HadamardTester RotationMap

namespace ConstraintGraph

/-- The darts of the powered constraint graph in an amplification round on a constraint graph with
edges `E`: a half-edge of the original graph, the labels of a walk of `T` steps from it in the
preprocessed graph, and its kill signals. They are the edges of the constraint graph that
composition is applied to. -/
abbrev AmplifyDart (E : Type*) (T q : ℕ) : Type _ :=
  (E × Bool) × (Fin T → PreprocessLabel (Fin 120)) × (Fin T → Fin q)

/-- The vertices of the amplification round: those of the composed constraint graph of the powered
one, whose alphabet is `WalkLabels (PreprocessLabel (Fin 120)) T → α`. -/
abbrev AmplifyVertex (E α : Type*) (T q : ℕ) : Type _ :=
  ComposePos (E × Bool) (AmplifyDart E T q) (WalkLabels (PreprocessLabel (Fin 120)) T → α) ⊕
    AmplifyDart E T q × Rand (WalkLabels (PreprocessLabel (Fin 120)) T → α)

/-- The edges of the amplification round: those of the composed constraint graph of the powered
one. -/
abbrev AmplifyEdge (E α : Type*) (T q : ℕ) : Type _ :=
  (AmplifyDart E T q × Rand (WalkLabels (PreprocessLabel (Fin 120)) T → α)) × Query

/- The instances on the vertices and edges of the round are assembled once for any alphabet, so
that those of the round over a concrete alphabet stay below the size limit of instance
synthesis. -/

instance {E α : Type*} [Fintype E] [Fintype α] [DecidableEq α] {T q : ℕ} :
    Fintype (AmplifyVertex E α T q) :=
  inferInstanceAs (Fintype (_ ⊕ _))

instance {E α : Type*} [Fintype E] [Fintype α] [DecidableEq α] {T q : ℕ} :
    Fintype (AmplifyEdge E α T q) :=
  inferInstanceAs (Fintype (_ × _))

section Round

variable {V E α : Type*} [Fintype E] [DecidableEq V] (G : ConstraintGraph V E α)

/-- **The amplification round** [Dinur, Theorem 4.1][Dinur2007]: preprocessing with the
non-explicit family of expanders `RotationMap.expanderFamily`, then powering along killed walks
truncated at `T` steps and killed at rate `q`, then composition back to the alphabet
`Bool × (HadamardTester.Query → Bool)`. -/
noncomputable def amplify (T q : ℕ) [NeZero q] [Fintype α] [DecidableEq α] :
    ConstraintGraph (AmplifyVertex E α T q) (AmplifyEdge E α T q) (Bool × (Query → Bool)) :=
  ((G.preprocess expanderFamily).power T q).toConstraintGraph.compose

variable [Fintype α] [DecidableEq α] [Nonempty α] {T q : ℕ} [NeZero q]

/-- **The amplification round preserves satisfiability**, for walks of at least one step and a
killing rate `q ≥ 2`. -/
theorem satisfiable_amplify_iff (hT : 1 ≤ T) (hq : 2 ≤ q) :
    (G.amplify T q).Satisfiable ↔ G.Satisfiable := by
  rw [amplify, satisfiable_compose_iff,
    RegularConstraintGraph.satisfiable_power_iff _ _ _ hT hq,
    satisfiable_preprocess_iff _ _ (by norm_num)]

/-- **The value of the amplification round** [Dinur, Theorem 4.1][Dinur2007]: for a killing rate
`q ≥ 2` and walks truncated at `T = 4 |α| (q - 1)` steps, it is at least
`(q - 1) / (476 (4 |α| ^ 2 + 16 |α| ^ 4 + 92928000 |α| ^ 5))` times
`min (UNSAT(G) / 1452000) (1 / T ^ 2)`. The factors `1452000` and `476` are lost by
preprocessing and composition; the factor linear in `q` is gained by powering, on the expander that
preprocessing provides. -/
theorem le_unsatVal_amplify (hq : 2 ≤ q) (hT : T = 4 * Fintype.card α * (q - 1)) :
    ((q : ℝ) - 1) / (476 * (4 * Fintype.card α ^ 2 + 16 * Fintype.card α ^ 4 +
        92928000 * Fintype.card α ^ 5)) *
      min (G.unsatVal / 1452000) (1 / T ^ 2) ≤ (G.amplify T q).unsatVal := by
  have hpow := (G.preprocess expanderFamily).le_unsatVal_power T q hq hT
    G.spectralExpansion_preprocess_expanderFamily_le
    (by norm_num)
  set K : ℝ := (Fintype.card α : ℝ)
  have hmu : 128 * K ^ 5 / (1 - (1 - 1 / 726000)) = 92928000 * K ^ 5 := by
    field_simp
    ring
  rw [hmu] at hpow
  have hs : 0 ≤ ((q : ℝ) - 1) / (4 * K ^ 2 + 16 * K ^ 4 + 92928000 * K ^ 5) := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    exact div_nonneg (by linarith) (by positivity)
  calc ((q : ℝ) - 1) / (476 * (4 * K ^ 2 + 16 * K ^ 4 + 92928000 * K ^ 5)) *
        min (G.unsatVal / 1452000) (1 / T ^ 2)
      = ((q - 1) / (4 * K ^ 2 + 16 * K ^ 4 + 92928000 * K ^ 5) *
          min (G.unsatVal / 1452000) (1 / T ^ 2)) / 476 := by
        rw [mul_comm 476, ← div_div]
        ring
    _ ≤ ((q - 1) / (4 * K ^ 2 + 16 * K ^ 4 + 92928000 * K ^ 5) *
          min (G.preprocess expanderFamily).toConstraintGraph.unsatVal (1 / T ^ 2)) / 476 := by
        gcongr ?_ / _
        exact mul_le_mul_of_nonneg_left
          (min_le_min_right _ G.le_unsatVal_preprocess_expanderFamily) hs
    _ ≤ ((G.preprocess expanderFamily).power T q).toConstraintGraph.unsatVal / 476 := by
        gcongr
    _ ≤ (G.amplify T q).unsatVal :=
        ((G.preprocess expanderFamily).power T q).toConstraintGraph.le_unsatVal_compose

end Round

/-! ### Size -/

section Size

/-- The size `K ^ (∑ ℓ ≤ T, 242 ^ ℓ)` of the alphabet of the powered constraint graph in an
amplification round with walks of length `T`, over an alphabet of size `K`. -/
def amplifyAlphabetCard (K T : ℕ) : ℕ :=
  K ^ ∑ ℓ ∈ range (T + 1), 242 ^ ℓ

/-- The number `2 ^ (k + 1) + 2 (2 ^ (2 k) + 2 ^ (4 k ^ 2) + 2 ^ (20 k ^ 2 + 15 k + 3)) (242 q) ^ T`
of vertices of an amplification round per edge of the original graph, where `k` is the size of the
alphabet of the powered graph: an alphabet of size `K`, walks of length `T`, killing rate `q`. -/
def amplifyVertexFactor (K T q : ℕ) : ℕ :=
  2 ^ (amplifyAlphabetCard K T + 1) + 2 * (2 ^ (2 * amplifyAlphabetCard K T) +
    2 ^ (4 * amplifyAlphabetCard K T ^ 2) +
    2 ^ (20 * amplifyAlphabetCard K T ^ 2 + 15 * amplifyAlphabetCard K T + 3)) * (242 * q) ^ T

/-- The number `34 · 2 ^ (20 k ^ 2 + 15 k + 3) (242 q) ^ T` of edges of an amplification round per
edge of the original graph, where `k` is the size of the alphabet of the powered graph: an alphabet
of size `K`, walks of length `T`, killing rate `q`. -/
def amplifyEdgeFactor (K T q : ℕ) : ℕ :=
  34 * 2 ^ (20 * amplifyAlphabetCard K T ^ 2 + 15 * amplifyAlphabetCard K T + 3) * (242 * q) ^ T

variable {E α : Type*} [Fintype E] [Fintype α] (T q : ℕ)

/-- The alphabet of the powered constraint graph in an amplification round has
`|α| ^ (∑ ℓ ≤ T, 242 ^ ℓ)` symbols. -/
theorem card_walkLabels_preprocessLabel :
    Fintype.card (WalkLabels (PreprocessLabel (Fin 120)) T → α) =
      amplifyAlphabetCard (Fintype.card α) T := by
  rw [RegularConstraintGraph.card_alphabet_power, amplifyAlphabetCard, card_label_preprocess,
    Fintype.card_fin]

/-- The powered constraint graph in an amplification round has `2 |E| (242 q) ^ T` darts. -/
theorem card_amplifyDart :
    Fintype.card (AmplifyDart E T q) = 2 * (242 * q) ^ T * Fintype.card E := by
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fun, card_label_preprocess,
    Fintype.card_fin]
  ring

/-- **The size of the amplification round**: every edge of the original graph gives
`amplifyVertexFactor |α| T q` vertices. Its vertices play no role. -/
theorem card_vertices_amplify [DecidableEq α] :
    Fintype.card (AmplifyVertex E α T q) =
      amplifyVertexFactor (Fintype.card α) T q * Fintype.card E := by
  rw [card_vertices_compose, card_amplifyDart, card_walkLabels_preprocessLabel, Fintype.card_prod,
    Fintype.card_bool, amplifyVertexFactor]
  ring

/-- **The size of the amplification round**: every edge of the original graph gives
`amplifyEdgeFactor |α| T q` edges. -/
theorem card_edges_amplify [DecidableEq α] :
    Fintype.card (AmplifyEdge E α T q) =
      amplifyEdgeFactor (Fintype.card α) T q * Fintype.card E := by
  rw [card_edges_compose, card_amplifyDart, card_walkLabels_preprocessLabel, amplifyEdgeFactor]
  ring

end Size

end ConstraintGraph

/-! ### Dinur's round -/

namespace Dinur

open ConstraintGraph

/-- A factor `c ≥ 1` that is at least twice a loss `L` turns `min (u / L) g` into at least
`min (2 u) g`. -/
private theorem min_two_mul_le {u g c L : ℝ} (hu : 0 ≤ u) (hg : 0 ≤ g) (hL : 0 < L)
    (hcL : 2 * L ≤ c) (hc : 1 ≤ c) : min (2 * u) g ≤ c * min (u / L) g := by
  rw [mul_min_of_nonneg _ _ (by linarith)]
  refine min_le_min ?_ (le_mul_of_one_le_left hg hc)
  calc 2 * u = 2 * L * (u / L) := by field_simp
    _ ≤ c * (u / L) := by gcongr

/-- The fixed alphabet `Σ₀` of Dinur's proof: the alphabet `Bool × (HadamardTester.Query → Bool)`
of composition, of `2 ^ 18` symbols. -/
abbrev Alphabet : Type :=
  Bool × (Query → Bool)

/-- The fixed alphabet has `2 ^ 18` symbols. -/
theorem card_alphabet : Fintype.card Alphabet = 2 ^ 18 :=
  card_alphabet_compose

/-- The killing rate `q = 2 ^ 165 + 1` of the walks of Dinur's round: large enough for the factor
`(q - 1) / (476 (4 K ^ 2 + 16 K ^ 4 + 92928000 K ^ 5))` gained by the round, where `K = 2 ^ 18` is
the size of the alphabet, to be at least twice the factor `1452000` lost by preprocessing, with a
factor `K` to spare: as `q - 1 = 2 ^ 57 K ^ 6`, it is at least `2 · 1452000 K`. -/
def killRate : ℕ :=
  2 ^ 165 + 1

/-- The length `T = 2 ^ 185 = 4 |Σ₀| (q - 1)` at which the walks of Dinur's round are
truncated. It is irreducible: the sizes of Dinur's round are triply exponential in `T`, and
neither the elaborator nor the kernel should ever try to evaluate them. -/
irreducible_def walkLength : ℕ :=
  2 ^ 185

instance : NeZero killRate :=
  ⟨Nat.succ_ne_zero _⟩

/-- The killing rate is at least `2`. -/
theorem two_le_killRate : 2 ≤ killRate :=
  Nat.succ_le_succ Nat.one_le_two_pow

/-- The walks of Dinur's round have at least one step. -/
theorem one_le_walkLength : 1 ≤ walkLength :=
  walkLength_def ▸ Nat.one_le_two_pow

/-- The walk length is the one that the powering bound asks for. -/
theorem walkLength_eq : walkLength = 4 * Fintype.card Alphabet * (killRate - 1) := by
  rw [card_alphabet, walkLength_def, killRate, Nat.add_sub_cancel]
  norm_num

/-- The threshold `γ = 1 / T ^ 2 = 2 ^ (-370)` up to which Dinur's round doubles the value. -/
noncomputable def gap : ℝ :=
  1 / (walkLength : ℝ) ^ 2

/-- The threshold is positive. -/
theorem gap_pos : 0 < gap := by
  unfold gap
  have : (0 : ℝ) < walkLength := by exact_mod_cast one_le_walkLength
  positivity

/-- The threshold is at most one. -/
theorem gap_le_one : gap ≤ 1 := by
  unfold gap
  have : (1 : ℝ) ≤ walkLength := by exact_mod_cast one_le_walkLength
  rw [div_le_one (by positivity)]
  nlinarith

variable {V E : Type*} [Fintype E] [DecidableEq V] (G : ConstraintGraph V E Alphabet)

/-- **Dinur's round preserves satisfiability.** -/
theorem satisfiable_amplify_iff :
    (G.amplify walkLength killRate).Satisfiable ↔ G.Satisfiable :=
  G.satisfiable_amplify_iff one_le_walkLength two_le_killRate

/-- **Dinur's main theorem** [Dinur, Theorem 4.1][Dinur2007]: Dinur's round, over the fixed
alphabet `Σ₀`, at least doubles the value of a constraint graph, up to the threshold `gap`. -/
theorem min_le_unsatVal_amplify :
    min (2 * G.unsatVal) gap ≤ (G.amplify walkLength killRate).unsatVal := by
  have h := G.le_unsatVal_amplify two_le_killRate walkLength_eq
  have hq : ((killRate : ℕ) : ℝ) - 1 = 2 ^ 165 := by
    rw [killRate]
    push_cast
    ring
  have hK : ((Fintype.card Alphabet : ℕ) : ℝ) = 2 ^ 18 := by
    rw [card_alphabet]
    norm_num
  rw [hq, hK, ← gap] at h
  refine le_trans ?_ h
  apply min_two_mul_le G.unsatVal_nonneg gap_pos.le (by positivity) <;> norm_num

/-- The number of vertices of Dinur's round per edge of the original graph. -/
def vertexFactor : ℕ :=
  amplifyVertexFactor (2 ^ 18) walkLength killRate

/-- The number of edges of Dinur's round per edge of the original graph. -/
def edgeFactor : ℕ :=
  amplifyEdgeFactor (2 ^ 18) walkLength killRate

/-- **The size of Dinur's round**: every edge of the original graph gives `vertexFactor`
vertices. -/
theorem card_vertices_amplify :
    Fintype.card (AmplifyVertex E Alphabet walkLength killRate) =
      vertexFactor * Fintype.card E := by
  rw [ConstraintGraph.card_vertices_amplify, card_alphabet, vertexFactor]

/-- **The size of Dinur's round**: every edge of the original graph gives `edgeFactor` edges. -/
theorem card_edges_amplify :
    Fintype.card (AmplifyEdge E Alphabet walkLength killRate) = edgeFactor * Fintype.card E := by
  rw [ConstraintGraph.card_edges_amplify, card_alphabet, edgeFactor]

end Dinur

end Cslib.PCP
