/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.QueryComplexity.Randomized
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Sion

/-!
# Yao's minimax principle for decision trees

The distributional complexity `D^ν_ε(f)` of `f` for a distribution `ν` on the inputs is the least
depth of a deterministic decision tree that errs with probability at most `ε` on inputs drawn from
`ν` (`QueryComplexity.distributionalComplexity`). **Yao's minimax principle** [Yao1977] says that
the randomized complexity is the distributional complexity of a hardest distribution:
`R_ε(f) = max_ν D^ν_ε(f)` (`QueryComplexity.randomizedComplexity_eq_iSup_distributionalComplexity`,
`QueryComplexity.exists_distributionalComplexity_eq_randomizedComplexity`).

One inequality is the averaging argument: some tree that an optimal randomized tree can draw does
as well as the randomized tree on inputs drawn from `ν`
(`RandomizedDecisionTree.Computes.exists_distributionalError_le`). This is the direction used for
lower bounds: a distribution on which every shallow tree errs often bounds `R_ε(f)` below
(`QueryComplexity.distributionalComplexity_le_randomizedComplexity`).

The other inequality is the minimax theorem for a finite two-player zero-sum game
(`Convexity.StdSimplex.exists_forall_sum_le_of_forall_exists_sum_le`), which we derive from Sion's
minimax theorem in Mathlib [Sion1958]. The algorithm player picks the set of inputs on which a tree
of depth at most `d` errs, of which there are finitely many, the input player picks an input, and
the payoff is `1` when the tree errs. If every distribution on the inputs has a tree of depth at
most `d` erring with probability at most `ε`, the minimax theorem gives a distribution over such
trees erring with probability at most `ε` on every input
(`QueryComplexity.exists_computes_of_forall_exists_distributionalError_le`).

## Main definitions

* `Cslib.QueryComplexity.distributionalComplexity`: the distributional complexity `D^ν_ε(f)`.

## Main results

* `Convexity.StdSimplex.exists_forall_sum_le_of_forall_exists_sum_le`: the minimax theorem for
  finite two-player zero-sum games.
* `Cslib.QueryComplexity.distributionalComplexity_le_randomizedComplexity`: `D^ν_ε(f) ≤ R_ε(f)`.
* `Cslib.QueryComplexity.exists_computes_of_forall_exists_distributionalError_le`: the converse
  for a fixed depth.
* `Cslib.QueryComplexity.randomizedComplexity_eq_iSup_distributionalComplexity`: **Yao's minimax
  principle**, `R_ε(f) = ⨆ ν, D^ν_ε(f)`.
* `Cslib.QueryComplexity.exists_distributionalComplexity_eq_randomizedComplexity`: some
  distribution is hardest.

## References

* [A. C.-C. Yao, *Probabilistic computations: toward a unified measure of complexity*][Yao1977]
* [M. Sion, *On general minimax theorems*][Sion1958]
-/

@[expose] public section

namespace Convexity.StdSimplex

/-- `x ↦ ∑ i, x i * a i` is linear. -/
private theorem isLinearMap_sum_mul {I : Type*} [Fintype I] (a : I → ℝ) :
    IsLinearMap ℝ fun x : I → ℝ => ∑ i, x i * a i :=
  ⟨fun x y => by simp [add_mul, Finset.sum_add_distrib],
    fun c x => by simp [Finset.mul_sum, mul_assoc]⟩

/-- The weight vectors of the distributions on a finite type form a convex set. -/
private theorem convex_range_weights (I : Type*) [Finite I] :
    Convex ℝ (Set.range fun p : StdSimplex ℝ I => (p.weights : I → ℝ)) := by
  have := Fintype.ofFinite I
  rw [range_toFun_comp_weights]
  refine Convex.inter (convex_iInter fun i => ?_) ?_
  · exact convex_halfSpace_ge ⟨fun x y => rfl, fun c x => rfl⟩ 0
  · simpa using convex_hyperplane (isLinearMap_sum_mul fun _ => (1 : ℝ)) 1

/-- The weight vectors of the distributions on a finite type form a compact set. -/
private theorem isCompact_range_weights (I : Type*) [Finite I] :
    IsCompact (Set.range fun p : StdSimplex ℝ I => (p.weights : I → ℝ)) :=
  isCompact_range (isEmbedding_toFun_comp_weights ℝ I).continuous

/-- **The minimax theorem for finite two-player zero-sum games** [Sion1958], in the form used by
Yao's principle. A row player picks `i : I`, a column player picks `j : J`, and the row player pays
`M i j`. If against every mixed strategy `q` of the column player some row `i` has expected payment
at most `c`, then some mixed strategy `p` of the row player has expected payment at most `c` against
every column `j`. -/
theorem exists_forall_sum_le_of_forall_exists_sum_le {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty I] (M : I → J → ℝ) {c : ℝ}
    (h : ∀ q : StdSimplex ℝ J, ∃ i, ∑ j, q.weights j * M i j ≤ c) :
    ∃ p : StdSimplex ℝ I, ∀ j, ∑ i, p.weights i * M i j ≤ c := by
  classical
  rcases isEmpty_or_nonempty J with hJ | hJ
  · exact ⟨.single (Classical.arbitrary I), fun j => isEmptyElim j⟩
  -- the expected payment, a bilinear function on pairs of weight vectors
  set φ : (I → ℝ) → (J → ℝ) → ℝ := fun x y => ∑ i, ∑ j, x i * y j * M i j
  have hφx (y : J → ℝ) : (fun x => φ x y) = fun x => ∑ i, x i * ∑ j, y j * M i j := by
    funext x
    simp only [φ, Finset.mul_sum, mul_assoc]
  have hφy (x : I → ℝ) : (fun y => φ x y) = fun y => ∑ j, y j * ∑ i, x i * M i j := by
    funext y
    simp only [φ, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  have hcont : Continuous fun p : (I → ℝ) × (J → ℝ) => φ p.1 p.2 := by
    simp only [φ]
    fun_prop
  -- a saddle point of `φ` on the two simplices
  obtain ⟨a, ⟨p, rfl⟩, b, ⟨q, rfl⟩, hab⟩ := Sion.exists_isSaddlePointOn (f := φ)
    (Set.range_nonempty _) (convex_range_weights I) (isCompact_range_weights I)
    (fun y _ =>
      (hcont.comp (Continuous.prodMk_left y)).lowerSemicontinuous.lowerSemicontinuousOn _)
    (fun y _ r => by
      rw [hφx]
      exact (convex_range_weights I).inter (convex_halfSpace_le (isLinearMap_sum_mul _) r))
    (convex_range_weights J) (Set.range_nonempty _) (isCompact_range_weights J)
    (fun x _ =>
      (hcont.comp (Continuous.prodMk_right x)).upperSemicontinuous.upperSemicontinuousOn _)
    (fun x _ r => by
      rw [hφy]
      exact (convex_range_weights J).inter (convex_halfSpace_ge (isLinearMap_sum_mul _) r))
  -- against the column strategy `q` some row `i` pays at most `c`, and `p` does no worse
  obtain ⟨i, hi⟩ := h q
  refine ⟨p, fun j => ?_⟩
  have h₁ := hab _ ⟨.single i, rfl⟩ _ ⟨.single j, rfl⟩
  simp only [φ, weights_single, Finsupp.single_apply] at h₁
  simp only [mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, Finset.sum_ite_irrel, Finset.sum_const_zero] at h₁
  exact h₁.trans hi

end Convexity.StdSimplex

namespace Cslib

open Convexity RandomizedDecisionTree

namespace QueryComplexity

variable {ι β : Type*} {f : (ι → Bool) → β} {ν : StdSimplex ℝ (ι → Bool)} {ε : ℝ} {d : ℕ}
  {t : DecisionTree ι β}

/-- The distributional complexity `D^ν_ε(f)`: the least depth of a decision tree that errs with
probability at most `ε` on inputs drawn from `ν`. It is `0` when no decision tree qualifies, which
over finitely many variables happens exactly for `ε < 0`. -/
noncomputable def distributionalComplexity (ε : ℝ) (ν : StdSimplex ℝ (ι → Bool))
    (f : (ι → Bool) → β) : ℕ :=
  sInf {d | ∃ t : DecisionTree ι β, t.distributionalError ν f ≤ ε ∧ t.depth ≤ d}

theorem distributionalComplexity_le_depth (h : t.distributionalError ν f ≤ ε) :
    distributionalComplexity ε ν f ≤ t.depth :=
  Nat.sInf_le ⟨t, h, le_rfl⟩

/-- `D^ν_ε(f) = 0` for `ε < 0`, where no decision tree qualifies. -/
theorem distributionalComplexity_of_neg (hε : ε < 0) : distributionalComplexity ε ν f = 0 :=
  Nat.sInf_eq_zero.mpr <| Or.inr <| Set.eq_empty_of_forall_notMem fun _ ⟨_, h, _⟩ =>
    (not_le.mpr hε) (DecisionTree.distributionalError_nonneg.trans h)

variable [Finite ι]

/-- For `ε ≥ 0` the distributional complexity is attained: some decision tree of depth
`D^ν_ε(f)` errs with probability at most `ε` on inputs drawn from `ν`. -/
theorem exists_distributionalError_le_depth_eq_distributionalComplexity (hε : 0 ≤ ε)
    (ν : StdSimplex ℝ (ι → Bool)) (f : (ι → Bool) → β) : ∃ t : DecisionTree ι β,
      t.distributionalError ν f ≤ ε ∧ t.depth = distributionalComplexity ε ν f := by
  obtain ⟨t, ht, -⟩ := DecisionTree.exists_computes_depth_eq_complexity f
  obtain ⟨t', ht', hd⟩ := Nat.sInf_mem (s := {d | ∃ t : DecisionTree ι β,
    t.distributionalError ν f ≤ ε ∧ t.depth ≤ d}) ⟨_, t, ht.distributionalError_eq_zero.trans_le hε,
      le_rfl⟩
  exact ⟨t', ht', le_antisymm hd (distributionalComplexity_le_depth ht')⟩

/-- **The easy direction of Yao's principle**: `D^ν_ε(f) ≤ R_ε(f)` for every distribution `ν` on
the inputs. To bound `R_ε(f)` below, it suffices to find a distribution on which every shallow
decision tree errs often. -/
theorem distributionalComplexity_le_randomizedComplexity (ε : ℝ) (ν : StdSimplex ℝ (ι → Bool))
    (f : (ι → Bool) → β) : distributionalComplexity ε ν f ≤ randomizedComplexity ε f := by
  rcases lt_or_ge ε 0 with hε | hε
  · rw [distributionalComplexity_of_neg hε]
    exact Nat.zero_le _
  obtain ⟨μ, hμ, hd⟩ := exists_computes_depth_eq_randomizedComplexity hε f
  obtain ⟨t, ht, hνt⟩ := hμ.exists_distributionalError_le ν
  exact (distributionalComplexity_le_depth hνt).trans ((depth_le_depth ht).trans_eq hd)

/-- **The hard direction of Yao's principle**, by the minimax theorem: if for every distribution
`ν` on the inputs some decision tree of depth at most `d` errs with probability at most `ε` on
inputs drawn from `ν`, then some randomized decision tree of depth at most `d` computes `f` with
error `ε`. -/
theorem exists_computes_of_forall_exists_distributionalError_le
    (h : ∀ ν : StdSimplex ℝ (ι → Bool), ∃ t : DecisionTree ι β,
      t.depth ≤ d ∧ t.distributionalError ν f ≤ ε) :
    ∃ μ : RandomizedDecisionTree ι β, μ.Computes ε f ∧ μ.depth ≤ d := by
  classical
  have := Fintype.ofFinite ι
  -- the pure strategies of the algorithm: the sets of inputs on which a tree of depth at most `d`
  -- errs
  let I := {S : Set (ι → Bool) // ∃ t : DecisionTree ι β, t.depth ≤ d ∧ {x | t.eval x ≠ f x} = S}
  have : Fintype I := Fintype.ofFinite I
  obtain ⟨t₀, ht₀, -⟩ := h (.single fun _ => false)
  have : Nonempty I := ⟨⟨_, t₀, ht₀, rfl⟩⟩
  choose tree htree_depth htree_err using fun S : I => S.2
  have hM (S : I) (x : ι → Bool) :
      (if (tree S).eval x = f x then 0 else 1 : ℝ) = if x ∈ S.1 then 1 else 0 := by
    rw [← htree_err S]
    by_cases hx : (tree S).eval x = f x <;> simp [hx]
  obtain ⟨p, hp⟩ := StdSimplex.exists_forall_sum_le_of_forall_exists_sum_le (I := I)
    (fun S x => if x ∈ S.1 then 1 else 0) (c := ε) fun q => by
      obtain ⟨t, ht, hq⟩ := h q
      refine ⟨⟨_, t, ht, rfl⟩, ?_⟩
      rw [DecisionTree.distributionalError_eq_sum, Finsupp.sum_fintype _ _ fun _ => zero_mul _]
        at hq
      refine le_of_eq_of_le (Finset.sum_congr rfl fun x _ => ?_) hq
      by_cases hx : t.eval x = f x <;> simp [hx]
  refine ⟨p.map tree, fun x => ?_, depth_le_iff.mpr fun t ht => ?_⟩
  · rw [errorProb_eq_sum, StdSimplex.weights_map,
      Finsupp.sum_mapDomain_index (fun _ => zero_mul _) fun _ _ _ => add_mul _ _ _,
      Finsupp.sum_fintype _ _ fun _ => zero_mul _]
    exact le_of_eq_of_le (Finset.sum_congr rfl fun S _ => by rw [hM]) (hp x)
  · obtain ⟨S, -, rfl⟩ := Finset.mem_image.mp
      (Finsupp.mapDomain_support (by simpa [StdSimplex.weights_map] using ht))
    exact htree_depth S

/-- `R_ε(f) ≤ d` exactly when `D^ν_ε(f) ≤ d` for every distribution `ν` on the inputs. -/
theorem randomizedComplexity_le_iff_forall_distributionalComplexity_le :
    randomizedComplexity ε f ≤ d ↔
      ∀ ν : StdSimplex ℝ (ι → Bool), distributionalComplexity ε ν f ≤ d := by
  refine ⟨fun h ν => (distributionalComplexity_le_randomizedComplexity ε ν f).trans h,
    fun h => ?_⟩
  rcases lt_or_ge ε 0 with hε | hε
  · rw [randomizedComplexity_of_neg hε]
    exact Nat.zero_le _
  obtain ⟨μ, hμ, hd⟩ := exists_computes_of_forall_exists_distributionalError_le fun ν =>
    let ⟨t, ht, hd⟩ := exists_distributionalError_le_depth_eq_distributionalComplexity hε ν f
    ⟨t, hd.trans_le (h ν), ht⟩
  exact (randomizedComplexity_le_depth hμ).trans hd

/-- **Yao's minimax principle**: the randomized decision tree complexity is the largest
distributional complexity over the distributions on the inputs, `R_ε(f) = ⨆ ν, D^ν_ε(f)`. -/
theorem randomizedComplexity_eq_iSup_distributionalComplexity (ε : ℝ) (f : (ι → Bool) → β) :
    randomizedComplexity ε f = ⨆ ν : StdSimplex ℝ (ι → Bool), distributionalComplexity ε ν f := by
  have hbdd : BddAbove (Set.range fun ν : StdSimplex ℝ (ι → Bool) =>
      distributionalComplexity ε ν f) :=
    ⟨randomizedComplexity ε f, Set.forall_mem_range.mpr fun ν =>
      distributionalComplexity_le_randomizedComplexity ε ν f⟩
  exact le_antisymm (randomizedComplexity_le_iff_forall_distributionalComplexity_le.mpr
    fun ν => le_ciSup hbdd ν) (ciSup_le fun ν =>
      distributionalComplexity_le_randomizedComplexity ε ν f)

/-- **Yao's minimax principle**, with a hardest distribution: some distribution `ν` on the inputs
has `D^ν_ε(f) = R_ε(f)`. -/
theorem exists_distributionalComplexity_eq_randomizedComplexity (ε : ℝ) (f : (ι → Bool) → β) :
    ∃ ν : StdSimplex ℝ (ι → Bool), distributionalComplexity ε ν f = randomizedComplexity ε f := by
  have hbdd : BddAbove (Set.range fun ν : StdSimplex ℝ (ι → Bool) =>
      distributionalComplexity ε ν f) :=
    ⟨randomizedComplexity ε f, Set.forall_mem_range.mpr fun ν =>
      distributionalComplexity_le_randomizedComplexity ε ν f⟩
  obtain ⟨ν, hν⟩ := Nat.sSup_mem (Set.range_nonempty _) hbdd
  exact ⟨ν, hν.trans (randomizedComplexity_eq_iSup_distributionalComplexity ε f).symm⟩

end QueryComplexity

end Cslib
