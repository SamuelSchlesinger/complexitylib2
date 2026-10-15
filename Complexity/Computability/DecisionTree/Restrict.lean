/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.DecisionTree.NormalForm

/-!
# Restricting decision trees

Fixing some variables can only make a function easier to compute by decision trees: answering the
fixed queries in a tree for `f` gives a tree for the restricted function that is no deeper
(`DecisionTree.restrict`, `DecisionTree.complexity_restrict_le`). Post-processing the output does
not make it harder either (`DecisionTree.complexity_comp_le`), and post-processing by an injective
map, such as negation, does not change it (`DecisionTree.complexity_comp_of_injective`).

## Main definitions

* `Cslib.DecisionTree.restrict`: a tree with some queries answered.

## Main results

* `Cslib.DecisionTree.complexity_restrict_le`: restricting does not raise decision tree
  complexity.
* `Cslib.DecisionTree.complexity_comp_of_injective`: post-processing by an injective map preserves
  decision tree complexity.
-/

@[expose] public section

namespace Cslib.DecisionTree

variable {ι β γ : Type*}

/-- `t` with the queries fixed by `ρ` answered: a variable `i` with `ρ i = some b` reads `b`. -/
def restrict (ρ : ι → Option Bool) : DecisionTree ι β → DecisionTree ι β
  | leaf b => leaf b
  | node i t₀ t₁ => match ρ i with
    | some b => cond b (restrict ρ t₁) (restrict ρ t₀)
    | none => node i (restrict ρ t₀) (restrict ρ t₁)

/-- The restricted tree computes the restricted function. -/
theorem eval_restrict (ρ : ι → Option Bool) (t : DecisionTree ι β) (x : ι → Bool) :
    (t.restrict ρ).eval x = t.eval fun i => (ρ i).getD (x i) := by
  induction t with
  | leaf b => rfl
  | node i t₀ t₁ ih₀ ih₁ =>
    simp only [restrict, eval_node]
    cases ρ i with
    | none => simp [ih₀, ih₁]
    | some b => cases b <;> simp [ih₀, ih₁]

theorem depth_restrict_le (ρ : ι → Option Bool) (t : DecisionTree ι β) :
    (t.restrict ρ).depth ≤ t.depth := by
  induction t with
  | leaf b => simp [restrict]
  | node i t₀ t₁ ih₀ ih₁ =>
    simp only [restrict, depth_node]
    cases ρ i with
    | none => simp only [depth_node]; omega
    | some b => cases b <;> simp only [Bool.cond_true, Bool.cond_false] <;> omega

variable [Finite ι]

/-- **Restricting does not raise decision tree complexity.** -/
theorem complexity_restrict_le (ρ : ι → Option Bool) (f : (ι → Bool) → β) :
    complexity (fun x => f fun i => (ρ i).getD (x i)) ≤ complexity f := by
  obtain ⟨t, ht, hd⟩ := exists_computes_depth_eq_complexity f
  refine (complexity_le_depth (t := t.restrict ρ) fun x => ?_).trans
    ((depth_restrict_le ρ t).trans hd.le)
  rw [eval_restrict, ht]

/-- Post-processing the output does not raise decision tree complexity. -/
theorem complexity_comp_le (g : β → γ) (f : (ι → Bool) → β) :
    complexity (fun x => g (f x)) ≤ complexity f := by
  obtain ⟨t, ht, hd⟩ := exists_computes_depth_eq_complexity f
  refine (complexity_le_depth (t := t.map g) fun x => ?_).trans (by rw [depth_map, hd])
  rw [eval_map, ht]

/-- **Post-processing by an injective map preserves decision tree complexity**: a left inverse
undoes it. -/
theorem complexity_comp_of_injective {g : β → γ} (hg : Function.Injective g)
    (f : (ι → Bool) → β) : complexity (fun x => g (f x)) = complexity f := by
  have : Nonempty β := ⟨f fun _ => false⟩
  refine le_antisymm (complexity_comp_le g f) ?_
  simpa only [Function.leftInverse_invFun hg _] using
    complexity_comp_le (Function.invFun g) fun x => g (f x)

/-- Negation preserves decision tree complexity. -/
theorem complexity_not (f : (ι → Bool) → Bool) :
    complexity (fun x => !f x) = complexity f :=
  complexity_comp_of_injective (fun _ _ => Bool.not_inj) f

end Cslib.DecisionTree
