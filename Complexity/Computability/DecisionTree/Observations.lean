/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.DecisionTree.Leaves

/-!
# Decision trees from finite observations

An output determined by finitely many Boolean observations has a small decision tree whenever
each nonconstant finite input domain admits a query for one varying observation. Queries may
depend on the current domain. The construction only branches when both answers occur, so its
leaf bound counts attained observation vectors rather than all possible Boolean vectors.

## Main results

* `Cslib.DecisionTree.exists_of_observations`: a tree has depth at most the observation count
  and at most one leaf per attained observation vector.
-/

@[expose] public section

namespace Cslib.DecisionTree

open Finset

variable {X I Q β : Type*} [Fintype I]

/-- A domain-dependent query for a varying observation yields a tree with no empty branches.
The output need only be constant on observation fibers inside the supplied finite domain. -/
theorem exists_of_observations (S : Finset X) (hS : S.Nonempty)
    (observe : X → I → Bool) (answer : Q → X → Bool) (output : X → β)
    (hout : ∀ x ∈ S, ∀ y ∈ S, observe x = observe y → output x = output y)
    (hquery : ∀ T : Finset X, T ⊆ S → T.Nonempty →
      (∃ x ∈ T, ∃ y ∈ T, observe x ≠ observe y) →
      ∃ (q : Q) (i : I), (∀ x ∈ T, answer q x = observe x i) ∧
        ∀ b : Bool, (T.filter fun x => observe x i = b).Nonempty) :
    ∃ t : DecisionTree Q β, (∀ x ∈ S, t.eval (fun q => answer q x) = output x) ∧
      t.depth ≤ Fintype.card I ∧ t.leafCount ≤ (S.image observe).card := by
  classical
  have build (remaining : Finset I) : ∀ T : Finset X, T ⊆ S → T.Nonempty →
      (∀ x ∈ T, ∀ y ∈ T, ∀ i ∉ remaining, observe x i = observe y i) →
      ∃ t : DecisionTree Q β, (∀ x ∈ T, t.eval (fun q => answer q x) = output x) ∧
        t.depth ≤ remaining.card ∧ t.leafCount ≤ (T.image observe).card := by
    induction remaining using Finset.strongInductionOn with
    | _ remaining ih =>
      intro T hTS hT hfixed
      obtain ⟨x₀, hx₀⟩ := hT
      by_cases hconstant : ∀ x ∈ T, observe x = observe x₀
      · exact ⟨.leaf (output x₀), fun x hx =>
          hout x₀ (hTS hx₀) x (hTS hx) (hconstant x hx).symm,
          Nat.zero_le _, card_pos.mpr ⟨observe x₀, mem_image.mpr ⟨x₀, hx₀, rfl⟩⟩⟩
      · obtain ⟨x, hx, hne⟩ := by simpa only [not_forall, not_imp] using hconstant
        obtain ⟨q, i, hq, hbranches⟩ := hquery T hTS ⟨x₀, hx₀⟩
          ⟨x, hx, x₀, hx₀, hne⟩
        have hi : i ∈ remaining := by
          by_contra hi
          obtain ⟨x, hx⟩ := hbranches false
          obtain ⟨y, hy⟩ := hbranches true
          have := hfixed x (mem_filter.mp hx).1 y (mem_filter.mp hy).1 i hi
          simp only [(mem_filter.mp hx).2, (mem_filter.mp hy).2, Bool.false_eq_true] at this
        have branch (b : Bool) : ∃ t : DecisionTree Q β,
            (∀ x ∈ T.filter (fun x => observe x i = b),
              t.eval (fun q => answer q x) = output x) ∧
            t.depth ≤ (remaining.erase i).card ∧
            t.leafCount ≤ ((T.filter fun x => observe x i = b).image observe).card := by
          apply ih (remaining.erase i) (erase_ssubset hi) _
            ((filter_subset _ _).trans hTS) (hbranches b)
          intro x hx y hy j hj
          by_cases hji : j = i
          · subst j
            exact (mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm
          · exact hfixed x (mem_filter.mp hx).1 y (mem_filter.mp hy).1 j
              (fun hjr => hj (mem_erase.mpr ⟨hji, hjr⟩))
        obtain ⟨left, hl, hld, hlc⟩ := branch false
        obtain ⟨right, hr, hrd, hrc⟩ := branch true
        refine ⟨.node q left right, ?_, ?_, ?_⟩
        · intro x hx
          simp only [eval_node, hq x hx]
          cases hb : observe x i
          · exact hl x (mem_filter.mpr ⟨hx, hb⟩)
          · exact hr x (mem_filter.mpr ⟨hx, hb⟩)
        · exact (Nat.add_le_add_right (max_le hld hrd) 1).trans_eq
            (card_erase_add_one hi)
        · have hcard : ((T.filter fun x => observe x i = false).image observe).card +
              ((T.filter fun x => observe x i = true).image observe).card =
              (T.image observe).card := by
            rw [← filter_image (s := T) (f := observe) (p := fun z => z i = false),
              ← filter_image (s := T) (f := observe) (p := fun z => z i = true)]
            simpa only [Bool.not_eq_false] using
              (card_filter_add_card_filter_not (s := T.image observe) fun z => z i = false)
          exact (Nat.add_le_add hlc hrc).trans_eq hcard
  simpa only [card_univ] using build univ S (Subset.refl _) hS
    (fun _ _ _ _ i hi => (hi (mem_univ i)).elim)

end Cslib.DecisionTree
