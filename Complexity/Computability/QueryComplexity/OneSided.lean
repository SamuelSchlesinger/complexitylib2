/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.DecisionTree.Restrict
public import Complexity.Computability.QueryComplexity.Relations

/-!
# One-sided measures and negation

For a value `b`, the one-sided measures `s_b(f)`, `bs_b(f)` and `C_b(f)` are the largest
sensitivity, block sensitivity and certificate complexity of `f` at an input of value `b`.

* **One-sided Nisan bound** `C_b(f) ≤ s_{¬b}(f) bs_b(f)`, a one-sided form of Nisan's bound
  `C(f) ≤ s(f) bs(f)` [Nisan1991]
  (`QueryComplexity.certificateComplexityFor_le_sensitivityFor_mul_blockSensitivityFor`). In
  Nisan's proof, every coordinate of a minimal sensitive block `B` at `x` is sensitive at `x`
  with `B` flipped, an input of value `¬f(x)`, so `|B| ≤ s_{¬f(x)}(f)`
  (`QueryComplexity.IsMinimalSensitiveBlock.card_le_sensitivityFor`).
* **Negation** keeps sensitive coordinates, sensitive blocks and certificates, so it preserves
  `s`, `bs` and `C` and exchanges the two values of the one-sided measures
  (`QueryComplexity.blockSensitivityFor_not`, `QueryComplexity.certificateComplexityFor_not`).
  With `D(¬f) = D(f)` this turns the bound `D(f) ≤ bs₀(f) C₁(f)` of
  [BealsBuhrmanCleveMoscaDeWolf2001] into its dual `D(f) ≤ bs₁(f) C₀(f)`
  (`DecisionTree.complexity_le_blockSensitivityFor_not_mul_certificateComplexityFor`), hence
  `D(f) ≤ min(C₀(f), C₁(f)) bs(f)` and, with the one-sided Nisan bound,
  `D(f) ≤ bs_{¬b}(f) s_{¬b}(f) bs_b(f)`.

## Main definitions

* `Cslib.BitString.sensitivityFor`: the sensitivity `s_b(f)` of the inputs where `f` has value `b`.

## Main results

* `Cslib.QueryComplexity.certificateComplexityAt_le_sensitivityFor_mul_blockSensitivityAt`:
  `C(f, x) ≤ s_{¬f(x)}(f) bs(f, x)`.
* `Cslib.QueryComplexity.certificateComplexityFor_le_sensitivityFor_mul_blockSensitivityFor`:
  `C_b(f) ≤ s_{¬b}(f) bs_b(f)`.
* `Cslib.BitString.sensitivity_not`, `Cslib.QueryComplexity.blockSensitivity_not`,
  `Cslib.QueryComplexity.certificateComplexity_not`: negation preserves `s`, `bs` and `C`.
* `Cslib.DecisionTree.complexity_le_blockSensitivityFor_not_mul_certificateComplexityFor`:
  `D(f) ≤ bs_{¬b}(f) C_b(f)`.
* `Cslib.DecisionTree.complexity_le_min_certificateComplexityFor_mul_blockSensitivity`:
  `D(f) ≤ min(C₀(f), C₁(f)) bs(f)`.
* `Cslib.DecisionTree.complexity_le_blockSensitivityFor_mul_sensitivityFor_mul_blockSensitivityFor`:
  `D(f) ≤ bs_{¬b}(f) s_{¬b}(f) bs_b(f)`.

## References

* [N. Nisan, *CREW PRAMs and decision trees*][Nisan1991]
* [R. Beals, H. Buhrman, R. Cleve, M. Mosca, R. de Wolf, *Quantum lower bounds by
  polynomials*][BealsBuhrmanCleveMoscaDeWolf2001]
* [H. Buhrman, R. de Wolf, *Complexity measures and decision tree complexity:
  a survey*][BuhrmanDeWolf2002]
-/

@[expose] public section

namespace Cslib

open Finset

variable {n : ℕ}

/-- Negation exchanges the inputs of value `b` and those of value `!b`. -/
private theorem filter_not_eq (f : BooleanFunction n) (b : Bool) :
    (univ.filter fun x => (!f x) = b) = univ.filter fun x => f x = !b := by
  ext x
  cases f x <;> cases b <;> simp

namespace BitString

/-! ### One-sided sensitivity -/

/-- `s_b(f)`: the largest sensitivity of `f` at an input where it has value `b`. -/
def sensitivityFor (f : BooleanFunction n) (b : Bool) : ℕ :=
  (univ.filter fun x => f x = b).sup (sensitivityAt f)

/-- The sensitivity at an input of value `b` is at most `s_b(f)`. -/
theorem sensitivityAt_le_sensitivityFor {f : BooleanFunction n} {x : BitString n} {b : Bool}
    (h : f x = b) : sensitivityAt f x ≤ sensitivityFor f b :=
  le_sup (f := sensitivityAt f) (mem_filter.2 ⟨mem_univ x, h⟩)

/-- `s_b(f) ≤ s(f)`. -/
theorem sensitivityFor_le_sensitivity (f : BooleanFunction n) (b : Bool) :
    sensitivityFor f b ≤ sensitivity f :=
  sup_mono (filter_subset _ _)

/-! ### Negation -/

/-- Negating a function keeps its sensitive coordinates. -/
@[simp]
theorem isSensitiveCoord_not {f : BooleanFunction n} {x : BitString n} {i : Fin n} :
    IsSensitiveCoord (fun y => !f y) x i ↔ IsSensitiveCoord f x i := by
  simp [IsSensitiveCoord]

/-- Negation preserves the sensitivity at an input. -/
theorem sensitivityAt_not (f : BooleanFunction n) (x : BitString n) :
    sensitivityAt (fun y => !f y) x = sensitivityAt f x := by
  unfold sensitivityAt sensitiveCoords
  congr 1
  ext i
  simp

/-- Negation preserves sensitivity. -/
theorem sensitivity_not (f : BooleanFunction n) :
    sensitivity (fun y => !f y) = sensitivity f := by
  rw [sensitivity, sensitivity, funext (sensitivityAt_not f)]

/-- Negation exchanges `s₀` and `s₁`. -/
theorem sensitivityFor_not (f : BooleanFunction n) (b : Bool) :
    sensitivityFor (fun y => !f y) b = sensitivityFor f (!b) := by
  rw [sensitivityFor, sensitivityFor, filter_not_eq, funext (sensitivityAt_not f)]

end BitString

open BitString

namespace QueryComplexity

variable {f : BooleanFunction n} {x : BitString n}

/-- Negating a function keeps its sensitive blocks. -/
@[simp]
theorem isSensitiveBlock_not {B : Block n} :
    IsSensitiveBlock (fun y => !f y) x B ↔ IsSensitiveBlock f x B := by
  simp [IsSensitiveBlock]

/-- Negating a function keeps its certificates. -/
@[simp]
theorem isCertificate_not {S : Finset (Fin n)} :
    IsCertificate (fun y => !f y) x S ↔ IsCertificate f x S := by
  simp [IsCertificate]

/-- Negation preserves the block sensitivity at an input. -/
theorem blockSensitivityAt_not (f : BooleanFunction n) (x : BitString n) :
    blockSensitivityAt (fun y => !f y) x = blockSensitivityAt f x := by
  have : sensitiveFamilies (fun y => !f y) x = sensitiveFamilies f x := by
    ext F
    simp [IsSensitiveFamily]
  rw [blockSensitivityAt, blockSensitivityAt, this]

/-- Negation preserves the certificate complexity at an input. -/
theorem certificateComplexityAt_not (f : BooleanFunction n) (x : BitString n) :
    certificateComplexityAt (fun y => !f y) x = certificateComplexityAt f x := by
  obtain ⟨S, hS, hSc⟩ := exists_isCertificate_card_eq f x
  obtain ⟨T, hT, hTc⟩ := exists_isCertificate_card_eq (fun y => !f y) x
  exact le_antisymm ((certificateComplexityAt_le (isCertificate_not.2 hS)).trans hSc.le)
    ((certificateComplexityAt_le (isCertificate_not.1 hT)).trans hTc.le)

/-- Negation preserves block sensitivity. -/
theorem blockSensitivity_not (f : BooleanFunction n) :
    blockSensitivity (fun y => !f y) = blockSensitivity f := by
  rw [blockSensitivity, blockSensitivity, funext (blockSensitivityAt_not f)]

/-- Negation preserves certificate complexity. -/
theorem certificateComplexity_not (f : BooleanFunction n) :
    certificateComplexity (fun y => !f y) = certificateComplexity f := by
  rw [certificateComplexity, certificateComplexity, funext (certificateComplexityAt_not f)]

/-- Negation exchanges `bs₀` and `bs₁`. -/
theorem blockSensitivityFor_not (f : BooleanFunction n) (b : Bool) :
    blockSensitivityFor (fun y => !f y) b = blockSensitivityFor f (!b) := by
  rw [blockSensitivityFor, blockSensitivityFor, filter_not_eq, funext (blockSensitivityAt_not f)]

/-- Negation exchanges `C₀` and `C₁`. -/
theorem certificateComplexityFor_not (f : BooleanFunction n) (b : Bool) :
    certificateComplexityFor (fun y => !f y) b = certificateComplexityFor f (!b) := by
  rw [certificateComplexityFor, certificateComplexityFor, filter_not_eq,
    funext (certificateComplexityAt_not f)]

/-! ### The one-sided Nisan bound -/

/-- A minimal sensitive block at `x` has at most `s_{¬f(x)}(f)` coordinates: they are all
sensitive at `x` with the block flipped, where `f` has the other value. -/
theorem IsMinimalSensitiveBlock.card_le_sensitivityFor {B : Block n}
    (hB : IsMinimalSensitiveBlock f x B) : #B ≤ sensitivityFor f (!f x) := by
  refine (card_le_sensitivityAt fun i hi => hB.isSensitiveCoord_flipBlock hi).trans
    (sensitivityAt_le_sensitivityFor ?_)
  have := hB.1
  unfold IsSensitiveBlock at this
  cases h1 : f (flipBlock B x) <;> cases h2 : f x <;> simp_all

/-- The union of a largest family of pairwise disjoint minimal sensitive blocks is a
certificate. -/
private theorem isCertificate_biUnion_of_maximal {F : Finset (Block n)}
    (hF : IsSensitiveFamily f x F) (hmin : ∀ B ∈ F, IsMinimalSensitiveBlock f x B)
    (hmax : ∀ G : Finset (Block n), IsSensitiveFamily f x G →
      (∀ B ∈ G, IsMinimalSensitiveBlock f x B) → #G ≤ #F) :
    IsCertificate f x (F.biUnion id) := by
  intro y hy
  by_contra hne
  -- the coordinates on which `y` differs from `x` form a sensitive block outside the family
  have hB : IsSensitiveBlock f x ({i | y i ≠ x i} : Finset (Fin n)) := by
    rw [IsSensitiveBlock, flipBlock_filter_ne]
    exact hne
  obtain ⟨C, hCsub, hC⟩ := hB.exists_isMinimalSensitiveBlock_subset
  have hdisj : ∀ B ∈ F, Disjoint C B := fun B hBF => disjoint_left.2 fun i hiC hiB =>
    (mem_filter.1 (hCsub hiC)).2 (hy i (mem_biUnion.2 ⟨B, hBF, hiB⟩))
  have hCF : C ∉ F := fun hCF => by
    obtain ⟨i, hi⟩ := hC.1.nonempty
    exact disjoint_left.1 (hdisj C hCF) hi hi
  -- adding it gives a larger family
  have hG : IsSensitiveFamily f x (insert C F) := by
    refine ⟨fun B hB => ?_, ?_⟩
    · rcases mem_insert.1 hB with rfl | hB
      · exact hC.1
      · exact hF.1 B hB
    · rw [coe_insert]
      exact hF.2.insert fun B hB _ => hdisj B hB
  have := hmax _ hG fun B hB => by
    rcases mem_insert.1 hB with rfl | hB
    · exact hC
    · exact hmin B hB
  rw [card_insert_of_notMem hCF] at this
  omega

/-- **One-sided Nisan bound at an input**: `C(f, x) ≤ s_{¬f(x)}(f) bs(f, x)`. -/
theorem certificateComplexityAt_le_sensitivityFor_mul_blockSensitivityAt (f : BooleanFunction n)
    (x : BitString n) :
    certificateComplexityAt f x ≤ sensitivityFor f (!f x) * blockSensitivityAt f x := by
  classical
  -- a largest family of pairwise disjoint minimal sensitive blocks
  obtain ⟨F, hF, hmax⟩ := exists_max_image
    ((sensitiveFamilies f x).filter fun F => ∀ B ∈ F, IsMinimalSensitiveBlock f x B) card
    ⟨∅, mem_filter.2 ⟨mem_sensitiveFamilies.2 ⟨by simp, by simp⟩, by simp⟩⟩
  obtain ⟨hFs, hFmin⟩ := mem_filter.1 hF
  rw [mem_sensitiveFamilies] at hFs
  have hcert := isCertificate_biUnion_of_maximal hFs hFmin fun G hG hGmin =>
    hmax G (mem_filter.2 ⟨mem_sensitiveFamilies.2 hG, hGmin⟩)
  calc certificateComplexityAt f x ≤ #(F.biUnion id) := certificateComplexityAt_le hcert
    _ ≤ ∑ B ∈ F, #B := card_biUnion_le
    _ ≤ #F * sensitivityFor f (!f x) :=
      sum_le_card_nsmul _ _ _ fun B hB => (hFmin B hB).card_le_sensitivityFor
    _ ≤ sensitivityFor f (!f x) * blockSensitivityAt f x := by
      rw [mul_comm]
      exact Nat.mul_le_mul_left _ (card_le_blockSensitivityAt hFs)

/-- **One-sided Nisan bound**: `C_b(f) ≤ s_{¬b}(f) bs_b(f)`. -/
theorem certificateComplexityFor_le_sensitivityFor_mul_blockSensitivityFor
    (f : BooleanFunction n) (b : Bool) :
    certificateComplexityFor f b ≤ sensitivityFor f (!b) * blockSensitivityFor f b :=
  Finset.sup_le fun x hx => by
    have hx : f x = b := (mem_filter.1 hx).2
    have := certificateComplexityAt_le_sensitivityFor_mul_blockSensitivityAt f x
    rw [hx] at this
    exact this.trans (Nat.mul_le_mul_left _ (blockSensitivityAt_le_blockSensitivityFor hx))

end QueryComplexity

namespace DecisionTree

open QueryComplexity

/-- **Decision tree complexity from one-sided measures**: `D(f) ≤ bs_{¬b}(f) C_b(f)` for either
value `b`. For `b = 1` this is the bound of Beals, Buhrman, Cleve, Mosca and de Wolf
[BealsBuhrmanCleveMoscaDeWolf2001]; negating the function gives the dual `D(f) ≤ bs₁(f) C₀(f)`. -/
theorem complexity_le_blockSensitivityFor_not_mul_certificateComplexityFor
    (f : BooleanFunction n) (b : Bool) :
    complexity f ≤ blockSensitivityFor f (!b) * certificateComplexityFor f b := by
  cases b with
  | false =>
    have := complexity_le_blockSensitivityFor_mul_certificateComplexityFor (fun y => !f y)
    rwa [complexity_not, blockSensitivityFor_not, certificateComplexityFor_not] at this
  | true => exact complexity_le_blockSensitivityFor_mul_certificateComplexityFor f

/-- `D(f) ≤ C_b(f) bs(f)` for either value `b` [BealsBuhrmanCleveMoscaDeWolf2001]. -/
theorem complexity_le_certificateComplexityFor_mul_blockSensitivity (f : BooleanFunction n)
    (b : Bool) : complexity f ≤ certificateComplexityFor f b * blockSensitivity f :=
  (complexity_le_blockSensitivityFor_not_mul_certificateComplexityFor f b).trans (by
    rw [mul_comm]
    exact Nat.mul_le_mul_left _ (blockSensitivityFor_le_blockSensitivity f _))

/-- `D(f) ≤ min(C₀(f), C₁(f)) bs(f)`. -/
theorem complexity_le_min_certificateComplexityFor_mul_blockSensitivity (f : BooleanFunction n) :
    complexity f ≤
      min (certificateComplexityFor f false) (certificateComplexityFor f true) *
        blockSensitivity f := by
  rcases min_choice (certificateComplexityFor f false) (certificateComplexityFor f true) with h | h
  all_goals
    rw [h]
    exact complexity_le_certificateComplexityFor_mul_blockSensitivity f _

/-- `D(f) ≤ bs_{¬b}(f) s_{¬b}(f) bs_b(f)`, from `D(f) ≤ bs_{¬b}(f) C_b(f)` and the one-sided Nisan
bound. In particular `D(f) ≤ bs₀(f) bs₁(f) s(f)`. -/
theorem complexity_le_blockSensitivityFor_mul_sensitivityFor_mul_blockSensitivityFor
    (f : BooleanFunction n) (b : Bool) :
    complexity f ≤ blockSensitivityFor f (!b) * sensitivityFor f (!b) * blockSensitivityFor f b :=
  (complexity_le_blockSensitivityFor_not_mul_certificateComplexityFor f b).trans
    ((Nat.mul_le_mul_left _
      (certificateComplexityFor_le_sensitivityFor_mul_blockSensitivityFor f b)).trans_eq
      (Nat.mul_assoc _ _ _).symm)

end DecisionTree

end Cslib
