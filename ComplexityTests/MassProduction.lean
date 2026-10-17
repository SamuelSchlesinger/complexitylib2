/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.MassProduction.Padding
import Complexity.Computability.Circuit.Simulation

/-!
# Circuit replication and mass-production contracts

These clients distinguish shared outputs from duplicated gates, weighted cost from gate count,
zero copies from unrepresentable positive batches, and exact-cost retention from optimization.
They also check row-major evaluation, input rewiring, padding and the rational copy budget.
-/

namespace ComplexityTests.MassProduction

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.MassProduction

private def sharedNot : Circuit signature 1 2 :=
  ⟨.gate .empty ⟨.not, fun _ => .input 0⟩, fun _ => .gate 0⟩

-- Both outputs of each copy share one NOT gate. Replication must not duplicate that gate.
example : (sharedNot.replicate 3).size = 3 := by simp [sharedNot]

example : (sharedNot.replicate 3).program.cost nonconstantCost = 3 := by
  rw [Circuit.cost_program_replicate]
  rfl

example : (sharedNot.replicate 3).program.cost (fun _ => 7) = 21 := by
  rw [Circuit.cost_program_replicate]
  rfl

example : (sharedNot.replicate 3).eval interpretation ![false, true, false] =
    ![true, true, false, false, true, true] := by decide

-- No gates survive zero replication, independently of the original output width.
example {σ : Signature} {n m : ℕ} (c : Circuit σ n m) (cost : σ.Op → ℕ) :
    (c.replicate 0).size = 0 ∧ (c.replicate 0).program.cost cost = 0 := by
  simp only [Circuit.size_replicate, Circuit.cost_program_replicate, Nat.zero_mul, and_self]

-- A circuit with no outputs may still have gates; replication retains their exact cost.
private def unusedNot : Circuit signature 1 0 :=
  ⟨.gate .empty ⟨.not, fun _ => .input 0⟩, Fin.elim0⟩

example : (unusedNot.replicate 4).size = 4 := by simp [unusedNot]

example : (unusedNot.replicate 4).program.cost nonconstantCost = 4 := by
  rw [Circuit.cost_program_replicate]
  rfl

-- Constant gates exist without inputs. They count towards size but not nonconstant cost.
private def constantTrue : Circuit signature 0 1 :=
  Circuit.oneGate (.const true) Fin.elim0

example : (constantTrue.replicateScalar 4).size = 4 ∧
    (constantTrue.replicateScalar 4).program.cost nonconstantCost = 0 := by
  constructor
  · simp [constantTrue]
  · rw [Circuit.cost_program_replicateScalar]
    rfl

example (k : ℕ) : massComplexity (fun _ : Fin 0 → Bool => true) k = 0 := by
  apply nonpos_iff_eq_zero.mp
  apply massComplexity_le_iff.mpr
  refine ⟨constantTrue.replicateScalar k, Circuit.Computes.replicateScalar (fun _ => rfl) k, ?_⟩
  rw [Circuit.cost_program_replicateScalar]
  simp only [constantTrue, Circuit.cost_program_oneGate, nonconstantCost_const, Nat.mul_zero,
    le_refl]

private def scalarNot : Circuit signature 1 1 := Circuit.oneGate .not (fun _ => 0)

-- Retaining one output of a three-copy circuit keeps all three gates, including unused ones.
example : ((scalarNot.replicateScalar 3).takeDirectProductPrefix 1 (by decide) (by decide)).size =
    3 := rfl

example : ((scalarNot.replicateScalar 3).takeDirectProductPrefix 1 (by decide)
    (by decide)).program.cost nonconstantCost = 3 := by
  rw [Circuit.cost_program_takeDirectProductPrefix, Circuit.cost_program_replicateScalar]
  rfl

example : ((scalarNot.replicateScalar 3).takeDirectProductPrefix 1 (by decide)
    (by decide)).Computes interpretation (directProduct (fun x : Fin 1 → Bool => !x 0) 1) :=
  (Circuit.Computes.replicateScalar (c := scalarNot) (fun _ => rfl) 3).takeDirectProductPrefix
    (by decide) (by decide)

private abbrev noOps : Signature where
  Op := Empty
  Arity := Empty.elim

private def noOpsI : Interpretation noOps Unit := fun op => op.elim

-- One zero-input output cannot be built over a signature without operations.
example : ecomplexityFrom noOpsI Empty.elim
    (directProduct (fun _ : Fin 0 → Unit => ()) 1) id = ⊤ := by
  rw [ecomplexityFrom_eq_top_iff]
  rintro ⟨⟨p, outputs⟩, _⟩
  cases p with
  | empty => cases outputs 0 with
    | input i => exact i.elim0
    | gate i => exact i.elim0
  | gate p line => exact line.op.elim

-- Zero copies of that same function still have zero cost: the 0 * top case is included.
example : ecomplexityFrom noOpsI Empty.elim
    (directProduct (fun _ : Fin 0 → Unit => ()) 0) id = 0 :=
  ecomplexityFrom_directProduct_zero

example : ecomplexityFrom noOpsI Empty.elim
    (directProduct (fun _ : Fin 0 → Unit => ()) 0) id ≤
      (0 : ℕ∞) * ecomplexityFrom noOpsI Empty.elim (single fun _ : Fin 0 → Unit => ()) id :=
  ecomplexityFrom_directProduct_le 0

-- Repeated input selections, not just permutations, are free in each block.
example (f : (Fin 3 → Bool) → Bool) (k : ℕ) :
    massComplexity (fun x : Fin 2 → Bool => f (x ∘ ![1, 0, 1])) k ≤ massComplexity f k :=
  massComplexity_comp_wiring_le _ k

-- Adding ignored tail coordinates keeps exactly the same minimum cost.
example (k : ℕ) : massComplexity (fun x : Fin 5 → Bool => !x 0) k =
    massComplexity (fun x : Fin 1 → Bool => !x 0) k :=
  massComplexity_comp_castLE (n := 1) (p := 5) (by decide) (by decide) (fun x => !x 0) k

example (f : (Fin 2 → Bool) → Bool) :
    ∃ c : Circuit signature 6 3, c.Computes interpretation (directProduct f 3) ∧
      (c.program.cost nonconstantCost : ℕ∞) = massComplexity f 3 :=
  exists_computes_cost_eq_massComplexity (f := f) (k := 3)

-- Natural division rounds the exponent down; zero exponents still allow one copy.
example : rationalCopyBudget 1 2 5 = 4 ∧ rationalCopyBudget 0 7 5 = 1 := by decide

-- Every unary Boolean function has a circuit of nonconstant cost at most one.
private def unaryImpl (f : (Fin 1 → Bool) → Bool) : Circuit signature 1 1 :=
  if f ![false] then
    if f ![true] then Circuit.oneGate (.const true) Fin.elim0
    else Circuit.oneGate .not (fun _ => 0)
  else
    if f ![true] then Circuit.wiring signature id
    else Circuit.oneGate (.const false) Fin.elim0

private theorem unaryImpl_spec (f : (Fin 1 → Bool) → Bool) :
    (unaryImpl f).Computes interpretation (single f) ∧
      (unaryImpl f).program.cost nonconstantCost ≤ 1 := by
  constructor
  · intro x
    have hx : x = ![x 0] := by
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      rfl
    rw [hx]
    funext i
    cases h0 : f ![false] <;> cases h1 : f ![true] <;> cases h : x 0 <;>
      simp [unaryImpl, h0, h1, Circuit.eval_oneGate, Cslib.Circuits.single, interpretation]
  · unfold unaryImpl
    cases f ![false] <;> cases f ![true] <;> decide

-- A concrete positive-length instance exercises the quantified bound contract.
example : MassProductionBound 0 1 1 1 := by
  intro f k hk hbound
  have hk' : k = 1 := by
    change k ≤ 1 at hbound
    lia
  subst k
  apply massComplexity_le_iff.mpr
  refine ⟨(unaryImpl f).replicateScalar 1, (unaryImpl_spec f).1.replicateScalar 1, ?_⟩
  rw [Circuit.cost_program_replicateScalar]
  have h := (unaryImpl_spec f).2
  simpa using h.trans (by decide : 1 ≤ 1 * (2 ^ 1 / 1))

-- The all-length conversion keeps the exponent and quantifies the constant before the functions.
example (h : MassProducesAt 1 3) : ∃ c, ∀ n, 0 < n →
    ∀ (f : (Fin n → Bool) → Bool) k, 0 < k → k ≤ 2 ^ (n / 3) →
      massComplexity f k ≤ (c * (2 ^ n / n) : ℕ) := by
  simpa only [MassProducesAtAllLengths, MassProductionBound, rationalCopyBudget, one_mul] using
    h.allLengths

end ComplexityTests.MassProduction
