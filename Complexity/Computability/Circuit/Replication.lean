/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.SourceComplexity
public import Complexity.Computability.Circuit.Pi
import Complexity.Computability.Circuit.Simulation
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Independent copies of a circuit

Inputs and outputs are arranged in consecutive blocks. Replication preserves sharing between
the outputs of each copy, and multiplies both gate count and arbitrary weighted cost exactly.
Keeping a positive initial batch requires only input and output wiring. The resulting minimum
cost is monotone even at zero copies, where a separate empty circuit suffices.

## Main definitions

* `Cslib.Circuits.directProduct`: independent copies of a scalar function.
* `Cslib.Circuits.Circuit.replicate`: independent copies of a multi-output circuit.
* `Cslib.Circuits.Circuit.replicateScalar`: the single-output specialization.
* `Cslib.Circuits.Circuit.takeDirectProductPrefix`: retain a positive initial batch.

## Main results

* `Cslib.Circuits.Circuit.eval_replicate`,
  `Cslib.Circuits.Circuit.cost_program_replicate`: exact replication semantics and cost.
* `Cslib.Circuits.ecomplexityFrom_directProduct_le`: the naive replication upper bound.
* `Cslib.Circuits.ecomplexityFrom_directProduct_mono`: monotonicity in the number of copies.
* `Cslib.Circuits.ecomplexityFrom_directProduct_comp_wiring_le`: blockwise input rewiring.

## References

* Adapted from `MassProduction/DirectProduct.lean` and `MassProduction/InputSplit.lean` in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.Circuits

universe v u
variable {σ : Signature.{v}} {U : Type u} {n m k : ℕ}

/-- Select one consecutive block of inputs. -/
def directProductInput (x : Fin (k * n) → U) (j : Fin k) : Fin n → U :=
  fun i => x (finProdFinEquiv (j, i))

/-- Apply a multi-output function independently to each input block. -/
def blockMap (f : (Fin n → U) → Fin m → U) (k : ℕ) :
    (Fin (k * n) → U) → Fin (k * m) → U :=
  fun x i => f (directProductInput x (finProdFinEquiv.symm i).1) (finProdFinEquiv.symm i).2

/-- Apply a scalar function independently to each input block. -/
def directProduct (f : (Fin n → U) → U) (k : ℕ) : (Fin (k * n) → U) → Fin k → U :=
  fun x j => f (directProductInput x j)

@[simp] theorem blockMap_apply (f : (Fin n → U) → Fin m → U)
    (x : Fin (k * n) → U) (j : Fin k) (i : Fin m) :
    blockMap f k x (finProdFinEquiv (j, i)) = f (directProductInput x j) i := by
  simp [blockMap]

namespace Circuit

/-- Disjoint-input copies of a circuit, preserving sharing within each copy. -/
def replicate (c : Circuit σ n m) : (k : ℕ) → Circuit σ (k * n) (k * m)
  | 0 => Circuit.wiring σ (Fin.elim0 ∘ Fin.cast (Nat.zero_mul m))
  | k + 1 =>
    (Circuit.wiring σ (Fin.cast (Nat.succ_mul k m))).comp
      (((replicate c k).comp (Circuit.wiring σ
        (Fin.cast (Nat.succ_mul k n).symm ∘ Fin.castAdd n))).append
        (c.comp (Circuit.wiring σ (Fin.cast (Nat.succ_mul k n).symm ∘ Fin.natAdd (k * n)))))

/-- Each output of each copy reads exactly its own input block. -/
theorem eval_replicate_apply (c : Circuit σ n m) (k : ℕ) (I : Interpretation σ U)
    (x : Fin (k * n) → U) (j : Fin k) (i : Fin m) :
    (c.replicate k).eval I x (finProdFinEquiv (j, i)) =
      c.eval I (directProductInput x j) i := by
  induction k with
  | zero => exact j.elim0
  | succ k ih =>
    simp only [replicate, eval_comp, eval_wiring, Function.comp_apply, eval_append]
    by_cases hj : j.val < k
    · let j' : Fin k := ⟨j.val, hj⟩
      rw [show Fin.cast (Nat.succ_mul k m) (finProdFinEquiv (j, i)) =
        Fin.castAdd m (finProdFinEquiv (j', i)) by
          apply Fin.ext
          simp [finProdFinEquiv, j']]
      rw [Fin.append_left, ih]
      rfl
    · have hj' : j.val = k := by lia
      rw [show Fin.cast (Nat.succ_mul k m) (finProdFinEquiv (j, i)) =
        Fin.natAdd (k * m) i by
          apply Fin.ext
          simp [finProdFinEquiv, hj', Nat.mul_comm, Nat.add_comm]]
      rw [Fin.append_right]
      congr 1
      funext a
      apply congrArg x
      apply Fin.ext
      simp [finProdFinEquiv, hj', Nat.mul_comm, Nat.add_comm]

/-- Replication computes the blockwise application of the original circuit. -/
@[simp] theorem eval_replicate (c : Circuit σ n m) (k : ℕ) (I : Interpretation σ U)
    (x : Fin (k * n) → U) :
    (c.replicate k).eval I x = blockMap (c.eval I) k x := by
  funext i
  obtain ⟨⟨j, i⟩, rfl⟩ := finProdFinEquiv.surjective i
  exact (c.eval_replicate_apply k I x j i).trans (blockMap_apply _ _ _ _).symm

/-- Replication multiplies arbitrary weighted cost exactly. -/
theorem cost_program_replicate (c : Circuit σ n m) (k : ℕ) (cost : σ.Op → ℕ) :
    (c.replicate k).program.cost cost = k * c.program.cost cost := by
  induction k with
  | zero => simp only [replicate, cost_program_wiring, Nat.zero_mul]
  | succ k ih =>
    simp only [replicate, cost_program_comp, cost_program_append, cost_program_wiring,
      Nat.zero_add, Nat.add_zero, ih, Nat.succ_mul]

/-- Replication multiplies the gate count exactly. -/
@[simp] theorem size_replicate (c : Circuit σ n m) (k : ℕ) :
    (c.replicate k).size = k * c.size := by
  simpa only [Program.cost_const, one_mul] using c.cost_program_replicate k (fun _ => 1)

/-- Single-output copies, with one output per input block. -/
def replicateScalar (c : Circuit σ n 1) (k : ℕ) : Circuit σ (k * n) k :=
  pi fun j => c.comp (Circuit.wiring σ fun i => finProdFinEquiv (j, i))

@[simp] theorem eval_replicateScalar (c : Circuit σ n 1) (k : ℕ) (I : Interpretation σ U)
    (x : Fin (k * n) → U) :
    (c.replicateScalar k).eval I x = directProduct (fun y => c.eval I y 0) k x := by
  simp only [replicateScalar, eval_pi, eval_comp, eval_wiring]
  rfl

/-- Scalar replication also preserves the exact weighted cost. -/
theorem cost_program_replicateScalar (c : Circuit σ n 1) (k : ℕ) (cost : σ.Op → ℕ) :
    (c.replicateScalar k).program.cost cost = k * c.program.cost cost := by
  simp only [replicateScalar, cost_program_pi, cost_program_comp, cost_program_wiring,
    Nat.zero_add, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

@[simp] theorem size_replicateScalar (c : Circuit σ n 1) (k : ℕ) :
    (c.replicateScalar k).size = k * c.size := by
  simpa only [Program.cost_const, one_mul] using c.cost_program_replicateScalar k (fun _ => 1)

/-- A scalar computation gives a concrete circuit for every finite direct product. -/
theorem Computes.replicateScalar {c : Circuit σ n 1} {I : Interpretation σ U}
    {f : (Fin n → U) → U} (hc : c.Computes I (single f)) (k : ℕ) :
    (c.replicateScalar k).Computes I (directProduct f k) := fun x => by
  rw [eval_replicateScalar]
  funext j
  exact congrFun (hc (directProductInput x j)) 0

/-- Retain a positive initial batch by rewiring inputs and selecting outputs, without adding
or removing gates. Discarded input blocks read the first retained block. -/
def takeDirectProductPrefix {large : ℕ} (c : Circuit σ (large * n) large) (small : ℕ)
    (hsmall : 0 < small) (hle : small ≤ large) : Circuit σ (small * n) small :=
  (Circuit.wiring σ (Fin.castLE hle)).comp (c.comp (Circuit.wiring σ fun i =>
    let ji := finProdFinEquiv.symm i
    finProdFinEquiv ((if h : ji.1.val < small then ⟨ji.1.val, h⟩ else ⟨0, hsmall⟩), ji.2)))

/-- Retaining a positive initial batch keeps the exact weighted cost. -/
theorem cost_program_takeDirectProductPrefix {small large : ℕ}
    (c : Circuit σ (large * n) large) (hsmall : 0 < small) (hle : small ≤ large)
    (cost : σ.Op → ℕ) :
    (c.takeDirectProductPrefix small hsmall hle).program.cost cost = c.program.cost cost := by
  simp only [takeDirectProductPrefix, cost_program_comp, cost_program_wiring,
    Nat.zero_add, Nat.add_zero]

/-- Retaining an initial batch preserves direct-product semantics. -/
theorem Computes.takeDirectProductPrefix {small large : ℕ} {c : Circuit σ (large * n) large}
    {I : Interpretation σ U} {f : (Fin n → U) → U}
    (hc : c.Computes I (directProduct f large)) (hsmall : 0 < small) (hle : small ≤ large) :
    (c.takeDirectProductPrefix small hsmall hle).Computes I (directProduct f small) := by
  intro x
  simp only [Circuit.takeDirectProductPrefix, eval_comp, eval_wiring]
  rw [hc]
  funext j
  apply congrArg f
  funext i
  simp only [directProductInput, Function.comp_apply, Equiv.symm_apply_apply]
  simp

end Circuit

variable {I : Interpretation σ U} {cost : σ.Op → ℕ} {f : (Fin n → U) → U}

/-- Zero copies have zero weighted complexity, even for a function with no circuit. -/
@[simp] theorem ecomplexityFrom_directProduct_zero :
    ecomplexityFrom I cost (directProduct f 0) id = 0 := by
  apply nonpos_iff_eq_zero.mp
  exact ecomplexityFrom_le_of_computesFrom
    (Circuit.wiring σ (Fin.elim0 : Fin 0 → Fin (0 * n))) (fun _ => funext fun i => i.elim0)

/-- Independently replicating a scalar implementation gives the naive weighted upper bound.
The statement includes zero copies and functions of infinite complexity. -/
theorem ecomplexityFrom_directProduct_le (k : ℕ) :
    ecomplexityFrom I cost (directProduct f k) id ≤
      (k : ℕ∞) * ecomplexityFrom I cost (single f) id := by
  rcases k.eq_zero_or_pos with rfl | hk
  · simp
  by_cases h : ecomplexityFrom I cost (single f) id = ⊤
  · simp [h, hk.ne']
  obtain ⟨c, hc, hcost⟩ := exists_computesFrom_cost_eq_ecomplexityFrom
    (ecomplexityFrom_ne_top_iff.mp h)
  exact (ecomplexityFrom_le_of_computesFrom _ (Circuit.Computes.replicateScalar hc k)).trans_eq
    (by rw [Circuit.cost_program_replicateScalar, Nat.cast_mul, hcost])

/-- Minimum weighted direct-product complexity is monotone in the number of copies. -/
theorem ecomplexityFrom_directProduct_mono {small large : ℕ} (hle : small ≤ large) :
    ecomplexityFrom I cost (directProduct f small) id ≤
      ecomplexityFrom I cost (directProduct f large) id := by
  rcases small.eq_zero_or_pos with rfl | hsmall
  · simp
  refine le_ecomplexityFrom_iff.mpr fun c hc => ?_
  exact (ecomplexityFrom_le_of_computesFrom _
    (Circuit.Computes.takeDirectProductPrefix hc hsmall hle)).trans_eq
    (by rw [Circuit.cost_program_takeDirectProductPrefix])

/-- Applying the same input wiring independently in every block adds no weighted cost. -/
theorem ecomplexityFrom_directProduct_comp_wiring_le {p : ℕ} (select : Fin n → Fin p) (k : ℕ) :
    ecomplexityFrom I cost (directProduct (fun x => f (x ∘ select)) k) id ≤
      ecomplexityFrom I cost (directProduct f k) id := by
  refine le_ecomplexityFrom_iff.mpr fun c hc => ?_
  change c.Computes I (directProduct f k) at hc
  let wiring := Circuit.wiring σ fun i : Fin (k * n) =>
    finProdFinEquiv ((finProdFinEquiv.symm i).1, select (finProdFinEquiv.symm i).2)
  have h : (c.comp wiring).ComputesFrom I (directProduct (fun x => f (x ∘ select)) k) id := by
    intro x
    rw [Circuit.eval_comp, hc]
    funext j
    apply congrArg f
    funext i
    simp only [directProductInput, wiring, Circuit.eval_wiring, Function.comp_apply,
      Equiv.symm_apply_apply, id_eq]
  exact (ecomplexityFrom_le_of_computesFrom _ h).trans_eq
    (by rw [Circuit.cost_program_comp, Circuit.cost_program_wiring, Nat.zero_add])

end Cslib.Circuits
