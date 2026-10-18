/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Sort.Bitonic.Basic
public import Complexity.Computability.Circuit.Boolean.CompareSwap
public import Complexity.Computability.Circuit.Parallel
public import Complexity.Computability.Circuit.Replication
public import Complexity.Computability.Circuit.Wiring
import Complexity.Algorithms.Lean.Sort.Bitonic.Correctness
import Mathlib.Tactic.Ring

/-!
# Batcher sorting circuits

Records occupy consecutive blocks of input wires. The key selects coordinates in
lexicographic order, with coordinate zero most significant. Each comparison moves whole
records and shares its comparison flag across the record bits. Descending layers reverse
ascending pairs, including ties; the complete sorter is not stable.
At depth `d` there are `2^d` records and `d * (d + 1) * 2^d / 4` comparisons.
The circuit constructor is executable; the gate-count theorems do not certify its running time.

## Main definitions

* `Cslib.Circuits.Boolean.bitonicLayerCircuit`: compare corresponding records in two halves.
* `Cslib.Circuits.Boolean.bitonicMergeCircuit`: merge a bitonic record array.
* `Cslib.Circuits.Boolean.bitonicSortCircuit`: sort a power-of-two record array.

## Main results

* `Cslib.Circuits.Boolean.eval_bitonicSortCircuit`: agreement with the generic algorithm.
* `Cslib.Circuits.Boolean.monotone_bitonicSortCircuit` and
  `Cslib.Circuits.Boolean.antitone_bitonicSortCircuit`: key sortedness in both directions.
* `Cslib.Circuits.Boolean.bitonicSortCircuit_perm`: preservation of complete records.
* `Cslib.Circuits.Boolean.four_mul_cost_program_bitonicSortCircuit`: exact weighted gate cost.

## References

* [K. E. Batcher, *Sorting Networks and Their Applications*][Batcher1968].
* Adapted from `MassProduction/SortingNetwork.lean` and `MassProduction/SortingCorrectness.lean` in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

/-- Compare corresponding records in two halves using independent copies of compare-exchange. -/
def bitonicLayerCircuit {k r : ℕ} (key : Fin k → Fin r) (n : ℕ) (ascending : Bool) :
    Circuit signature ((n + n) * r) ((n + n) * r) :=
  (Circuit.wiring signature (scatter n r)).comp
    (((pair key ascending).replicate n).comp (Circuit.wiring signature (gather n r)))
where
  /-- Compare-exchange in the requested direction; descending order reverses the pair. -/
  pair {k r : ℕ} (key : Fin k → Fin r) (ascending : Bool) :
      Circuit signature (r + r) (r + r) :=
    if ascending then compareSwapCircuit key else
      (Circuit.wiring signature (compareSwapCircuit.swapInput r)).comp (compareSwapCircuit key)
  /-- Read a comparison's two records from the two halves. -/
  pairInput {n r : ℕ} (j : Fin n) : Fin (r + r) → Fin ((n + n) * r) :=
    Fin.addCases (fun b => finProdFinEquiv (Fin.castAdd n j, b))
      (fun b => finProdFinEquiv (Fin.natAdd n j, b))
  /-- Gather corresponding records into adjacent pairs. -/
  gather (n r : ℕ) : Fin (n * (r + r)) → Fin ((n + n) * r) :=
    fun i => pairInput (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  /-- Scatter the compared pairs back into the two record halves. -/
  scatter (n r : ℕ) : Fin ((n + n) * r) → Fin (n * (r + r)) :=
    fun i =>
      let jb := finProdFinEquiv.symm i
      Fin.addCases (fun j => finProdFinEquiv (j, Fin.castAdd r jb.2))
        (fun j => finProdFinEquiv (j, Fin.natAdd r jb.2)) jb.1

open bitonicLayerCircuit

open Classical in
private theorem eval_pair {k r : ℕ} (key : Fin k → Fin r) (ascending : Bool)
    (x y : BitString r) :
    (pair key ascending).eval interpretation (Fin.append x y) =
      let swap := if ascending then toLex (y ∘ key) < toLex (x ∘ key)
        else ¬toLex (y ∘ key) < toLex (x ∘ key)
      Fin.append (if swap then y else x) (if swap then x else y) := by
  cases ascending <;> simp only [pair, Bool.false_eq_true, ↓reduceIte, Circuit.eval_comp,
    Circuit.eval_wiring, eval_compareSwapCircuit] <;>
    split_ifs <;> funext i <;> cases i using Fin.addCases <;>
    simp_all [compareSwapCircuit.swapInput, Function.comp_def, -Fin.natAdd_eq_addNat]

/-- Gather reads corresponding records from the two halves without changing their bits. -/
theorem bitonicLayerCircuit.gather_pair {n r : ℕ} (x : BitString ((n + n) * r)) (j : Fin n) :
    directProductInput (x ∘ gather n r) j =
      Fin.append (directProductInput x (Fin.castAdd n j))
        (directProductInput x (Fin.natAdd n j)) := by
  funext b
  cases b using Fin.addCases <;>
    simp [directProductInput, gather, pairInput, -Fin.natAdd_eq_addNat]

/-- Reading complete output records agrees with the generic bitonic comparison layer. -/
theorem eval_bitonicLayerCircuit {k r : ℕ} (key : Fin k → Fin r) (n : ℕ) (ascending : Bool)
    (x : BitString ((n + n) * r)) :
    directProductInput ((bitonicLayerCircuit key n ascending).eval interpretation x) =
      BitonicSort.compareLayer (fun record : BitString r => toLex (record ∘ key)) ascending
        (directProductInput x) := by
  classical
  funext j b
  cases j using Fin.addCases <;>
    simp only [directProductInput, bitonicLayerCircuit, Circuit.eval_comp, Circuit.eval_wiring,
      Function.comp_apply, scatter, Equiv.symm_apply_apply, Fin.addCases_left,
      Fin.addCases_right, Circuit.eval_replicate_apply, gather_pair, eval_pair]
  all_goals
    simp only [BitonicSort.compareLayer, BitonicSort.compareLayer.source, Function.comp_apply,
      Fin.addCases_left, Fin.addCases_right]
    split_ifs <;>
      simp_all only [Fin.append_left, Fin.append_right, directProductInput] <;>
      contradiction

/-- Each of the `n` comparisons is charged once, including constants and negations. -/
@[simp] theorem size_bitonicLayerCircuit {k r : ℕ} (key : Fin k → Fin r) (n : ℕ)
    (ascending : Bool) :
    (bitonicLayerCircuit key n ascending).size = n * (compareSwapCircuit key).size := by
  cases ascending <;> simp [bitonicLayerCircuit, pair]

/-- Recursively merge a bitonic array of complete records. -/
def bitonicMergeCircuit {k r : ℕ} (key : Fin k → Fin r) : (depth : ℕ) → Bool →
    Circuit signature (BitonicSort.arity depth * r) (BitonicSort.arity depth * r)
  | 0, _ => Circuit.id signature _
  | depth + 1, ascending =>
    (halves (n := BitonicSort.arity depth)
      (bitonicMergeCircuit key depth ascending) (bitonicMergeCircuit key depth ascending)).comp
        (bitonicLayerCircuit key (BitonicSort.arity depth) ascending)
where
  /-- Select the first half of a flat record array. -/
  firstHalf (n r : ℕ) : Fin (n * r) → Fin ((n + n) * r) :=
    fun i => finProdFinEquiv (Fin.castAdd n (finProdFinEquiv.symm i).1,
      (finProdFinEquiv.symm i).2)
  /-- Select the second half of a flat record array. -/
  secondHalf (n r : ℕ) : Fin (n * r) → Fin ((n + n) * r) :=
    fun i => finProdFinEquiv (Fin.natAdd n (finProdFinEquiv.symm i).1,
      (finProdFinEquiv.symm i).2)
  /-- Apply a circuit to each record half, transporting only the flat wire indices. -/
  halves {n r : ℕ} (left right : Circuit signature (n * r) (n * r)) :
      Circuit signature ((n + n) * r) ((n + n) * r) :=
    let rows := (finSumFinEquiv.prodCongr (Equiv.refl (Fin r))).trans finProdFinEquiv
    let blocks := (finProdFinEquiv.sumCongr finProdFinEquiv).trans finSumFinEquiv
    let distribute := Equiv.sumProdDistrib (Fin n) (Fin n) (Fin r)
    (Circuit.wiringOn signature blocks rows distribute).comp
      ((left.parallel right).comp (Circuit.wiringOn signature rows blocks distribute.symm))

open bitonicMergeCircuit

/-- The first flat input block is the first half of the record array. -/
theorem bitonicMergeCircuit.records_firstHalf {n r : ℕ} (x : BitString ((n + n) * r)) :
    directProductInput (x ∘ firstHalf n r) = directProductInput x ∘ Fin.castAdd n := by
  funext j b
  simp only [firstHalf, directProductInput, Function.comp_apply, Equiv.symm_apply_apply]

/-- The second flat input block is the second half of the record array. -/
theorem bitonicMergeCircuit.records_secondHalf {n r : ℕ} (x : BitString ((n + n) * r)) :
    directProductInput (x ∘ secondHalf n r) = directProductInput x ∘ Fin.natAdd n := by
  funext j b
  simp only [secondHalf, directProductInput, Function.comp_apply, Equiv.symm_apply_apply]

private theorem eval_halves {n r : ℕ} (left right : Circuit signature (n * r) (n * r))
    (x : BitString ((n + n) * r)) :
    directProductInput ((halves left right).eval interpretation x) =
      Fin.append (directProductInput (left.eval interpretation (x ∘ firstHalf n r)))
        (directProductInput (right.eval interpretation (x ∘ secondHalf n r))) := by
  funext j bit
  cases j using Fin.addCases <;>
    simp [halves, Circuit.eval_wiringOn, directProductInput, firstHalf, secondHalf,
      Function.comp_def, -finProdFinEquiv_symm_apply, -Fin.natAdd_eq_addNat]

/-- The native circuit realizes bitonic merge on complete records. -/
theorem eval_bitonicMergeCircuit {k r : ℕ} (key : Fin k → Fin r) (depth : ℕ)
    (ascending : Bool) (x : BitString (BitonicSort.arity depth * r)) :
    directProductInput ((bitonicMergeCircuit key depth ascending).eval interpretation x) =
      BitonicSort.merge (fun record : BitString r => toLex (record ∘ key)) depth ascending
        (directProductInput x) := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    change BitString ((BitonicSort.arity depth + BitonicSort.arity depth) * r) at x
    simp only [bitonicMergeCircuit]
    erw [Circuit.eval_comp, eval_halves]
    simp only [ih, records_firstHalf, records_secondHalf, BitonicSort.merge]
    erw [eval_bitonicLayerCircuit]
    rfl

/-- Sort the two halves in opposite directions, then merge the complete record array. -/
def bitonicSortCircuit {k r : ℕ} (key : Fin k → Fin r) : (depth : ℕ) → Bool →
    Circuit signature (BitonicSort.arity depth * r) (BitonicSort.arity depth * r)
  | 0, _ => Circuit.id signature _
  | depth + 1, ascending =>
    (bitonicMergeCircuit key (depth + 1) ascending).comp
      (halves (n := BitonicSort.arity depth)
        (bitonicSortCircuit key depth true) (bitonicSortCircuit key depth false))

/-- The native circuit realizes Batcher sorting on complete records. -/
theorem eval_bitonicSortCircuit {k r : ℕ} (key : Fin k → Fin r) (depth : ℕ)
    (ascending : Bool) (x : BitString (BitonicSort.arity depth * r)) :
    directProductInput ((bitonicSortCircuit key depth ascending).eval interpretation x) =
      BitonicSort.sort (fun record : BitString r => toLex (record ∘ key)) depth ascending
        (directProductInput x) := by
  induction depth generalizing ascending with
  | zero => rfl
  | succ depth ih =>
    change BitString ((BitonicSort.arity depth + BitonicSort.arity depth) * r) at x
    rw [bitonicSortCircuit]
    erw [Circuit.eval_comp, eval_bitonicMergeCircuit, eval_halves]
    simp only [ih, records_firstHalf, records_secondHalf, BitonicSort.sort]
    rfl

/-- The output keys of ascending sorting are nondecreasing. -/
theorem monotone_bitonicSortCircuit {k r : ℕ} (key : Fin k → Fin r) (depth : ℕ)
    (x : BitString (BitonicSort.arity depth * r)) :
    Monotone (fun j => toLex (directProductInput
      ((bitonicSortCircuit key depth true).eval interpretation x) j ∘ key)) := by
  rw [eval_bitonicSortCircuit]
  exact BitonicSort.monotone_sort (fun record : BitString r => toLex (record ∘ key)) depth _

/-- The output keys of descending sorting are nonincreasing. -/
theorem antitone_bitonicSortCircuit {k r : ℕ} (key : Fin k → Fin r) (depth : ℕ)
    (x : BitString (BitonicSort.arity depth * r)) :
    Antitone (fun j => toLex (directProductInput
      ((bitonicSortCircuit key depth false).eval interpretation x) j ∘ key)) := by
  rw [eval_bitonicSortCircuit]
  exact BitonicSort.antitone_sort (fun record : BitString r => toLex (record ∘ key)) depth _

/-- Sorting preserves the multiset of complete input records, including payload and duplicates. -/
theorem bitonicSortCircuit_perm {k r : ℕ} (key : Fin k → Fin r) (depth : ℕ)
    (ascending : Bool) (x : BitString (BitonicSort.arity depth * r)) :
    (List.ofFn (directProductInput
      ((bitonicSortCircuit key depth ascending).eval interpretation x))).Perm
        (List.ofFn (directProductInput x)) := by
  rw [eval_bitonicSortCircuit]
  exact BitonicSort.sort_perm _ _ _ _

private theorem cost_pair {k r : ℕ} (key : Fin k → Fin r) (ascending : Bool)
    (cost : signature.Op → ℕ) :
    (pair key ascending).program.cost cost = (compareSwapCircuit key).program.cost cost := by
  cases ascending with
  | false =>
    change ((Circuit.wiring signature (compareSwapCircuit.swapInput r)).comp
      (compareSwapCircuit key)).program.cost cost = _
    rw [Circuit.cost_program_comp, Circuit.cost_program_wiring, Nat.add_zero]
  | true => rfl

/-- A layer uses `n` copies of the comparator under any assignment of gate costs. -/
theorem cost_program_bitonicLayerCircuit {k r : ℕ} (key : Fin k → Fin r) (n : ℕ)
    (ascending : Bool) (cost : signature.Op → ℕ) :
    (bitonicLayerCircuit key n ascending).program.cost cost =
      n * (compareSwapCircuit key).program.cost cost := by
  simp only [bitonicLayerCircuit, Circuit.cost_program_comp, Circuit.cost_program_wiring,
    Circuit.cost_program_replicate, cost_pair, Nat.zero_add, Nat.add_zero]

private theorem cost_halves {n r : ℕ} (left right : Circuit signature (n * r) (n * r))
    (cost : signature.Op → ℕ) :
    (halves left right).program.cost cost = left.program.cost cost + right.program.cost cost := by
  simp only [halves, Circuit.cost_program_comp, Circuit.cost_program_wiringOn,
    Circuit.cost_program_parallel, Nat.zero_add, Nat.add_zero]

/-- Exact merge cost: `depth * 2^depth / 2` comparisons, stated without natural division. -/
theorem two_mul_cost_program_bitonicMergeCircuit {k r : ℕ} (key : Fin k → Fin r)
    (depth : ℕ) (ascending : Bool) (cost : signature.Op → ℕ) :
    2 * (bitonicMergeCircuit key depth ascending).program.cost cost =
      depth * 2 ^ depth * (compareSwapCircuit key).program.cost cost := by
  induction depth with
  | zero => simp [bitonicMergeCircuit, Circuit.id]
  | succ depth ih =>
    have hrec : (bitonicMergeCircuit key (depth + 1) ascending).program.cost cost =
        BitonicSort.arity depth * (compareSwapCircuit key).program.cost cost +
          2 * (bitonicMergeCircuit key depth ascending).program.cost cost := by
      simp only [bitonicMergeCircuit]
      erw [Circuit.cost_program_comp, cost_halves, cost_program_bitonicLayerCircuit]
      ring
    rw [hrec]
    calc
      _ = 2 * (2 * (bitonicMergeCircuit key depth ascending).program.cost cost) +
          2 * BitonicSort.arity depth * (compareSwapCircuit key).program.cost cost := by ring
      _ = 2 * (depth * 2 ^ depth * (compareSwapCircuit key).program.cost cost) +
          2 * BitonicSort.arity depth * (compareSwapCircuit key).program.cost cost := by rw [ih]
      _ = _ := by rw [BitonicSort.arity_eq_two_pow, Nat.pow_succ]; ring

/-- Exact sorting cost: `depth * (depth + 1) * 2^depth / 4` comparisons. The identity includes
depth zero, empty keys, empty records, and arbitrary gate costs. -/
theorem four_mul_cost_program_bitonicSortCircuit {k r : ℕ} (key : Fin k → Fin r)
    (depth : ℕ) (ascending : Bool) (cost : signature.Op → ℕ) :
    4 * (bitonicSortCircuit key depth ascending).program.cost cost =
      depth * (depth + 1) * 2 ^ depth * (compareSwapCircuit key).program.cost cost := by
  induction depth generalizing ascending with
  | zero => simp [bitonicSortCircuit, Circuit.id]
  | succ depth ih =>
    have hrec : (bitonicSortCircuit key (depth + 1) ascending).program.cost cost =
        (bitonicSortCircuit key depth true).program.cost cost +
          (bitonicSortCircuit key depth false).program.cost cost +
            (bitonicMergeCircuit key (depth + 1) ascending).program.cost cost := by
      rw [bitonicSortCircuit]
      erw [Circuit.cost_program_comp, cost_halves]
    rw [hrec]
    calc
      _ = 4 * (bitonicSortCircuit key depth true).program.cost cost +
          4 * (bitonicSortCircuit key depth false).program.cost cost +
            2 * (2 * (bitonicMergeCircuit key (depth + 1) ascending).program.cost cost) := by ring
      _ = depth * (depth + 1) * 2 ^ depth * (compareSwapCircuit key).program.cost cost +
          depth * (depth + 1) * 2 ^ depth * (compareSwapCircuit key).program.cost cost +
            2 * ((depth + 1) * 2 ^ (depth + 1) * (compareSwapCircuit key).program.cost cost) := by
        rw [ih, ih, two_mul_cost_program_bitonicMergeCircuit]
      _ = _ := by rw [Nat.pow_succ]; ring

/-- Exact total gate count, including constants and negations. -/
theorem four_mul_size_bitonicSortCircuit {k r : ℕ} (key : Fin k → Fin r) (depth : ℕ)
    (ascending : Bool) :
    4 * (bitonicSortCircuit key depth ascending).size =
      depth * (depth + 1) * 2 ^ depth * (if r = 0 then 0 else 6 * k + 6 * r + 2) := by
  simpa only [Program.cost_const, one_mul, size_compareSwapCircuit] using
    four_mul_cost_program_bitonicSortCircuit key depth ascending (fun _ => 1)

end Cslib.Circuits.Boolean
