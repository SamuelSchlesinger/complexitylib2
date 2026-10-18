/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Sorting
public import Complexity.Algorithms.Lean.Sort.Bitonic.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Sorting circuits with saved comparison decisions

Sort records once, retain the comparison controls, and reverse those decisions on new payloads.
The circuits use the existing CSLib circuit representation. The forward circuit computes each
comparison once and retains both its decision and complement, sharing the original negation.
Descending ties follow the existing bitonic sort. Reversal inspects only these controls, so
answer payloads may have a different width and need not contain keys or unique identifiers.

A trace has `BitonicSort.sortTraceSize d` decisions stored as twice that many control wires,
followed by `BitonicSort.arity d` consecutive records. The reverse circuit expects complementary
control pairs; arbitrary pairs are not asserted to describe a permutation.

Retaining controls adds no gates to ordinary sorting for nonempty records. At empty width the
forward circuit still computes its controls, whereas the ordinary sorter has no outputs and
uses no gates. Reversal costs six gates per answer bit and comparison. These are circuit gate
costs with free wiring, not bounds on retained storage or the circuit constructor's runtime.

## Main definitions

* `Cslib.Circuits.Boolean.bitonicSortTraceCircuit`: sort and retain comparison controls.
* `Cslib.Circuits.Boolean.bitonicUnsortCircuit`: reverse saved decisions on new payloads.
* `Cslib.Circuits.Boolean.bitonicSortTraceCircuit.pack`: controls followed by records.

## Main results

* `Cslib.Circuits.Boolean.eval_bitonicSortTraceCircuit`: exact trace and sorted-record semantics.
* `Cslib.Circuits.Boolean.eval_bitonicUnsortCircuit`: reverse arbitrary paired decisions.
* `Cslib.Circuits.Boolean.eval_bitonicUnsortCircuit_sort`: restore transformed sorted records.
  The transformation is a semantic parameter; its implementation cost is not included.
* `Cslib.Circuits.Boolean.cost_program_bitonicSortTraceCircuit_eq`: no extra sorting gates at
  nonzero record width, under arbitrary gate weights.
* `Cslib.Circuits.Boolean.size_bitonicUnsortCircuit`: exact reversal gate count.

## References

* [K. E. Batcher, *Sorting Networks and Their Applications*][Batcher1968].
* Extends the sorting backend adapted from
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

namespace bitonicSortTraceCircuit

/-- Flatten a finite array of equal-width records. -/
def flatten {n r : ℕ} (x : Fin n → BitString r) : BitString (n * r) :=
  fun i => x (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

@[simp] theorem directProductInput_flatten {n r : ℕ} (x : Fin n → BitString r) :
    directProductInput (flatten x) = x := by
  funext i b
  simp only [directProductInput, flatten, Equiv.symm_apply_apply]

/-- The controls retain both a decision and its complement. -/
def controls {t n r : ℕ} (x : BitString (t * 2 + n * r)) : Fin t → BitString 2 :=
  directProductInput (x ∘ Fin.castAdd (n * r))

/-- The payload records following the controls. -/
def records {t n r : ℕ} (x : BitString (t * 2 + n * r)) : Fin n → BitString r :=
  directProductInput (x ∘ Fin.natAdd (t * 2))

/-- Encode control pairs followed by records. -/
def pack {t n r : ℕ} (c : Fin t → BitString 2) (x : Fin n → BitString r) :
    BitString (t * 2 + n * r) :=
  Fin.append (flatten c) (flatten x)

@[simp] theorem controls_pack {t n r : ℕ} (c : Fin t → BitString 2)
    (x : Fin n → BitString r) : controls (pack c x) = c := by
  funext i b
  simp only [controls, pack, flatten, directProductInput, Function.comp_apply,
    Fin.append_left, Equiv.symm_apply_apply]

@[simp] theorem records_pack {t n r : ℕ} (c : Fin t → BitString 2)
    (x : Fin n → BitString r) : records (pack c x) = x := by
  funext i b
  simp only [records, pack, flatten, directProductInput, Function.comp_apply,
    Fin.append_right, Equiv.symm_apply_apply]

@[simp] theorem pack_comp_natAdd {t n r : ℕ} (c : Fin t → BitString 2)
    (x : Fin n → BitString r) : pack c x ∘ Fin.natAdd (t * 2) = flatten x :=
  Fin.append_comp_natAdd _ _

private theorem ext {t n r : ℕ} {x y : BitString (t * 2 + n * r)}
    (hc : controls x = controls y) (hd : records x = records y) : x = y := by
  funext i
  cases i using Fin.addCases with
  | left i =>
    obtain ⟨⟨j, b⟩, rfl⟩ := finProdFinEquiv.surjective i
    exact congrFun (congrFun hc j) b
  | right i =>
    obtain ⟨⟨j, b⟩, rfl⟩ := finProdFinEquiv.surjective i
    exact congrFun (congrFun hd j) b

/-- Collect two circuits' controls before their concatenated record outputs. -/
def collect {input a b n m r : ℕ}
    (left : Circuit signature input (a * 2 + n * r))
    (right : Circuit signature input (b * 2 + m * r)) :
    Circuit signature input ((a + b) * 2 + (n + m) * r) :=
  (Circuit.wiring signature (Fin.addCases
    (fun i =>
      let jb := finProdFinEquiv.symm i
      Fin.addCases
        (fun j => Fin.castAdd (b * 2 + m * r) (Fin.castAdd (n * r)
          (finProdFinEquiv (j, jb.2))))
        (fun j => Fin.natAdd (a * 2 + n * r) (Fin.castAdd (m * r)
          (finProdFinEquiv (j, jb.2)))) jb.1)
    (fun i =>
      let jb := finProdFinEquiv.symm i
      Fin.addCases
        (fun j => Fin.castAdd (b * 2 + m * r) (Fin.natAdd (a * 2)
          (finProdFinEquiv (j, jb.2))))
        (fun j => Fin.natAdd (a * 2 + n * r) (Fin.natAdd (b * 2)
          (finProdFinEquiv (j, jb.2)))) jb.1))).comp (left.append right)

private theorem controls_collect {input a b n m r : ℕ}
    (left : Circuit signature input (a * 2 + n * r))
    (right : Circuit signature input (b * 2 + m * r)) (x : BitString input) :
    controls ((collect left right).eval interpretation x) =
      Fin.append (controls (left.eval interpretation x))
        (controls (right.eval interpretation x)) := by
  funext j bit
  cases j using Fin.addCases <;>
    simp only [controls, collect, directProductInput, Circuit.eval_comp, Circuit.eval_wiring,
      Circuit.eval_append, Function.comp_apply, Fin.addCases_left,
      Fin.addCases_right, Fin.append_left, Fin.append_right, Equiv.symm_apply_apply]

private theorem records_collect {input a b n m r : ℕ}
    (left : Circuit signature input (a * 2 + n * r))
    (right : Circuit signature input (b * 2 + m * r)) (x : BitString input) :
    records ((collect left right).eval interpretation x) =
      Fin.append (records (left.eval interpretation x))
        (records (right.eval interpretation x)) := by
  funext j bit
  cases j using Fin.addCases <;>
    simp only [records, collect, directProductInput, Circuit.eval_comp, Circuit.eval_wiring,
      Circuit.eval_append, Function.comp_apply, Fin.addCases_left,
      Fin.addCases_right, Fin.append_left, Fin.append_right, Equiv.symm_apply_apply]

private theorem cost_collect {input a b n m r : ℕ}
    (left : Circuit signature input (a * 2 + n * r))
    (right : Circuit signature input (b * 2 + m * r)) (cost : signature.Op → ℕ) :
    (collect left right).program.cost cost = left.program.cost cost + right.program.cost cost := by
  simp only [collect, Circuit.cost_program_comp, Circuit.cost_program_append,
    Circuit.cost_program_wiring, Nat.add_zero]

/-- Preserve the first controls while executing the second circuit on its payload. -/
def chain {input a b n m r : ℕ}
    (first : Circuit signature input (a * 2 + n * r))
    (second : Circuit signature (n * r) (b * 2 + m * r)) :
    Circuit signature input ((a + b) * 2 + m * r) :=
  (Circuit.wiring signature (Fin.addCases
    (fun i =>
      let jb := finProdFinEquiv.symm i
      Fin.addCases
        (fun j => Fin.castAdd (b * 2 + m * r) (finProdFinEquiv (j, jb.2)))
        (fun j => Fin.natAdd (a * 2) (Fin.castAdd (m * r)
          (finProdFinEquiv (j, jb.2)))) jb.1)
    (Fin.natAdd (a * 2) ∘ Fin.natAdd (b * 2)))).comp
    (((Circuit.id signature (a * 2)).parallel second).comp first)

private theorem controls_chain {input a b n m r : ℕ}
    (first : Circuit signature input (a * 2 + n * r))
    (second : Circuit signature (n * r) (b * 2 + m * r)) (x : BitString input) :
    controls ((chain first second).eval interpretation x) =
      Fin.append (controls (first.eval interpretation x))
        (controls (second.eval interpretation
          (first.eval interpretation x ∘ Fin.natAdd (a * 2)))) := by
  funext j bit
  cases j using Fin.addCases <;>
    simp only [controls, chain, directProductInput, Circuit.eval_comp, Circuit.eval_wiring,
      Circuit.eval_parallel, Circuit.id, Function.comp_id, Function.comp_apply, Fin.addCases_left,
      Fin.addCases_right, Fin.append_left, Fin.append_right, Equiv.symm_apply_apply]

private theorem records_chain {input a b n m r : ℕ}
    (first : Circuit signature input (a * 2 + n * r))
    (second : Circuit signature (n * r) (b * 2 + m * r)) (x : BitString input) :
    records ((chain first second).eval interpretation x) =
      records (second.eval interpretation (first.eval interpretation x ∘ Fin.natAdd (a * 2))) := by
  funext j bit
  simp only [records, chain, directProductInput, Circuit.eval_comp, Circuit.eval_wiring,
      Circuit.eval_parallel, Circuit.id, Function.comp_id, Function.comp_apply,
      Fin.addCases_right, Fin.append_right]

private theorem cost_chain {input a b n m r : ℕ}
    (first : Circuit signature input (a * 2 + n * r))
    (second : Circuit signature (n * r) (b * 2 + m * r)) (cost : signature.Op → ℕ) :
    (chain first second).program.cost cost =
      first.program.cost cost + second.program.cost cost := by
  simp only [chain, Circuit.cost_program_comp, Circuit.cost_program_parallel, Circuit.id,
    Circuit.cost_program_wiring, Nat.zero_add, Nat.add_zero]

private theorem eval_collect {input a b n m r : ℕ}
    (left : Circuit signature input (a * 2 + n * r))
    (right : Circuit signature input (b * 2 + m * r)) (x : BitString input) :
    (collect left right).eval interpretation x =
      pack (Fin.append (controls (left.eval interpretation x))
        (controls (right.eval interpretation x)))
        (Fin.append (records (left.eval interpretation x))
          (records (right.eval interpretation x))) := by
  apply ext <;> simp only [controls_collect, records_collect, controls_pack, records_pack]

private theorem eval_chain {input a b n m r : ℕ}
    (first : Circuit signature input (a * 2 + n * r))
    (second : Circuit signature (n * r) (b * 2 + m * r))
    (x : BitString input) (c : Fin a → BitString 2) (y : Fin n → BitString r)
    (h : first.eval interpretation x = pack c y) :
    (chain first second).eval interpretation x =
      pack (Fin.append c (controls (second.eval interpretation (flatten y))))
        (records (second.eval interpretation (flatten y))) := by
  apply ext <;>
    simp only [controls_chain, records_chain, controls_pack, records_pack, h, pack_comp_natAdd]

/-- Pair each decision with its complement. -/
def pairs {n : ℕ} (flags : BitString n) : Fin n → BitString 2 :=
  fun i => ![flags i, !flags i]

theorem pairs_append {n m : ℕ} (x : BitString n) (y : BitString m) :
    pairs (Fin.append x y) = Fin.append (pairs x) (pairs y) := by
  funext i b
  cases i using Fin.addCases <;> simp only [pairs, Fin.append_left, Fin.append_right]

/-- Descending compare-exchange reverses both the payload and the two control wires. -/
def pair {r : ℕ} (flag : Circuit signature (r + r) 1) (ascending : Bool) :
    Circuit signature (r + r) (2 + (r + r)) :=
  if ascending then compareSwapCircuit.record flag else
    (Circuit.wiring signature (Fin.addCases
      (Fin.castAdd (r + r) ∘ Fin.rev)
      (Fin.natAdd 2 ∘ compareSwapCircuit.swapInput r))).comp
        (compareSwapCircuit.record flag)

private theorem eval_pair {r : ℕ} (flag : Circuit signature (r + r) 1) (ascending : Bool)
    (x y : BitString r) :
    (pair flag ascending).eval interpretation (Fin.append x y) =
      let b := if ascending then flag.eval interpretation (Fin.append x y) 0
        else !flag.eval interpretation (Fin.append x y) 0
      Fin.append ![b, !b] (if b then Fin.append y x else Fin.append x y) := by
  cases ascending <;> cases h : flag.eval interpretation (Fin.append x y) 0 <;>
    funext i
  all_goals
    cases i using Fin.addCases with
    | left i =>
      fin_cases i <;> simp [pair, compareSwapCircuit.eval_record, h]
    | right i =>
      cases i using Fin.addCases <;>
        simp [pair, compareSwapCircuit.eval_record, h, compareSwapCircuit.swapInput,
          -Fin.natAdd_eq_addNat]

private theorem cost_pair {r : ℕ} (flag : Circuit signature (r + r) 1) (ascending : Bool)
    (cost : signature.Op → ℕ) :
    (pair flag ascending).program.cost cost =
      (compareSwapCircuit.record flag).program.cost cost := by
  cases ascending with
  | true => rfl
  | false =>
    unfold pair
    erw [Circuit.cost_program_comp, Circuit.cost_program_wiring, Nat.add_zero]

/-- Compare a layer and retain all of its controls before the payload. -/
def layer {k r : ℕ} (key : Fin k → Fin r) (n : ℕ) (ascending : Bool) :
    Circuit signature ((n + n) * r) (n * 2 + (n + n) * r) :=
  let comparator := pair
    (Formula.lexLt (Fin.natAdd r ∘ key) (Fin.castAdd r ∘ key)).toCircuit ascending
  (Circuit.wiring signature (Fin.addCases
    (fun i =>
      let jb := finProdFinEquiv.symm i
      finProdFinEquiv (jb.1, Fin.castAdd (r + r) jb.2))
    (fun i =>
      let jb := finProdFinEquiv.symm i
      Fin.addCases
        (fun j => finProdFinEquiv (j, Fin.natAdd 2 (Fin.castAdd r jb.2)))
        (fun j => finProdFinEquiv (j, Fin.natAdd 2 (Fin.natAdd r jb.2))) jb.1))).comp
    ((comparator.replicate n).comp (Circuit.wiring signature (bitonicLayerCircuit.gather n r)))

open Classical in
private theorem flag_eq_decide {k r : ℕ} (key : Fin k → Fin r) (x y : BitString r) :
    (Formula.lexLt (Fin.natAdd r ∘ key) (Fin.castAdd r ∘ key)).toCircuit.eval interpretation
      (Fin.append x y) 0 = decide (toLex (y ∘ key) < toLex (x ∘ key)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Formula.eval_toCircuit, Formula.eval_lexLt_iff, Function.comp_def,
    Fin.append_left, Fin.append_right, decide_eq_true_eq]

private theorem eval_layer {k r : ℕ} (key : Fin k → Fin r) (n : ℕ) (ascending : Bool)
    (x : BitString ((n + n) * r)) :
    (layer key n ascending).eval interpretation x =
      pack (pairs (BitonicSort.layerFlags (fun row : BitString r => toLex (row ∘ key))
        ascending (directProductInput x)))
        (BitonicSort.compareLayer (fun row : BitString r => toLex (row ∘ key))
          ascending (directProductInput x)) := by
  classical
  apply ext
  · rw [controls_pack]
    funext j bit
    simp only [controls, layer, directProductInput, Circuit.eval_comp,
      Circuit.eval_wiring, Function.comp_apply, Fin.addCases_left,
      Equiv.symm_apply_apply, Circuit.eval_replicate_apply, bitonicLayerCircuit.gather_pair,
      eval_pair, Fin.append_left, flag_eq_decide, pairs, BitonicSort.layerFlags]
    cases ascending <;>
      simp only [Bool.false_eq_true, ↓reduceIte, decide_not, Bool.not_not] <;>
      congr 2 <;> first
      | exact Bool.decide_congr Iff.rfl
      | exact congrArg Bool.not (Bool.decide_congr Iff.rfl)
  · rw [records_pack]
    funext j bit
    cases j using Fin.addCases <;>
      simp only [records, layer, directProductInput, Circuit.eval_comp,
        Circuit.eval_wiring, Function.comp_apply, Fin.addCases_right, Fin.addCases_left,
        Equiv.symm_apply_apply, Circuit.eval_replicate_apply, bitonicLayerCircuit.gather_pair,
        eval_pair, Fin.append_right, flag_eq_decide, BitonicSort.compareLayer,
        BitonicSort.compareLayer.source]
    all_goals
      cases ascending <;>
        simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq,
          Bool.not_eq_true', decide_eq_false_iff_not] <;>
        split_ifs <;>
        simp_all only [Fin.append_left, Fin.append_right, directProductInput] <;>
        contradiction

private theorem cost_layer {k r : ℕ} (key : Fin k → Fin r) (n : ℕ) (ascending : Bool)
    (cost : signature.Op → ℕ) :
    (layer key n ascending).program.cost cost = n *
      (compareSwapCircuit.record
        (Formula.lexLt (Fin.natAdd r ∘ key) (Fin.castAdd r ∘ key)).toCircuit).program.cost
          cost := by
  simp only [layer, Circuit.cost_program_comp, Circuit.cost_program_wiring,
    Circuit.cost_program_replicate, cost_pair, Nat.zero_add, Nat.add_zero]

/-- Run one traced circuit on each half of a record array. -/
def halves {a b n r : ℕ} (left : Circuit signature (n * r) (a * 2 + n * r))
    (right : Circuit signature (n * r) (b * 2 + n * r)) :
    Circuit signature ((n + n) * r) ((a + b) * 2 + (n + n) * r) :=
  collect (left.comp (Circuit.wiring signature (bitonicMergeCircuit.firstHalf n r)))
    (right.comp (Circuit.wiring signature (bitonicMergeCircuit.secondHalf n r)))

private theorem eval_halves {a b n r : ℕ} (left : Circuit signature (n * r) (a * 2 + n * r))
    (right : Circuit signature (n * r) (b * 2 + n * r)) (x : BitString ((n + n) * r)) :
    (halves left right).eval interpretation x =
      pack (Fin.append
        (controls (left.eval interpretation (x ∘ bitonicMergeCircuit.firstHalf n r)))
        (controls (right.eval interpretation (x ∘ bitonicMergeCircuit.secondHalf n r))))
        (Fin.append
          (records (left.eval interpretation (x ∘ bitonicMergeCircuit.firstHalf n r)))
          (records (right.eval interpretation (x ∘ bitonicMergeCircuit.secondHalf n r)))) := by
  simp only [halves, eval_collect, Circuit.eval_comp, Circuit.eval_wiring]

private theorem cost_halves {a b n r : ℕ} (left : Circuit signature (n * r) (a * 2 + n * r))
    (right : Circuit signature (n * r) (b * 2 + n * r)) (cost : signature.Op → ℕ) :
    (halves left right).program.cost cost = left.program.cost cost + right.program.cost cost := by
  simp only [halves, cost_collect, Circuit.cost_program_comp, Circuit.cost_program_wiring,
    Nat.zero_add]

end bitonicSortTraceCircuit

open bitonicSortTraceCircuit
open BitonicSort (arity mergeTraceSize sortTraceSize)


/-- Bitonic merge, retaining comparison decisions before the merged records. -/
def bitonicMergeTraceCircuit {k r : ℕ} (key : Fin k → Fin r) : (d : ℕ) → Bool →
    Circuit signature (arity d * r) (mergeTraceSize d * 2 + arity d * r)
  | 0, _ => Circuit.wiring signature (Fin.addCases Fin.elim0 id)
  | d + 1, ascending =>
    chain (layer key (arity d) ascending)
      (halves (bitonicMergeTraceCircuit key d ascending) (bitonicMergeTraceCircuit key d ascending))

/-- Bitonic sorting, retaining comparison decisions before the sorted records. -/
def bitonicSortTraceCircuit {k r : ℕ} (key : Fin k → Fin r) : (d : ℕ) → Bool →
    Circuit signature (arity d * r) (sortTraceSize d * 2 + arity d * r)
  | 0, _ => Circuit.wiring signature (Fin.addCases Fin.elim0 id)
  | d + 1, ascending =>
    chain (halves (bitonicSortTraceCircuit key d true) (bitonicSortTraceCircuit key d false))
      (bitonicMergeTraceCircuit key (d + 1) ascending)

/-- The forward merge exposes exactly the semantic trace and merged records. -/
theorem eval_bitonicMergeTraceCircuit {k r : ℕ} (key : Fin k → Fin r) (d : ℕ)
    (ascending : Bool) (x : BitString (arity d * r)) :
    (bitonicMergeTraceCircuit key d ascending).eval interpretation x =
      pack (pairs (BitonicSort.mergeTrace (fun row : BitString r => toLex (row ∘ key))
        d ascending (directProductInput x)))
        (BitonicSort.merge (fun row : BitString r => toLex (row ∘ key))
          d ascending (directProductInput x)) := by
  induction d with
  | zero =>
    dsimp only [bitonicMergeTraceCircuit, mergeTraceSize, BitonicSort.merge, BitonicSort.mergeTrace]
    funext i
    cases i using Fin.addCases with
    | left i => exact Fin.elim0 i
    | right i =>
      simp only [Circuit.eval_wiring, Function.comp_apply, Fin.addCases_right,
        pack, Fin.append_right, flatten, directProductInput, Prod.mk.eta,
        Equiv.apply_symm_apply, id_eq]
  | succ d ih =>
    dsimp only [arity] at x
    simp only [bitonicMergeTraceCircuit, mergeTraceSize, arity,
      BitonicSort.mergeTrace, BitonicSort.merge]
    erw [eval_chain _ _ _ _ _ (eval_layer key (arity d) ascending x), eval_halves]
    simp only [ih, controls_pack, records_pack, bitonicMergeCircuit.records_firstHalf,
      bitonicMergeCircuit.records_secondHalf, directProductInput_flatten, pairs_append]

/-- The forward sorter exposes exactly the semantic trace and sorted records. -/
theorem eval_bitonicSortTraceCircuit {k r : ℕ} (key : Fin k → Fin r) (d : ℕ)
    (ascending : Bool) (x : BitString (arity d * r)) :
    (bitonicSortTraceCircuit key d ascending).eval interpretation x =
      pack (pairs (BitonicSort.sortTrace (fun row : BitString r => toLex (row ∘ key))
        d ascending (directProductInput x)))
        (BitonicSort.sort (fun row : BitString r => toLex (row ∘ key))
          d ascending (directProductInput x)) := by
  induction d generalizing ascending with
  | zero =>
    dsimp only [bitonicSortTraceCircuit, sortTraceSize, BitonicSort.sort, BitonicSort.sortTrace]
    funext i
    cases i using Fin.addCases with
    | left i => exact Fin.elim0 i
    | right i =>
      simp only [Circuit.eval_wiring, Function.comp_apply, Fin.addCases_right,
        pack, Fin.append_right, flatten, directProductInput, Prod.mk.eta,
        Equiv.apply_symm_apply, id_eq]
  | succ d ih =>
    dsimp only [arity] at x
    simp only [bitonicSortTraceCircuit, sortTraceSize, arity,
      BitonicSort.sortTrace, BitonicSort.sort]
    erw [eval_chain _ _ _ _ _ (eval_halves _ _ x), eval_bitonicMergeTraceCircuit]
    simp only [ih, arity, mergeTraceSize, controls_pack, records_pack,
      bitonicMergeCircuit.records_firstHalf,
      bitonicMergeCircuit.records_secondHalf, directProductInput_flatten]
    erw [controls_pack, records_pack, ← pairs_append, ← pairs_append]

/-- A traced merge computes each comparator once, retaining its existing control pair. -/
theorem cost_program_bitonicMergeTraceCircuit {k r : ℕ} (key : Fin k → Fin r) (d : ℕ)
    (ascending : Bool) (cost : signature.Op → ℕ) :
    (bitonicMergeTraceCircuit key d ascending).program.cost cost = mergeTraceSize d *
      (compareSwapCircuit.record
        (Formula.lexLt (Fin.natAdd r ∘ key) (Fin.castAdd r ∘ key)).toCircuit).program.cost
          cost := by
  induction d with
  | zero => simp [bitonicMergeTraceCircuit, mergeTraceSize]
  | succ d ih =>
    simp only [bitonicMergeTraceCircuit]
    erw [cost_chain, cost_layer, cost_halves, ih, mergeTraceSize]
    ring

/-- A traced sort computes each comparator once, retaining its existing control pair. -/
theorem cost_program_bitonicSortTraceCircuit {k r : ℕ} (key : Fin k → Fin r) (d : ℕ)
    (ascending : Bool) (cost : signature.Op → ℕ) :
    (bitonicSortTraceCircuit key d ascending).program.cost cost = sortTraceSize d *
      (compareSwapCircuit.record
        (Formula.lexLt (Fin.natAdd r ∘ key) (Fin.castAdd r ∘ key)).toCircuit).program.cost
          cost := by
  induction d generalizing ascending with
  | zero => simp [bitonicSortTraceCircuit, sortTraceSize]
  | succ d ih =>
    simp only [bitonicSortTraceCircuit]
    erw [cost_chain, cost_halves, ih, ih, cost_program_bitonicMergeTraceCircuit, sortTraceSize]
    ring


namespace bitonicSortTraceCircuit

/-- Select controls and records independently by free wiring. -/
def select {a t n m r : ℕ} (cs : Fin a → Fin t) (rs : Fin n → Fin m) :
    Circuit signature (t * 2 + m * r) (a * 2 + n * r) :=
  Circuit.wiring signature (Fin.addCases
    (fun i =>
      let jb := finProdFinEquiv.symm i
      Fin.castAdd (m * r) (finProdFinEquiv (cs jb.1, jb.2)))
    (fun i =>
      let jb := finProdFinEquiv.symm i
      Fin.natAdd (t * 2) (finProdFinEquiv (rs jb.1, jb.2))))

private theorem eval_select {a t n m r : ℕ} (cs : Fin a → Fin t) (rs : Fin n → Fin m)
    (c : Fin t → BitString 2) (x : Fin m → BitString r) :
    (select cs rs).eval interpretation (pack c x) = pack (c ∘ cs) (x ∘ rs) := by
  apply ext <;>
    simp only [controls_pack, records_pack] <;>
    funext j bit <;>
    simp only [controls, records, select, Circuit.eval_wiring, Function.comp_apply,
      Fin.addCases_left, Fin.addCases_right, pack, directProductInput, Fin.append_left,
      Fin.append_right, flatten, Equiv.symm_apply_apply]

/-- Reverse a comparison layer, reading the saved decision and its complement. -/
def unlayer (n r : ℕ) : Circuit signature (n * 2 + (n + n) * r) ((n + n) * r) :=
  (Circuit.wiring signature (bitonicLayerCircuit.scatter n r)).comp
    (((compareSwapCircuit.switch r).replicate n).comp
      (Circuit.wiring signature (fun i =>
        let jb := finProdFinEquiv.symm i
        Fin.addCases
          (fun bit => Fin.castAdd ((n + n) * r) (finProdFinEquiv (jb.1, bit)))
          (Fin.addCases
            (fun bit => Fin.natAdd (n * 2) (finProdFinEquiv (Fin.castAdd n jb.1, bit)))
            (fun bit => Fin.natAdd (n * 2) (finProdFinEquiv (Fin.natAdd n jb.1, bit)))) jb.2)))

private theorem unlayer_input {n r : ℕ} (flags : BitString n)
    (x : Fin (n + n) → BitString r) (j : Fin n) :
    (fun bit : Fin (2 + (r + r)) =>
      pack (pairs flags) x (Fin.addCases
        (fun bit => Fin.castAdd ((n + n) * r) (finProdFinEquiv (j, bit)))
        (Fin.addCases
          (fun bit => Fin.natAdd (n * 2) (finProdFinEquiv (Fin.castAdd n j, bit)))
          (fun bit => Fin.natAdd (n * 2) (finProdFinEquiv (Fin.natAdd n j, bit)))) bit)) =
      Fin.append ![flags j, !flags j] (Fin.append (x (Fin.castAdd n j)) (x (Fin.natAdd n j))) := by
  funext bit
  cases bit using Fin.addCases with
  | left bit =>
    simp only [Fin.addCases_left, pack, Fin.append_left, flatten, Equiv.symm_apply_apply, pairs]
  | right bit =>
    cases bit using Fin.addCases <;>
      simp only [Fin.addCases_right, Fin.addCases_left, pack, Fin.append_right, Fin.append_left,
        flatten, Equiv.symm_apply_apply]

private theorem eval_unlayer (n r : ℕ) (flags : BitString n) (x : Fin (n + n) → BitString r) :
    directProductInput ((unlayer n r).eval interpretation (pack (pairs flags) x)) =
      BitonicSort.routeLayer flags x := by
  funext j bit
  cases j using Fin.addCases <;>
    simp only [unlayer, Circuit.eval_comp, Circuit.eval_wiring, directProductInput,
      Function.comp_apply, bitonicLayerCircuit.scatter, Equiv.symm_apply_apply,
      Fin.addCases_left, Fin.addCases_right, Circuit.eval_replicate_apply]
  all_goals
    unfold directProductInput
    simp only [Function.comp_def, Equiv.symm_apply_apply]
    erw [unlayer_input, compareSwapCircuit.eval_switch]
    simp only [BitonicSort.routeLayer, Fin.append_left, Fin.append_right]
    split_ifs <;> simp only [Fin.append_left, Fin.append_right]

private theorem cost_unlayer (n r : ℕ) (cost : signature.Op → ℕ) :
    (unlayer n r).program.cost cost = n * (2 * r * (2 * cost .and + cost .or)) := by
  simp only [unlayer, Circuit.cost_program_comp, Circuit.cost_program_wiring,
    Circuit.cost_program_replicate, compareSwapCircuit.cost_switch, Nat.zero_add, Nat.add_zero]

/-- Reverse two independent circuits using the matching halves of their controls and records. -/
def unhalves {a b n r : ℕ} (left : Circuit signature (a * 2 + n * r) (n * r))
    (right : Circuit signature (b * 2 + n * r) (n * r)) :
    Circuit signature ((a + b) * 2 + (n + n) * r) ((n + n) * r) :=
  (Circuit.wiring signature (fun i =>
    let jb := finProdFinEquiv.symm i
    Fin.addCases
      (fun j => Fin.castAdd (n * r) (finProdFinEquiv (j, jb.2)))
      (fun j => Fin.natAdd (n * r) (finProdFinEquiv (j, jb.2))) jb.1)).comp
    ((left.comp (select (Fin.castAdd b) (Fin.castAdd n))).append
      (right.comp (select (Fin.natAdd a) (Fin.natAdd n))))

private theorem eval_unhalves {a b n r : ℕ} (left : Circuit signature (a * 2 + n * r) (n * r))
    (right : Circuit signature (b * 2 + n * r) (n * r))
    (c : Fin (a + b) → BitString 2) (x : Fin (n + n) → BitString r) :
    directProductInput ((unhalves left right).eval interpretation (pack c x)) =
      Fin.append
        (directProductInput (left.eval interpretation
          (pack (c ∘ Fin.castAdd b) (x ∘ Fin.castAdd n))))
        (directProductInput (right.eval interpretation
          (pack (c ∘ Fin.natAdd a) (x ∘ Fin.natAdd n)))) := by
  funext j bit
  cases j using Fin.addCases <;>
    simp only [unhalves, directProductInput, Circuit.eval_comp, Circuit.eval_wiring,
      Function.comp_apply, Equiv.symm_apply_apply, Fin.addCases_left, Fin.addCases_right,
      Circuit.eval_append, Fin.append_left, Fin.append_right, eval_select]

private theorem cost_unhalves {a b n r : ℕ} (left : Circuit signature (a * 2 + n * r) (n * r))
    (right : Circuit signature (b * 2 + n * r) (n * r)) (cost : signature.Op → ℕ) :
    (unhalves left right).program.cost cost =
      left.program.cost cost + right.program.cost cost := by
  simp only [unhalves, select, Circuit.cost_program_comp, Circuit.cost_program_append,
    Circuit.cost_program_wiring, Nat.zero_add, Nat.add_zero]

/-- Preserve the first controls while undoing the second stage, then undo the first stage. -/
def unchain {a b n r : ℕ} (first : Circuit signature (a * 2 + n * r) (n * r))
    (second : Circuit signature (b * 2 + n * r) (n * r)) :
    Circuit signature ((a + b) * 2 + n * r) (n * r) :=
  first.comp ((Circuit.wiring signature (fun i =>
    let jb := finProdFinEquiv.symm i
    Fin.castAdd (n * r) (finProdFinEquiv (Fin.castAdd b jb.1, jb.2)))).append
      (second.comp (select (Fin.natAdd a) id)))

private theorem eval_unchain {a b n r : ℕ} (first : Circuit signature (a * 2 + n * r) (n * r))
    (second : Circuit signature (b * 2 + n * r) (n * r))
    (c : Fin (a + b) → BitString 2) (x : Fin n → BitString r) :
    (unchain first second).eval interpretation (pack c x) =
      first.eval interpretation (pack (c ∘ Fin.castAdd b)
        (directProductInput (second.eval interpretation (pack (c ∘ Fin.natAdd a) x)))) := by
  simp only [unchain, Circuit.eval_comp, Circuit.eval_append, eval_select, Function.comp_id]
  congr 1
  funext i
  cases i using Fin.addCases with
  | left i =>
    simp only [Fin.append_left, Circuit.eval_wiring, Function.comp_apply, pack, flatten,
      Equiv.symm_apply_apply]
  | right i =>
    simp only [Fin.append_right, pack, flatten, directProductInput, Prod.mk.eta,
      Equiv.apply_symm_apply]

private theorem cost_unchain {a b n r : ℕ} (first : Circuit signature (a * 2 + n * r) (n * r))
    (second : Circuit signature (b * 2 + n * r) (n * r)) (cost : signature.Op → ℕ) :
    (unchain first second).program.cost cost =
      first.program.cost cost + second.program.cost cost := by
  simp only [unchain, select, Circuit.cost_program_comp, Circuit.cost_program_append,
    Circuit.cost_program_wiring, Nat.zero_add]
  exact Nat.add_comm _ _

theorem pairs_comp {a b : ℕ} (flags : BitString a) (f : Fin b → Fin a) :
    pairs (flags ∘ f) = pairs flags ∘ f := rfl

end bitonicSortTraceCircuit

/-- Undo the child merges before reversing the first comparison layer. -/
def bitonicUnmergeCircuit (r : ℕ) : (d : ℕ) →
    Circuit signature (mergeTraceSize d * 2 + arity d * r) (arity d * r)
  | 0 => Circuit.wiring signature (Fin.natAdd 0)
  | d + 1 =>
    unchain (unlayer (arity d) r) (unhalves (bitonicUnmergeCircuit r d) (bitonicUnmergeCircuit r d))

/-- Undo the final merge before reversing the two child sorts. -/
def bitonicUnsortCircuit (r : ℕ) : (d : ℕ) →
    Circuit signature (sortTraceSize d * 2 + arity d * r) (arity d * r)
  | 0 => Circuit.wiring signature (Fin.natAdd 0)
  | d + 1 =>
    unchain (unhalves (bitonicUnsortCircuit r d) (bitonicUnsortCircuit r d))
      (bitonicUnmergeCircuit r (d + 1))

/-- The reverse merge implements reversal for every paired trace and payload. -/
theorem eval_bitonicUnmergeCircuit (r d : ℕ) (flags : BitString (mergeTraceSize d))
    (x : Fin (arity d) → BitString r) :
    directProductInput ((bitonicUnmergeCircuit r d).eval interpretation (pack (pairs flags) x)) =
      BitonicSort.unrouteMerge d flags x := by
  induction d with
  | zero =>
    simp only [bitonicUnmergeCircuit, BitonicSort.unrouteMerge]
    erw [Circuit.eval_wiring]
    exact records_pack _ _
  | succ d ih =>
    dsimp only [arity, mergeTraceSize] at flags x
    simp only [bitonicUnmergeCircuit, arity, mergeTraceSize, BitonicSort.unrouteMerge]
    erw [eval_unchain, eval_unhalves]
    simp only [← pairs_comp, ih]
    exact eval_unlayer _ _ _ _

/-- The reverse sorter implements reversal for every paired trace and payload. -/
theorem eval_bitonicUnsortCircuit (r d : ℕ) (flags : BitString (sortTraceSize d))
    (x : Fin (arity d) → BitString r) :
    directProductInput ((bitonicUnsortCircuit r d).eval interpretation (pack (pairs flags) x)) =
      BitonicSort.unrouteSort d flags x := by
  induction d with
  | zero =>
    simp only [bitonicUnsortCircuit, BitonicSort.unrouteSort]
    erw [Circuit.eval_wiring]
    exact records_pack _ _
  | succ d ih =>
    dsimp only [arity, sortTraceSize] at flags x
    simp only [bitonicUnsortCircuit, arity, sortTraceSize, BitonicSort.unrouteSort]
    erw [eval_unchain]
    simp only [← pairs_comp]
    erw [eval_bitonicUnmergeCircuit, eval_unhalves]
    simp only [← pairs_comp, ih]

/-- A reverse merge charges only switching; saved controls require no new negations. -/
theorem cost_program_bitonicUnmergeCircuit (r d : ℕ) (cost : signature.Op → ℕ) :
    (bitonicUnmergeCircuit r d).program.cost cost =
      mergeTraceSize d * (2 * r * (2 * cost .and + cost .or)) := by
  induction d with
  | zero => simp [bitonicUnmergeCircuit, mergeTraceSize]
  | succ d ih =>
    simp only [bitonicUnmergeCircuit]
    erw [cost_unchain, cost_unlayer, cost_unhalves, ih, mergeTraceSize]
    ring

/-- A reverse sort charges only switching; saved controls require no new negations. -/
theorem cost_program_bitonicUnsortCircuit (r d : ℕ) (cost : signature.Op → ℕ) :
    (bitonicUnsortCircuit r d).program.cost cost =
      sortTraceSize d * (2 * r * (2 * cost .and + cost .or)) := by
  induction d with
  | zero => simp [bitonicUnsortCircuit, sortTraceSize]
  | succ d ih =>
    simp only [bitonicUnsortCircuit]
    erw [cost_unchain, cost_unhalves, ih, cost_program_bitonicUnmergeCircuit, sortTraceSize]
    ring

/-- Retaining the trace adds no gates to ordinary sorting when records are nonempty. -/
theorem cost_program_bitonicSortTraceCircuit_eq {k r : ℕ} (key : Fin k → Fin r) (d : ℕ)
    (ascending : Bool) (hr : r ≠ 0) (cost : signature.Op → ℕ) :
    (bitonicSortTraceCircuit key d ascending).program.cost cost =
      (bitonicSortCircuit key d ascending).program.cost cost := by
  have hrecord : (compareSwapCircuit.record
      (Formula.lexLt (Fin.natAdd r ∘ key) (Fin.castAdd r ∘ key)).toCircuit).program.cost cost =
      (compareSwapCircuit key).program.cost cost := by
    rw [compareSwapCircuit.cost_record_eq_exchange]
    rw [compareSwapCircuit, ite_eq_right hr]
  have h := four_mul_cost_program_bitonicSortCircuit key d ascending cost
  rw [cost_program_bitonicSortTraceCircuit, hrecord]
  rw [← BitonicSort.four_mul_sortTraceSize, Nat.mul_assoc] at h
  lia

/-- Exact gate count, including the comparison constant and shared negation at empty width. -/
theorem size_bitonicSortTraceCircuit {k r : ℕ} (key : Fin k → Fin r) (d : ℕ) (ascending : Bool) :
    (bitonicSortTraceCircuit key d ascending).size = sortTraceSize d * (6 * k + 6 * r + 2) := by
  have h := cost_program_bitonicSortTraceCircuit key d ascending (fun _ => 1)
  rw [compareSwapCircuit.cost_record] at h
  simp only [Program.cost_const, one_mul, Formula.size_toCircuit, Formula.size_lexLt] at h
  rw [h]
  ring

/-- Reversing a sort uses six gates per payload bit and comparison. -/
theorem size_bitonicUnsortCircuit (r d : ℕ) :
    (bitonicUnsortCircuit r d).size = sortTraceSize d * (6 * r) := by
  have h := cost_program_bitonicUnsortCircuit r d (fun _ => 1)
  simp only [Program.cost_const, one_mul] at h
  rw [h]
  ring

/-- Saved controls restore transformed records, even when the answer has a different width. -/
theorem eval_bitonicUnsortCircuit_sort {k r v : ℕ} (key : Fin k → Fin r) (d : ℕ)
    (ascending : Bool) (f : BitString r → BitString v) (x : BitString (arity d * r)) :
    let output := (bitonicSortTraceCircuit key d ascending).eval interpretation x
    directProductInput ((bitonicUnsortCircuit v d).eval interpretation
      (pack (controls output) (f ∘ records output))) = f ∘ directProductInput x := by
  dsimp only
  rw [eval_bitonicSortTraceCircuit, controls_pack, records_pack, eval_bitonicUnsortCircuit]
  exact BitonicSort.unrouteSort_comp_sort _ _ _ _ _

end Cslib.Circuits.Boolean
