/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.RoutingValues
public import Complexity.Computability.Circuit.Boolean.Substitution
public import Complexity.Foundations.Data.BitString.Basic
import Complexity.Foundations.Data.Nat.Log
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Batched table lookup with one sort

A fixed table is hardwired into one source record per address. Query addresses are input wires;
queries and padding are destination records. Sort once, broadcast matching source values, and
reverse the saved sorting decisions on the values alone. Selecting the original request positions
then returns the answers in input order, including repeated addresses. No request identifiers or
restoration ranks are used. Empty keys, empty values, and zero requests are allowed.

The circuit uses CSLib's native `Circuit` representation. Input preparation shares exactly two
constant gates, including when one or both are unused. The exact weighted cost and total gate count
include these constants; the polynomial gate bound does not certify constructor runtime.

## Main definitions

* `Cslib.Circuits.Boolean.batchLookupCircuit`: lookup with inferred sorting depth and padding.
* `Cslib.Circuits.Boolean.batchLookupCircuit.withPadding`: lookup with a supplied record count.

## Main results

* `Cslib.Circuits.Boolean.eval_batchLookupCircuit`: arbitrary repeated queries are answered exactly.
* `Cslib.Circuits.Boolean.batchLookupCircuit.size_withPadding`: exact total gate count.
* `Cslib.Circuits.Boolean.size_batchLookupCircuit_le`: a bound linear in table size plus request
  count and field width, and quadratic in sorting depth.

## References

Simplifies the nonuniform lookup construction in
[S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction],
using the sorting network of
[K. E. Batcher, *Sorting Networks and Their Applications*][Batcher1968].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open bitonicSortTraceCircuit broadcastCircuit

namespace batchLookupCircuit

section Layout

variable {k v requests padding d : ℕ}

/-- The symbolic records: requests, one source per address, and padding destinations. -/
def rows (table : BitString k → BitString v) :
    Fin (requests + (2 ^ k + padding)) → Fin (k + 1 + v) → Fin (requests * k) ⊕ Bool :=
  Fin.append
    (fun request => Fin.append
      (Fin.snoc (fun bit => .inl (finProdFinEquiv (request, bit))) (.inr true))
      (fun _ => .inr false))
    (Fin.append
      (fun source => Sum.inr ∘ Fin.append (Fin.snoc ((BitString.equivFin k).symm source) false)
        (table ((BitString.equivFin k).symm source)))
      (fun _ => Sum.inr ∘ Fin.append (Fin.snoc (fun _ => false) true) (fun _ => false)))

/-- Flatten the records into variables and constants for the padded sorting network. -/
def substitution (table : BitString k → BitString v)
    (h : requests + (2 ^ k + padding) = BitonicSort.arity d) :
    Fin (BitonicSort.arity d * (k + 1 + v)) → Fin (requests * k) ⊕ Bool :=
  fun i => let jb := finProdFinEquiv.symm i
    rows table (Fin.cast h.symm jb.1) jb.2

/-- Interpret the symbolic record layout on the query input. -/
private def layout (table : BitString k → BitString v)
    (h : requests + (2 ^ k + padding) = BitonicSort.arity d) (x : BitString (requests * k)) :
    BitString (BitonicSort.arity d * (k + 1 + v)) :=
  substitute (substitution table h) x

/-- The original position of a request in the padded layout. -/
def requestIndex (h : requests + (2 ^ k + padding) = BitonicSort.arity d)
    (request : Fin requests) : Fin (BitonicSort.arity d) :=
  Fin.cast h (Fin.castAdd (2 ^ k + padding) request)

/-- The original position of a hardwired table entry in the padded layout. -/
private def sourceIndex (h : requests + (2 ^ k + padding) = BitonicSort.arity d)
    (source : Fin (2 ^ k)) : Fin (BitonicSort.arity d) :=
  Fin.cast h (Fin.natAdd requests (Fin.castAdd padding source))

private theorem layout_apply (table : BitString k → BitString v)
    (h : requests + (2 ^ k + padding) = BitonicSort.arity d) (x : BitString (requests * k))
    (i : Fin (requests + (2 ^ k + padding))) (bit : Fin (k + 1 + v)) :
    directProductInput (layout table h x) (Fin.cast h i) bit = (rows table i bit).elim x id := by
  simp [layout, substitution, substitute, directProductInput]

private theorem request_key (table : BitString k → BitString v)
    (h : requests + (2 ^ k + padding) = BitonicSort.arity d) (x : BitString (requests * k))
    (request : Fin requests) :
    header (layout table h x) (requestIndex h request) ∘ Fin.castSucc =
      directProductInput x request := by
  funext bit
  change header (layout table h x) (requestIndex h request) bit.castSucc =
    x (finProdFinEquiv (request, bit))
  simp [header, Function.comp_def, requestIndex, layout_apply, rows]

private theorem request_tag (table : BitString k → BitString v)
    (h : requests + (2 ^ k + padding) = BitonicSort.arity d) (x : BitString (requests * k))
    (request : Fin requests) :
    header (layout table h x) (requestIndex h request) (Fin.last k) = true := by
  simp [header, Function.comp_def, requestIndex, layout_apply, rows]

private theorem source_key (table : BitString k → BitString v)
    (h : requests + (2 ^ k + padding) = BitonicSort.arity d) (x : BitString (requests * k))
    (source : Fin (2 ^ k)) :
    header (layout table h x) (sourceIndex h source) ∘ Fin.castSucc =
      (BitString.equivFin k).symm source := by
  funext bit
  simp [header, Function.comp_def, sourceIndex, layout_apply, rows]

private theorem source_tag (table : BitString k → BitString v)
    (h : requests + (2 ^ k + padding) = BitonicSort.arity d) (x : BitString (requests * k))
    (source : Fin (2 ^ k)) :
    header (layout table h x) (sourceIndex h source) (Fin.last k) = false := by
  simp [header, Function.comp_def, sourceIndex, layout_apply, rows]

private theorem source_value (table : BitString k → BitString v)
    (h : requests + (2 ^ k + padding) = BitonicSort.arity d) (x : BitString (requests * k))
    (source : Fin (2 ^ k)) :
    value (layout table h x) (sourceIndex h source) =
      table ((BitString.equivFin k).symm source) := by
  funext bit
  simp [value, Function.comp_def, sourceIndex, layout_apply, rows]

private theorem unique_source (table : BitString k → BitString v)
    (h : requests + (2 ^ k + padding) = BitonicSort.arity d) (x : BitString (requests * k))
    (source : Fin (2 ^ k)) (i : Fin (BitonicSort.arity d))
    (hkey : header (layout table h x) i ∘ Fin.castSucc =
      header (layout table h x) (sourceIndex h source) ∘ Fin.castSucc)
    (htag : header (layout table h x) i (Fin.last k) = false) : i = sourceIndex h source := by
  obtain ⟨i, rfl⟩ := (finCongr h).surjective i
  revert hkey htag
  refine Fin.addCases (fun request hkey htag => ?_) (fun i => ?_) i
  · have := request_tag table h x request
    simp only [requestIndex] at this
    exact Bool.noConfusion (this.symm.trans htag)
  · refine Fin.addCases (fun j hkey htag => ?_) (fun pad hkey htag => ?_) i
    · change header (layout table h x) (sourceIndex h j) ∘ Fin.castSucc = _ at hkey
      rw [source_key, source_key] at hkey
      exact congrArg (sourceIndex h) ((BitString.equivFin k).symm.injective hkey)
    · simp [header, Function.comp_def, layout_apply, rows] at htag

/-- Select the value fields at the original request positions by free wiring. -/
def outputs (h : requests + (2 ^ k + padding) = BitonicSort.arity d) :
    Circuit signature (BitonicSort.arity d * v) (requests * v) :=
  Circuit.wiring signature fun i => let jb := finProdFinEquiv.symm i
    finProdFinEquiv (requestIndex h jb.1, jb.2)

/-- Batched lookup using a specified power-of-two record count and padding. -/
def withPadding {k v requests padding d : ℕ} (table : BitString k → BitString v)
    (h : requests + (2 ^ k + padding) = BitonicSort.arity d) :
    Circuit signature (requests * k) (requests * v) :=
  (outputs h).comp ((routeValuesCircuit (Fin.castSucc) (Fin.last k) d v).comp
    (substituteCircuit (substitution table h)))

/-- Every request receives its table value, including repeated addresses. -/
theorem eval_withPadding {k v requests padding d : ℕ} (table : BitString k → BitString v)
    (h : requests + (2 ^ k + padding) = BitonicSort.arity d) (x : BitString (requests * k)) :
    directProductInput ((withPadding table h).eval interpretation x) =
      table ∘ directProductInput x := by
  funext request bit
  have hr := eval_routeValuesCircuit_of_unique_source (Fin.castSucc) (Fin.last k)
    (layout table h x) (sourceIndex h ((BitString.equivFin k) (directProductInput x request)))
    (requestIndex h request) (by simp [source_key, request_key])
    (source_tag table h x _) (request_tag table h x request) (unique_source table h x _)
  rw [source_value, Equiv.symm_apply_apply] at hr
  simpa only [withPadding, Circuit.eval_comp, outputs, Circuit.eval_wiring,
    eval_substituteCircuit, directProductInput, Function.comp_apply, Equiv.symm_apply_apply,
    layout] using congrFun hr bit


/-- Input preparation adds exactly two shared constant gates to the routing cost. -/
theorem cost_program_withPadding {k v requests padding d : ℕ}
    (table : BitString k → BitString v)
    (h : requests + (2 ^ k + padding) = BitonicSort.arity d) (cost : signature.Op → ℕ) :
    (withPadding table h).program.cost cost =
      (routeValuesCircuit Fin.castSucc (Fin.last k) d v).program.cost cost +
        cost (.const false) + cost (.const true) := by
  simp only [withPadding, outputs, Circuit.cost_program_comp,
    Circuit.cost_program_wiring, cost_program_substituteCircuit]
  ac_rfl

/-- Exact total gate count, including all constants and negations. -/
theorem size_withPadding {k v requests padding d : ℕ}
    (table : BitString k → BitString v)
    (h : requests + (2 ^ k + padding) = BitonicSort.arity d) :
    (withPadding table h).size =
      BitonicSort.sortTraceSize d * (12 * (k + v) + 14) +
        (1 + (BitonicSort.arity d - 1) * (6 * k + 1) + v * (1 + 4 * BitonicSort.arity d)) + 2 := by
  have ha : BitonicSort.arity d ≠ 0 := by
    rw [BitonicSort.arity_eq_two_pow]
    exact pow_ne_zero _ (by decide)
  have hc := cost_program_withPadding table h (fun _ => 1)
  simp only [Program.cost_const, one_mul, size_routeValuesCircuit, size_broadcastCircuit,
    ite_eq_right ha] at hc
  rw [hc]
  ring


/-- A factored gate bound, linear in record count and field width and quadratic in depth. -/
theorem size_withPadding_le {k v requests padding d : ℕ}
    (table : BitString k → BitString v)
    (h : requests + (2 ^ k + padding) = BitonicSort.arity d) :
    (withPadding table h).size ≤
      24 * BitonicSort.arity d * (d + 1) ^ 2 * (k + v + 1) := by
  have ha : 1 ≤ BitonicSort.arity d := by
    rw [BitonicSort.arity_eq_two_pow]
    exact Nat.one_le_pow _ _ (by decide)
  have hd : 1 ≤ (d + 1) ^ 2 := Nat.one_le_pow _ _ (by lia)
  have ht : BitonicSort.sortTraceSize d ≤ BitonicSort.arity d * (d + 1) ^ 2 := by
    have hh := BitonicSort.four_mul_sortTraceSize d
    rw [← BitonicSort.arity_eq_two_pow] at hh
    nlinarith
  have hl : 1 + (BitonicSort.arity d - 1) * (6 * k + 1) +
      v * (1 + 4 * BitonicSort.arity d) + 2 ≤ 10 * BitonicSort.arity d * (k + v + 1) := by
    have hn := Nat.mul_le_mul_right (6 * k + 1) (Nat.sub_le (BitonicSort.arity d) 1)
    nlinarith
  have hm := Nat.mul_le_mul ht (show 12 * (k + v) + 14 ≤ 14 * (k + v + 1) by lia)
  have hp := Nat.mul_le_mul_left (10 * BitonicSort.arity d * (k + v + 1)) hd
  rw [size_withPadding]
  nlinarith

end Layout

/-- The least sorting depth accommodating all requests and one source per address. -/
def depth (requests k : ℕ) : ℕ := Nat.clog 2 (requests + 2 ^ k)

/-- The number of unused destinations filling the next power-of-two record count. -/
def padding (requests k : ℕ) : ℕ := BitonicSort.arity (depth requests k) - (requests + 2 ^ k)

/-- The canonical padding fills its sorting network exactly. -/
theorem add_padding_eq_arity (requests k : ℕ) :
    requests + (2 ^ k + padding requests k) = BitonicSort.arity (depth requests k) := by
  have h := Nat.le_pow_clog (by decide : 1 < 2) (requests + 2 ^ k)
  simp only [padding, depth, BitonicSort.arity_eq_two_pow]
  lia

end batchLookupCircuit

open batchLookupCircuit

/-- Look up all input addresses in one hardwired table, preserving request order.
Padding and sorting depth are inferred from the number of requests and the key width. -/
def batchLookupCircuit {k v : ℕ} (table : BitString k → BitString v) (requests : ℕ) :
    Circuit signature (requests * k) (requests * v) :=
  withPadding table (add_padding_eq_arity requests k)

/-- The complete circuit computes the table value at each input address. -/
@[simp] theorem eval_batchLookupCircuit {k v : ℕ} (table : BitString k → BitString v) (requests : ℕ)
    (x : BitString (requests * k)) :
    (batchLookupCircuit table requests).eval interpretation x = blockMap table requests x := by
  funext i
  obtain ⟨⟨request, bit⟩, rfl⟩ := finProdFinEquiv.surjective i
  rw [blockMap_apply]
  exact congrFun (congrFun (eval_withPadding table (add_padding_eq_arity requests k) x) request) bit

/-- Batched lookup uses at most the displayed bound in table size plus request count.
This bounds circuit gates, not the running time of the circuit constructor. -/
theorem size_batchLookupCircuit_le {k v : ℕ} (table : BitString k → BitString v) (requests : ℕ) :
    (batchLookupCircuit table requests).size ≤
      48 * (requests + 2 ^ k) * (Nat.clog 2 (requests + 2 ^ k) + 1) ^ 2 * (k + v + 1) := by
  have hn : requests + 2 ^ k ≠ 0 := by positivity
  calc
    _ ≤ 24 * BitonicSort.arity (depth requests k) * (depth requests k + 1) ^ 2 * (k + v + 1) :=
      size_withPadding_le table (add_padding_eq_arity requests k)
    _ ≤ 24 * (2 * (requests + 2 ^ k)) * (depth requests k + 1) ^ 2 * (k + v + 1) := by
      gcongr
      rw [BitonicSort.arity_eq_two_pow]
      exact Nat.pow_clog_le_mul (by decide : 1 < 2) hn
    _ = _ := by dsimp only [depth]; ring

/-- Independent applications of any fixed table admit a shared lookup circuit. -/
theorem complexity_blockMap_le_lookup {k v : ℕ} (table : BitString k → BitString v) (requests : ℕ) :
    complexity interpretation (blockMap table requests) ≤
      48 * (requests + 2 ^ k) * (Nat.clog 2 (requests + 2 ^ k) + 1) ^ 2 * (k + v + 1) :=
  (complexity_le_of_computes (batchLookupCircuit table requests)
    (eval_batchLookupCircuit table requests)).trans (size_batchLookupCircuit_le table requests)

end Cslib.Circuits.Boolean
