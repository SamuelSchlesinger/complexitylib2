/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Repeat

/-!
# Collecting runs in finite vectors

`OracleComp.replicateFin` collects successive runs as a function on `Fin count`.
Listing its coordinates gives exactly the existing list-valued repetition program; the
typed vector does not introduce a new sampling primitive or an efficiency assumption.
Closed `ProbComp` runs draw independent values.

## Main definitions

* `Cslib.OracleComp.replicateFin`: collect successive runs in a length-indexed vector.

## Main results

* `Cslib.OracleComp.map_ofFn_replicateFin`: agreement with list-valued repetition.
* `Cslib.ProbComp.mem_support_replicateFin_iff`: support is coordinatewise, even for infinite types.
* `Cslib.ProbComp.eval_replicateFin`: independent finite coordinates have the product law.
* `Cslib.ProbComp.eval_replicateFin_map`: list-valued encodings preserve the joint law.
* `Cslib.ProbComp.eval_replicateFin_of_uniformList`: a flat fair-bit seed supplies every run.

## References

This is the length-indexed interface to `OracleComp.replicate` and its product-distribution laws.
-/

@[expose] public section

namespace Cslib

namespace OracleComp

universe u v

variable {Query : Type u} {spec : OracleSpec.{u, v} Query} {α : Type v}

/-- Collect successive runs as a length-indexed vector, in execution order. -/
def replicateFin : (count : ℕ) → OracleComp spec α → OracleComp spec (Fin count → α)
  | 0, _ => pure Fin.elim0
  | count + 1, program => do
    let first ← program
    let rest ← replicateFin count program
    return Fin.cons first rest

/-- Listing the coordinates gives exactly the existing repeated-run program. -/
@[simp] theorem map_ofFn_replicateFin (count : ℕ) (program : OracleComp spec α) :
    List.ofFn <$> replicateFin count program = replicate count program := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp [replicateFin, replicate_succ, map_bind, Functor.map_map, List.ofFn_succ, ← ih]

end OracleComp

namespace ProbComp

open Probability

variable {α : Type}

/-- The vector support consists exactly of the tuples of individually supported values. -/
theorem mem_support_replicateFin_iff (count : ℕ) (program : ProbComp α)
    (values : Fin count → α) :
    values ∈ (eval (OracleComp.replicateFin count program)).support ↔
      ∀ i, values i ∈ (eval program).support := by
  have h : List.ofFn values ∈ (eval (OracleComp.replicate count program)).support ↔
      values ∈ (eval (OracleComp.replicateFin count program)).support := by
    rw [← OracleComp.map_ofFn_replicateFin, eval_map, PMF.mem_support_map_iff]
    simp only [List.ofFn_injective.eq_iff, exists_eq_right]
  rw [← h, mem_support_replicate_iff]
  simp

/-- Finite coordinate distributions give the independent product law. -/
theorem eval_replicateFin [Finite α] (count : ℕ) (program : ProbComp α) :
    eval (OracleComp.replicateFin count program) =
      Probability.PMF.pi (fun _ : Fin count => eval program) := by
  apply PMF.map_injective List.ofFn_injective
  rw [← eval_map, OracleComp.map_ofFn_replicateFin, eval_replicate]

/-- Repeating a representation of each sampled value gives the represented vector law. -/
theorem eval_replicateFin_map {β : Type} {source : ProbComp α} {encoded : ProbComp β}
    {encode : α → β} (h : eval encoded = (eval source).map encode) (count : ℕ) :
    eval (OracleComp.replicate count encoded) =
      (eval (OracleComp.replicateFin count source)).map
        (fun values => List.ofFn (fun i => encode (values i))) := by
  rw [eval_replicate_map h, ← OracleComp.map_ofFn_replicateFin, eval_map, PMF.map_comp]
  simp only [Function.comp_def, List.map_ofFn]

/-- Mapping each coordinate after independent runs agrees with mapping each run's outcome.
Neither outcome type needs to be finite. -/
theorem eval_replicateFin_map_coords {β : Type} (count : ℕ) (program : ProbComp α)
    (f : α → β) :
    eval (OracleComp.replicateFin count (f <$> program)) =
      (eval (OracleComp.replicateFin count program)).map (fun values i => f (values i)) := by
  apply PMF.map_injective List.ofFn_injective
  rw [← eval_map, OracleComp.map_ofFn_replicateFin, PMF.map_comp]
  exact eval_replicateFin_map (eval_map f program) count

/-- Disjoint blocks of one uniform tape realize a vector of independently sampled values.
The output type may be infinite, and either the count or the block width may be zero. -/
theorem eval_replicateFin_of_uniformList (count width : ℕ) (program : ProbComp α)
    (evaluate : List Bool → α)
    (hlaw : eval program = (BitString.uniformList width).map evaluate) :
    eval (OracleComp.replicateFin count program) =
      (BitString.uniformList (count * width)).map (fun tape i =>
        evaluate (List.ofFn (BitString.block (BitString.ofList (count * width) tape) i))) := by
  apply PMF.map_injective List.ofFn_injective
  rw [← eval_map, OracleComp.map_ofFn_replicateFin,
    eval_replicate_of_uniformList count width program evaluate hlaw, PMF.map_comp]
  simp only [Function.comp_def, BitString.listRows_eq_ofFn, List.map_ofFn]

end ProbComp

end Cslib
