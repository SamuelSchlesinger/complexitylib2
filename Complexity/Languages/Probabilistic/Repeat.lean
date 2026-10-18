/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Basic
public import Complexity.Probability.BitString.List
public import Complexity.Probability.Product

/-!
# Bounded repetition of probabilistic programs

`OracleComp.replicate` collects the results of an ordinary `List.mapM` traversal in execution
order. Closed runs draw independent samples, even when the output type is infinite. Efficiency
is certified separately in `Computability.Probabilistic.Repeat`.

## Main definitions

* `Cslib.OracleComp.replicate`: collect a bounded number of runs.
* `Cslib.OracleComp.countTrue`, `.testProbabilityLT`: count successes and test rational thresholds.

## Main results

* `Cslib.OracleComp.replicate_add`, `.replicate_snoc`: split an execution into segments.
* `Cslib.ProbComp.eval_replicate`: finite outputs have the independent product law.
* `Cslib.ProbComp.eval_replicate_map`: transport a sampling law through repeated draws.
* `Cslib.ProbComp.eval_countTrue`: the success count is a sum of independent indicators.
* `Cslib.ProbComp.countTrue_le`: every supported success count respects the trial budget.
* `Cslib.ProbComp.eval_replicate_of_uniform`: realize the joint law from independent finite seeds.
* `Cslib.ProbComp.eval_replicate_of_uniformList`: collect independent draws from one flat bit list.

## References

Adapted from `Languages/Probabilistic/Repeat.lean` on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the existing typed program interface and list
traversal.
-/

@[expose] public section

namespace Cslib

open Probability

namespace OracleComp

universe u v

variable {Query : Type u} {spec : OracleSpec.{u, v} Query} {α β : Type v}

/-- Collect the results of a bounded number of runs in execution order. -/
def replicate (count : ℕ) (program : OracleComp spec α) : OracleComp spec (List α) :=
  (List.replicate count ()).mapM (fun _ => program)

@[simp] theorem replicate_zero (program : OracleComp spec α) :
    replicate 0 program = pure [] := rfl

theorem replicate_succ (count : ℕ) (program : OracleComp spec α) :
    replicate (count + 1) program = program >>= fun first =>
      List.cons first <$> replicate count program := by
  simp [replicate, List.replicate_succ, bind_pure_comp]

/-- Split repeated runs into two consecutive segments. -/
theorem replicate_add (first second : ℕ) (program : OracleComp spec α) :
    replicate (first + second) program = (do
      let front ← replicate first program
      let back ← replicate second program
      return front ++ back) := by
  simp only [replicate, List.replicate_add, List.mapM_append]

/-- Split off the last draw of a repeated program. -/
theorem replicate_snoc (count : ℕ) (program : OracleComp spec α) :
    replicate (count + 1) program = (do
      let front ← replicate count program
      (fun last => front ++ [last]) <$> program) := by
  simpa [replicate, bind_pure_comp] using replicate_add count 1 program

/-- Deterministic postprocessing commutes with collecting the draws. -/
theorem replicate_map (count : ℕ) (program : OracleComp spec α) (f : α → β) :
    replicate count (f <$> program) = List.map f <$> replicate count program := by
  induction count with
  | zero => simp
  | succ count ih =>
    simp only [replicate_succ, ih, bind_map_left, map_bind, Functor.map_map, List.map_cons]

variable {spec : OracleSpec.{u, 0} Query}

/-- Count the true results of a bounded number of runs of a Boolean program. -/
def countTrue (count : ℕ) (program : OracleComp spec Bool) : OracleComp spec ℕ :=
  List.count true <$> replicate count program

/-- Compare an empirical acceptance rate with a rational threshold by natural cross-products.
Accuracy theorems require a positive count and denominator; the program is total at zero. -/
def testProbabilityLT (count numerator denominator : ℕ)
    (program : OracleComp spec Bool) : OracleComp spec Bool :=
  (fun successes => decide (successes * denominator < count * numerator)) <$>
    countTrue count program

end OracleComp

namespace ProbComp

variable {α Seed : Type}

/-- A supported collected result has the prescribed length and supported entries. -/
theorem mem_support_replicate_iff (count : ℕ) (program : ProbComp α) (values : List α) :
    values ∈ (eval (OracleComp.replicate count program)).support ↔
      values.length = count ∧ ∀ value ∈ values, value ∈ (eval program).support := by
  induction count generalizing values with
  | zero => cases values <;> simp
  | succ count ih =>
    cases values with
    | nil => simp [OracleComp.replicate_succ]
    | cons value rest => simp [OracleComp.replicate_succ, ih, and_assoc, and_left_comm]

/-- Repetition preserves equality of closed-program distributions, including infinite outputs. -/
theorem eval_replicate_congr {first second : ProbComp α} (h : eval first = eval second)
    (count : ℕ) : eval (OracleComp.replicate count first) =
      eval (OracleComp.replicate count second) := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [OracleComp.replicate_succ, eval_bind, eval_map, h, ih]

/-- An encoded sampling law lifts to repeated draws without requiring either type to be finite
or the encoding to be injective. The order and multiplicity of all draws are preserved. -/
theorem eval_replicate_map {β : Type} {source : ProbComp α} {encoded : ProbComp β}
    {encode : α → β} (h : eval encoded = (eval source).map encode) (count : ℕ) :
    eval (OracleComp.replicate count encoded) =
      (eval (OracleComp.replicate count source)).map (List.map encode) := by
  rw [← eval_map] at h
  rw [eval_replicate_congr h, OracleComp.replicate_map, eval_map]

/-- Repeated closed runs have the independent product law for any finite output distribution. -/
theorem eval_replicate [Finite α] (count : ℕ) (program : ProbComp α) :
    eval (OracleComp.replicate count program) =
      (Probability.PMF.pi (fun _ : Fin count => eval program)).map List.ofFn := by
  induction count with
  | zero =>
    simp only [OracleComp.replicate_zero, eval_pure, PMF.map, Function.comp_def,
      List.ofFn_zero, PMF.bind_const]
  | succ count ih =>
    rw [OracleComp.replicate_succ, eval_bind]
    simp [eval_map, ih, Probability.PMF.pi_fin_succ, PMF.map_bind, PMF.map_comp,
      Function.comp_def, List.ofFn_succ]

/-- Counting successful repeated trials is the sum of independent Boolean indicators. -/
theorem eval_countTrue (count : ℕ) (program : ProbComp Bool) :
    eval (OracleComp.countTrue count program) =
      (Probability.PMF.pi (fun _ : Fin count => eval program)).map
        (fun bits => ∑ i, (bits i).toNat) := by
  rw [OracleComp.countTrue, eval_map, eval_replicate, PMF.map_comp]
  congr 1
  funext bits
  change (List.ofFn bits).count true = ∑ i, (bits i).toNat
  induction count with
  | zero => simp
  | succ count ih =>
    rw [List.ofFn_succ, List.count_cons, ih, Fin.sum_univ_succ]
    cases bits 0 <;> simp [Nat.add_comm]

/-- Every supported result is bounded by the number of trials, including zero trials. -/
theorem countTrue_le (count : ℕ) (program : ProbComp Bool) {successes : ℕ}
    (h : successes ∈ (eval (OracleComp.countTrue count program)).support) : successes ≤ count := by
  rw [OracleComp.countTrue, eval_map, PMF.mem_support_map_iff] at h
  obtain ⟨votes, hvotes, rfl⟩ := h
  exact List.count_le_length.trans_eq ((mem_support_replicate_iff _ _ _).mp hvotes).1

/-- Repeated closed runs use independent uniform seeds, including at count zero. The output
type need not be finite. -/
theorem eval_replicate_of_uniform [Fintype Seed] [Nonempty Seed]
    (count : ℕ) (program : ProbComp α) (evaluate : Seed → α)
    (hlaw : eval program = (PMF.uniformOfFintype Seed).map evaluate) :
    eval (OracleComp.replicate count program) =
      (PMF.uniformOfFintype (Fin count → Seed)).map
        (fun seeds => List.ofFn (fun i => evaluate (seeds i))) := by
  induction count with
  | zero =>
    rw [OracleComp.replicate_zero, eval_pure]
    simp only [List.ofFn_zero, Function.const_def, PMF.map_const]
  | succ count ih =>
    rw [OracleComp.replicate_succ, eval_bind, hlaw]
    simp only [eval_map, ih]
    rw [← Probability.PMF.uniformOfFintype_map_equiv
      (Fin.consEquiv (fun _ : Fin (count + 1) => Seed)), PMF.map_comp,
      ← Probability.PMF.uniformOfFintype_prod]
    simp [PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def, Fin.consEquiv,
      List.ofFn_succ]

/-- One flat uniform bit list supplies independent seeds for every repeated run, including
zero repetitions and zero-width seeds. -/
theorem eval_replicate_of_uniformList (count width : ℕ) (program : ProbComp α)
    (evaluate : List Bool → α)
    (hlaw : eval program = (BitString.uniformList width).map evaluate) :
    eval (OracleComp.replicate count program) =
      (BitString.uniformList (count * width)).map
        (fun tape => (BitString.listRows count width tape).map evaluate) := by
  have hseed : eval program = (PMF.uniformOfFintype (BitString width)).map
      (fun bits => evaluate (List.ofFn bits)) := by
    simpa only [BitString.uniformList, PMF.map_comp, Function.comp_def] using hlaw
  rw [eval_replicate_of_uniform count program _ hseed]
  simpa only [PMF.map_comp, Function.comp_def, List.map_ofFn] using
    (congrArg (PMF.map (List.map evaluate)) (BitString.uniformList_listRows count width)).symm

end ProbComp

end Cslib
