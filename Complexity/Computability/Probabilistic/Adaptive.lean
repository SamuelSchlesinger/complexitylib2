/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Iteration
public import Complexity.Computability.Probabilistic.PPT
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Probabilistic.CoinTape
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Probability.BitString.List

/-!
# Strict PPT adaptive iteration

A bounded probabilistic loop is strict PPT when its step is strict PPT and one invariant bounds
the encoded size of every reachable state. The same rule proves the final invariant. The step
may capture the original input. Constant-growth and length-nonincreasing variants supply the
size invariant automatically.

Internally, a polynomial-length random tape is split into independent blocks. The total typed
saved-coin evaluator gives a deterministic fold, certified by the existing tidy TM calculus.
Clients supply ordinary programs and invariants, without machines, replay code or decoders.

## Main results

* `Cslib.Probability.IsPPTOn.iterate_spec`: certify efficiency and the final supported invariant.
* `Cslib.Probability.IsPPTOn.iterateWith_spec`: allow the step to capture the original input.
* `Cslib.Probability.IsPPTOn.iterate_of_bounded_growth`, `.iterate_of_length_le`: automatic
  intermediate-size bounds.

## References

Adapted from `Computability/Probabilistic/Adaptive.lean` on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, reusing the tidy fold calculus.
-/

@[expose] public section

namespace Cslib.Probability

open Turing.MultiTapeTM

variable {α State : Type} {input : α ↪ List Bool} {stateEncoding : State ↪ List Bool}

/-- One invariant proves both a polynomial resource bound and the final supported postcondition.
The resource invariant must hold on every possible execution, not just with high probability. -/
theorem IsPPTOn.iterate_spec {initial : α → State} {count : α → ℕ}
    {step : State → ProbComp State}
    (hcount : ComputableTidilyInPolyTime count input encUnary)
    (hinitial : ComputableTidilyInPolyTime initial input stateEncoding)
    (hstep : IsPPTOn stateEncoding stateEncoding step)
    (invariant : α → ℕ → State → Prop) (hbase : ∀ a, invariant a 0 (initial a))
    (hpreserve : ∀ a i state, i < count a → invariant a i state →
      ∀ next ∈ (ProbComp.eval (step state)).support, invariant a (i + 1) next)
    {size : ℕ → ℕ} (hsize : PolynomiallyBounded size)
    (hbound : ∀ a i state, i ≤ count a → invariant a i state →
      (stateEncoding state).length ≤ size (input a).length) :
    IsPPTOn input stateEncoding (fun a => OracleComp.iterate (count a) step (initial a)) ∧
      ∀ a state, state ∈ (ProbComp.eval (OracleComp.iterate (count a) step (initial a))).support →
        invariant a (count a) state := by
  obtain ⟨c, d, evaluate, hevaluate, hsupport, hlaw⟩ := hstep.exists_total_seeded_evaluator
  obtain ⟨cs, ds, hs⟩ := polynomiallyBounded_iff_le.mp hsize
  let bound (a : α) := cs * ((input a).length + 1) ^ ds
  let budget (a : α) := c * (bound a + 1) ^ d
  have hbudgetEff : ComputableTidilyInPolyTime budget input encUnary := by
    dsimp only [budget, bound]
    fun_prop
  have hbudget (a : α) (i : ℕ) (state : State) (hi : i ≤ count a)
      (hinvariant : invariant a i state) :
      c * ((stateEncoding state).length + 1) ^ d ≤ budget a :=
    Nat.mul_le_mul_left c (Nat.pow_le_pow_left
      (Nat.add_le_add_right ((hbound a i state hi hinvariant).trans (hs _)) 1) d)
  have hfold : ComputableTidilyInPolyTime (fun pair : α × List Bool =>
      (BitString.listRows (count pair.1) (budget pair.1) pair.2).foldl evaluate (initial pair.1))
      (encPair input encBits) stateEncoding := by
    have hrows : ComputableTidilyInPolyTime (fun pair : α × List Bool =>
        BitString.listRows (count pair.1) (budget pair.1) pair.2)
        (encPair input encBits) (encList encBits) := by
      have hfirst := ComputableTidilyInPolyTime.fst input encBits
      exact ComputableTidilyInPolyTime.bitsRowsWithInput (hcount.comp hfirst)
        (hbudgetEff.comp hfirst) (ComputableTidilyInPolyTime.snd input encBits)
    have hstart := hinitial.comp (ComputableTidilyInPolyTime.fst input encBits)
    refine (hrows.foldl_spec hstart hevaluate
      (fun pair consumed state => invariant pair.1 consumed.length state)
      (fun pair => hbase pair.1) ?_
      (size := fun n => cs * (n + 1) ^ ds) (by fun_prop) ?_).1
    · intro pair consumed state coins hprefix hinvariant
      have hlength := hprefix.length_le
      simp only [List.length_append, List.length_singleton, BitString.length_listRows] at hlength
      simpa only [List.length_append, List.length_singleton] using
        hpreserve pair.1 consumed.length state (by lia) hinvariant _ (hsupport state coins)
    · intro pair consumed state hprefix hinvariant
      have hlength := hprefix.length_le
      simp only [BitString.length_listRows] at hlength
      have hstate := (hbound pair.1 consumed.length state hlength hinvariant).trans (hs _)
      exact hstate.trans (Nat.mul_le_mul_left cs (Nat.pow_le_pow_left
        (by simp only [length_encPair]; lia) ds))
  let replayed (a : α) : ProbComp State := do
    let coins ← BitString.sampleList (count a * budget a)
    return (BitString.listRows (count a) (budget a) coins).foldl evaluate (initial a)
  have hbits : ComputableTidilyInPolyTime (fun a => count a * budget a) input encUnary :=
    ComputableTidilyInPolyTime.unary_mul.comp (hcount.prod hbudgetEff)
  have hefficient : IsPPTOn input stateEncoding replayed :=
    hbits.sampleList.bind_with hfold.isPPTOn
  refine ⟨hefficient.congr ?_, fun a => ProbComp.iterate_invariant (count a) step (initial a)
    (invariant a) (hbase a) (fun i hi state hinvariant => hpreserve a i state hi hinvariant)⟩
  intro a
  have hjoint := ProbComp.eval_iterate_of_uniform (Seed := BitString (budget a))
    (count a) step (initial a) (fun state bits => evaluate state (List.ofFn bits))
    (invariant a) (hbase a) (fun i hi state hinvariant => hpreserve a i state hi hinvariant)
    (fun i hi state hinvariant => by
      simpa only [BitString.uniformList, PMF.map_comp, Function.comp_def] using
        hlaw state (budget a) (hbudget a i state hi.le hinvariant))
  rw [hjoint]
  have hrows := congrArg (PMF.map (fun rows : List (List Bool) => rows.foldl evaluate (initial a)))
    (BitString.uniformList_listRows (count a) (budget a))
  simpa only [replayed, ProbComp.eval_bind, BitString.eval_sampleList, ProbComp.eval_pure,
    PMF.map_comp, Function.comp_def, ← List.foldl_map, List.map_ofFn, PMF.map,
    PMF.bind_bind, PMF.pure_bind] using hrows

/-- The loop body may capture the original input. The joint step certificate charges for both
that input and the changing state; the client invariant describes only the changing state. -/
theorem IsPPTOn.iterateWith_spec {initial : α → State} {count : α → ℕ}
    {step : α → State → ProbComp State}
    (hcount : ComputableTidilyInPolyTime count input encUnary)
    (hinitial : ComputableTidilyInPolyTime initial input stateEncoding)
    (hstep : IsPPTOn (encPair input stateEncoding) stateEncoding (fun pair => step pair.1 pair.2))
    (invariant : α → ℕ → State → Prop) (hbase : ∀ a, invariant a 0 (initial a))
    (hpreserve : ∀ a i state, i < count a → invariant a i state →
      ∀ next ∈ (ProbComp.eval (step a state)).support, invariant a (i + 1) next)
    {size : ℕ → ℕ} (hsize : PolynomiallyBounded size)
    (hbound : ∀ a i state, i ≤ count a → invariant a i state →
      (stateEncoding state).length ≤ size (input a).length) :
    IsPPTOn input stateEncoding (fun a => OracleComp.iterate (count a) (step a) (initial a)) ∧
      ∀ a state,
        state ∈ (ProbComp.eval (OracleComp.iterate (count a) (step a) (initial a))).support →
        invariant a (count a) state := by
  let packedStep (pair : α × State) : ProbComp (α × State) :=
    (fun next => (pair.1, next)) <$> step pair.1 pair.2
  have hpackedStep : IsPPTOn (encPair input stateEncoding)
      (encPair input stateEncoding) packedStep :=
    hstep.pair (ComputableTidilyInPolyTime.fst input stateEncoding)
  have hstart := ComputableTidilyInPolyTime.id'.prod hinitial
  have hpacked := (IsPPTOn.iterate_spec hcount hstart hpackedStep
    (fun a i pair => pair.1 = a ∧ invariant a i pair.2)
    (fun a => ⟨rfl, hbase a⟩)
    (by
      rintro a i ⟨captured, state⟩ hi ⟨rfl, hstate⟩ next hnext
      simp only [packedStep, ProbComp.eval_map, PMF.mem_support_map_iff] at hnext
      obtain ⟨value, hvalue, rfl⟩ := hnext
      exact ⟨rfl, hpreserve captured i state hi hstate value hvalue⟩)
    (size := fun n => 2 * n + size n + 1) (by fun_prop)
    (by
      rintro a i ⟨captured, state⟩ hi ⟨rfl, hstate⟩
      simp only [length_encPair]
      have := hbound captured i state hi hstate
      lia)).1
  refine ⟨(hpacked.map (ComputableTidilyInPolyTime.snd input stateEncoding)).congr ?_, fun a =>
    ProbComp.iterate_invariant (count a) (step a) (initial a)
      (invariant a) (hbase a) (fun i hi state hinvariant => hpreserve a i state hi hinvariant)⟩
  intro a
  rw [OracleComp.iterate_map (count a) (step a) packedStep (fun state => (a, state))
    (fun _ => rfl) (initial a)]
  simp only [ProbComp.eval_map, PMF.map_comp, Function.comp_def]
  exact PMF.map_id _

/-- A strict PPT step with constant growth can be repeated a polynomial number of times. -/
theorem IsPPTOn.iterate_of_bounded_growth {initial : α → State} {count : α → ℕ}
    {step : State → ProbComp State}
    (hcount : ComputableTidilyInPolyTime count input encUnary)
    (hinitial : ComputableTidilyInPolyTime initial input stateEncoding)
    (hstep : IsPPTOn stateEncoding stateEncoding step)
    {growth : ℕ} (hgrowth : ∀ state next, next ∈ (ProbComp.eval (step state)).support →
      (stateEncoding next).length ≤ (stateEncoding state).length + growth) :
    IsPPTOn input stateEncoding (fun a => OracleComp.iterate (count a) step (initial a)) := by
  obtain ⟨ci, di, hi⟩ := hinitial.polyBounded_length
  obtain ⟨cc, dc, hc⟩ := hcount.polyBounded_length
  simp only [encUnary_apply, List.length_replicate] at hc
  exact (IsPPTOn.iterate_spec hcount hinitial hstep
    (fun a i state => (stateEncoding state).length ≤
      (stateEncoding (initial a)).length + i * growth)
    (by simp)
    (by
      intro a i state _ hinvariant next hnext
      have := hgrowth state next hnext
      nlinarith)
    (size := fun n => ci * (n + 1) ^ di + cc * (n + 1) ^ dc * growth) (by fun_prop)
    (fun a i state hiCount hinvariant => hinvariant.trans
      (Nat.add_le_add (hi a) (Nat.mul_le_mul_right growth (hiCount.trans (hc a)))))).1

/-- Iteration of a step that never increases its encoded state needs no extra size invariant. -/
theorem IsPPTOn.iterate_of_length_le {initial : α → State} {count : α → ℕ}
    {step : State → ProbComp State}
    (hcount : ComputableTidilyInPolyTime count input encUnary)
    (hinitial : ComputableTidilyInPolyTime initial input stateEncoding)
    (hstep : IsPPTOn stateEncoding stateEncoding step)
    (hshrink : ∀ state next, next ∈ (ProbComp.eval (step state)).support →
      (stateEncoding next).length ≤ (stateEncoding state).length) :
    IsPPTOn input stateEncoding (fun a => OracleComp.iterate (count a) step (initial a)) :=
  IsPPTOn.iterate_of_bounded_growth hcount hinitial hstep (growth := 0) (by simpa using hshrink)

end Cslib.Probability
