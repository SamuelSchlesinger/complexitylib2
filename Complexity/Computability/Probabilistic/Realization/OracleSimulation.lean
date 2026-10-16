/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Configuration
public import Complexity.Computability.Probabilistic.PPT
public import Complexity.Computability.Machines.Turing.MultiTape.Machine.Finite
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Oracle
import Complexity.Computability.Probabilistic.Finite
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Computability.Probabilistic.Adaptive
import Complexity.Languages.Probabilistic.Simulation
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Mathlib.Tactic.Linarith

/-!
# A certified stateful oracle interpreter

The interpreter retains finite machine storage and the handler's state in one encoded value.
A local step uses the original transition table and a certified closed handler. Each certificate
charges captured input, requests, replies, state and retained configuration storage.

## Main definitions

* `Cslib.Probability.OracleSimulation.step`: a native step with explicit handler state.

## Main results

* `Cslib.Probability.OracleSimulation.isPPTOn_step`: the single-step PPT certificate.
* `Cslib.Probability.OracleSimulation.step_eq_run_interpret`: the exact stateful step law.
* `Cslib.Probability.OracleSimulation.isPPTOn_run`: a bounded run with a state invariant is PPT.

## References

Adapts `Computability/Probabilistic/Realization/OracleSimulation.lean` on the cslib `crypto`
branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8` to the shared interpreter and tidy calculus.
-/

@[expose] public section

namespace Cslib.Probability.OracleSimulation
open _root_.Turing _root_.Turing.MultiTapeMachine _root_.Turing.MultiTapeTM
variable {k : ℕ} {Control Operation α State : Type} [DecidableEq Operation]

/-- Execute one native step, retaining all machine storage and the handler's state. -/
noncomputable def step (machine : MultiTapePTM k Bool Control Operation)
    (handler : α → Operation × List Bool → State → ProbComp (List Bool × State)) (a : α)
    (pair : FiniteConfig k Bool Control Operation × State) :
    ProbComp (FiniteConfig k Bool Control Operation × State) :=
  match pair.1.tapes.state with
  | none => pure pair
  | some control => do
    let coin ← ProbComp.uniform Bool
    match machine.tr control pair.1.tapes.inputSymbol pair.1.tapes.workTapeSymbols
        pair.1.answerSymbols coin with
    | .step action symbol move => pure (pair.1.step action symbol move, pair.2)
    | .query channel next => do
      let (answer, state) ← handler a (channel, (pair.1.channels channel).1) pair.2
      return (pair.1.receive channel next answer, state)

/-- One interpreted step retains the full finite configuration and final handler state. -/
theorem step_eq_run_interpret (machine : MultiTapePTM k Bool Control Operation)
    (handler : α → Operation × List Bool → State → ProbComp (List Bool × State)) (a : α)
    (pair : FiniteConfig k Bool Control Operation × State) :
    step machine handler a pair =
      (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifFin n))
          (handler a))
        (machine.finiteStep
          (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
          (fun op word => ProbOracleComp.query (op, word)) pair.1)).run pair.2 := by
  cases hstate : pair.1.tapes.state with
  | none => simp [step, MultiTapeMachine.finiteStep, hstate]
  | some control =>
    simp only [step, MultiTapeMachine.finiteStep, hstate, bind_pure_comp,
      OracleComp.interpret_bind, StateT.run_bind,
      ProbOracleComp.interpret_sample, OracleComp.run_interpret_lift,
      bind_map_left]
    congr 1
    funext coin
    cases machine.tr control pair.1.tapes.inputSymbol pair.1.tapes.workTapeSymbols
        pair.1.answerSymbols coin <;>
      simp only [OracleComp.interpret_map, OracleComp.interpret_pure,
        ProbOracleComp.interpret_query, StateT.run_map, StateT.run_pure]
    rfl

variable [Finite Control]

/-- A certified stateful handler makes one complete interpreter step PPT. -/
theorem isPPTOn_step [Fintype Operation] {input : α ↪ List Bool}
    {stateEncoding : State ↪ List Bool}
    (machine : MultiTapePTM k Bool Control Operation)
    {handler : α → Operation × List Bool → State → ProbComp (List Bool × State)}
    (hhandler : IsPPTOn
      (encPair input (encPair (encPair (encFinite Operation) encBits) stateEncoding))
      (encPair encBits stateEncoding) (fun pair => handler pair.1 pair.2.1 pair.2.2)) :
    IsPPTOn (encPair input (encPair encFiniteConfig stateEncoding))
      (encPair encFiniteConfig stateEncoding)
      (fun pair => step machine handler pair.1 pair.2) := by
  unfold step
  apply IsPPTOn.finite_cases (tagEncoding := encFinite (Option Control))
    (branch := fun control (pair : α × (FiniteConfig k Bool Control Operation × State)) =>
      match control with
    | none => pure pair.2
    | some control => do
      let coin ← ProbComp.uniform Bool
      match machine.tr control pair.2.1.tapes.inputSymbol pair.2.1.tapes.workTapeSymbols
          pair.2.1.answerSymbols coin with
      | .step action symbol move => pure (pair.2.1.step action symbol move, pair.2.2)
      | .query channel next => do
        let (answer, state) ← handler pair.1 (channel, (pair.2.1.channels channel).1) pair.2.2
        return (pair.2.1.receive channel next answer, state))
  · fun_prop
  · intro control
    cases control with
    | none => fun_prop
    | some control =>
      apply (isPPTOn_uniform_bool _).bind_with
      apply IsPPTOn.finite_cases
        (tag := fun pair : (α × (FiniteConfig k Bool Control Operation × State)) × Bool =>
          (pair.1.2.1.tapes.inputSymbol, pair.1.2.1.tapes.workTapeSymbols,
            pair.1.2.1.answerSymbols, pair.2))
        (tagEncoding := encPair (encFinite (Option Bool))
          (encPair (encFinite (Fin k → Option Bool))
            (encPair (encFinite (Operation → Option Bool)) encBool)))
        (branch := fun symbols (pair : (α × (FiniteConfig k Bool Control Operation × State)) ×
            Bool) =>
          match machine.tr control symbols.1 symbols.2.1 symbols.2.2.1 symbols.2.2.2 with
          | .step action symbol move => pure (pair.1.2.1.step action symbol move, pair.1.2.2)
          | .query channel next => do
            let (answer, state) ←
              handler pair.1.1 (channel, (pair.1.2.1.channels channel).1) pair.1.2.2
            return (pair.1.2.1.receive channel next answer, state))
      · fun_prop
      · rintro ⟨inputSymbol, workSymbols, answerSymbols, coin⟩
        cases machine.tr control inputSymbol workSymbols answerSymbols coin with
        | step action symbol move => fun_prop
        | query channel next =>
          apply IsPPTOn.bind_with (left := encPair encBits stateEncoding)
          · fun_prop
          · fun_prop

/-- A bounded native run with a stateful PPT handler is PPT. A local invariant bounds reply
length and private-state growth; the loop certificate charges all interpreter storage. -/
theorem isPPTOn_run [Finite Operation] {input : α ↪ List Bool}
    {stateEncoding : State ↪ List Bool} (machine : MultiTapePTM k Bool Control Operation)
    {word : α → List Bool} {count : α → ℕ}
    {handler : α → Operation × List Bool → State → ProbComp (List Bool × State)}
    {initial : α → State} (hword : ComputableTidilyInPolyTime word input encBits)
    (hcount : ComputableTidilyInPolyTime count input encUnary)
    (hhandler : IsPPTOn
      (encPair input (encPair (encPair (encFinite Operation) encBits) stateEncoding))
      (encPair encBits stateEncoding) (fun pair => handler pair.1 pair.2.1 pair.2.2))
    (hinitial : ComputableTidilyInPolyTime initial input stateEncoding)
    (invariant : α → State → Prop) (hinit : ∀ a, invariant a (initial a))
    {resources : ℕ → ℕ} (hresources : PolynomiallyBounded resources)
    (hpreserve : ∀ a request state, invariant a state →
      ∀ result ∈ (ProbComp.eval (handler a request state)).support,
        invariant a result.2 ∧
        result.1.length ≤ resources ((input a).length + request.2.length) ∧
        (stateEncoding result.2).length ≤ (stateEncoding state).length +
          resources ((input a).length + request.2.length)) :
    IsPPTOn input (encPair encBits stateEncoding) (fun a =>
      (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifFin n))
          (handler a)) (machine.runOracle (count a) (word a))).run (initial a)) := by
  let _ := Fintype.ofFinite Operation
  obtain ⟨cw, dw, hwordSize⟩ := hword.polyBounded_length
  simp only [encBits_apply] at hwordSize
  obtain ⟨ct, dt, htime⟩ := hcount.polyBounded_length
  simp only [encUnary_apply, List.length_replicate] at htime
  obtain ⟨ci, di, hinitialSize⟩ := hinitial.polyBounded_length
  obtain ⟨cr, dr, hresourceSize⟩ := polynomiallyBounded_iff_le.mp hresources
  obtain ⟨cf, hconfigurationSize⟩ :=
    length_encFiniteConfig_le (k := k) (State := Control) (Oracle := Operation)
  let time (n : ℕ) := ct * (n + 1) ^ dt
  let budget (n : ℕ) := cr * (n + time n + 1) ^ dr
  let start (a : α) := (FiniteConfig.init (k := k) (Oracle := Operation)
    machine.initial (word a), initial a)
  let loopInvariant (a : α) (i : ℕ) (pair : FiniteConfig k Bool Control Operation × State) :=
    FiniteConfig.SpaceBound (word a).length i (budget (input a).length) pair.1 ∧
      invariant a pair.2 ∧ (stateEncoding pair.2).length ≤
        (stateEncoding (initial a)).length + i * budget (input a).length
  have hbudget (a : α) (word : List Bool) (hword : word.length ≤ count a) :
      resources ((input a).length + word.length) ≤ budget (input a).length :=
    (hresourceSize _).trans (Nat.mul_le_mul_left cr (Nat.pow_le_pow_left
      (by have := htime a; dsimp only [time]; lia) dr))
  have hstart : ComputableTidilyInPolyTime start input (encPair encFiniteConfig stateEncoding) := by
    dsimp only [start]
    fun_prop
  have hloop := (IsPPTOn.iterateWith_spec hcount hstart (isPPTOn_step machine hhandler)
    loopInvariant (fun a => ⟨FiniteConfig.spaceBound_init _ _ _, hinit a, by simp [start]⟩)
    (by
      rintro a i ⟨cfg, state⟩ hi ⟨hcfg, hs, hsize⟩ next hnext
      cases hcontrol : cfg.tapes.state with
      | none =>
        simp only [step, hcontrol, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hnext
        subst next
        exact ⟨hcfg.mono le_rfl (Nat.le_succ i) le_rfl, hs, by
          dsimp only at hsize ⊢
          nlinarith⟩
      | some control =>
        simp only [step, hcontrol, ProbComp.eval_bind, PMF.mem_support_bind_iff] at hnext
        obtain ⟨coin, _, hnext⟩ := hnext
        cases haction : machine.tr control cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
            cfg.answerSymbols coin with
        | step action symbol move =>
          simp only [haction, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hnext
          subst next
          exact ⟨hcfg.step action symbol move, hs, by dsimp only at hsize ⊢; nlinarith⟩
        | query channel control =>
          simp only [haction, ProbComp.eval_bind, PMF.mem_support_bind_iff] at hnext
          obtain ⟨⟨answer, state'⟩, hanswer, hnext⟩ := hnext
          simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hnext
          subst next
          obtain ⟨hs', hreply, hgrowth⟩ := hpreserve a _ state hs (answer, state') hanswer
          have hb := hbudget a (cfg.channels channel).1 ((hcfg.query channel).trans hi.le)
          exact ⟨hcfg.receive channel control answer (hreply.trans hb), hs', by
            dsimp only at hsize hgrowth ⊢
            nlinarith⟩)
    (size := fun n => 2 * cf * (cw * (n + 1) ^ dw + time n + budget n + 1) +
      ci * (n + 1) ^ di + time n * budget n + 1) (by dsimp only [time, budget]; fun_prop)
    (by
      rintro a i ⟨cfg, state⟩ hi ⟨hcfg, _, hstate⟩
      have ht : i ≤ time (input a).length := hi.trans (htime a)
      have hf := hconfigurationSize _ _ _ cfg hcfg
      have hs := hinitialSize a
      have hw := hwordSize a
      simp only [length_encPair]
      dsimp only at hstate hw ⊢
      nlinarith)).1
  have hproject : ComputableTidilyInPolyTime
      (fun pair : FiniteConfig k Bool Control Operation × State =>
        (pair.1.tapes.output, pair.2))
      (encPair encFiniteConfig stateEncoding) (encPair encBits stateEncoding) := by fun_prop
  refine (hloop.map hproject).congr ?_
  intro a
  rw [MultiTapePTM.runOracle]
  change _ = ProbComp.eval ((OracleComp.interpret (m := StateT State ProbComp) _
    (MultiTapeMachine.run machine _ _ (count a) (word a))).run (initial a))
  rw [← MultiTapeMachine.finiteRunFrom_init, MultiTapeMachine.finiteRunFrom,
    OracleComp.interpret_map, StateT.run_map, OracleComp.run_interpret_iterate]
  simp only [← step_eq_run_interpret, start]

end Cslib.Probability.OracleSimulation
