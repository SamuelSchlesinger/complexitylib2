/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Oracle
public import Complexity.Computability.Complexity.Classes.Oracle.Simulation
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Polynomial time relative to an oracle in polynomial time

An oracle language decided in polynomial time adds nothing to polynomial time: `P^A = P` and
`NP^A = NP` for `A ∈ P` [Arora and Barak, Section 3.4][AroraBarak09].

A computation in polynomial time relative to `A` is the clocked run, with every coin fixed to
`false`, of a finite oracle machine (`Cslib.Probability.IsOraclePPTOn.exists_fin_run_pure_false`).
That run iterates one instruction on finite storage (`Turing.MultiTapePTM.answerStep`), which
answers a query with the decider of `A` on the pending request. Against an oracle computed in
polynomial time the instruction is polynomial-time (`Turing.MultiTapePTM.answerStep_pt`), the
storage grows by a bounded amount per instruction, and the clock is polynomial, so the run is
polynomial-time (`Turing.MultiTapePTM.computableTidilyInPolyTime_run`,
`Cslib.Complexity.ComputableInPolyTimeWithOracle.computableTidilyInPolyTime`).

## Main results

* `Turing.MultiTapePTM.answerStep_pt`: an instruction against a polynomial-time oracle is
  polynomial-time.
* `Turing.MultiTapePTM.computableTidilyInPolyTime_run`: a clocked run against a polynomial-time
  oracle is polynomial-time.
* `Cslib.Complexity.ComputableInPolyTimeWithOracle.computableTidilyInPolyTime`: polynomial time
  relative to an oracle in `P` is polynomial time.
* `Cslib.Complexity.PWithOracle_eq_P`, `Cslib.Complexity.NPWithOracle_eq_NP`: `P^A = P` and
  `NP^A = NP` for `A ∈ P`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib MultiTapeMachine MultiTapeTM

variable {k : ℕ} {Control Operation : Type} [DecidableEq Operation] [Finite Control]
  [Fintype Operation] (machine : MultiTapePTM k Bool Control Operation)

/-- **An instruction against a polynomial-time oracle is polynomial-time.** Against an oracle
answering `[g w]` to a request `w`, with `g` polynomial-time, an instruction is polynomial-time in
the encoded configuration: it either installs `g` of the pending request or is local. -/
theorem answerStep_pt {g : List Bool → Bool} (hg : ComputableTidilyInPolyTime g encBits encBool) :
    ComputableTidilyInPolyTime (machine.answerStep fun q => [g q.2]) encFiniteConfig
      encFiniteConfig := by
  have h : ComputableTidilyInPolyTime (fun cfg => if (machine.pendingQuery cfg).isSome then
      machine.receiveBit (cfg, g (machine.pendingRequest cfg)) else machine.localStep cfg)
      encFiniteConfig encFiniteConfig :=
    ComputableTidilyInPolyTime.cond
      ((ComputableTidilyInPolyTime.of_finite Option.isSome).comp machine.pendingQuery_pt)
      (machine.receiveBit_pt.comp
        (ComputableTidilyInPolyTime.id'.prod (hg.comp machine.pendingRequest_pt)))
      machine.localStep_pt
  exact h.of_enc_eq fun cfg => by rw [answerStep_bit]

omit [Fintype Operation] in
/-- **A clocked run against a polynomial-time oracle is polynomial-time.** Against the oracle
answering `[g w]` to a request `w`, where `g` is polynomial-time, the run with every coin fixed to
`false` under the clock `c * (n + 1) ^ d` is polynomial-time in the encoded input. -/
theorem computableTidilyInPolyTime_run [Finite Operation] {α : Type} {input : α ↪ List Bool}
    {g : List Bool → Bool} (hg : ComputableTidilyInPolyTime g encBits encBool) (c d : ℕ) :
    ComputableTidilyInPolyTime (fun a => OracleComp.interpret (m := Id) (fun q => [g q.2])
      (machine.run (pure false) (fun op word => OracleComp.query (op, word))
        (c * ((input a).length + 1) ^ d) (input a))) input encBits := by
  classical
  let _ := Fintype.ofFinite Operation
  obtain ⟨cf, hcf⟩ := length_encFiniteConfig_le (k := k) (State := Control) (Oracle := Operation)
  have hcount : ComputableTidilyInPolyTime (fun a => c * ((input a).length + 1) ^ d) input
      encUnary :=
    ((ComputableTidilyInPolyTime.unary_eval (Polynomial.C c * (Polynomial.X + 1) ^ d)).comp
      (ComputableTidilyInPolyTime.encoding_length input)).of_enc_eq fun a => by simp
  have hinit : ComputableTidilyInPolyTime
      (fun a => FiniteConfig.init (k := k) (Oracle := Operation) machine.initial (input a))
      input encFiniteConfig :=
    ComputableTidilyInPolyTime.finiteConfig_init (by fun_prop) _
  have hspace (a : α) (i : ℕ) : FiniteConfig.SpaceBound (input a).length i 1
      ((machine.answerStep fun q => [g q.2])^[i]
        (FiniteConfig.init machine.initial (input a))) := by
    induction i with
    | zero => exact FiniteConfig.spaceBound_init _ _ _
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact machine.spaceBound_answerStep g ih
  have hbound : PolyBounded (fun a => (input a).length)
      (fun a => cf * ((input a).length + c * ((input a).length + 1) ^ d + 1 + 1)) :=
    PolyBounded.mono (PolyBounded.of_polynomiallyBounded (fun a => (input a).length)
      (bound := fun L => cf * (L + c * (L + 1) ^ d + 1 + 1)) (by fun_prop)) fun _ => le_rfl
  have hit := ComputableTidilyInPolyTime.iterate hcount hinit (machine.answerStep_pt hg) hbound
    fun a i hi => (hcf _ _ _ _ (hspace a i)).trans (Nat.mul_le_mul_left cf (by omega))
  have hout : ComputableTidilyInPolyTime
      (fun cfg : FiniteConfig k Bool Control Operation => cfg.tapes.output) encFiniteConfig
      encBits := by fun_prop
  exact (hout.comp hit).of_enc_eq fun a => by rw [interpret_run_pure_false]; rfl

end Turing.MultiTapePTM

namespace Cslib.Complexity

open Probability Turing.MultiTapeTM

variable {α β : Type} {enc : α ↪ List Bool} {A : Set (List Bool)}

open Classical in
/-- **Polynomial time relative to an oracle in `P` is polynomial time.** Relative to an oracle
language decided in polynomial time, a function computable in polynomial time relative to it is
computable in polynomial time: every query is answered by running the decider. -/
theorem ComputableInPolyTimeWithOracle.computableTidilyInPolyTime {f : α → β}
    {output : β ↪ List Bool} (hA : A ∈ P encBits)
    (hf : ComputableInPolyTimeWithOracle A f enc output) :
    ComputableTidilyInPolyTime f enc output := by
  obtain ⟨g, hg, hgA⟩ := hA
  have hg' : g = fun w => decide (w ∈ A) := funext fun w =>
    Bool.eq_iff_iff.mpr ⟨fun h => decide_eq_true ((hgA w).mpr h),
      fun h => (hgA w).mp (of_decide_eq_true h)⟩
  subst hg'
  obtain ⟨program, hcert, hprogram⟩ := hf
  obtain ⟨k, m, machine, c, d, hrun⟩ := hcert.exists_fin_run_pure_false
  refine (machine.computableTidilyInPolyTime_run (input := enc) hg c d).of_enc_eq fun a => ?_
  rw [← hprogram a, ← hrun a (languageOracle A)]
  rfl

/-- **`P` relative to an oracle in `P` is `P`.** -/
theorem PWithOracle_eq_P (hA : A ∈ P encBits) (enc : α ↪ List Bool) :
    PWithOracle A enc = P enc :=
  Set.Subset.antisymm (fun _ ⟨f, hf, hL⟩ => ⟨f, hf.computableTidilyInPolyTime hA, hL⟩)
    (P_subset_PWithOracle A enc)

/-- **`NP` relative to an oracle in `P` is `NP`.** -/
theorem NPWithOracle_eq_NP (hA : A ∈ P encBits) (enc : α ↪ List Bool) :
    NPWithOracle A enc = NP enc :=
  Set.Subset.antisymm (fun _ ⟨p, V, hV, hL⟩ => ⟨p, V, hV.computableTidilyInPolyTime hA, hL⟩)
    (NP_subset_NPWithOracle A enc)

end Cslib.Complexity
