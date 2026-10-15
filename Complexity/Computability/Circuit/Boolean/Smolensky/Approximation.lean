/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Smolensky.Gates
public import Complexity.Computability.Circuit.Depth
public import Complexity.Computability.Circuit.Program

/-!
# Smolensky's approximation of circuits

A circuit of the AC⁰[p] basis of depth `d` agrees with a function of degree at most
`((p - 1) ℓ) ^ d` over `ZMod p` on all but `size · 2 ^ n / 2 ^ ℓ` inputs
(`exists_lowDegree_approx`) [Razborov1987], [Smolensky1987].

The circuit is evaluated on pairs: the true function computed by a wire, and its approximant
(`pairInterpretation`). An operation applied to pairs computes the true function of its arguments
and applies the gate approximator of `exists_gate_approx` chosen for these true arguments to their
approximants. So the approximants multiply degrees by `(p - 1) ℓ` per level of depth, and they are
exact at every input where no gate approximator errs on its true arguments, which leaves at most
`2 ^ n / 2 ^ ℓ` inputs per gate.

## Main results

* `Cslib.Circuits.Boolean.Smolensky.exists_lowDegree_approx`: Smolensky's approximation theorem.

## References

* [A. A. Razborov, *Lower bounds on the size of bounded depth circuits over a complete basis with
  logical addition*][Razborov1987]
* [R. Smolensky, *Algebraic methods in the theory of lower bounds for Boolean circuit
  complexity*][Smolensky1987]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Smolensky

open Finset BitString

variable {p : ℕ} [Fact p.Prime] {n ℓ : ℕ}

/-- The gate approximator chosen by `exists_gate_approx` for an operation whose arguments depend on
the input as `u`. -/
noncomputable def gateApprox (hℓ : 1 ≤ ℓ) (op : ModBasis.signature.Op)
    (u : BitString n → Fin (ModBasis.signature.Arity op) → Bool) :
    (Fin (ModBasis.signature.Arity op) → ZMod p) → ZMod p :=
  Classical.choose (exists_gate_approx (p := p) hℓ op u)

theorem gateApprox_spec (hℓ : 1 ≤ ℓ) (op : ModBasis.signature.Op)
    (u : BitString n → Fin (ModBasis.signature.Arity op) → Bool) :
    (∀ (D : ℕ) (v : Fin (ModBasis.signature.Arity op) → BitString n → ZMod p),
      (∀ k, v k ∈ lowDegree (ZMod p) n D) →
        (fun x => gateApprox hℓ op u fun k => v k x) ∈ lowDegree (ZMod p) n ((p - 1) * ℓ * D)) ∧
      #(univ.filter fun x => gateApprox hℓ op u (fun k => bitVal (ZMod p) (u x k)) ≠
          bitVal (ZMod p) (ModBasis.interpretation p op (u x))) * 2 ^ ℓ ≤ 2 ^ n :=
  Classical.choose_spec (exists_gate_approx (p := p) hℓ op u)

/-- The interpretation on pairs of a true function and its approximant. -/
noncomputable def pairInterpretation (hℓ : 1 ≤ ℓ) :
    Interpretation ModBasis.signature ((BitString n → Bool) × (BitString n → ZMod p)) :=
  fun op args => (fun x => ModBasis.interpretation p op fun a => (args a).1 x,
    fun x => gateApprox hℓ op (fun x a => (args a).1 x) fun a => (args a).2 x)

/-- The inputs as pairs: the input bit and its value in `ZMod p`. -/
def inputPair (i : Fin n) : (BitString n → Bool) × (BitString n → ZMod p) :=
  (fun x => x i, fun x => bitVal (ZMod p) (x i))

variable {g : ℕ} (hℓ : 1 ≤ ℓ) (P : Program ModBasis.signature n g)

/-- The true functions of the pair evaluation are the gate functions of the program. -/
theorem fst_trace_pair (w : Wire n g) (x : BitString n) :
    (P.trace (pairInterpretation (p := p) hℓ) inputPair w).1 x =
      P.trace (ModBasis.interpretation p) x w := by
  -- the first components form a homomorphism to the pointwise interpretation, then evaluate at `x`
  let pointwise : Interpretation ModBasis.signature (BitString n → Bool) :=
    fun op args x => ModBasis.interpretation p op fun a => args a x
  let h₁ : Homomorphism (pairInterpretation (p := p) hℓ) pointwise := ⟨Prod.fst, fun _ _ => rfl⟩
  let h₂ : Homomorphism pointwise (ModBasis.interpretation p) := ⟨fun f => f x, fun _ _ => rfl⟩
  cases w with
  | input i => rfl
  | gate k =>
    have e₁ := congrFun (P.map_eval h₁ inputPair) k
    have e₂ := congrFun (P.map_eval h₂ fun i x => x i) k
    exact (congrFun e₁ x).trans e₂

/-- The pair at a gate is its operation applied to the pairs at its wires. -/
theorem trace_pair_gate (k : Fin g) :
    P.trace (pairInterpretation (p := p) hℓ) inputPair (.gate k) =
      pairInterpretation hℓ (P.lines k).op fun a =>
        P.trace (pairInterpretation hℓ) inputPair ((P.lines k).wires a) :=
  (P.lines_eval (pairInterpretation hℓ) inputPair k).symm

/-- **Degrees of the approximants**: at most `((p - 1) ℓ) ^ depth`. -/
theorem snd_trace_pair_mem (w : Wire n g) :
    (P.trace (pairInterpretation (p := p) hℓ) inputPair w).2 ∈
      lowDegree (ZMod p) n (((p - 1) * ℓ) ^ P.wireDepths w) := by
  have hp := (Fact.out : p.Prime).two_le
  have hbase : 1 ≤ (p - 1) * ℓ := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  refine P.wire_induction (P := fun w => (P.trace (pairInterpretation (p := p) hℓ) inputPair w).2 ∈
    lowDegree (ZMod p) n (((p - 1) * ℓ) ^ P.wireDepths w)) (fun i => ?_) (fun k ih => ?_) w
  · simp only [Program.wireDepths_input, pow_zero]
    exact bitVal_mem_lowDegree i
  · rw [trace_pair_gate, Program.wireDepths_gateWire]
    have hpos := P.depths_pos k
    have hdeg := (gateApprox_spec (p := p) hℓ (P.lines k).op (fun x a =>
      (P.trace (pairInterpretation (p := p) hℓ) inputPair ((P.lines k).wires a)).1 x)).1
      (((p - 1) * ℓ) ^ (P.depths k - 1)) _ fun a => lowDegree_mono
        (Nat.pow_le_pow_right hbase (by have := P.wireDepths_lines_lt k a; omega)) (ih a)
    rw [show P.depths k = (P.depths k - 1) + 1 by omega, pow_succ']
    exact hdeg

/-- The inputs on which the approximator chosen for gate `k` errs on its true arguments. -/
noncomputable def errorSet (k : Fin g) : Finset (BitString n) :=
  univ.filter fun x => gateApprox (p := p) hℓ (P.lines k).op
      (fun x a => (P.trace (pairInterpretation (p := p) hℓ) inputPair ((P.lines k).wires a)).1 x)
      (fun a => bitVal (ZMod p)
        ((P.trace (pairInterpretation (p := p) hℓ) inputPair ((P.lines k).wires a)).1 x)) ≠
    bitVal (ZMod p) (ModBasis.interpretation p (P.lines k).op
      (fun a => (P.trace (pairInterpretation (p := p) hℓ) inputPair ((P.lines k).wires a)).1 x))

theorem card_errorSet_mul_le (k : Fin g) : #(errorSet (p := p) hℓ P k) * 2 ^ ℓ ≤ 2 ^ n :=
  (gateApprox_spec (p := p) hℓ (P.lines k).op _).2

/-- **Exactness of the approximants** where no gate approximator errs. -/
theorem snd_trace_pair_eq {x : BitString n} (hx : ∀ k, x ∉ errorSet (p := p) hℓ P k)
    (w : Wire n g) :
    (P.trace (pairInterpretation (p := p) hℓ) inputPair w).2 x =
      bitVal (ZMod p) ((P.trace (pairInterpretation (p := p) hℓ) inputPair w).1 x) := by
  refine P.wire_induction (P := fun w =>
    (P.trace (pairInterpretation (p := p) hℓ) inputPair w).2 x =
    bitVal (ZMod p) ((P.trace (pairInterpretation (p := p) hℓ) inputPair w).1 x)) (fun i => rfl)
    (fun k ih => ?_) w
  rw [trace_pair_gate]
  have := hx k
  simp only [errorSet, mem_filter, mem_univ, true_and, not_not] at this
  change gateApprox (p := p) hℓ (P.lines k).op _ (fun a => (P.trace
    (pairInterpretation (p := p) hℓ) inputPair ((P.lines k).wires a)).2 x) = _
  simp only [ih]
  exact this

/-- **Smolensky's approximation theorem.** A circuit of the AC⁰[p] basis of depth `d` agrees with a
function of degree at most `((p - 1) ℓ) ^ d` over `ZMod p` on all but `size · 2 ^ n / 2 ^ ℓ`
inputs, for every `ℓ ≥ 1`. -/
theorem exists_lowDegree_approx (hℓ : 1 ≤ ℓ) (C : Circuit ModBasis.signature n 1) :
    ∃ Q ∈ lowDegree (ZMod p) n (((p - 1) * ℓ) ^ C.depth),
      #(univ.filter fun x => Q x ≠ bitVal (ZMod p) (C.eval (ModBasis.interpretation p) x 0)) *
        2 ^ ℓ ≤ C.size * 2 ^ n := by
  classical
  have hp := (Fact.out : p.Prime).two_le
  have hbase : 1 ≤ (p - 1) * ℓ := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  refine ⟨(C.program.trace (pairInterpretation (p := p) hℓ) inputPair (C.outputs 0)).2,
    lowDegree_mono (Nat.pow_le_pow_right hbase (C.outputDepths_le_depth 0))
      (snd_trace_pair_mem hℓ C.program _), ?_⟩
  -- the inputs where the approximant errs are inputs where some gate approximator errs
  have hsub : (univ.filter fun x =>
      (C.program.trace (pairInterpretation (p := p) hℓ) inputPair (C.outputs 0)).2 x ≠
        bitVal (ZMod p) (C.eval (ModBasis.interpretation p) x 0)) ⊆
      univ.biUnion (errorSet hℓ C.program) := fun x hx => by
    rw [mem_filter] at hx
    by_contra hno
    simp only [mem_biUnion, mem_univ, true_and, not_exists] at hno
    exact hx.2 ((snd_trace_pair_eq hℓ C.program hno _).trans (by
      rw [fst_trace_pair]
      rfl))
  calc _ ≤ #(univ.biUnion (errorSet (p := p) hℓ C.program)) * 2 ^ ℓ :=
        Nat.mul_le_mul_right _ (card_le_card hsub)
    _ ≤ (∑ k, #(errorSet (p := p) hℓ C.program k)) * 2 ^ ℓ :=
        Nat.mul_le_mul_right _ card_biUnion_le
    _ ≤ ∑ _k : Fin C.size, 2 ^ n := by
        rw [sum_mul]
        exact sum_le_sum fun k _ => card_errorSet_mul_le hℓ C.program k
    _ = C.size * 2 ^ n := by simp

end Cslib.Circuits.Boolean.Smolensky
