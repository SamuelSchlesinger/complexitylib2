/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Arithmetic
public import Complexity.Foundations.Data.MvPolynomial.Hessian
public import Cslib.Computability.Circuit.Simulation
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Algebra.Order.Floor.Div
import Complexity.Computability.Circuit.Program
import Complexity.Computability.Circuit.Simulation
import Complexity.Foundations.LinearAlgebra.Rank

/-!
# Hessian rank bounds multiplication count

At a fixed point, each multiplication adds a symmetrized outer product of gradients to the
span of the previously available Hessians. Its rank is at most two. All wire Hessians lie in
the span of these contributions, so a circuit's output Hessian has rank at most twice its
multiplication count. A shared gate contributes once, however often its value is reused.

The theorem concerns equality of formal polynomials, over a field of any characteristic.
Agreement of polynomial functions on a finite field does not suffice. Constants and additions
are free; every multiplication, including multiplication by a scalar, costs one. Input and
output wiring is free. The program theorem also permits supplied input polynomials whose
Hessians vanish at the chosen point, including arbitrary affine inputs.

This ports the Hessian application of the Algebraic library to the native circuit API.

## Main results

* `Cslib.Circuits.Program.rank_hessian_trace_le`: a bound for every program wire.
* `Cslib.Circuits.Circuit.hessian_rank_le`: output rank is at most twice multiplication count.
* `Cslib.Circuits.Circuit.hessian_rank_ceilDiv_two_le`: half the target's Hessian rank,
  rounded up, lower-bounds the multiplication count of a circuit computing it.

## References

* The source application is `Applications/Hessian.lean` in
  [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*][Schlesinger2026Algebraic].
* [P. Bürgisser, M. Clausen, M. A. Shokrollahi, *Algebraic Complexity
  Theory*][BurgisserClausenShokrollahi1997] for background on arithmetic circuits.
-/

@[expose] public section

namespace Cslib.Circuits

open MvPolynomial

variable {C K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] {n g m : ℕ}

private noncomputable def hessianInteraction (point : ι → K) :
    (op : ArithOp C) → (Fin op.arity → MvPolynomial ι K) → (ι → K) →ₗ[K] (ι → K)
  | .add, _ => 0
  | .const _, _ => 0
  | .mul, args => Matrix.toLin'
      (Matrix.vecMulVec (gradient point (args 0)) (gradient point (args 1)) +
        Matrix.vecMulVec (gradient point (args 1)) (gradient point (args 0)))

private theorem rank_hessianInteraction_le (point : ι → K) (op : ArithOp C)
    (args : Fin op.arity → MvPolynomial ι K) :
    (hessianInteraction point op args).rank ≤ (2 * op.mulCost : ℕ) := by
  have outer (a b : ι → K) : (Matrix.toLin' (Matrix.vecMulVec a b)).rank ≤ 1 := by
    rw [← Matrix.natCast_rank_eq_rank_toLin']
    exact_mod_cast Matrix.rank_vecMulVec_le a b
  cases op with
  | add => simp [hessianInteraction, ArithOp.mulCost]
  | const c => simp [hessianInteraction, ArithOp.mulCost]
  | mul =>
    simpa [hessianInteraction, ArithOp.mulCost, one_add_one_eq_two] using
      (LinearMap.rank_add_le _ _).trans (add_le_add
        (outer (gradient point (args 0)) (gradient point (args 1)))
        (outer (gradient point (args 1)) (gradient point (args 0))))

private theorem Program.hessian_trace_mem_span (p : Program (arithSignature C) n g)
    (constant : C → K) (point : ι → K) (input : Fin n → MvPolynomial ι K)
    (hinput : ∀ i, hessian point (input i) = 0) (w : Wire n g) :
    Matrix.toLin' (hessian point
        (p.trace (arithInterpretationWith C (MvPolynomial.C ∘ constant)) input w)) ∈
      Submodule.span K (Set.range fun k => hessianInteraction point (p.lines k).op
        (fun a => p.trace (arithInterpretationWith C (MvPolynomial.C ∘ constant)) input
          ((p.lines k).wires a))) := by
  let I : Interpretation (arithSignature C) (MvPolynomial ι K) :=
    arithInterpretationWith C (MvPolynomial.C ∘ constant)
  let S := Submodule.span K (Set.range fun k => hessianInteraction point (p.lines k).op
    (fun a => p.trace I input ((p.lines k).wires a)))
  have step (op : ArithOp C) (args : Fin op.arity → MvPolynomial ι K)
      (hargs : ∀ a, Matrix.toLin' (hessian point (args a)) ∈ S)
      (hnew : hessianInteraction point op args ∈ S) :
      Matrix.toLin' (hessian point (I op args)) ∈ S := by
    cases op with
    | add => simpa [I] using S.add_mem (hargs 0) (hargs 1)
    | const c => simp [I]
    | mul =>
      simpa [I, hessian_mul, hessianInteraction] using
        S.add_mem (S.add_mem (S.smul_mem (MvPolynomial.eval point (args 1)) (hargs 0))
          (S.smul_mem (MvPolynomial.eval point (args 0)) (hargs 1))) hnew
  refine p.wire_induction
    (P := fun w => Matrix.toLin' (hessian point (p.trace I input w)) ∈ S)
    (fun i => ?_) (fun k ih => ?_) w
  · simp [hinput]
  · rw [p.trace_gate]
    exact step _ _ ih (Submodule.subset_span ⟨k, rfl⟩)

omit [DecidableEq ι] in
/-- With input Hessians zero at the chosen point, every wire's Hessian rank is at most twice
the number of multiplication gates. Inputs may be arbitrary affine polynomials. -/
theorem Program.rank_hessian_trace_le (p : Program (arithSignature C) n g)
    (constant : C → K) (point : ι → K) (input : Fin n → MvPolynomial ι K)
    (hinput : ∀ i, hessian point (input i) = 0) (w : Wire n g) :
    (hessian point
      (p.trace (arithInterpretationWith C (MvPolynomial.C ∘ constant)) input w)).rank ≤
        2 * p.cost ArithOp.mulCost := by
  classical
  have h := LinearMap.rank_le_sum_of_mem_span _ _ (fun k => 2 * (p.lines k).op.mulCost)
    (p.hessian_trace_mem_span constant point input hinput w)
    (fun k => rank_hessianInteraction_le point (p.lines k).op _)
  rw [← Matrix.natCast_rank_eq_rank_toLin', ← Nat.cast_sum, ← Finset.mul_sum,
    ← p.cost_eq_sum] at h
  exact_mod_cast h

/-- A formal polynomial computed by an arithmetic circuit has Hessian rank at most twice the
number of multiplication gates. This applies separately to every selected output. -/
theorem Circuit.hessian_rank_le (c : Circuit (arithSignature C) n m) (constant : C → K)
    (point : Fin n → K) (j : Fin m) :
    (hessian point
      (c.eval (arithInterpretationWith C (MvPolynomial.C ∘ constant)) X j)).rank ≤
        2 * c.program.cost ArithOp.mulCost :=
  c.program.rank_hessian_trace_le constant point X (hessian_X point) (c.outputs j)

/-- Half the target's Hessian rank, rounded up, lower-bounds the multiplication count.
The computation premise is equality of formal polynomials. -/
theorem Circuit.hessian_rank_ceilDiv_two_le (c : Circuit (arithSignature C) n m)
    (constant : C → K) (point : Fin n → K) (j : Fin m) (polynomial : MvPolynomial (Fin n) K)
    (hcompute : c.eval (arithInterpretationWith C (MvPolynomial.C ∘ constant)) X j = polynomial) :
    (hessian point polynomial).rank ⌈/⌉ 2 ≤ c.program.cost ArithOp.mulCost := by
  apply (ceilDiv_le_iff_le_mul (by decide)).mpr
  rw [← hcompute]
  exact c.hessian_rank_le constant point j

end Cslib.Circuits
