/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.ConstDepth
public import Complexity.Computability.Circuit.Boolean.Unbounded
public import Complexity.Computability.Circuit.Pi
public import Complexity.Foundations.Data.BitString.Parity
import Complexity.Computability.Circuit.Boolean.Hastad
import Complexity.Computability.Languages.Slice
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# AC⁰ and parity

**AC⁰** is the class of languages decided, at every input length, by circuits of negations and
conjunctions and disjunctions of unbounded fan-in, of polynomial size and constant depth
[Arora and Barak, Chapter 6][AroraBarak09]. By Håstad's theorem
(`Unbounded.two_pow_le_size_of_computes_parity`), **parity is not in AC⁰**
[Arora and Barak, Theorem 14.1][AroraBarak09], [FurstSaxeSipser1984], [Ajtai1983], [Hastad1986].
AC⁰ contains the constant languages and is closed under the Boolean operations, by the small
circuits `constCircuit`, `notCircuit` and `binCircuit`.

## Main definitions

* `Cslib.Circuits.Boolean.Unbounded.AC0`: the class AC⁰.
* `Cslib.Circuits.Boolean.Unbounded.constCircuit`, `notCircuit`, `binCircuit`: a constant, a
  negation, and a gate of two arguments on top of circuits.

## Main results

* `Cslib.Circuits.Boolean.Unbounded.parity_notMem_AC0`: parity is not in AC⁰.
* `Cslib.Circuits.Boolean.Unbounded.AC0.compl`, `AC0.inf`, `AC0.sup`: AC⁰ is closed under the
  Boolean operations.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [M. Furst, J. B. Saxe, M. Sipser, *Parity, circuits, and the polynomial-time
  hierarchy*][FurstSaxeSipser1984]
* [M. Ajtai, *Σ¹₁-formulae on finite structures*][Ajtai1983]
* [J. Håstad, *Almost optimal lower bounds for small depth circuits*][Hastad1986]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Unbounded

open Finset

variable {n : ℕ}

/-! ### AC⁰ -/

/-- **AC⁰**: the languages over `Bool` decided, at every input length, by circuits of negations and
unbounded fan-in conjunctions and disjunctions of polynomially bounded size and constant depth. -/
def AC0 : Set (Language Bool) :=
  ConstDepth interpretation

/-- **Parity is not in AC⁰.** -/
theorem parity_notMem_AC0 : Language.ofSlices parity ∉ AC0 := by
  rintro ⟨d, size, hsize, hC⟩
  -- the size bound at the lengths `s (16 s + 1) ^ d` is a polynomial in `s`
  have hpoly : PolynomiallyBounded fun s => size (s * (16 * s + 1) ^ d) :=
    hsize.comp (by fun_prop)
  obtain ⟨s, hlt, hs⟩ := (hpoly.eventually_lt_two_pow.and (Filter.eventually_ge_atTop 2)).exists
  obtain ⟨C, hCcomp, hCdepth, hCsize⟩ := hC (s * (16 * s + 1) ^ d)
  rw [Language.slice_ofSlices] at hCcomp
  have h := two_pow_le_size_of_computes_parity hCcomp hs
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hCdepth))
  omega

/-! ### Small circuits -/

/-- The constant `b`, as a circuit of one gate: the conjunction or the disjunction of no
arguments. -/
def constCircuit : Bool → Circuit signature n 1
  | true => Circuit.oneGate (Op.and 0 : signature.Op) Fin.elim0
  | false => Circuit.oneGate (Op.or 0 : signature.Op) Fin.elim0

@[simp] theorem eval_constCircuit (b : Bool) (x : BitString n) (j : Fin 1) :
    (constCircuit b).eval interpretation x j = b := by
  cases b <;> simp [constCircuit]

@[simp] theorem size_constCircuit (b : Bool) : (constCircuit (n := n) b).size = 1 := by
  cases b <;> rfl

theorem depth_constCircuit_le (b : Bool) : (constCircuit (n := n) b).depth ≤ 1 := by
  cases b <;> exact (Circuit.depth_oneGate _ _).le

/-- The circuit `C` followed by a negation. -/
def notCircuit (C : Circuit signature n 1) : Circuit signature n 1 :=
  (Circuit.oneGate (σ := signature) Op.not fun _ => 0).comp C

@[simp] theorem eval_notCircuit (C : Circuit signature n 1) (x : BitString n) (j : Fin 1) :
    (notCircuit C).eval interpretation x j = !C.eval interpretation x 0 := by
  rw [notCircuit, Circuit.eval_comp, Circuit.eval_oneGate, interpretation_not]

@[simp] theorem size_notCircuit (C : Circuit signature n 1) : (notCircuit C).size = C.size + 1 := by
  rw [notCircuit, Circuit.size_comp, Circuit.size_oneGate, add_comm]

theorem depth_notCircuit_le (C : Circuit signature n 1) : (notCircuit C).depth ≤ C.depth + 1 := by
  have := (Circuit.depth_oneGate (σ := signature) (n := 1) Op.not fun _ => 0).le
  exact (Circuit.depth_comp_le _ _).trans (by omega)

/-- The circuits `C` and `D` side by side, followed by a gate `op` of two arguments. -/
def binCircuit (op : Op) (h : op.arity = 2) (C D : Circuit signature n 1) :
    Circuit signature n 1 :=
  (Circuit.oneGate (σ := signature) op fun a => Fin.cast h a).comp (C.append D)

/-- The gate of `binCircuit op h C D` applied to the outputs of `C` and `D`. -/
theorem eval_binCircuit (op : Op) (h : op.arity = 2) (C D : Circuit signature n 1)
    (x : BitString n) (j : Fin 1) :
    (binCircuit op h C D).eval interpretation x j = interpretation op fun a =>
      ![C.eval interpretation x 0, D.eval interpretation x 0] (Fin.cast h a) := by
  rw [binCircuit, Circuit.eval_comp, Circuit.eval_oneGate, Circuit.eval_append]
  congr 1
  funext a
  refine Fin.cases ?_ (fun b => ?_) (Fin.cast h a)
  · exact Fin.append_left _ _ 0
  · rw [Subsingleton.elim b 0]
    exact Fin.append_right _ _ 0

@[simp] theorem eval_binCircuit_and (C D : Circuit signature n 1) (x : BitString n) (j : Fin 1) :
    (binCircuit (.and 2) rfl C D).eval interpretation x j =
      (C.eval interpretation x 0 && D.eval interpretation x 0) := by
  rw [eval_binCircuit, interpretation_and]
  simp [Fin.forall_fin_two]

@[simp] theorem eval_binCircuit_or (C D : Circuit signature n 1) (x : BitString n) (j : Fin 1) :
    (binCircuit (.or 2) rfl C D).eval interpretation x j =
      (C.eval interpretation x 0 || D.eval interpretation x 0) := by
  rw [eval_binCircuit, interpretation_or]
  simp [Fin.exists_fin_two]

@[simp] theorem size_binCircuit (op : Op) (h : op.arity = 2) (C D : Circuit signature n 1) :
    (binCircuit op h C D).size = C.size + D.size + 1 := by
  rw [binCircuit, Circuit.size_comp, Circuit.size_append, Circuit.size_oneGate, add_comm]

theorem depth_binCircuit_le (op : Op) (h : op.arity = 2) (C D : Circuit signature n 1) :
    (binCircuit op h C D).depth ≤ max C.depth D.depth + 1 := by
  have := (Circuit.depth_oneGate (σ := signature) op fun a => Fin.cast h a).le
  have := Circuit.depth_append_le C D
  exact (Circuit.depth_comp_le _ _).trans (by omega)

namespace AC0

variable {L M : Language Bool}

/-- The empty language is in AC⁰. -/
theorem zero_mem : (0 : Language Bool) ∈ AC0 :=
  ⟨1, fun _ => 1, by fun_prop, fun _ => ⟨constCircuit false, fun x => by
    funext j
    simp [single], depth_constCircuit_le _, (size_constCircuit _).le⟩⟩

/-- The full language is in AC⁰. -/
theorem top_mem : (⊤ : Language Bool) ∈ AC0 :=
  ⟨1, fun _ => 1, by fun_prop, fun _ => ⟨constCircuit true, fun x => by
    funext j
    simp [single], depth_constCircuit_le _, (size_constCircuit _).le⟩⟩

/-- AC⁰ is closed under complement. -/
theorem compl (hL : L ∈ AC0) : Lᶜ ∈ AC0 := by
  obtain ⟨d, size, hsize, hC⟩ := hL
  refine ⟨d + 1, fun n => size n + 1, by fun_prop, fun n => ?_⟩
  obtain ⟨C, hCc, hCd, hCs⟩ := hC n
  refine ⟨notCircuit C, fun x => ?_, (depth_notCircuit_le C).trans (by omega), by simpa using hCs⟩
  funext j
  simp [single, hCc x]

/-- AC⁰ is closed under intersection. -/
theorem inf (hL : L ∈ AC0) (hM : M ∈ AC0) : L ⊓ M ∈ AC0 := by
  obtain ⟨d, size, hsize, hC⟩ := hL
  obtain ⟨d', size', hsize', hC'⟩ := hM
  refine ⟨max d d' + 1, fun n => size n + size' n + 1, by fun_prop, fun n => ?_⟩
  obtain ⟨C, hCc, hCd, hCs⟩ := hC n
  obtain ⟨D, hDc, hDd, hDs⟩ := hC' n
  refine ⟨binCircuit (.and 2) rfl C D, fun x => ?_, (depth_binCircuit_le _ _ C D).trans (by omega),
    by simp only [size_binCircuit]; omega⟩
  funext j
  simp [single, hCc x, hDc x]

/-- AC⁰ is closed under union. -/
theorem sup (hL : L ∈ AC0) (hM : M ∈ AC0) : L ⊔ M ∈ AC0 := by
  obtain ⟨d, size, hsize, hC⟩ := hL
  obtain ⟨d', size', hsize', hC'⟩ := hM
  refine ⟨max d d' + 1, fun n => size n + size' n + 1, by fun_prop, fun n => ?_⟩
  obtain ⟨C, hCc, hCd, hCs⟩ := hC n
  obtain ⟨D, hDc, hDd, hDs⟩ := hC' n
  refine ⟨binCircuit (.or 2) rfl C D, fun x => ?_, (depth_binCircuit_le _ _ C D).trans (by omega),
    by simp only [size_binCircuit]; omega⟩
  funext j
  simp [single, hCc x, hDc x]

end AC0

end Cslib.Circuits.Boolean.Unbounded
