/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Hastad
public import Complexity.Computability.Circuit.Depth
public import Complexity.Computability.Circuit.Pi
public import Complexity.Computability.Circuit.Boolean.ConstDepth
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# AC⁰ and parity

**AC⁰** is the class of languages decided, at every input length, by circuits of negations and
conjunctions and disjunctions of unbounded fan-in, of polynomial size and constant depth
[Arora and Barak, Chapter 6][AroraBarak09]. **Parity is not in AC⁰** [FurstSaxeSipser1984],
[Ajtai1983], [Hastad1986]: a circuit of depth `d` for the parity of `n` bits has at least `2 ^ s`
gates whenever `s ≥ 2` and `s (16 s + 1) ^ d ≤ n` (`Circuit.two_pow_le_size_of_computes_parity`),
by the same stages of restrictions as for formulas (`exists_extension_shallow`), now over the gates
of the circuit sorted by depth.

## Main definitions

* `Cslib.Circuits.Boolean.Unbounded.AC0`: the class AC⁰.

## Main results

* `Cslib.Circuits.Circuit.two_pow_le_size_of_computes_parity`: Håstad's theorem
  for circuits.
* `Cslib.Circuits.Boolean.Unbounded.parity_notMem_AC0`: parity is not in AC⁰.
* `Cslib.Circuits.Boolean.Unbounded.AC0.compl`, `AC0.inf`, `AC0.sup`: AC⁰ is closed under the
  Boolean operations.

## References

* [M. Furst, J. B. Saxe, M. Sipser, *Parity, circuits, and the polynomial-time
  hierarchy*][FurstSaxeSipser1984]
* [M. Ajtai, *Σ¹₁-formulae on finite structures*][Ajtai1983]
* [J. Håstad, *Almost optimal lower bounds for small depth circuits*][Hastad1986]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Unbounded

open Finset

variable {n s g : ℕ} {ρ : Restriction n}

/-! ### Circuits -/

/-- The operation and argument functions of gate `k` of a program. -/
def lineGate (p : Program signature n g) (k : Fin g) :
    Σ op : signature.Op, Fin (signature.Arity op) → BitString n → Bool :=
  ⟨(p.lines k).op, fun a x => p.trace interpretation x ((p.lines k).wires a)⟩

/-- Gate `k` computes its operation applied to the functions on its wires. -/
theorem gateFun_lineGate (p : Program signature n g) (k : Fin g) :
    gateFun (lineGate p k) = fun x => p.eval interpretation x k :=
  funext fun x => p.lines_eval interpretation x k

/-- **One stage, for programs.** If every gate of depth at most `j` is shallow under `ρ` and there
are fewer than `2 ^ s` gates, some extension of `ρ` leaving `ℓ` bits free makes every gate of
depth at most `j + 1` shallow. -/
theorem exists_stage_program {p : Program signature n g} (hs : 2 ≤ s) (hg : g < 2 ^ s) {j : ℕ}
    (hρ : ∀ k, p.depths k ≤ j → Shallow s ρ fun x => p.eval interpretation x k) {ℓ : ℕ}
    (hsℓ : s ≤ ℓ) (hℓ : (16 * s + 1) * ℓ ≤ #ρ.free) :
    ∃ ρ' ∈ ρ.extensions ℓ, ∀ k, p.depths k ≤ j + 1 →
      Shallow s ρ' fun x => p.eval interpretation x k := by
  classical
  obtain ⟨ρ', hρ', hgood⟩ := exists_extension_shallow (univ.filter fun k => p.depths k = j + 1)
    (lineGate p) (((card_filter_le _ _).trans_eq (card_fin g)).trans_lt hg) (by omega)
    (fun k hk a => by
      have hdepth := (mem_filter.1 hk).2
      have hlt := p.wireDepths_lines_lt k a
      simp only [lineGate]
      cases hw : (p.lines k).wires a with
      | input i =>
        simp only [Program.trace_input]
        exact shallow_proj hs ρ i
      | gate k' =>
        rw [hw, Program.wireDepths_gateWire] at hlt
        exact hρ k' (by omega)) hsℓ hℓ
  refine ⟨ρ', hρ', fun k hk => ?_⟩
  rcases Nat.lt_or_ge (p.depths k) (j + 1) with hlt | hge
  · exact (hρ k (by omega)).mono (Restriction.mem_extensions.1 hρ').1
  · rw [← gateFun_lineGate]
    exact hgood k (mem_filter.2 ⟨mem_univ k, by omega⟩)

/-- **The stages, for programs.** After `j ≤ d` stages, a restriction leaves `n / (16 s + 1) ^ j`
bits free and makes every gate of depth at most `j` shallow. -/
private theorem exists_restriction_stages_program {p : Program signature n g} (hs : 2 ≤ s)
    (hg : g < 2 ^ s) {d : ℕ} (hn : s * (16 * s + 1) ^ d ≤ n) :
    ∀ j ≤ d, ∃ ρ : Restriction n, #ρ.free = n / (16 * s + 1) ^ j ∧
      ∀ k, p.depths k ≤ j → Shallow s ρ fun x => p.eval interpretation x k
  | 0, _ => ⟨fun _ => none, by simp, fun k hk => absurd hk (by
      have := p.depths_pos k
      omega)⟩
  | j + 1, hj => by
    obtain ⟨ρ, hfree, hρ⟩ := exists_restriction_stages_program hs hg hn j (by omega)
    obtain ⟨ρ', hρ', hgood⟩ := exists_stage_program hs hg hρ
      (le_div_pow_of_mul_pow_le (by omega) hj hn) (hfree ▸ mul_div_pow_succ_le n s j)
    exact ⟨ρ', (Restriction.mem_extensions.1 hρ').2, hgood⟩

/-- **Håstad's theorem** for circuits with unbounded fan-in. A circuit of depth `d` computing the
parity of `n` bits has at least `2 ^ s` gates, for every `s ≥ 2` with `s (16 s + 1) ^ d ≤ n`. -/
theorem _root_.Cslib.Circuits.Circuit.two_pow_le_size_of_computes_parity
    {C : Circuit signature n 1} (hC : C.Computes interpretation (single (parity n))) (hs : 2 ≤ s)
    (hn : s * (16 * s + 1) ^ C.depth ≤ n) : 2 ^ s ≤ C.size := by
  by_contra! hS
  obtain ⟨ρ, hfree, hρ⟩ := exists_restriction_stages_program (p := C.program) hs hS hn C.depth
    le_rfl
  -- the output is shallow at the end
  have hout : Shallow s ρ fun x => C.program.trace interpretation x (C.outputs 0) := by
    cases hw : C.outputs 0 with
    | input i => exact shallow_proj hs ρ i
    | gate k =>
      refine hρ k ?_
      have := C.outputDepths_le_depth 0
      simp only [Circuit.outputDepths, Function.comp_apply, hw,
        Program.wireDepths_gateWire] at this
      exact this
  have heq : (fun x => C.program.trace interpretation x (C.outputs 0)) = parity n :=
    funext fun x => congrFun (hC x) 0
  rw [heq] at hout
  exact not_shallow_parity (hfree ▸ le_div_pow_of_mul_pow_le (by omega) le_rfl hn) hout

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
  have h := Circuit.two_pow_le_size_of_computes_parity hCcomp hs
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
  cases b <;> exact Circuit.depth_oneGate_le _ _

/-- The circuit `C` followed by a negation. -/
def notCircuit (C : Circuit signature n 1) : Circuit signature n 1 :=
  (Circuit.oneGate (σ := signature) Op.not fun _ => 0).comp C

@[simp] theorem eval_notCircuit (C : Circuit signature n 1) (x : BitString n) (j : Fin 1) :
    (notCircuit C).eval interpretation x j = !C.eval interpretation x 0 := by
  rw [notCircuit, Circuit.eval_comp, Circuit.eval_oneGate, interpretation_not]

@[simp] theorem size_notCircuit (C : Circuit signature n 1) : (notCircuit C).size = C.size + 1 := by
  rw [notCircuit, Circuit.size_comp, Circuit.size_oneGate, add_comm]

theorem depth_notCircuit_le (C : Circuit signature n 1) : (notCircuit C).depth ≤ C.depth + 1 := by
  have := Circuit.depth_oneGate_le (σ := signature) (n := 1) Op.not fun _ => 0
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
  have := Circuit.depth_oneGate_le (σ := signature) op fun a => Fin.cast h a
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
