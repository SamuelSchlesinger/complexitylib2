/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Computability.Circuit.Homomorphism
public import Cslib.Computability.Circuit.Synthesis
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Piecewise
public import Mathlib.Logic.Function.DependsOn
public import Mathlib.Order.SetNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Defs

/-!
# Formulas

A formula over a signature is a tree of operation symbols with inputs at its leaves, that is, a
circuit in which every gate is read once. It is evaluated under an interpretation like a circuit
(`Formula.eval`). Formulas are the free monad on the polynomial functor of the signature; a
dedicated inductive type gives them readable constructors and structural induction.

The *leaf size* `Formula.leafSize` counts the input leaves, the measure of formula lower bounds
[Jukna, Chapter 6][Jukna2012]. Nullary operations, such as constants, are not counted: constants
can be eliminated from a formula for a nonconstant function, so this changes no lower bound, and
it gives constant functions leaf size zero. `Formula.size` counts the operation nodes, constants
included. A formula with operations of arity at most `r` has at most `r ^ d` leaves at depth `d`
(`Formula.leafSize_le_pow_depth`) and at most `(r - 1) s + 1` leaves with `s` operation nodes
(`Formula.leafSize_le`), and it is a circuit with at most one gate for each operation node
(`Formula.exists_circuit`). Counting only the leaves labelled by inputs of a set `Y`
(`Formula.leafSizeIn`) splits the leaf size among disjoint blocks of inputs
(`Formula.sum_leafSizeIn_le_leafSize`), and a formula with no leaf in `Y` depends only on the
inputs outside `Y` (`Formula.dependsOn_eval_of_leafSizeIn_eq_zero`).

## Main definitions

* `Cslib.Circuits.Formula`: formulas over a signature.
* `Cslib.Circuits.Formula.eval`, `Cslib.Circuits.Formula.Computes`: evaluation.
* `Cslib.Circuits.Formula.leafSize`, `Cslib.Circuits.Formula.size`,
  `Cslib.Circuits.Formula.depth`: the number of input leaves, the number of operation nodes, and
  the depth.
* `Cslib.Circuits.Formula.leafSizeIn`: the number of input leaves in a set of inputs.
* `Cslib.Circuits.Formula.depthWith`: the depth when each operation costs a given number of levels.

## Main results

* `Cslib.Circuits.Formula.map_eval`: evaluation commutes with homomorphisms.
* `Cslib.Circuits.Formula.leafSize_le_pow_depth`, `Cslib.Circuits.Formula.leafSize_le`: leaf size
  under bounded fan-in.
* `Cslib.Circuits.Formula.exists_circuit`: a formula is a circuit of at most the same size.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits

universe v

/-- A formula over the signature `σ` with inputs `Fin n`: an input, or an operation applied to
formulas. -/
inductive Formula (σ : Signature.{v}) (n : ℕ) : Type v where
  /-- An input. -/
  | input (i : Fin n)
  /-- An operation applied to formulas for its arguments. -/
  | gate (op : σ.Op) (args : Fin (σ.Arity op) → Formula σ n)

namespace Formula

variable {σ : Signature.{v}} {n : ℕ} {U V : Type*}

/-- Evaluate a formula under an interpretation. -/
def eval (F : Formula σ n) (I : Interpretation σ U) (x : Fin n → U) : U :=
  match F with
  | input i => x i
  | gate op args => I op fun j => (args j).eval I x

@[simp] theorem eval_input (I : Interpretation σ U) (i : Fin n) (x : Fin n → U) :
    (input i : Formula σ n).eval I x = x i :=
  rfl

@[simp] theorem eval_gate (I : Interpretation σ U) (op : σ.Op)
    (args : Fin (σ.Arity op) → Formula σ n) (x : Fin n → U) :
    (gate op args).eval I x = I op fun j => (args j).eval I x :=
  rfl

/-- Evaluating a formula commutes with a homomorphism. -/
theorem map_eval {I₁ : Interpretation σ U} {I₂ : Interpretation σ V} (h : Homomorphism I₁ I₂)
    (F : Formula σ n) (x : Fin n → U) : h.map (F.eval I₁ x) = F.eval I₂ (h.map ∘ x) := by
  induction F with
  | input i => rfl
  | gate op args ih =>
    rw [eval_gate, h.homomorphic, eval_gate]
    congr 1
    funext j
    exact ih j

/-- A formula computes `f` when it agrees with `f` on every input. -/
def Computes (F : Formula σ n) (I : Interpretation σ U) (f : (Fin n → U) → U) : Prop :=
  ∀ x, F.eval I x = f x

theorem computes_iff {F : Formula σ n} {I : Interpretation σ U} {f : (Fin n → U) → U} :
    F.Computes I f ↔ F.eval I = f :=
  funext_iff.symm

/-- The leaf size: the number of input leaves. Nullary operations, such as constants, are not
counted. -/
def leafSize : Formula σ n → ℕ
  | input _ => 1
  | gate _ args => ∑ j, (args j).leafSize

/-- The number of operation nodes, nullary ones included. -/
def size : Formula σ n → ℕ
  | input _ => 0
  | gate _ args => (∑ j, (args j).size) + 1

/-- The depth: inputs have depth zero, and an operation node is one deeper than its arguments, so
nullary operations have depth one, as gates do in circuits. -/
def depth : Formula σ n → ℕ
  | input _ => 0
  | gate _ args => (Finset.univ.sup fun j => (args j).depth) + 1

@[simp] theorem leafSize_input (i : Fin n) : (input i : Formula σ n).leafSize = 1 :=
  rfl

@[simp] theorem leafSize_gate (op : σ.Op) (args : Fin (σ.Arity op) → Formula σ n) :
    (gate op args).leafSize = ∑ j, (args j).leafSize :=
  rfl

@[simp] theorem size_input (i : Fin n) : (input i : Formula σ n).size = 0 :=
  rfl

@[simp] theorem size_gate (op : σ.Op) (args : Fin (σ.Arity op) → Formula σ n) :
    (gate op args).size = (∑ j, (args j).size) + 1 :=
  rfl

@[simp] theorem depth_input (i : Fin n) : (input i : Formula σ n).depth = 0 :=
  rfl

@[simp] theorem depth_gate (op : σ.Op) (args : Fin (σ.Arity op) → Formula σ n) :
    (gate op args).depth = (Finset.univ.sup fun j => (args j).depth) + 1 :=
  rfl

/-- The operation nodes of a formula, as subformulas: the formula itself if it is an operation
node, followed by the operation nodes of its arguments. -/
def gates : Formula σ n → List (Formula σ n)
  | input _ => []
  | gate op args => gate op args :: (List.ofFn fun j => (args j).gates).flatten

@[simp] theorem gates_input (i : Fin n) : (input i : Formula σ n).gates = [] :=
  rfl

/-- A formula has as many operation nodes as its size. -/
@[simp] theorem length_gates (F : Formula σ n) : F.gates.length = F.size := by
  induction F with
  | input i => rfl
  | gate op args ih =>
    simp only [gates, List.length_cons, List.length_flatten, List.map_ofFn, size_gate]
    rw [Fin.sum_ofFn]
    exact congrArg (· + 1) (Finset.sum_congr rfl fun j _ => ih j)

/-- Inputs are not operation nodes. -/
theorem input_notMem_gates (i : Fin n) (F : Formula σ n) : input i ∉ F.gates := by
  induction F with
  | input j => simp
  | gate op args ih =>
    simp only [gates, List.mem_cons, reduceCtorEq, false_or, List.mem_flatten, List.mem_ofFn]
    rintro ⟨_, ⟨j, rfl⟩, h⟩
    exact ih j h

theorem mem_gates_self (op : σ.Op) (args : Fin (σ.Arity op) → Formula σ n) :
    gate op args ∈ (gate op args).gates :=
  List.mem_cons_self

theorem gates_subset_gates_gate (op : σ.Op) (args : Fin (σ.Arity op) → Formula σ n)
    (j : Fin (σ.Arity op)) : (args j).gates ⊆ (gate op args).gates := fun _ hG =>
  List.mem_cons_of_mem _ (List.mem_flatten.2 ⟨_, List.mem_ofFn.2 ⟨j, rfl⟩, hG⟩)

/-- The operation nodes of an operation node of `F` are operation nodes of `F`. -/
theorem gates_subset_of_mem_gates {G F : Formula σ n} (h : G ∈ F.gates) : G.gates ⊆ F.gates := by
  induction F with
  | input i => simp at h
  | gate op args ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact List.Subset.refl _
    · obtain ⟨_, hl, hG⟩ := List.mem_flatten.1 h
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hl
      exact List.Subset.trans (ih j hG) (gates_subset_gates_gate op args j)

/-- An argument of an operation node of `F` is an input or an operation node of `F`. -/
theorem arg_mem_gates {F : Formula σ n} {op : σ.Op} {args : Fin (σ.Arity op) → Formula σ n}
    (h : gate op args ∈ F.gates) (j : Fin (σ.Arity op)) :
    (∃ i, args j = input i) ∨ args j ∈ F.gates := by
  cases hj : args j with
  | input i => exact Or.inl ⟨i, rfl⟩
  | gate op' args' =>
    refine Or.inr (gates_subset_of_mem_gates h (gates_subset_gates_gate op args j ?_))
    rw [hj]
    exact mem_gates_self op' args'

/-- With operations of arity at most `r`, a formula of depth `d` has at most `r ^ d` leaves. -/
theorem leafSize_le_pow_depth {r : ℕ} (hr : ∀ op, σ.Arity op ≤ r) (F : Formula σ n) :
    F.leafSize ≤ r ^ F.depth := by
  induction F with
  | input i => simp
  | gate op args ih =>
    set d := Finset.univ.sup fun j => (args j).depth
    rw [leafSize_gate, depth_gate, pow_succ]
    calc ∑ j, (args j).leafSize ≤ ∑ j, r ^ (args j).depth := Finset.sum_le_sum fun j _ => ih j
      _ ≤ Fintype.card (Fin (σ.Arity op)) • r ^ d :=
          Finset.sum_le_card_nsmul _ _ _ fun j _ => Nat.pow_le_pow_right
            (Nat.pos_of_ne_zero fun h => absurd (j.isLt.trans_le (hr op)) (by omega))
            (Finset.le_sup (f := fun j => (args j).depth) (Finset.mem_univ j))
      _ ≤ r ^ d * r := by
          rw [Fintype.card_fin, smul_eq_mul, mul_comm]
          exact Nat.mul_le_mul_left _ (hr op)

/-- With operations of arity at most `r`, a formula with `s` operation nodes has at most
`(r - 1) s + 1` leaves. -/
theorem leafSize_le {r : ℕ} (hr : ∀ op, σ.Arity op ≤ r) (F : Formula σ n) :
    F.leafSize ≤ (r - 1) * F.size + 1 := by
  induction F with
  | input i => simp
  | gate op args ih =>
    rw [leafSize_gate, size_gate]
    calc ∑ j, (args j).leafSize ≤ ∑ j, ((r - 1) * (args j).size + 1) :=
          Finset.sum_le_sum fun j _ => ih j
      _ = (r - 1) * ∑ j, (args j).size + σ.Arity op := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
          simp
      _ ≤ (r - 1) * ((∑ j, (args j).size) + 1) + 1 := by
          have := hr op
          rw [Nat.mul_succ]
          omega

/-- The number of input leaves labelled by inputs in `Y`. -/
def leafSizeIn (Y : Finset (Fin n)) : Formula σ n → ℕ
  | input i => if i ∈ Y then 1 else 0
  | gate _ args => ∑ j, (args j).leafSizeIn Y

@[simp] theorem leafSizeIn_input (Y : Finset (Fin n)) (i : Fin n) :
    (input i : Formula σ n).leafSizeIn Y = if i ∈ Y then 1 else 0 :=
  rfl

@[simp] theorem leafSizeIn_gate (Y : Finset (Fin n)) (op : σ.Op)
    (args : Fin (σ.Arity op) → Formula σ n) :
    (gate op args).leafSizeIn Y = ∑ j, (args j).leafSizeIn Y :=
  rfl

/-- Disjoint blocks of inputs share out the leaves. -/
theorem sum_leafSizeIn_le_leafSize {ι : Type*} {s : Finset ι} {Y : ι → Finset (Fin n)}
    (hY : (s : Set ι).PairwiseDisjoint Y) (F : Formula σ n) :
    ∑ i ∈ s, F.leafSizeIn (Y i) ≤ F.leafSize := by
  induction F with
  | input j =>
    simp only [leafSizeIn_input, leafSize_input, ← Finset.card_filter]
    refine Finset.card_le_one.2 fun a ha b hb => ?_
    by_contra hab
    exact Finset.disjoint_left.1 (hY (Finset.mem_filter.1 ha).1 (Finset.mem_filter.1 hb).1 hab)
      (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2
  | gate op args ih =>
    simp only [leafSizeIn_gate, leafSize_gate]
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun j _ => ih j

@[simp] theorem leafSizeIn_univ (F : Formula σ n) : F.leafSizeIn Finset.univ = F.leafSize := by
  induction F with
  | input i => simp
  | gate op args ih => simp [ih]

@[simp] theorem leafSizeIn_empty (F : Formula σ n) : F.leafSizeIn ∅ = 0 := by
  induction F with
  | input i => simp
  | gate op args ih => simp [ih]

theorem leafSizeIn_le_leafSize (Y : Finset (Fin n)) (F : Formula σ n) :
    F.leafSizeIn Y ≤ F.leafSize := by
  simpa using F.sum_leafSizeIn_le_leafSize (s := {Y}) (Y := id) (by simp)

/-- A formula with no leaf in `Y` depends only on the inputs outside `Y`. -/
theorem dependsOn_eval_of_leafSizeIn_eq_zero {Y : Finset (Fin n)} {F : Formula σ n}
    (hF : F.leafSizeIn Y = 0) (I : Interpretation σ U) :
    DependsOn (F.eval I) (↑Y)ᶜ := by
  induction F with
  | input i =>
    have hi : i ∉ Y := by simpa using hF
    exact fun x y h => h i hi
  | gate op args ih =>
    rw [leafSizeIn_gate, Finset.sum_eq_zero_iff] at hF
    intro x y h
    simp only [eval_gate]
    congr 1
    funext j
    exact ih j (hF j (Finset.mem_univ j)) h

/-- A formula with no leaf in `Y` ignores the inputs in `Y`. -/
theorem eval_piecewise_eq_of_leafSizeIn_eq_zero {Y : Finset (Fin n)} {F : Formula σ n}
    (hF : F.leafSizeIn Y = 0) (I : Interpretation σ U) (x x' z : Fin n → U) :
    F.eval I (Y.piecewise x z) = F.eval I (Y.piecewise x' z) :=
  dependsOn_eval_of_leafSizeIn_eq_zero hF I fun i hi => by simp [show i ∉ Y by simpa using hi]

/-- The depth when an operation node costs `cost op` levels instead of one: `depthWith 1` is the
depth, and charging nothing for negations gives the depth of formulas with free negations. -/
def depthWith (cost : σ.Op → ℕ) : Formula σ n → ℕ
  | input _ => 0
  | gate op args => (Finset.univ.sup fun j => (args j).depthWith cost) + cost op

@[simp] theorem depthWith_input (cost : σ.Op → ℕ) (i : Fin n) :
    (input i : Formula σ n).depthWith cost = 0 :=
  rfl

@[simp] theorem depthWith_gate (cost : σ.Op → ℕ) (op : σ.Op)
    (args : Fin (σ.Arity op) → Formula σ n) :
    (gate op args).depthWith cost = (Finset.univ.sup fun j => (args j).depthWith cost) + cost op :=
  rfl

@[simp] theorem depthWith_one (F : Formula σ n) : F.depthWith 1 = F.depth := by
  induction F with
  | input i => rfl
  | gate op args ih => simp [ih]

/-- Cheaper operations give a smaller depth. -/
theorem depthWith_mono {cost cost' : σ.Op → ℕ} (h : ∀ op, cost op ≤ cost' op) (F : Formula σ n) :
    F.depthWith cost ≤ F.depthWith cost' := by
  induction F with
  | input i => rfl
  | gate op args ih =>
    exact Nat.add_le_add (Finset.sup_mono_fun fun j _ => ih j) (h op)

/-- A formula is synthesized with one gate for each operation node. -/
theorem synthesis_eval (I : Interpretation σ U) (F : Formula σ n) :
    Synthesis I (inputs n) {F.eval I} F.size := by
  induction F with
  | input i => exact Synthesis.of_mem ⟨i, rfl⟩
  | gate op args ih => exact Synthesis.gate_of_syntheses op _ _ ih

/-- A formula is a circuit with at most one gate for each operation node. -/
theorem exists_circuit (I : Interpretation σ U) (F : Formula σ n) :
    ∃ c : Circuit σ n 1, c.Computes I (single (F.eval I)) ∧ c.size ≤ F.size :=
  (F.synthesis_eval I).exists_circuit

/-- A function computed by a formula is computed by a circuit with at most one gate for each
operation node. -/
theorem Computes.exists_circuit {F : Formula σ n} {I : Interpretation σ U}
    {f : (Fin n → U) → U} (hF : F.Computes I f) :
    ∃ c : Circuit σ n 1, c.Computes I (single f) ∧ c.size ≤ F.size :=
  computes_iff.1 hF ▸ F.exists_circuit I

end Formula

end Cslib.Circuits
