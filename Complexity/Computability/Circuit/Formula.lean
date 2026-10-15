/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Pi
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
included. A formula of depth `d` with operations of arity at most `r` has at most `r ^ d` leaves
(`Formula.leafSize_le_pow_depth`) and, for `r ≥ 2`, fewer than `r ^ d` operation nodes
(`Formula.size_lt_pow_depth`); with `s` operation nodes it has at most `(r - 1) s + 1` leaves
(`Formula.leafSize_le`). A formula is a circuit with one gate for each operation node and at most
its depth (`Formula.toCircuit`). Counting only the leaves labelled by inputs of a set `Y`
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
* `Cslib.Circuits.Formula.bind`: substitution of formulas for the inputs; `Formula.rename`
  renames the inputs, and `Formula.lift` and `Formula.substLast` add an input and substitute for
  it.
* `Cslib.Circuits.Formula.toCircuit`: a formula as a single-output circuit.

## Main results

* `Cslib.Circuits.Formula.map_eval`: evaluation commutes with homomorphisms.
* `Cslib.Circuits.Formula.leafSize_le_pow_depth`, `Cslib.Circuits.Formula.leafSize_le`: leaf size
  under bounded fan-in.
* `Cslib.Circuits.Formula.size_lt_pow_depth`: size under bounded fan-in.
* `Cslib.Circuits.Formula.Computes.toCircuit`, `Cslib.Circuits.Formula.size_toCircuit`,
  `Cslib.Circuits.Formula.depth_toCircuit_le`: a formula is a circuit computing the same function,
  of the same size and at most the same depth.

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

/-- A formula computes `f` exactly when its evaluation is `f`. -/
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

/-- With operations of arity at most `r`, where `2 ≤ r`, a formula of depth `d` has fewer than
`r ^ d` operation nodes. -/
theorem size_lt_pow_depth {r : ℕ} (hr : ∀ op, σ.Arity op ≤ r) (hr₂ : 2 ≤ r) (F : Formula σ n) :
    F.size < r ^ F.depth := by
  induction F with
  | input i => simp
  | gate op args ih =>
    set d := Finset.univ.sup fun j => (args j).depth
    have hd : 1 ≤ r ^ d := Nat.one_le_pow _ _ (by omega)
    have hsum : ∑ j, ((args j).size + 1) ≤ σ.Arity op * r ^ d := by
      calc ∑ j, ((args j).size + 1) ≤ ∑ _j : Fin (σ.Arity op), r ^ d :=
            Finset.sum_le_sum fun j _ => (ih j).trans_le (Nat.pow_le_pow_right (by omega)
              (Finset.le_sup (f := fun j => (args j).depth) (Finset.mem_univ j)))
        _ = σ.Arity op * r ^ d := by simp
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one] at hsum
    rw [size_gate, depth_gate, pow_succ, mul_comm]
    have hk := hr op
    rcases Nat.lt_or_ge (σ.Arity op) 2 with hk₂ | hk₂
    · calc (∑ j, (args j).size) + 1 ≤ r ^ d := by
            obtain h | h : σ.Arity op = 0 ∨ σ.Arity op = 1 := by omega
            · have : σ.Arity op * r ^ d = 0 := by rw [h, zero_mul]
              omega
            · have : σ.Arity op * r ^ d = r ^ d := by rw [h, one_mul]
              omega
        _ < 2 * r ^ d := by omega
        _ ≤ r * r ^ d := Nat.mul_le_mul_right _ hr₂
    · calc (∑ j, (args j).size) + 1 < (∑ j, (args j).size) + σ.Arity op := by omega
        _ ≤ σ.Arity op * r ^ d := hsum
        _ ≤ r * r ^ d := Nat.mul_le_mul_right _ hk

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

/-- The leaves in a set of inputs are at most all leaves. -/
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

/-- A formula without input leaves computes a constant. -/
theorem eval_eq_of_leafSize_eq_zero {F : Formula σ n} (hF : F.leafSize = 0) (I : Interpretation σ U)
    (x y : Fin n → U) : F.eval I x = F.eval I y :=
  DependsOn.empty (by
    simpa using dependsOn_eval_of_leafSizeIn_eq_zero (Y := Finset.univ) (by simpa using hF) I) x y

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

/-! ### Substitution -/

/-- Substitute the formula `s i` for every leaf labelled by input `i`: the bind of formulas as a
free monad. -/
def bind {m : ℕ} : Formula σ n → (Fin n → Formula σ m) → Formula σ m
  | input i, s => s i
  | gate op args, s => gate op fun j => (args j).bind s

variable {m : ℕ}

@[simp] theorem input_bind (i : Fin n) (s : Fin n → Formula σ m) : (input i).bind s = s i :=
  rfl

@[simp] theorem gate_bind (op : σ.Op) (args : Fin (σ.Arity op) → Formula σ n)
    (s : Fin n → Formula σ m) : (gate op args).bind s = gate op fun j => (args j).bind s :=
  rfl

@[simp] theorem eval_bind (I : Interpretation σ U) (F : Formula σ n) (s : Fin n → Formula σ m)
    (x : Fin m → U) : (F.bind s).eval I x = F.eval I fun i => (s i).eval I x := by
  induction F with
  | input i => rfl
  | gate op args ih => simp only [gate_bind, eval_gate, ih]

@[simp] theorem bind_input (F : Formula σ n) : F.bind input = F := by
  induction F with
  | input i => rfl
  | gate op args ih => simp only [gate_bind, ih]

@[simp] theorem bind_assoc {k : ℕ} (F : Formula σ n) (s : Fin n → Formula σ m)
    (t : Fin m → Formula σ k) : (F.bind s).bind t = F.bind fun i => (s i).bind t := by
  induction F with
  | input i => rfl
  | gate op args ih => simp only [gate_bind, ih]

/-- Substituting for each input a formula with at most one leaf does not raise the leaf size. -/
theorem leafSize_bind_le {s : Fin n → Formula σ m} (hs : ∀ i, (s i).leafSize ≤ 1)
    (F : Formula σ n) : (F.bind s).leafSize ≤ F.leafSize := by
  induction F with
  | input i => exact hs i
  | gate op args ih =>
    rw [gate_bind, leafSize_gate, leafSize_gate]
    exact Finset.sum_le_sum fun j _ => ih j

/-- The formula reading input `f i` where `F` reads input `i`. -/
def rename (f : Fin n → Fin m) (F : Formula σ n) : Formula σ m :=
  F.bind fun i => input (f i)

@[simp] theorem eval_rename (I : Interpretation σ U) (f : Fin n → Fin m) (F : Formula σ n)
    (x : Fin m → U) : (F.rename f).eval I x = F.eval I (x ∘ f) := by
  simp [rename, Function.comp_def]

/-- Renaming the inputs keeps the leaf size. -/
@[simp] theorem leafSize_rename (f : Fin n → Fin m) (F : Formula σ n) :
    (F.rename f).leafSize = F.leafSize := by
  induction F with
  | input i => rfl
  | gate op args ih => simp only [rename, gate_bind, leafSize_gate] at ih ⊢; simp only [ih]

@[simp] theorem rename_rename {k : ℕ} (f : Fin n → Fin m) (g : Fin m → Fin k) (F : Formula σ n) :
    (F.rename f).rename g = F.rename (g ∘ f) := by
  simp [rename]

/-- A formula on `n` inputs as one on `n + 1` inputs that ignores the last. -/
def lift (F : Formula σ n) : Formula σ (n + 1) :=
  F.rename Fin.castSucc

/-- `C` with the formula `K` in place of its last input. -/
def substLast (C : Formula σ (n + 1)) (K : Formula σ n) : Formula σ n :=
  C.bind (Fin.snoc (α := fun _ => Formula σ n) input K)

@[simp] theorem eval_lift (I : Interpretation σ U) (F : Formula σ n) (y : Fin (n + 1) → U) :
    F.lift.eval I y = F.eval I fun i => y i.castSucc :=
  eval_rename I _ F y

@[simp] theorem leafSize_lift (F : Formula σ n) : F.lift.leafSize = F.leafSize :=
  leafSize_rename _ F

@[simp] theorem eval_substLast (I : Interpretation σ U) (C : Formula σ (n + 1)) (K : Formula σ n)
    (x : Fin n → U) : (C.substLast K).eval I x = C.eval I (Fin.snoc x (K.eval I x)) := by
  rw [substLast, eval_bind]
  congr 1
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp

@[simp] theorem lift_substLast (F : Formula σ n) (K : Formula σ n) : F.lift.substLast K = F := by
  simp [lift, rename, substLast]

@[simp] theorem input_last_substLast (K : Formula σ n) : (input (Fin.last n)).substLast K = K := by
  simp [substLast]

@[simp] theorem input_castSucc_substLast (i : Fin n) (K : Formula σ n) :
    (input i.castSucc).substLast K = input i := by
  simp [substLast]

/-- Substituting into an operation node substitutes into its arguments. -/
theorem gate_substLast (op : σ.Op) (args : Fin (σ.Arity op) → Formula σ (n + 1))
    (K : Formula σ n) : (gate op args).substLast K = gate op fun j => (args j).substLast K :=
  rfl

/-! ### Formulas as circuits -/

/-- A formula as a circuit: an input leaf is a wire, and an operation node is a gate on the
circuits of its arguments, side by side. -/
def toCircuit : Formula σ n → Circuit σ n 1
  | input i => Circuit.wiring σ fun _ => i
  | gate op args => (Circuit.oneGate op id).comp (Circuit.pi fun a => (args a).toCircuit)

@[simp] theorem eval_toCircuit (I : Interpretation σ U) (F : Formula σ n) (x : Fin n → U)
    (j : Fin 1) : F.toCircuit.eval I x j = F.eval I x := by
  induction F generalizing j with
  | input i => rfl
  | gate op args ih =>
    rw [toCircuit, Circuit.eval_comp, Circuit.eval_oneGate, Circuit.eval_pi, eval_gate]
    exact congrArg (I op) (funext fun a => ih a 0)

/-- The circuit of a formula computes what the formula computes. -/
theorem Computes.toCircuit {I : Interpretation σ U} {F : Formula σ n} {f : (Fin n → U) → U}
    (hF : F.Computes I f) : F.toCircuit.Computes I (single f) := fun x => by
  funext j
  rw [eval_toCircuit, computes_iff.1 hF]
  rfl

/-- The circuit of a formula has one gate for each operation node. -/
@[simp] theorem size_toCircuit (F : Formula σ n) : F.toCircuit.size = F.size := by
  induction F with
  | input i => rfl
  | gate op args ih =>
    rw [toCircuit, Circuit.size_comp, Circuit.size_pi, Circuit.size_oneGate, size_gate]
    simp only [ih]

/-- With costs, the circuit of a formula is no deeper than the formula. -/
theorem depthWith_toCircuit_le (cost : σ.Op → ℕ) (F : Formula σ n) :
    F.toCircuit.depthWith cost ≤ F.depthWith cost := by
  induction F with
  | input i => exact (Circuit.depthWith_le_iff cost _).2 fun _ => le_rfl
  | gate op args ih =>
    rw [toCircuit, depthWith_gate, add_comm]
    exact (Circuit.depthWith_comp_le _ _ _).trans (Nat.add_le_add
      (Circuit.depthWith_oneGate _ _ _).le (Circuit.depthWith_pi_le _ _ fun a => (ih a).trans
        (Finset.le_sup (f := fun a => (args a).depthWith cost) (Finset.mem_univ a))))

/-- The circuit of a formula is no deeper than the formula. -/
theorem depth_toCircuit_le (F : Formula σ n) : F.toCircuit.depth ≤ F.depth := by
  simpa only [Circuit.depthWith_one, depthWith_one] using depthWith_toCircuit_le 1 F

end Formula

end Cslib.Circuits
