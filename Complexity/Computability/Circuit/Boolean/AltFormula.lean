/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Unbounded
public import Complexity.Computability.Circuit.Formula
public import Complexity.Computability.Circuit.Pi
public import Mathlib.Data.Fintype.Pi
import Complexity.Computability.Circuit.CompositionDepth
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators

/-!
# Alternating formulas

An *alternating formula* of depth `d` over `n` variables is a formula in negation normal form
whose unbounded fan-in AND and OR gates alternate along every path from the root, with `d` gates on
each path and signed inputs at the bottom (`AltFormula n d`): a signed input `(i, s)` reads bit `i`,
negated when `s`. Its root operation is given when it is evaluated (`AltFormula.eval`), and its
size counts the AND and OR gates; signed inputs are free (`AltFormula.size`). This is the model of
constant-depth circuits in which negations are free and only at the inputs.

Substituting signed inputs for the inputs costs nothing (`AltFormula.mapInputs`), and negating
every input computes the negation with the dual root operation (`AltFormula.eval_neg`). Every
function has alternating formulas of depth two of size `2 ^ n + 1` (`AltFormula.exists_depth_two`).
An alternating formula of depth `d` is a circuit over the unbounded fan-in basis of depth at most
`d + 1` with at most `n` more gates, computing the negated inputs first
(`AltFormula.exists_circuit`).

## Main definitions

* `Cslib.Circuits.Boolean.AltFormula`: alternating formulas of a given depth.
* `Cslib.Circuits.Boolean.AltFormula.eval`, `Cslib.Circuits.Boolean.AltFormula.size`: their
  meaning, for a root operation, and their number of gates.

## Main results

* `Cslib.Circuits.Boolean.AltFormula.exists_depth_two`: normal forms as alternating formulas.
* `Cslib.Circuits.Boolean.AltFormula.exists_circuit`: alternating formulas as circuits over the
  unbounded fan-in basis.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Finset

/-- The operation at the root of an alternating formula. -/
inductive AltOp where
  /-- Conjunction. -/
  | and
  /-- Disjunction. -/
  | or
  deriving DecidableEq

/-- De Morgan duality swaps conjunction and disjunction. -/
def AltOp.dual : AltOp → AltOp
  | .and => .or
  | .or => .and

/-- Alternating formulas of depth `d` over `n` variables: signed inputs at depth zero, and a list
of alternating formulas of depth `d` below each gate of depth `d + 1`. -/
abbrev AltFormula (n : ℕ) : ℕ → Type
  | 0 => Fin n × Bool
  | d + 1 => List (AltFormula n d)

namespace AltFormula

variable {n : ℕ}

/-- The number of AND and OR gates; signed inputs are free. -/
def size : {d : ℕ} → AltFormula n d → ℕ
  | 0, _ => 0
  | _ + 1, fs => 1 + (fs.map size).sum

/-- Evaluate an alternating formula with `op` at the root. -/
def eval : {d : ℕ} → AltOp → AltFormula n d → BitString n → Bool
  | 0, _, l, x => l.2.xor (x l.1)
  | _ + 1, .and, fs, x => fs.all fun f => eval .or f x
  | _ + 1, .or, fs, x => fs.any fun f => eval .and f x

/-- Substitute signed inputs for the inputs. This changes no gates. -/
def mapInputs {m : ℕ} (ρ : Fin n → Fin m × Bool) : {d : ℕ} → AltFormula n d → AltFormula m d
  | 0, l => ((ρ l.1).1, l.2.xor (ρ l.1).2)
  | _ + 1, fs => fs.map (mapInputs ρ)

/-- Negate every input; with the dual root operation, this computes the negation
(`AltFormula.eval_neg`). -/
def neg {d : ℕ} (f : AltFormula n d) : AltFormula n d :=
  mapInputs (fun i => (i, true)) f

@[simp] theorem size_mapInputs {m d : ℕ} (ρ : Fin n → Fin m × Bool) (f : AltFormula n d) :
    size (mapInputs ρ f) = size f := by
  induction d with
  | zero => rfl
  | succ d ih => simp [size, mapInputs, List.map_map, Function.comp_def, ih]

theorem eval_mapInputs {m d : ℕ} (ρ : Fin n → Fin m × Bool) (f : AltFormula n d) (op : AltOp)
    (x : BitString m) :
    eval op (mapInputs ρ f) x = eval op f fun i => (ρ i).2.xor (x (ρ i).1) := by
  induction d generalizing op with
  | zero => exact Bool.xor_assoc ..
  | succ d ih =>
    cases op <;> simp [eval, mapInputs, List.all_map, List.any_map, Function.comp_def, ih]

@[simp] theorem size_neg {d : ℕ} (f : AltFormula n d) : size (neg f) = size f :=
  size_mapInputs _ f

/-- **De Morgan's law**: negating every input and dualizing the root operation negates the
value. -/
theorem eval_neg {d : ℕ} (f : AltFormula n d) (op : AltOp) (x : BitString n) :
    eval op.dual (neg f) x = !eval op f x := by
  induction d generalizing op with
  | zero => simp [neg, mapInputs, eval]
  | succ d ih =>
    have hn : neg f = f.map neg := rfl
    have ha (g : AltFormula n d) : eval .and (neg g) x = !eval .or g x := ih g .or
    have ho (g : AltFormula n d) : eval .or (neg g) x = !eval .and g x := ih g .and
    cases op <;> simp [hn, AltOp.dual, eval, List.all_map, List.any_map, Function.comp_def,
      List.not_all_eq_any_not, List.not_any_eq_all_not, ha, ho]

/-! ### Building alternating formulas -/

/-- One gate over a finite family of alternating formulas. -/
noncomputable def gate {d : ℕ} {ι : Type*} [Fintype ι] (fs : ι → AltFormula n d) :
    AltFormula n (d + 1) :=
  univ.toList.map fs

theorem size_gate {d : ℕ} {ι : Type*} [Fintype ι] (fs : ι → AltFormula n d) :
    size (gate fs) = 1 + ∑ i, size (fs i) := by
  simp [gate, size, List.map_map, Finset.sum_map_toList, Function.comp_def]

theorem eval_gate_and {d : ℕ} {ι : Type*} [Fintype ι] (fs : ι → AltFormula n d)
    (x : BitString n) : eval .and (gate fs) x = true ↔ ∀ i, eval .or (fs i) x = true := by
  simp [gate, eval, List.all_map, List.all_eq_true, Function.comp_def]

theorem eval_gate_or {d : ℕ} {ι : Type*} [Fintype ι] (fs : ι → AltFormula n d)
    (x : BitString n) : eval .or (gate fs) x = true ↔ ∃ i, eval .and (fs i) x = true := by
  simp [gate, eval, List.any_map, List.any_eq_true, Function.comp_def]

/-- Merge the roots of a finite family of alternating formulas into one, without adding a gate
layer. -/
noncomputable def merge {d : ℕ} {ι : Type*} [Fintype ι] (fs : ι → AltFormula n (d + 1)) :
    AltFormula n (d + 1) :=
  (univ.toList.map fs).flatten

theorem eval_merge_and {d : ℕ} {ι : Type*} [Fintype ι] (fs : ι → AltFormula n (d + 1))
    (x : BitString n) : eval .and (merge fs) x = true ↔ ∀ i, eval .and (fs i) x = true := by
  simp [merge, eval, List.all_flatten, List.all_map, List.all_eq_true, Function.comp_def]

theorem eval_merge_or {d : ℕ} {ι : Type*} [Fintype ι] (fs : ι → AltFormula n (d + 1))
    (x : BitString n) : eval .or (merge fs) x = true ↔ ∃ i, eval .or (fs i) x = true := by
  simp [merge, eval, List.any_flatten, List.any_map, List.any_eq_true, Function.comp_def]

theorem size_merge_le {d : ℕ} {ι : Type*} [Fintype ι] (fs : ι → AltFormula n (d + 1)) :
    size (merge fs) ≤ 1 + ∑ i, size (fs i) := by
  have h (ls : List (AltFormula n (d + 1))) :
      size (d := d + 1) ls.flatten ≤ 1 + (ls.map size).sum := by
    induction ls with
    | nil => simp [size]
    | cons f ls ih =>
      simp only [List.flatten_cons, size, List.map_append, List.sum_append, List.map_cons,
        List.sum_cons] at *
      omega
  simpa [merge, List.map_map, Function.comp_def, Finset.sum_map_toList] using
    h (univ.toList.map fs)

/-- A constant, as an alternating formula of any depth at least two. -/
def constant (n d : ℕ) (op : AltOp) (b : Bool) : AltFormula n (d + 2) :=
  if b = decide (op = .and) then [] else [[]]

theorem eval_constant (n d : ℕ) (op : AltOp) (b : Bool) (x : BitString n) :
    eval op (constant n d op b) x = b := by
  cases op <;> cases b <;> simp [constant, eval]

theorem size_constant_le (n d : ℕ) (op : AltOp) (b : Bool) : size (constant n d op b) ≤ 2 := by
  cases op <;> cases b <;> simp [constant, size]

/-- The clause excluding exactly the input `y`. -/
noncomputable def excludingClause (y : BitString n) : AltFormula n 1 :=
  gate fun i : Fin n => (i, y i)

theorem eval_excludingClause (y x : BitString n) :
    eval .or (excludingClause y) x = true ↔ x ≠ y := by
  rw [excludingClause, eval_gate_or]
  simp only [eval, Bool.xor_iff_ne]
  constructor
  · rintro ⟨i, hi⟩ h
    exact hi (congrFun h i).symm
  · intro h
    by_contra he
    apply h
    funext i
    have he' : ∀ i, y i = x i := by simpa only [not_exists, not_not] using he
    exact (he' i).symm

theorem size_excludingClause (y : BitString n) : size (excludingClause y) = 1 := by
  rw [excludingClause, size_gate]
  simp [size]

/-- The formula in conjunctive normal form excluding every false input of `f`. -/
noncomputable def cnf (f : BitString n → Bool) : AltFormula n 2 :=
  gate fun y : {y : BitString n // f y = false} => excludingClause y.1

theorem eval_cnf (f : BitString n → Bool) (x : BitString n) : eval .and (cnf f) x = f x := by
  apply Bool.eq_iff_iff.2
  rw [cnf, eval_gate_and]
  simp only [eval_excludingClause]
  constructor
  · intro h
    cases hf : f x with
    | false => exact (h ⟨x, hf⟩ rfl).elim
    | true => rfl
  · intro h y he
    subst x
    exact Bool.noConfusion (h.symm.trans y.2)

theorem size_cnf_le (f : BitString n → Bool) : size (cnf f) ≤ 2 ^ n + 1 := by
  have hc : Fintype.card {y : BitString n // f y = false} ≤ 2 ^ n := by
    simpa using Fintype.card_subtype_le fun y : BitString n => f y = false
  rw [cnf, size_gate]
  simp only [size_excludingClause, sum_const, card_univ, smul_eq_mul, mul_one]
  omega

/-- **Normal forms**: every Boolean function has alternating formulas of depth two, with either
root operation, of size at most `2 ^ n + 1`. -/
theorem exists_depth_two (f : BitString n → Bool) (op : AltOp) :
    ∃ g : AltFormula n 2, size g ≤ 2 ^ n + 1 ∧ ∀ x, eval op g x = f x := by
  cases op with
  | and => exact ⟨cnf f, size_cnf_le f, eval_cnf f⟩
  | or =>
    refine ⟨neg (cnf fun x => !f x), ?_, fun x => ?_⟩
    · simpa only [size_neg] using size_cnf_le fun x => !f x
    · exact (eval_neg _ .and x).trans (by simp [eval_cnf])

/-! ### Alternating formulas as circuits -/

/-- An alternating formula as a formula over the unbounded fan-in basis, on the positive inputs
`0, …, n - 1` followed by the negated inputs `n, …, 2 n - 1`. -/
def toFormula : {d : ℕ} → AltOp → AltFormula n d → Formula Unbounded.signature (n + n)
  | 0, _, l => .input (if l.2 then Fin.natAdd n l.1 else Fin.castAdd n l.1)
  | _ + 1, .and, fs => .gate (.and fs.length) fun j => toFormula .or (fs.get j)
  | _ + 1, .or, fs => .gate (.or fs.length) fun j => toFormula .and (fs.get j)

/-- The positive inputs followed by the negated inputs. -/
def literals (x : BitString n) : BitString (n + n) :=
  Fin.append x fun i => !x i

private theorem decide_forall_get {α : Type*} (l : List α) (p : α → Bool) :
    decide (∀ j : Fin l.length, p (l.get j) = true) = l.all p := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, List.all_eq_true]
  exact ⟨fun h a ha => by obtain ⟨j, rfl⟩ := List.get_of_mem ha; exact h j,
    fun h j => h _ (List.get_mem l j)⟩

private theorem decide_exists_get {α : Type*} (l : List α) (p : α → Bool) :
    decide (∃ j : Fin l.length, p (l.get j) = true) = l.any p := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, List.any_eq_true]
  exact ⟨fun ⟨j, hj⟩ => ⟨_, List.get_mem l j, hj⟩,
    fun ⟨a, ha, hpa⟩ => by obtain ⟨j, rfl⟩ := List.get_of_mem ha; exact ⟨j, hpa⟩⟩

theorem eval_toFormula {d : ℕ} (op : AltOp) (f : AltFormula n d) (x : BitString n) :
    (toFormula op f).eval Unbounded.interpretation (literals x) = eval op f x := by
  induction d generalizing op with
  | zero =>
    obtain ⟨i, s⟩ := f
    cases s
    · simp only [toFormula, Bool.false_eq_true, ↓reduceIte, Formula.eval_input, literals,
        Fin.append_left, eval, Bool.false_xor]
    · simp only [toFormula, ↓reduceIte, Formula.eval_input, literals, Fin.append_right, eval,
        Bool.true_xor]
  | succ d ih =>
    cases op
    · simp only [toFormula, Formula.eval_gate, Unbounded.interpretation_and, ih, eval]
      exact decide_forall_get f fun g => eval .or g x
    · simp only [toFormula, Formula.eval_gate, Unbounded.interpretation_or, ih, eval]
      exact decide_exists_get f fun g => eval .and g x

theorem size_toFormula {d : ℕ} (op : AltOp) (f : AltFormula n d) :
    (toFormula op f).size = size f := by
  induction d generalizing op with
  | zero => rfl
  | succ d ih =>
    have h (g : AltOp) : ∑ j : Fin (List.length f), (toFormula g (f.get j)).size =
        (f.map size).sum := by
      simp only [ih]
      rw [← List.sum_ofFn, List.ofFn_comp', List.ofFn_get]
    cases op <;> simp only [toFormula, Formula.size_gate, h, size] <;> omega

theorem depth_toFormula_le {d : ℕ} (op : AltOp) (f : AltFormula n d) :
    (toFormula op f).depth ≤ d := by
  induction d generalizing op with
  | zero => exact Nat.zero_le _
  | succ d ih =>
    cases op <;> exact Nat.succ_le_succ (Finset.sup_le fun j _ => ih _ _)

/-- The circuit computing the positive and the negated inputs, with one negation gate per
input. -/
def literalsCircuit (n : ℕ) : Circuit Unbounded.signature n (n + n) :=
  (Circuit.wiring _ id).append (Circuit.pi fun i => Circuit.oneGate .not fun _ => i)

theorem eval_literalsCircuit (x : BitString n) :
    (literalsCircuit n).eval Unbounded.interpretation x = literals x := by
  rw [literalsCircuit, Circuit.eval_append, Circuit.eval_pi]
  rfl

theorem size_literalsCircuit (n : ℕ) : (literalsCircuit n).size = n := by
  simp [literalsCircuit]

theorem depth_literalsCircuit_le (n : ℕ) : (literalsCircuit n).depth ≤ 1 :=
  (Circuit.depth_append_le _ _).trans (max_le (by simp)
    (Circuit.depth_pi_le _ fun _ => (Circuit.depth_oneGate _ _).le))

/-- **Alternating formulas are circuits**: an alternating formula of depth `d` computing `f`
with root `op` is a circuit over the unbounded fan-in basis of depth at most `d + 1` with at most
`n` more gates, negating every input first. -/
theorem exists_circuit {d : ℕ} (op : AltOp) (f : AltFormula n d) :
    ∃ c : Circuit Unbounded.signature n 1,
      c.Computes Unbounded.interpretation (single (eval op f)) ∧ c.depth ≤ d + 1 ∧
        c.size = size f + n := by
  refine ⟨(toFormula op f).toCircuit.comp (literalsCircuit n), fun x => ?_, ?_, ?_⟩
  · rw [Circuit.eval_comp, eval_literalsCircuit]
    funext j
    rw [Formula.eval_toCircuit, eval_toFormula]
    rfl
  · refine (Circuit.depth_comp_le _ _).trans ?_
    have h₁ := (Formula.depth_toCircuit_le (toFormula op f)).trans (depth_toFormula_le op f)
    have h₂ := depth_literalsCircuit_le n
    omega
  · rw [Circuit.size_comp, size_literalsCircuit, Formula.size_toCircuit, size_toFormula,
      Nat.add_comm]

end AltFormula

end Cslib.Circuits.Boolean
