/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Data.Finset.Sum
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Ring

/-!
# Fair semi-circuits over the full binary basis

Following [Mishra and Santhanam, Section 2.3][MishraSanthanam2026], a *fair semi-circuit* is an
affine system of equations over `𝔽₂` followed by an acyclic circuit over the full binary basis
`B₂`. Its internal values are *parameters*, *auxiliary variables* and *gates*, all named by
natural numbers. The affine system consists of equations `∑ terms = rhs` in the parameters and
auxiliary variables, each with at most three terms; it is *fair* when every assignment to the
parameters extends to exactly one assignment of the auxiliary variables satisfying all equations
(`SemiCircuit.WellFormed.solvable`, `SemiCircuit.WellFormed.unique`), which is equivalent to the
invertibility of the auxiliary matrix of the source. Each gate applies an arbitrary operation
`Bool → Bool → Bool` to two arguments, each a constant or an internal value with a smaller name,
so the order of names is a topological order. The output is a literal.

Equations are named separately from internal values. A *child* of an internal value `t` is a gate
reading `t` or an equation containing `t` (`SemiCircuit.children`); a gate reading `t` twice is a
single child. The *degree* of `t` is its number of children (`SemiCircuit.deg`).

Rerouting replaces every occurrence of an internal value `v` by a literal
(`SemiCircuit.subst`), absorbing negations into the operations of gates and the right-hand sides
of equations. It preserves the value of every gate and the truth of every equation on assignments
giving `v` the value of the literal (`Gate.eval_subst`, `Equation.holds_subst`), and it changes no
child of any value other than `v` and the target of the literal (`SemiCircuit.children_subst`).

## Main definitions

* `Cslib.Circuits.Boolean.B2.Gate`, `Cslib.Circuits.Boolean.B2.Equation`: gates and equations.
* `Cslib.Circuits.Boolean.B2.SemiCircuit`: semi-circuits, with `SemiCircuit.Consistent`
  assignments, `SemiCircuit.WellFormed`, `SemiCircuit.children`, `SemiCircuit.deg` and
  `SemiCircuit.size`.
* `Cslib.Circuits.Boolean.B2.SemiCircuit.subst`: rerouting an internal value to a literal.

## Main results

* `Cslib.Circuits.Boolean.B2.Gate.eval_subst`, `Cslib.Circuits.Boolean.B2.Equation.holds_subst`:
  rerouting preserves evaluation.
* `Cslib.Circuits.Boolean.B2.SemiCircuit.children_subst`: rerouting changes no other children.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
* [M. G. Find, A. Golovnev, E. A. Hirsch and A. S. Kulikov, *A better-than-3n lower bound for the
  circuit complexity of an explicit function*][FindGolovnevHirschKulikov2016]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.B2

open Finset

/-! ### Arguments, literals, gates and equations -/

/-- An argument of a gate: a constant or the internal value with the given name. -/
inductive Arg where
  /-- A constant. -/
  | const (b : Bool)
  /-- An internal value. -/
  | node (i : ℕ)
  deriving DecidableEq

namespace Arg

/-- The value of an argument under an assignment of the internal values. -/
def eval (val : ℕ → Bool) : Arg → Bool
  | const b => b
  | node i => val i

@[simp] theorem eval_const (val : ℕ → Bool) (b : Bool) : (const b).eval val = b := rfl

@[simp] theorem eval_node (val : ℕ → Bool) (i : ℕ) : (node i).eval val = val i := rfl

/-- The argument `node v` replaced by the argument of the literal `ℓ`. -/
def substArg (a : Arg) (v : ℕ) (target : Arg) : Arg :=
  if a = node v then target else a

/-- Changing the assignment away from the internal values an argument reads keeps its value. -/
theorem eval_congr {a : Arg} {val val' : ℕ → Bool} (h : ∀ i, a = node i → val i = val' i) :
    a.eval val = a.eval val' := by
  cases a with
  | const b => rfl
  | node i => exact h i rfl

end Arg

/-- A literal: an argument, negated when `neg` holds. Outputs and reroutings are literals. -/
structure Lit where
  /-- The argument. -/
  arg : Arg
  /-- Whether the argument is negated. -/
  neg : Bool
  deriving DecidableEq

namespace Lit

/-- The value of a literal. -/
def eval (ℓ : Lit) (val : ℕ → Bool) : Bool :=
  ℓ.arg.eval val ^^ ℓ.neg

/-- The constant literal `b`. -/
def const (b : Bool) : Lit := ⟨.const b, false⟩

/-- The literal `t ⊕ c` of the internal value `t`. -/
def node (t : ℕ) (c : Bool) : Lit := ⟨.node t, c⟩

@[simp] theorem eval_const (b : Bool) (val : ℕ → Bool) : (const b).eval val = b := by
  simp [const, eval]

@[simp] theorem eval_node (t : ℕ) (c : Bool) (val : ℕ → Bool) :
    (node t c).eval val = (val t ^^ c) := rfl

/-- Reroute the internal value `v` in a literal to the literal `ℓ`. -/
def subst (o : Lit) (v : ℕ) (ℓ : Lit) : Lit :=
  if o.arg = .node v then ⟨ℓ.arg, o.neg ^^ ℓ.neg⟩ else o

theorem eval_subst {o : Lit} {v : ℕ} {ℓ : Lit} {val : ℕ → Bool} (h : val v = ℓ.eval val) :
    (o.subst v ℓ).eval val = o.eval val := by
  unfold subst
  split_ifs with ho
  · simp only [eval, ho, Arg.eval_node, h]
    cases ℓ.arg.eval val <;> cases o.neg <;> cases ℓ.neg <;> rfl
  · rfl

end Lit

/-- A gate of the acyclic part: an operation of the full binary basis `B₂` applied to two
arguments. -/
structure Gate where
  /-- The operation of the gate. -/
  op : Bool → Bool → Bool
  /-- The first argument. -/
  left : Arg
  /-- The second argument. -/
  right : Arg

namespace Gate

/-- The value of a gate, given the values of its arguments. -/
def eval (g : Gate) (val : ℕ → Bool) : Bool :=
  g.op (g.left.eval val) (g.right.eval val)

/-- The gate reads the internal value `t`. -/
def Reads (g : Gate) (t : ℕ) : Prop :=
  g.left = .node t ∨ g.right = .node t

instance (g : Gate) : DecidablePred g.Reads :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- A gate's value depends only on the internal values it reads. -/
theorem eval_congr {g : Gate} {val val' : ℕ → Bool} (h : ∀ i, g.Reads i → val i = val' i) :
    g.eval val = g.eval val' := by
  unfold eval
  rw [Arg.eval_congr (a := g.left) (fun i hi => h i (Or.inl hi)),
    Arg.eval_congr (a := g.right) (fun i hi => h i (Or.inr hi))]

/-- The negation absorbed into the operation when the argument `a` is rerouted. -/
def substNeg (a : Arg) (v : ℕ) (ℓ : Lit) : Bool :=
  if a = .node v then ℓ.neg else false

/-- Reroute the internal value `v` to the literal `ℓ`: arguments `node v` read the argument of
`ℓ`, and the negation of `ℓ` is absorbed into the operation. -/
def subst (g : Gate) (v : ℕ) (ℓ : Lit) : Gate where
  op x y := g.op (x ^^ substNeg g.left v ℓ) (y ^^ substNeg g.right v ℓ)
  left := g.left.substArg v ℓ.arg
  right := g.right.substArg v ℓ.arg

theorem eval_substArg {a : Arg} {v : ℕ} {ℓ : Lit} {val : ℕ → Bool} (h : val v = ℓ.eval val) :
    ((a.substArg v ℓ.arg).eval val ^^ substNeg a v ℓ) = a.eval val := by
  unfold Arg.substArg substNeg
  split_ifs with ha
  · rw [ha, Arg.eval_node, h, Lit.eval]
  · simp

/-- Rerouting `v` to a literal with the value of `v` preserves the value of every gate. -/
theorem eval_subst {g : Gate} {v : ℕ} {ℓ : Lit} {val : ℕ → Bool} (h : val v = ℓ.eval val) :
    (g.subst v ℓ).eval val = g.eval val := by
  simp only [eval, subst, eval_substArg h]

theorem substArg_eq_node_of_ne {a : Arg} {v z : ℕ} {target : Arg} (hzv : z ≠ v)
    (hzt : target ≠ .node z) : a.substArg v target = .node z ↔ a = .node z := by
  unfold Arg.substArg
  by_cases ha : a = .node v
  · rw [ite_eq_left ha, ha]
    exact ⟨fun h => absurd h hzt, fun h => absurd (Arg.node.inj h) (Ne.symm hzv)⟩
  · rw [ite_eq_right ha]

theorem eq_node_of_substArg_eq_node {a : Arg} {v z : ℕ} {target : Arg}
    (h : a.substArg v target = .node z) : a = .node z ∨ (a = .node v ∧ target = .node z) := by
  unfold Arg.substArg at h
  by_cases ha : a = .node v
  · rw [ite_eq_left ha] at h; exact Or.inr ⟨ha, h⟩
  · rw [ite_eq_right ha] at h; exact Or.inl h

theorem reads_subst_of_ne {g : Gate} {v : ℕ} {ℓ : Lit} {z : ℕ} (hzv : z ≠ v)
    (hzℓ : ℓ.arg ≠ .node z) : (g.subst v ℓ).Reads z ↔ g.Reads z := by
  unfold Reads subst
  simp only [substArg_eq_node_of_ne hzv hzℓ]

theorem reads_of_reads_subst {g : Gate} {v : ℕ} {ℓ : Lit} {z : ℕ} (h : (g.subst v ℓ).Reads z) :
    g.Reads z ∨ (g.Reads v ∧ ℓ.arg = .node z) := by
  unfold Reads subst at *
  rcases h with h | h <;> rcases eq_node_of_substArg_eq_node h with h' | ⟨h', h''⟩
  · exact Or.inl (Or.inl h')
  · exact Or.inr ⟨Or.inl h', h''⟩
  · exact Or.inl (Or.inr h')
  · exact Or.inr ⟨Or.inr h', h''⟩

end Gate

/-- An equation of the affine system: the sum over `𝔽₂` of the values of its terms is `rhs`. -/
structure Equation where
  /-- The internal values occurring in the equation. -/
  terms : Finset ℕ
  /-- The right-hand side. -/
  rhs : Bool

/-- Add `t` to a set of terms over `𝔽₂`: remove it if present, insert it otherwise. -/
def toggle (s : Finset ℕ) (t : ℕ) : Finset ℕ :=
  if t ∈ s then s.erase t else insert t s

theorem sum_toggle (s : Finset ℕ) (t : ℕ) (val : ℕ → Bool) :
    ∑ i ∈ toggle s t, val i = ∑ i ∈ s, val i + val t := by
  unfold toggle
  split_ifs with ht
  · rw [← Finset.add_sum_erase s val ht, add_comm (val t), add_assoc, BooleanRing.add_self,
      add_zero]
  · rw [Finset.sum_insert ht, add_comm]

theorem mem_toggle {s : Finset ℕ} {t z : ℕ} : z ∈ toggle s t ↔ (z ∈ s ↔ z ≠ t) := by
  unfold toggle
  by_cases hz : z = t
  · subst hz
    split_ifs with ht <;> simp [ht]
  · split_ifs with ht <;> simp [hz]

theorem card_toggle_le (s : Finset ℕ) (t : ℕ) : (toggle s t).card ≤ s.card + 1 := by
  unfold toggle
  split_ifs with h
  · exact (Finset.card_erase_le).trans (Nat.le_succ _)
  · exact Finset.card_insert_le _ _

namespace Equation

/-- The equation holds under an assignment of the internal values. -/
def Holds (E : Equation) (val : ℕ → Bool) : Prop :=
  ∑ i ∈ E.terms, val i = E.rhs

instance (E : Equation) (val : ℕ → Bool) : Decidable (E.Holds val) :=
  inferInstanceAs (Decidable (_ = _))

/-- Reroute the term `v` of an equation to the literal `ℓ`. -/
def subst (E : Equation) (v : ℕ) (ℓ : Lit) : Equation :=
  if v ∈ E.terms then
    match ℓ.arg with
    | .const b => ⟨E.terms.erase v, E.rhs ^^ b ^^ ℓ.neg⟩
    | .node t => ⟨toggle (E.terms.erase v) t, E.rhs ^^ ℓ.neg⟩
  else E

/-- Rerouting `v` to a literal with the value of `v` preserves the truth of every equation. -/
theorem holds_subst {E : Equation} {v : ℕ} {ℓ : Lit} {val : ℕ → Bool}
    (h : val v = ℓ.eval val) : (E.subst v ℓ).Holds val ↔ E.Holds val := by
  unfold subst
  split_ifs with hv
  · unfold Holds
    rw [← Finset.add_sum_erase E.terms val hv, h]
    obtain ⟨a, c⟩ := ℓ
    clear h
    cases a with
    | const b =>
      simp only [Lit.eval, Arg.eval_const]
      generalize ∑ i ∈ E.terms.erase v, val i = S
      generalize E.rhs = r
      revert S r b c; decide
    | node t =>
      simp only [Lit.eval, Arg.eval_node, sum_toggle]
      generalize ∑ i ∈ E.terms.erase v, val i = S
      generalize E.rhs = r
      generalize val t = x
      revert S r x c; decide
  · exact Iff.rfl

theorem mem_subst_of_ne {E : Equation} {v : ℕ} {ℓ : Lit} {z : ℕ} (hzv : z ≠ v)
    (hzℓ : ℓ.arg ≠ .node z) : z ∈ (E.subst v ℓ).terms ↔ z ∈ E.terms := by
  unfold subst
  split_ifs with hv
  · rcases ℓ with ⟨_ | t, c⟩
    · simp [Finset.mem_erase, hzv]
    · have hzt : z ≠ t := fun h => hzℓ (by simp [h])
      simp only [mem_toggle, Finset.mem_erase, ne_eq, hzv, not_false_eq_true, true_and]
      exact ⟨fun h => h.2 hzt, fun h => ⟨fun _ => hzt, fun _ => h⟩⟩
  · exact Iff.rfl

theorem mem_of_mem_subst {E : Equation} {v : ℕ} {ℓ : Lit} {z : ℕ}
    (h : z ∈ (E.subst v ℓ).terms) : z ∈ E.terms ∨ (v ∈ E.terms ∧ ℓ.arg = .node z) := by
  unfold subst at h
  split_ifs at h with hv
  · rcases ℓ with ⟨_ | t, c⟩
    · exact Or.inl (Finset.mem_of_mem_erase h)
    · by_cases hzt : z = t
      · exact Or.inr ⟨hv, by simp [hzt]⟩
      · exact Or.inl (Finset.mem_of_mem_erase ((mem_toggle.1 h).2 hzt))
  · exact Or.inl h

theorem card_subst_le {E : Equation} {v : ℕ} {ℓ : Lit} :
    (E.subst v ℓ).terms.card ≤ E.terms.card := by
  unfold subst
  split_ifs with hv
  · rcases ℓ with ⟨_ | t, c⟩
    · exact Finset.card_erase_le
    · have h := Finset.card_erase_of_mem hv
      have hpos : 0 < E.terms.card := Finset.card_pos.2 ⟨v, hv⟩
      calc (toggle (E.terms.erase v) t).card ≤ (E.terms.erase v).card + 1 :=
            card_toggle_le _ _
        _ = E.terms.card := by omega
  · exact le_rfl

end Equation

/-! ### Semi-circuits -/

/-- A semi-circuit: parameters, auxiliary variables and gates named by natural numbers, the gates
and the equations of the affine system, and an output literal. Only the gates in `gates` and the
equations in `eqns` belong to the semi-circuit; `gate` and `eqn` are arbitrary elsewhere. -/
structure SemiCircuit where
  /-- The parameters. -/
  params : Finset ℕ
  /-- The auxiliary variables of the affine system. -/
  aux : Finset ℕ
  /-- The gates of the acyclic part. -/
  gates : Finset ℕ
  /-- The gate with each name. -/
  gate : ℕ → Gate
  /-- The names of the equations of the affine system. -/
  eqns : Finset ℕ
  /-- The equation with each name. -/
  eqn : ℕ → Equation
  /-- The output. -/
  out : Lit

namespace SemiCircuit

variable (C : SemiCircuit)

/-- The internal values: parameters, auxiliary variables and gates. -/
def live : Finset ℕ :=
  C.params ∪ C.aux ∪ C.gates

/-- All equations of the affine system hold. -/
def EqnsHold (val : ℕ → Bool) : Prop :=
  ∀ e ∈ C.eqns, (C.eqn e).Holds val

/-- Every gate has the value of its operation on its arguments. -/
def GatesHold (val : ℕ → Bool) : Prop :=
  ∀ J ∈ C.gates, val J = (C.gate J).eval val

/-- A consistent assignment of the internal values satisfies every equation and every gate. -/
def Consistent (val : ℕ → Bool) : Prop :=
  C.EqnsHold val ∧ C.GatesHold val

/-- The size: the number of gates plus the number of equations. -/
def size : ℕ :=
  C.gates.card + C.eqns.card

/-- The gates reading `t`. -/
def gateChildren (t : ℕ) : Finset ℕ :=
  C.gates.filter fun J => (C.gate J).Reads t

/-- The equations containing `t`. -/
def eqnChildren (t : ℕ) : Finset ℕ :=
  C.eqns.filter fun e => t ∈ (C.eqn e).terms

/-- The children of `t`: the gates reading it (on the left) and the equations containing it (on
the right). -/
def children (t : ℕ) : Finset (ℕ ⊕ ℕ) :=
  (C.gateChildren t).disjSum (C.eqnChildren t)

/-- The degree of `t`: its number of children. -/
def deg (t : ℕ) : ℕ :=
  (C.children t).card

theorem deg_eq (t : ℕ) : C.deg t = (C.gateChildren t).card + (C.eqnChildren t).card :=
  Finset.card_disjSum _ _

@[simp] theorem inl_mem_children {t J : ℕ} :
    Sum.inl J ∈ C.children t ↔ J ∈ C.gates ∧ (C.gate J).Reads t := by
  simp [children, gateChildren]

@[simp] theorem inr_mem_children {t e : ℕ} :
    Sum.inr e ∈ C.children t ↔ e ∈ C.eqns ∧ t ∈ (C.eqn e).terms := by
  simp [children, eqnChildren]

/-- The constraints of the semi-circuit: its gates (on the left) and equations (on the right). -/
def constraints : Finset (ℕ ⊕ ℕ) :=
  C.gates.disjSum C.eqns

theorem children_subset_constraints (t : ℕ) : C.children t ⊆ C.constraints :=
  Finset.disjSum_mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

/-- A semi-circuit is well formed when its roles are disjoint, gates read constants or internal
values (gates only with smaller names), equations have at most three terms among the parameters and auxiliary
variables, the output reads a constant or an internal value, and the affine system is fair: every
assignment of the parameters extends to a solution, whose auxiliary values are unique. -/
structure WellFormed : Prop where
  disjoint_params_aux : Disjoint C.params C.aux
  disjoint_params_gates : Disjoint C.params C.gates
  disjoint_aux_gates : Disjoint C.aux C.gates
  reads_lt : ∀ J ∈ C.gates, ∀ i ∈ C.gates, (C.gate J).Reads i → i < J
  reads_live : ∀ J ∈ C.gates, ∀ i, (C.gate J).Reads i → i ∈ C.live
  terms_subset : ∀ e ∈ C.eqns, (C.eqn e).terms ⊆ C.params ∪ C.aux
  card_terms_le : ∀ e ∈ C.eqns, (C.eqn e).terms.card ≤ 3
  out_live : ∀ i, C.out.arg = .node i → i ∈ C.live
  solvable : ∀ u : ℕ → Bool, ∃ val, (∀ j ∈ C.params, val j = u j) ∧ C.EqnsHold val
  unique : ∀ val val' : ℕ → Bool, (∀ j ∈ C.params, val j = val' j) → C.EqnsHold val →
    C.EqnsHold val' → ∀ v ∈ C.aux, val v = val' v

/-! ### Rerouting -/

/-- Reroute the internal value `v` to the literal `ℓ` in every gate, equation and the output. -/
def subst (v : ℕ) (ℓ : Lit) : SemiCircuit where
  params := C.params
  aux := C.aux
  gates := C.gates
  gate J := (C.gate J).subst v ℓ
  eqns := C.eqns
  eqn e := (C.eqn e).subst v ℓ
  out := C.out.subst v ℓ

variable {C}

theorem eqnsHold_subst {v : ℕ} {ℓ : Lit} {val : ℕ → Bool} (h : val v = ℓ.eval val) :
    (C.subst v ℓ).EqnsHold val ↔ C.EqnsHold val := by
  unfold EqnsHold
  simp only [subst, Equation.holds_subst h]

theorem gatesHold_subst {v : ℕ} {ℓ : Lit} {val : ℕ → Bool} (h : val v = ℓ.eval val) :
    (C.subst v ℓ).GatesHold val ↔ C.GatesHold val := by
  unfold GatesHold
  simp only [subst, Gate.eval_subst h]

theorem consistent_subst {v : ℕ} {ℓ : Lit} {val : ℕ → Bool} (h : val v = ℓ.eval val) :
    (C.subst v ℓ).Consistent val ↔ C.Consistent val := by
  unfold Consistent
  rw [eqnsHold_subst h, gatesHold_subst h]

/-- Rerouting `v` changes no child of any internal value other than `v` and the target of the
literal. -/
theorem children_subst {v : ℕ} {ℓ : Lit} {z : ℕ} (hzv : z ≠ v) (hzℓ : ℓ.arg ≠ .node z) :
    (C.subst v ℓ).children z = C.children z := by
  ext (J | e)
  · simp only [inl_mem_children]
    exact and_congr_right fun _ => Gate.reads_subst_of_ne hzv hzℓ
  · simp only [inr_mem_children]
    exact and_congr_right fun _ => Equation.mem_subst_of_ne hzv hzℓ

/-- After rerouting `v` to `t`, the children of `t` are among the former children of `t` and
`v`. -/
theorem children_subst_subset (v : ℕ) (ℓ : Lit) (z : ℕ) :
    (C.subst v ℓ).children z ⊆ C.children z ∪ C.children v := by
  intro x hx
  rw [Finset.mem_union]
  rcases x with J | e
  · simp only [inl_mem_children] at hx ⊢
    rcases Gate.reads_of_reads_subst hx.2 with h | ⟨h, _⟩
    · exact Or.inl ⟨hx.1, h⟩
    · exact Or.inr ⟨hx.1, h⟩
  · simp only [inr_mem_children] at hx ⊢
    rcases Equation.mem_of_mem_subst hx.2 with h | ⟨h, _⟩
    · exact Or.inl ⟨hx.1, h⟩
    · exact Or.inr ⟨hx.1, h⟩

theorem constraints_subst (v : ℕ) (ℓ : Lit) : (C.subst v ℓ).constraints = C.constraints := rfl

theorem size_subst (v : ℕ) (ℓ : Lit) : (C.subst v ℓ).size = C.size := rfl


/-! ### Solutions of the affine system -/

theorem Equation.holds_add_add {E : Equation} {val val' val'' : ℕ → Bool} (h : E.Holds val)
    (h' : E.Holds val') (h'' : E.Holds val'') : E.Holds (val + val' + val'') := by
  unfold Equation.Holds at *
  simp only [Pi.add_apply, Finset.sum_add_distrib, h, h', h'']
  generalize E.rhs = r
  revert r; decide

theorem eqnsHold_add_add {val val' val'' : ℕ → Bool} (h : C.EqnsHold val) (h' : C.EqnsHold val')
    (h'' : C.EqnsHold val'') : C.EqnsHold (val + val' + val'') :=
  fun e he => Equation.holds_add_add (h e he) (h' e he) (h'' e he)

theorem eqnsHold_congr {val val' : ℕ → Bool} (hC : C.WellFormed)
    (h : ∀ i ∈ C.params ∪ C.aux, val i = val' i) : C.EqnsHold val ↔ C.EqnsHold val' := by
  unfold EqnsHold Equation.Holds
  refine forall₂_congr fun e he => ?_
  rw [Finset.sum_congr rfl fun i hi => h i (hC.terms_subset e he hi)]

/-- Every assignment of the parameters of a well-formed semi-circuit extends to a consistent
assignment of all internal values: solve the affine system, then evaluate the gates in the order
of their names. -/
theorem WellFormed.exists_consistent (hC : C.WellFormed) (u : ℕ → Bool) :
    ∃ val, (∀ j ∈ C.params, val j = u j) ∧ C.Consistent val := by
  obtain ⟨val₀, hu, heq⟩ := hC.solvable u
  have key : ∀ k, ∃ val, (∀ i, i ∉ C.gates → val i = val₀ i) ∧
      ∀ J ∈ C.gates, J < k → val J = (C.gate J).eval val := by
    intro k
    induction k with
    | zero => exact ⟨val₀, fun _ _ => rfl, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
    | succ k ih =>
      obtain ⟨val, hval, hgate⟩ := ih
      by_cases hk : k ∈ C.gates
      · have heval : ∀ J ∈ C.gates, J ≤ k →
            (C.gate J).eval (Function.update val k ((C.gate k).eval val)) =
              (C.gate J).eval val := fun J hJ hJk => Gate.eval_congr fun i hi =>
          Function.update_of_ne (by
            rintro rfl
            exact absurd (hC.reads_lt J hJ i hk hi) (not_lt.2 hJk)) _ _
        refine ⟨Function.update val k ((C.gate k).eval val), fun i hi => ?_, ?_⟩
        · rw [Function.update_of_ne (by rintro rfl; exact hi hk)]
          exact hval i hi
        · intro J hJ hJk
          rcases (Nat.lt_succ_iff.1 hJk).lt_or_eq with h | rfl
          · rw [heval J hJ h.le, Function.update_of_ne h.ne, hgate J hJ h]
          · rw [heval J hJ le_rfl, Function.update_self]
      · exact ⟨val, hval, fun J hJ hJk => hgate J hJ
          (lt_of_le_of_ne (Nat.lt_succ_iff.1 hJk) (by rintro rfl; exact hk hJ))⟩
  obtain ⟨val, hval, hgate⟩ := key (C.gates.sup id + 1)
  have hng : ∀ i ∈ C.params ∪ C.aux, i ∉ C.gates := by
    intro i hi hg
    rcases Finset.mem_union.1 hi with hi | hi
    · exact Finset.disjoint_left.1 hC.disjoint_params_gates hi hg
    · exact Finset.disjoint_left.1 hC.disjoint_aux_gates hi hg
  refine ⟨val, fun j hj => (hval j (hng j (Finset.mem_union_left _ hj))).trans (hu j hj),
    (eqnsHold_congr hC fun i hi => hval i (hng i hi)).2 heq,
    fun J hJ => hgate J hJ (Nat.lt_succ_of_le (Finset.le_sup (f := id) hJ))⟩

/-- On the solutions of the affine system, the internal value `t` is the affine function
`c + ∑ j ∈ T, u j` of the parameters `u`. -/
def AffineIn (t : ℕ) (c : Bool) (T : Finset ℕ) : Prop :=
  T ⊆ C.params ∧ ∀ val, C.EqnsHold val → val t = c + ∑ j ∈ T, val j

/-- Every parameter is an affine function of the parameters. -/
theorem affineIn_param {x : ℕ} (hx : x ∈ C.params) : C.AffineIn x false {x} :=
  ⟨Finset.singleton_subset_iff.2 hx, fun val _ => by
    rw [Finset.sum_singleton]; cases val x <;> rfl⟩

/-- The indicator bit string of `j`. -/
def indicator (j : ℕ) : ℕ → Bool := fun i => decide (i = j)

theorem sum_indicator (T : Finset ℕ) (j : ℕ) : ∑ i ∈ T, indicator j i = decide (j ∈ T) := by
  have h : ∀ i, indicator j i = if j = i then (1 : Bool) else 0 := fun i => by
    unfold indicator
    split_ifs with hij
    · rw [decide_eq_true hij.symm]; rfl
    · rw [decide_eq_false (Ne.symm hij)]; rfl
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_ite_eq]
  split_ifs with hj
  · rw [decide_eq_true hj]; rfl
  · rw [decide_eq_false hj]; rfl

/-- The affine expression of an internal value in the parameters is unique. -/
theorem AffineIn.unique (hC : C.WellFormed) {t : ℕ} {c c' : Bool} {T T' : Finset ℕ}
    (h : C.AffineIn t c T) (h' : C.AffineIn t c' T') : c = c' ∧ T = T' := by
  have key : ∀ u : ℕ → Bool, c + ∑ j ∈ T, u j = c' + ∑ j ∈ T', u j := by
    intro u
    obtain ⟨val, hu, heq⟩ := hC.solvable u
    rw [← Finset.sum_congr rfl fun j hj => hu j (h.1 hj),
      ← Finset.sum_congr rfl fun j hj => hu j (h'.1 hj), ← h.2 val heq, ← h'.2 val heq]
  have hc : c = c' := by simpa using key 0
  refine ⟨hc, Finset.ext fun j => ?_⟩
  have := key (indicator j)
  rw [sum_indicator, sum_indicator, hc, add_right_inj] at this
  simpa using this

end SemiCircuit

/-! ### Affine functions of finitely many bits -/

/-- A function of bits that depends only on the coordinates in `M` and preserves sums of three
points is affine: a constant plus the sum of the coordinates in some `T ⊆ M`. -/
theorem exists_affine_of_add_add {M : Finset ℕ} {g : (ℕ → Bool) → Bool}
    (hcongr : ∀ u u' : ℕ → Bool, (∀ j ∈ M, u j = u' j) → g u = g u')
    (hadd : ∀ u u' u'' : ℕ → Bool, g (u + u' + u'') = g u + g u' + g u'') :
    ∃ T ⊆ M, ∀ u, g u = g 0 + ∑ j ∈ T, u j := by
  classical
  let e : ℕ → ℕ → Bool := SemiCircuit.indicator
  have hsum : ∀ A : Finset ℕ, g (∑ j ∈ A, e j) = g 0 + ∑ j ∈ A, (g (e j) + g 0) := by
    intro A
    induction A using Finset.induction_on with
    | empty => simp
    | @insert j A hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj]
      have := hadd (e j) (∑ i ∈ A, e i) 0
      rw [add_zero] at this
      rw [this, ih]
      ring
  refine ⟨M.filter fun j => g (e j) + g 0 = true, Finset.filter_subset _ _, fun u => ?_⟩
  have hu : g u = g (∑ j ∈ M.filter (fun j => u j = true), e j) := by
    apply hcongr
    intro i hi
    rw [Finset.sum_apply]
    change u i = ∑ j ∈ M.filter (fun j => u j = true), SemiCircuit.indicator j i
    have : ∀ j, SemiCircuit.indicator j i = SemiCircuit.indicator i j := fun j => by
      simp [SemiCircuit.indicator, eq_comm]
    simp only [this, SemiCircuit.sum_indicator, Finset.mem_filter, hi, true_and]
    cases u i <;> rfl
  rw [hu, hsum]
  congr 1
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  cases u j <;> cases g (e j) + g 0 <;> rfl

namespace SemiCircuit

variable {C : SemiCircuit}

/-- Every auxiliary variable of a well-formed semi-circuit is an affine function of the
parameters on the solutions of the affine system. -/
theorem WellFormed.exists_affineIn (hC : C.WellFormed) {v : ℕ} (hv : v ∈ C.aux) :
    ∃ c T, C.AffineIn v c T := by
  classical
  let sol : (ℕ → Bool) → ℕ → Bool := fun u => (hC.solvable u).choose
  have hsol : ∀ u, (∀ j ∈ C.params, sol u j = u j) ∧ C.EqnsHold (sol u) :=
    fun u => (hC.solvable u).choose_spec
  have hval : ∀ val, C.EqnsHold val → val v = sol val v := fun val hval =>
    hC.unique _ _ (fun j hj => ((hsol val).1 j hj).symm) hval (hsol val).2 v hv
  obtain ⟨T, hT, hg⟩ := exists_affine_of_add_add (M := C.params) (g := fun u => sol u v)
    (fun u u' h => hC.unique _ _ (fun j hj => by rw [(hsol u).1 j hj, (hsol u').1 j hj, h j hj])
      (hsol u).2 (hsol u').2 v hv)
    (fun u u' u'' => by
      have := hC.unique (sol (u + u' + u'')) (sol u + sol u' + sol u'')
        (fun j hj => by simp only [Pi.add_apply, (hsol _).1 j hj])
        (hsol _).2 (eqnsHold_add_add (hsol u).2 (hsol u').2 (hsol u'').2) v hv
      simpa using this)
  exact ⟨sol 0 v, T, hT, fun val hv' => by rw [hval val hv', hg]⟩

/-- An auxiliary variable can depend only on parameters occurring in the affine system. -/
theorem AffineIn.mem_terms {t : ℕ} {c : Bool} {T : Finset ℕ} (hC : C.WellFormed)
    (h : C.AffineIn t c T) (ht : t ∉ C.params) {x : ℕ} (hx : x ∈ T) :
    ∃ e ∈ C.eqns, x ∈ (C.eqn e).terms := by
  by_contra hne
  push Not at hne
  obtain ⟨val, -, heq⟩ := hC.solvable 0
  have hxp := h.1 hx
  have hupd : ∀ i, i ≠ x → Function.update val x (!val x) i = val i :=
    fun i hi => Function.update_of_ne hi _ _
  have heq' : C.EqnsHold (Function.update val x (!val x)) := by
    intro e he
    unfold Equation.Holds
    rw [Finset.sum_congr rfl fun i hi => hupd i (by rintro rfl; exact hne e he hi)]
    exact heq e he
  have h1 := h.2 _ heq'
  rw [hupd t (by rintro rfl; exact ht hxp), h.2 val heq, ← Finset.add_sum_erase T _ hx,
    ← Finset.add_sum_erase T _ hx, Function.update_self,
    Finset.sum_congr rfl fun i hi => hupd i (Finset.ne_of_mem_erase hi)] at h1
  cases val x <;> simp at h1

/-- A parameter occurring in the affine system is a summand of some auxiliary variable. -/
theorem exists_affineIn_of_mem_terms (hC : C.WellFormed) {x e : ℕ} (hx : x ∈ C.params)
    (he : e ∈ C.eqns) (hxe : x ∈ (C.eqn e).terms) :
    ∃ Q ∈ C.aux, ∃ c T, C.AffineIn Q c T ∧ x ∈ T := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨val, -, heq⟩ := hC.solvable 0
  obtain ⟨val', hval', heq'⟩ := hC.solvable (Function.update val x (!val x))
  have hagree : ∀ i ∈ (C.eqn e).terms, i ≠ x → val i = val' i := by
    intro i hi hix
    rcases Finset.mem_union.1 (hC.terms_subset e he hi) with hi | hi
    · rw [hval' i hi, Function.update_of_ne hix]
    · obtain ⟨c, T, hT⟩ := hC.exists_affineIn hi
      have hxT : x ∉ T := fun h => hne i hi c T hT h
      rw [hT.2 val heq, hT.2 val' heq']
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hval' j (hT.1 hj), Function.update_of_ne (by rintro rfl; exact hxT hj)]
  have h1 := heq e he
  have h2 := heq' e he
  unfold Equation.Holds at h1 h2
  rw [← Finset.add_sum_erase _ _ hxe] at h1 h2
  rw [hval' x hx, Function.update_self] at h2
  rw [Finset.sum_congr rfl fun i hi => hagree i (Finset.mem_of_mem_erase hi)
    (Finset.ne_of_mem_erase hi), ← h2] at h1
  cases val x <;> simp at h1

end SemiCircuit

end Cslib.Circuits.Boolean.B2
