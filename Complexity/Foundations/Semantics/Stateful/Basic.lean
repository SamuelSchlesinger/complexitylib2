/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Foundations.Data.PFunctor.Free
public import Cslib.Foundations.Semantics.FLTS.Basic

/-!
# Stateful specifications and adaptive clients

Specifications describe mathematical states, typed operations and admissibility. Clients use
Quang Dao's upstream `PFunctor.FreeM`; continuations may depend on earlier answers. The state
interpreter and its histories have no computational-model or performance claim. In particular,
pure Lean computation in continuations is not charged as a machine instruction.

## Main definitions

* `Spec`: stateful operation semantics with typed answers and admissibility.
* `Spec.toFLTS`: the underlying functional labelled transition system (`Cslib.FLTS`) of state
  transitions.
* `Spec.run`: the final state and typed observation trace of a history.
* `Spec.ValidHistory`: each operation of a history is admissible in the state it reaches.
* `Spec.totalCost`: state-dependent charges summed along a history.
* `Spec.signature`: the polynomial functor of operations and their observation types.
* `Spec.Client`: terminating, potentially infinitely branching adaptive clients.
* `Spec.runClient`: mathematical interpretation with the selected operation history.
* `eval`: the result and final state of a client, without its history.
* `product`: independent abstract components; concrete independence is a realization obligation.

## Main results

* `Spec.fst_run_eq_toFLTS_mtr`: the state component of `Spec.run` agrees with `FLTS.mtr`.
* `Spec.run_append`, `Spec.validHistory_append`, `Spec.totalCost_append`: history composition laws.
* `Spec.totalCost_le_length_mul`, `Spec.totalCost_const`, `Spec.totalCost_one`: uniform and
  constant history charge bounds.
* `Spec.validHistory_of_forall_valid`: total interfaces have no history admissibility obligations.
* `Spec.run_runClient`: the history recorded by `Spec.runClient` reaches the computed final state.
* `Spec.runClient_bind`, `eval_bind`: sequential composition preserves state, answers and history
  order.
* `eval_eq_liftM`: `eval` agrees with `PFunctor.FreeM.liftM` into `StateM`.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*, Chapter 17][CLRS2009].
* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][Hopcroft2006].
-/

@[expose] public section

namespace Cslib.Stateful

universe u v w x y

/-- A deterministic abstract state machine with operation-dependent observations.
Only admissible operations are constrained by refinement certificates. -/
structure Spec where
  /-- Mathematical states, independent of a storage representation. -/
  State : Type u
  /-- Operations available to clients. -/
  Op : Type v
  /-- The observation type returned by each operation. -/
  Result : Op → Type w
  /-- The specified state transition and observation. -/
  step : (s : State) → (o : Op) → State × Result o
  /-- Preconditions under which an operation's implementation must satisfy its contract. -/
  valid : State → Op → Prop := fun _ _ => True

namespace Spec

variable (D : Spec.{u, v, w})

/-- Forget typed observations to view state transitions as a functional labelled transition
system. -/
def toFLTS : FLTS D.State D.Op := ⟨fun s o => (D.step s o).1⟩

/-- The transition function of `D.toFLTS` is the state component of `D.step`. -/
@[simp] theorem toFLTS_tr (s : D.State) (o : D.Op) :
    D.toFLTS.tr s o = (D.step s o).1 := rfl

/-- The final state and complete typed observation trace of a history. -/
def run (s : D.State) : List D.Op → D.State × List (Sigma D.Result)
  | [] => (s, [])
  | o :: os =>
    let next := D.step s o
    let rest := run next.1 os
    (rest.1, ⟨o, next.2⟩ :: rest.2)

/-- Each operation is admissible in the state reached by its predecessors. -/
def ValidHistory (s : D.State) : List D.Op → Prop
  | [] => True
  | o :: os => D.valid s o ∧ ValidHistory (D.step s o).1 os

/-- State-dependent charges summed along the abstract execution. -/
def totalCost (charge : D.State → D.Op → Nat) (s : D.State) : List D.Op → Nat
  | [] => 0
  | o :: os => charge s o + totalCost charge (D.step s o).1 os

/-- Running the empty history keeps the state and observes nothing. -/
@[simp] theorem run_nil (s : D.State) : D.run s (@List.nil (no_index D.Op)) = (s, []) := rfl

/-- Running a nonempty history steps once and prepends the typed observation. -/
@[simp] theorem run_cons (s : D.State) (o : D.Op) (os : List D.Op) :
    D.run s (@List.cons (no_index D.Op) o os) =
      ((D.run (D.step s o).1 os).1, ⟨o, (D.step s o).2⟩ :: (D.run (D.step s o).1 os).2) := rfl

/-- The final state of `D.run` agrees with the multi-step transition of `D.toFLTS`. -/
theorem fst_run_eq_toFLTS_mtr (s : D.State) (os : List D.Op) :
    (D.run s os).1 = D.toFLTS.mtr s os := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => exact ih (D.step s o).1

/-- The empty history is admissible in every state. -/
@[simp] theorem validHistory_nil (s : D.State) :
    D.ValidHistory s (@List.nil (no_index D.Op)) ↔ True := Iff.rfl

/-- A nonempty history is admissible when its first operation is valid and the tail is admissible
from the next state. -/
@[simp] theorem validHistory_cons (s : D.State) (o : D.Op) (os : List D.Op) :
    D.ValidHistory s (@List.cons (no_index D.Op) o os) ↔
      D.valid s o ∧ D.ValidHistory (D.step s o).1 os := Iff.rfl

/-- Total interfaces have no history admissibility obligations. -/
theorem validHistory_of_forall_valid (h : ∀ s o, D.valid s o)
    (s : D.State) (os : List D.Op) : D.ValidHistory s os := by
  induction os generalizing s with
  | nil => trivial
  | cons o os ih => exact ⟨h s o, ih _⟩

/-- The empty history costs nothing. -/
@[simp] theorem totalCost_nil (charge : D.State → D.Op → Nat) (s : D.State) :
    D.totalCost charge s (@List.nil (no_index D.Op)) = 0 := rfl

/-- The cost of a nonempty history adds the first operation's charge to the tail cost from the
next state. -/
@[simp] theorem totalCost_cons (charge : D.State → D.Op → Nat) (s : D.State)
    (o : D.Op) (os : List D.Op) :
    D.totalCost charge s (@List.cons (no_index D.Op) o os) =
      charge s o + D.totalCost charge (D.step s o).1 os := rfl

/-- Concatenation preserves both the state and the observation order. -/
theorem run_append (s : D.State) (xs ys : List D.Op) :
    D.run s (xs ++ ys) =
      ((D.run (D.run s xs).1 ys).1, (D.run s xs).2 ++ (D.run (D.run s xs).1 ys).2) := by
  induction xs generalizing s with
  | nil => rfl
  | cons o os ih => simp [ih]

/-- Charges compose at the intermediate abstract state. -/
theorem totalCost_append (charge : D.State → D.Op → Nat) (s : D.State)
    (xs ys : List D.Op) :
    D.totalCost charge s (xs ++ ys) =
      D.totalCost charge s xs + D.totalCost charge (D.run s xs).1 ys := by
  induction xs generalizing s with
  | nil => simp
  | cons o os ih => simp [ih, Nat.add_assoc]

/-- Uniform operation bounds imply a bound proportional to history length. -/
theorem totalCost_le_length_mul (charge : D.State → D.Op → Nat) (T : Nat)
    (h : ∀ s o, D.valid s o → charge s o ≤ T) {s : D.State} {os : List D.Op}
    (hv : D.ValidHistory s os) : D.totalCost charge s os ≤ os.length * T := by
  induction os generalizing s with
  | nil => simp
  | cons o os ih =>
    have hstep := h s o hv.1
    have hrest := ih hv.2
    simp only [totalCost_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- A constant charge `K` per operation totals `K` times the length of the history. -/
theorem totalCost_const (K : Nat) (s : D.State) (os : List D.Op) :
    D.totalCost (fun _ _ => K) s os = os.length * K := by
  induction os generalizing s with
  | nil => simp
  | cons o os ih => simp [ih, Nat.add_mul, Nat.add_comm]

/-- A unit charge per operation totals the length of the history. -/
theorem totalCost_one (s : D.State) (os : List D.Op) :
    D.totalCost (fun _ _ => 1) s os = os.length := by
  simpa using D.totalCost_const 1 s os

/-- The polynomial operation signature, shared with upstream effectful programs. -/
abbrev signature : PFunctor.{v, w} := ⟨D.Op, D.Result⟩

/-- An adaptive client: each continuation may depend on the observed answer.
Inductive clients have no infinite execution branch; branching need not be finite. -/
abbrev Client (α : Type y) := D.signature.FreeM α

/-- Interpret a client mathematically, retaining its chosen operation history. -/
def runClient {α : Type y} (s : D.State) : D.Client α → α × D.State × List D.Op
  | .pure a => (a, s, [])
  | .liftBind o k =>
    let next := D.step s o
    let rest := runClient next.1 (k next.2)
    (rest.1, rest.2.1, o :: rest.2.2)

/-- Interpreting a pure client returns its value, preserves the state, and records no operations. -/
@[simp, nolint simpNF] theorem runClient_pure {α : Type y} (s : D.State) (a : α) :
    D.runClient s (@PFunctor.FreeM.pure (no_index D.signature) α a) = (a, s, []) := rfl

/-- Interpreting a `pure` client returns its value, preserves the state, and records no
operations. -/
@[simp] theorem runClient_pure' {α : Type y} (s : D.State) (a : α) :
    D.runClient s (@Pure.pure (no_index D.Client) _ α a) = (a, s, []) := rfl

/-- Interpreting a single lifted operation steps the specification once. -/
@[simp] theorem runClient_lift (s : D.State) (o : D.Op) :
    @runClient D (no_index (D.Result o)) s (@PFunctor.FreeM.lift (no_index D.signature) o) =
      ((D.step s o).2, (D.step s o).1, [o]) := rfl

/-- Interpreting an operation call steps the specification and continues from the resulting state
and answer. -/
@[simp, nolint simpNF] theorem runClient_liftBind {α : Type y} (s : D.State) (o : D.Op)
    (k : D.Result o → D.Client α) :
    D.runClient s (@PFunctor.FreeM.liftBind (no_index D.signature) α o k) =
      ((D.runClient (D.step s o).1 (k (D.step s o).2)).1,
       (D.runClient (D.step s o).1 (k (D.step s o).2)).2.1,
       o :: (D.runClient (D.step s o).1 (k (D.step s o).2)).2.2) := rfl

/-- Interpreting a lifted operation bound to a continuation steps the specification and continues
from the resulting state and answer. -/
@[simp] theorem runClient_lift_bind {α : Type y} (s : D.State) (o : D.Op)
    (k : D.Result o → D.Client α) :
    D.runClient s
        (@PFunctor.FreeM.bind (no_index D.signature) (no_index (D.Result o)) α
          (@PFunctor.FreeM.lift (no_index D.signature) o) k) =
      ((D.runClient (D.step s o).1 (k (D.step s o).2)).1,
       (D.runClient (D.step s o).1 (k (D.step s o).2)).2.1,
       o :: (D.runClient (D.step s o).1 (k (D.step s o).2)).2.2) := rfl

/-- Interpreting a lifted operation monadically bound to a continuation steps the specification and
continues from the resulting state and answer. -/
@[simp] theorem runClient_lift_bind' {α : Type w} (s : D.State) (o : D.Op)
    (k : D.Result o → D.Client α) :
    D.runClient s
        (@Bind.bind (no_index D.Client) _ (no_index (D.Result o)) α
          (@PFunctor.FreeM.lift (no_index D.signature) o) k) =
      ((D.runClient (D.step s o).1 (k (D.step s o).2)).1,
       (D.runClient (D.step s o).1 (k (D.step s o).2)).2.1,
       o :: (D.runClient (D.step s o).1 (k (D.step s o).2)).2.2) := rfl

/-- The actual history chosen by an adaptive client has its computed final state. -/
theorem run_runClient {α : Type y} (p : D.Client α) (s : D.State) :
    (D.run s (D.runClient s p).2.2).1 = (D.runClient s p).2.1 := by
  induction p generalizing s with
  | pure a => rfl
  | liftBind o k ih => exact ih (D.step s o).2 (D.step s o).1

end Spec

namespace Spec

variable {D : Spec.{u, v, w}} {α β : Type y}

/-- Admissibility splits at the mathematical state reached by the first history. -/
theorem validHistory_append (s : D.State) (xs ys : List D.Op) :
    D.ValidHistory s (xs ++ ys) ↔
      D.ValidHistory s xs ∧ D.ValidHistory (D.run s xs).1 ys := by
  induction xs generalizing s with
  | nil => simp
  | cons o xs ih => simp [ih, and_assoc]

/-- Sequential interpretation concatenates the histories actually selected by the client. -/
theorem runClient_bind (p : D.Client α) (k : α → D.Client β) (s : D.State) :
    D.runClient s (p.bind k) =
      let first := D.runClient s p
      let rest := D.runClient first.2.1 (k first.1)
      (rest.1, rest.2.1, first.2.2 ++ rest.2.2) := by
  induction p generalizing s with
  | pure a => rfl
  | liftBind o cont ih =>
    exact congrArg (fun r : β × D.State × List D.Op => (r.1, r.2.1, o :: r.2.2))
      (ih (D.step s o).2 (D.step s o).1)

end Spec

variable {D : Spec.{u, v, w}} {α β : Type y}

/-- Observe results and state without displaying the operation history. -/
def eval (D : Spec.{u, v, w}) (p : D.Client α) (s : D.State) : α × D.State :=
  ((D.runClient s p).1, (D.runClient s p).2.1)

/-- Evaluating a pure client returns its value and leaves the state unchanged. -/
@[simp, nolint simpNF] theorem eval_pure (s : D.State) (a : α) :
    eval D (@PFunctor.FreeM.pure (no_index D.signature) α a) s = (a, s) := rfl

/-- Evaluating a `pure` client returns its value and leaves the state unchanged. -/
@[simp] theorem eval_pure' (s : D.State) (a : α) :
    eval D (@Pure.pure (no_index D.Client) _ α a) s = (a, s) := rfl

/-- Evaluating a single lifted operation steps the state and returns its answer. -/
@[simp] theorem eval_lift (s : D.State) (o : D.Op) :
    @eval (no_index (D.Result o)) D (@PFunctor.FreeM.lift (no_index D.signature) o) s =
      ((D.step s o).2, (D.step s o).1) := rfl

/-- Evaluating an operation call steps the state and continues with the observed answer. -/
@[simp, nolint simpNF] theorem eval_liftBind (s : D.State) (o : D.Op)
    (k : D.Result o → D.Client α) :
    eval D (@PFunctor.FreeM.liftBind (no_index D.signature) α o k) s =
      eval D (k (D.step s o).2) (D.step s o).1 := rfl

/-- Evaluating a lifted operation bound to a continuation steps the state and continues with the
observed answer. -/
@[simp] theorem eval_lift_bind (s : D.State) (o : D.Op) (k : D.Result o → D.Client α) :
    eval D
        (@PFunctor.FreeM.bind (no_index D.signature) (no_index (D.Result o)) α
          (@PFunctor.FreeM.lift (no_index D.signature) o) k) s =
      eval D (k (D.step s o).2) (D.step s o).1 := rfl

/-- Evaluating a lifted operation monadically bound to a continuation steps the state and continues
with the observed answer. -/
@[simp] theorem eval_lift_bind' {α : Type w} (s : D.State) (o : D.Op)
    (k : D.Result o → D.Client α) :
    eval D
        (@Bind.bind (no_index D.Client) _ (no_index (D.Result o)) α
          (@PFunctor.FreeM.lift (no_index D.signature) o) k) s =
      eval D (k (D.step s o).2) (D.step s o).1 := rfl

/-- Evaluating `p.bind k` evaluates `p`, then the continuation `k` at its result from the state
`p` reaches. -/
theorem eval_bind (p : D.Client α) (k : α → D.Client β) (s : D.State) :
    eval D (p.bind k) s = eval D (k (eval D p s).1) (eval D p s).2 := by
  induction p generalizing s with
  | pure a => rfl
  | liftBind o cont ih => exact ih _ _

/-- `eval` agrees with interpreting the free monad into `StateM D.State` via `PFunctor.FreeM.liftM`
when states, operation answers, and client results share a universe. -/
theorem eval_eq_liftM {D : Spec.{u, v, u}} {α : Type u} (p : D.Client α) (s : D.State) :
    (p.liftM (m := StateM D.State) fun o s => ((D.step s o).2, (D.step s o).1)).run s =
      eval D p s := by
  induction p generalizing s with
  | pure a => rfl
  | liftBind o k ih => exact ih (D.step s o).2 (D.step s o).1

/-- Two independent abstract components. A backend must separately justify their independence. -/
abbrev product (D E : Spec.{u, v, w}) : Spec where
  State := D.State × E.State
  Op := D.Op ⊕ E.Op
  Result
    | .inl o => D.Result o
    | .inr o => E.Result o
  step s
    | .inl o => let r := D.step s.1 o; ((r.1, s.2), r.2)
    | .inr o => let r := E.step s.2 o; ((s.1, r.1), r.2)
  valid s
    | .inl o => D.valid s.1 o
    | .inr o => E.valid s.2 o

/-- Stepping the left component of a product specification preserves the right state. -/
@[simp] theorem product_step_inl (D E : Spec.{u, v, w}) (s : D.State × E.State) (o : D.Op) :
    (product D E).step s (.inl o) = (((D.step s.1 o).1, s.2), (D.step s.1 o).2) := rfl

/-- Stepping the right component of a product specification preserves the left state. -/
@[simp] theorem product_step_inr (D E : Spec.{u, v, w}) (s : D.State × E.State) (o : E.Op) :
    (product D E).step s (.inr o) = ((s.1, (E.step s.2 o).1), (E.step s.2 o).2) := rfl

/-- Admissibility of a left operation in a product specification depends only on the left state. -/
@[simp] theorem product_valid_inl (D E : Spec.{u, v, w}) (s : D.State × E.State) (o : D.Op) :
    (product D E).valid s (.inl o) ↔ D.valid s.1 o := Iff.rfl

/-- Admissibility of a right operation in a product specification depends only on the right
state. -/
@[simp] theorem product_valid_inr (D E : Spec.{u, v, w}) (s : D.State × E.State) (o : E.Op) :
    (product D E).valid s (.inr o) ↔ E.valid s.2 o := Iff.rfl

end Cslib.Stateful
