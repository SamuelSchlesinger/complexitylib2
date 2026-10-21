/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Foundations.Data.PFunctor.Free

/-!
# Stateful specifications and adaptive clients

Specifications describe mathematical states, typed operations and admissibility. Clients use
Quang Dao's upstream `PFunctor.FreeM`; continuations may depend on earlier answers. The state
interpreter and its histories have no computational-model or performance claim. In particular,
pure Lean computation in continuations is not charged as a machine instruction.

## Main definitions

* `Spec`: stateful operation semantics with typed answers and admissibility.
* `Spec.Client`: terminating, potentially infinitely branching adaptive clients.
* `Spec.runClient`: mathematical interpretation with the selected operation history.
* `product`: independent abstract components; concrete independence is a realization obligation.

## Main results

* `Spec.runClient_bind`: sequential composition preserves state, answers and history order.
* `Spec.totalCost_append`: state-dependent charges compose along a history.
-/

@[expose] public section

namespace Cslib.Stateful

universe u v w x y

/-- A deterministic abstract state machine with operation-dependent observations.
Only admissible operations are constrained by refinement certificates. -/
structure Spec where
  State : Type u
  Op : Type v
  Result : Op → Type w
  step : (s : State) → (o : Op) → State × Result o
  valid : State → Op → Prop := fun _ _ => True

namespace Spec

variable (D : Spec.{u, v, w})

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

@[simp] theorem run_nil (s : D.State) : D.run s [] = (s, []) := rfl

@[simp] theorem totalCost_nil (charge : D.State → D.Op → Nat) (s : D.State) :
    D.totalCost charge s [] = 0 := rfl

/-- Concatenation preserves both the state and the observation order. -/
theorem run_append (s : D.State) (xs ys : List D.Op) :
    D.run s (xs ++ ys) =
      ((D.run (D.run s xs).1 ys).1, (D.run s xs).2 ++ (D.run (D.run s xs).1 ys).2) := by
  induction xs generalizing s with
  | nil => rfl
  | cons o os ih => simp [run, ih]

/-- Charges compose at the intermediate abstract state. -/
theorem totalCost_append (charge : D.State → D.Op → Nat) (s : D.State)
    (xs ys : List D.Op) :
    D.totalCost charge s (xs ++ ys) =
      D.totalCost charge s xs + D.totalCost charge (D.run s xs).1 ys := by
  induction xs generalizing s with
  | nil => simp [totalCost]
  | cons o os ih => simp [totalCost, run, ih, Nat.add_assoc]

/-- Uniform operation bounds imply a bound proportional to history length. -/
theorem totalCost_le_length_mul (charge : D.State → D.Op → Nat) (T : Nat)
    (h : ∀ s o, D.valid s o → charge s o ≤ T) {s : D.State} {os : List D.Op}
    (hv : D.ValidHistory s os) : D.totalCost charge s os ≤ os.length * T := by
  induction os generalizing s with
  | nil => simp [totalCost]
  | cons o os ih =>
    have hstep := h s o hv.1
    have hrest := ih hv.2
    simp only [totalCost, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- The polynomial operation signature, shared with upstream effectful programs. -/
def signature : PFunctor.{v, w} := ⟨D.Op, D.Result⟩

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
  | nil => simp [ValidHistory, run]
  | cons o xs ih => simp [ValidHistory, run, ih, and_assoc]

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

theorem eval_bind (p : D.Client α) (k : α → D.Client β) (s : D.State) :
    eval D (p.bind k) s = eval D (k (eval D p s).1) (eval D p s).2 := by
  induction p generalizing s with
  | pure a => rfl
  | liftBind o cont ih => exact ih _ _

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

/-- Total interfaces have no history admissibility obligations. -/
theorem valid_history_of_total (D : Spec.{u, v, w}) (h : ∀ s o, D.valid s o)
    (s : D.State) (os : List D.Op) : D.ValidHistory s os := by
  induction os generalizing s with
  | nil => trivial
  | cons o os ih => exact ⟨h s o, ih _⟩


end Cslib.Stateful
