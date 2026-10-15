/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Fintype.Sum

/-!
# The output tape up to two symbols

A decision procedure halts with output `[b]`. Since the output tape is append-only, whether a run
has produced exactly one symbol, and which one, is determined by a four-valued summary of the
output written so far (`Turing.OutView`): nothing, one symbol `b`, or more than one. The summary
is updated symbol by symbol (`Turing.OutView.push`), which is what lets reductions and circuit
simulations track acceptance with a bounded amount of information per time step.

## Main definitions

* `Turing.OutView`, `Turing.OutView.ofList`, `Turing.OutView.push`.

## Main results

* `Turing.OutView.ofList_append_toList`: summarising commutes with emitting a symbol.
* `Turing.OutView.ofList_eq_one_iff`: the summary is `one b` exactly for the output `[b]`.
-/

@[expose] public section

namespace Turing

/-- What has been written on the output tape: nothing, a single symbol, or more than one. A
decision procedure halts with output `[b]`, and since the output tape is append-only this view is
all that has to be tracked to see the answer. -/
inductive OutView where
  /-- Nothing has been written. -/
  | empty
  /-- Exactly one symbol has been written. -/
  | one (b : Bool)
  /-- At least two symbols have been written. -/
  | many
  deriving DecidableEq, Fintype

namespace OutView

/-- The view of an output word. -/
def ofList : List Bool → OutView
  | [] => empty
  | [b] => one b
  | _ :: _ :: _ => many

/-- The view after emitting an optional symbol. -/
def push : OutView → Option Bool → OutView
  | o, none => o
  | empty, some b => one b
  | one _, some _ => many
  | many, some _ => many

/-- All four views. -/
def all : List OutView := [empty, one false, one true, many]

@[simp] theorem length_all : all.length = 4 := rfl

@[simp] theorem mem_all (o : OutView) : o ∈ all := by
  rcases o with _ | (_ | _) | _ <;> simp [all]

@[simp] theorem ofList_nil : ofList [] = empty := rfl

theorem ofList_append_toList (l : List Bool) (o : Option Bool) :
    ofList (l ++ o.toList) = (ofList l).push o := by
  rcases o with _ | b
  · simp [push]
  · rcases l with _ | ⟨a, _ | ⟨a', l⟩⟩ <;> rfl

theorem ofList_eq_one_iff {l : List Bool} {b : Bool} : ofList l = one b ↔ l = [b] := by
  rcases l with _ | ⟨a, _ | ⟨a', l⟩⟩ <;> simp [ofList]

@[simp] theorem card_eq : Fintype.card OutView = 4 := rfl

/-- The index of an output view, for numbering. -/
def index : OutView → ℕ
  | .empty => 0
  | .one false => 1
  | .one true => 2
  | .many => 3

theorem index_injective : Function.Injective index := by
  rintro (_ | (_ | _) | _) (_ | (_ | _) | _) h <;> simp_all [index]

end OutView

end Turing
