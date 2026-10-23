/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Basic
public import Mathlib.Data.List.Forall2

/-!
# Probabilistic list traversal

The support of ordinary `List.mapM` consists exactly of the lists whose entries are supported
by the corresponding calls. The relation also records the exact output length. These are
semantic laws; computational efficiency is provided separately in `Computability.Probabilistic`.

## Main results

* `Cslib.ProbComp.mem_support_mapM_iff`: pointwise support characterizes list traversal.
-/

@[expose] public section

namespace Cslib.ProbComp

/-- The support of list traversal is exactly the pointwise support of the individual calls. -/
theorem mem_support_mapM_iff {α β : Type} (program : α → ProbComp β)
    (inputs : List α) (outputs : List β) :
    outputs ∈ (eval (inputs.mapM program)).support ↔
      List.Forall₂ (fun a b => b ∈ (eval (program a)).support) inputs outputs := by
  induction inputs generalizing outputs with
  | nil => cases outputs <;> simp
  | cons a inputs ih =>
    cases outputs with
    | nil => simp [List.mapM_cons]
    | cons b outputs =>
      simp only [PMF.mem_support_iff] at ih
      simp [List.mapM_cons, ih, and_comm]

end Cslib.ProbComp
