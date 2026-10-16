/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# Polynomial-time folds

The polynomial-time counterparts of Christian Reitwiessner's degree-bounded fold rules. A
`SizedListEncoding` accounts for list lengths, elements and suffixes, leaving only a polynomial
bound on the intermediate accumulator. The step may carry a fixed parameter.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.foldl'`: a fold with bounded accumulators.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.foldlWith`: a fold with a fixed parameter.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

variable {γ α β π : Type} {encIn : γ ↪ List Bool} {encA : α ↪ List Bool}
  {encB : β ↪ List Bool} {encL : List α ↪ List Bool} {encP : π ↪ List Bool}
  [ListEncoding encA encL] [SizedListEncoding encA encL]

/-- A left fold is polynomial-time when its step is polynomial-time and its intermediate
accumulators have polynomially bounded encoded length. -/
theorem foldl' {list : γ → List α} {init : γ → β} {step : β → α → β}
    (hlist : ComputableTidilyInPolyTime list encIn encL)
    (hinit : ComputableTidilyInPolyTime init encIn encB)
    (hstep : ComputableTidilyInPolyTime (fun p : β × α => step p.1 p.2)
      (encPair encB encA) encB)
    {B : γ → ℕ} (hB : PolyBounded (fun x => (encIn x).length) B)
    (hstates : ∀ x, ∀ i ≤ (list x).length,
      (encB (((list x).take i).foldl step (init x))).length ≤ B x) :
    ComputableTidilyInPolyTime (fun x => (list x).foldl step (init x)) encIn encB := by
  obtain ⟨_, _, hlist⟩ := hlist.exists_degree
  obtain ⟨_, _, hinit⟩ := hinit.exists_degree
  obtain ⟨_, _, hstep⟩ := hstep.exists_degree
  obtain ⟨c, d, hB⟩ := hB
  exact (ComputableTidilyInDegree.foldl' hlist hinit hstep
    (show DegreeBounded (fun x => (encIn x).length) B d from ⟨c, hB⟩)
    hstates).computableTidilyInPolyTime

/-- A polynomial-time fold whose step also uses a fixed, polynomial-time computable parameter. -/
theorem foldlWith {par : γ → π} {list : γ → List α} {init : γ → β}
    {step : π → β → α → β}
    (hpar : ComputableTidilyInPolyTime par encIn encP)
    (hlist : ComputableTidilyInPolyTime list encIn encL)
    (hinit : ComputableTidilyInPolyTime init encIn encB)
    (hstep : ComputableTidilyInPolyTime (fun p : (π × β) × α => step p.1.1 p.1.2 p.2)
      (encPair (encPair encP encB) encA) encB)
    {B : γ → ℕ} (hB : PolyBounded (fun x => (encIn x).length) B)
    (hstates : ∀ x, ∀ i ≤ (list x).length,
      (encB (((list x).take i).foldl (step (par x)) (init x))).length ≤ B x) :
    ComputableTidilyInPolyTime (fun x => (list x).foldl (step (par x)) (init x)) encIn encB := by
  obtain ⟨_, _, hpar⟩ := hpar.exists_degree
  obtain ⟨_, _, hlist⟩ := hlist.exists_degree
  obtain ⟨_, _, hinit⟩ := hinit.exists_degree
  obtain ⟨_, _, hstep⟩ := hstep.exists_degree
  obtain ⟨c, d, hB⟩ := hB
  exact (ComputableTidilyInDegree.foldlWith hpar hlist hinit hstep
    (show DegreeBounded (fun x => (encIn x).length) B d from ⟨c, hB⟩)
    hstates).computableTidilyInPolyTime

end Turing.MultiTapeTM.ComputableTidilyInPolyTime
