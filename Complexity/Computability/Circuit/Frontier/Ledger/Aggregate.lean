/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Unbounded
public import Complexity.Computability.Circuit.Frontier.Ledger.Basic
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Aggregate gates

An operation of arity `k` *aggregates* in a commutative monoid `T` when its value is read off a
product of contributions of its arguments: `f x = ψ (∏ i, φ i (x i))`. Every operation of the
Boolean basis of unbounded fan-in (negation, and conjunction and disjunction of any number of
arguments) aggregates in `ZMod 2` under multiplication, and every function of the number of true
arguments modulo `m`, such as parity and `MOD_m`, aggregates in `ZMod m` under addition.

If every special gate of a program aggregates in `T`, the special gates have a ledger in the
monoid `T ^ k` of functions from the `k` special gates to `T`
(`Frontier.exists_ledger_of_aggregates`): the contribution of a wire to a special gate is the
product of its contributions to the argument slots of that gate that read it. So `k` aggregate
gates cost `k log |T|` in the frontier lower bound.

## Main definitions

* `Cslib.Circuits.Frontier.Aggregates f T`: the operation `f` aggregates in `T`.

## Main results

* `Cslib.Circuits.Frontier.exists_ledger_of_aggregates`: aggregate gates have a ledger.
* `Cslib.Circuits.Frontier.aggregates_unbounded`: the operations of the Boolean basis of
  unbounded fan-in aggregate in `ZMod 2`.
* `Cslib.Circuits.Frontier.aggregates_countMod`: functions of the number of true arguments
  modulo `m` aggregate in `ZMod m`.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

universe v

variable {U : Type*}

/-- An operation of arity `k` *aggregates* in a commutative monoid `T` when its value is read
off a product of contributions of its arguments. -/
def Aggregates {k : ℕ} (f : (Fin k → U) → U) (T : Type*) [CommMonoid T] : Prop :=
  ∃ (φ : Fin k → U → T) (ψ : T → U), ∀ x, f x = ψ (∏ i, φ i (x i))

/-- **Aggregate gates have a ledger.** If every special gate of a program aggregates in `T`,
the special gates have a ledger in the monoid of functions from the special gates to `T`. -/
theorem exists_ledger_of_aggregates [Nonempty U] {σ : Signature.{v}} {n s : ℕ}
    (p : Program σ n s) (I : Interpretation σ U) (special : ℕ → Prop)
    (T : Type*) [CommMonoid T] (h : ∀ g : Fin s, special g → Aggregates (I (p.lines g).op) T) :
    Nonempty (Ledger special p I ({g : Fin s // special g} → T)) := by
  classical
  choose φ ψ hφψ using h
  refine ⟨{
    -- A wire contributes to a special gate the product of its contributions to the slots of
    -- that gate that read it.
    contribution := fun w u g => ∏ a with (p.lines g).wires a = w, φ g g.2 a u
    -- The special gate numbered `k` reads off its own coordinate; the other numbers are never
    -- consulted.
    readout := fun m k =>
      if hk : k < s then
        if hs : special k then ψ ⟨k, hk⟩ hs (m ⟨⟨k, hk⟩, hs⟩) else Classical.arbitrary U
      else Classical.arbitrary U
    readout_prod := fun v g hg => ?_ }⟩
  simp only [g.isLt, hg, ↓reduceDIte, Fin.eta, Finset.prod_apply, hφψ g hg]
  refine congrArg (ψ g hg) ?_
  -- Group the slots of `g` by the wire they read.
  rw [← Finset.prod_fiberwise Finset.univ (p.lines g).wires]
  refine Finset.prod_congr rfl fun w _ => Finset.prod_congr rfl fun a ha => ?_
  rw [(Finset.mem_filter.1 ha).2]

/-- **The Boolean basis of unbounded fan-in aggregates.** Negation, conjunction and disjunction
of any number of arguments aggregate in `ZMod 2` under multiplication: a conjunction is the
product of its arguments read as `1` for true and `0` for false, and a disjunction is the
negation of the product of the negations. -/
theorem aggregates_unbounded (op : Boolean.Unbounded.Op) :
    Aggregates (Boolean.Unbounded.interpretation op) (ZMod 2) := by
  cases op with
  | not => exact ⟨fun _ b => if b then 0 else 1, fun t => decide (t = 1), fun x => by
      cases h : x 0 <;> simp [h]⟩
  | and m => exact ⟨fun _ b => if b then 1 else 0, fun t => decide (t = 1), fun x => by
      simp [Finset.prod_boole]⟩
  | or m => exact ⟨fun _ b => if !b then 1 else 0, fun t => decide (t ≠ 1), fun x => by
      simp [Finset.prod_boole]⟩

open Finset in
/-- **Counting modulo `m` aggregates.** Every function of the number of true arguments modulo
`m` aggregates in `ZMod m` under addition: each true argument contributes `1` to the count.
Parity and the `MOD_m` gates are of this form. -/
theorem aggregates_countMod (k m : ℕ) (f : ZMod m → Bool) :
    Aggregates (fun x : Fin k → Bool => f (#{i | x i = true} : ℕ)) (Multiplicative (ZMod m)) :=
  ⟨fun _ b => .ofAdd (if b then 1 else 0), fun t => f t.toAdd, fun x => by
    simp [toAdd_prod, Finset.sum_boole]⟩

end Cslib.Circuits.Frontier
