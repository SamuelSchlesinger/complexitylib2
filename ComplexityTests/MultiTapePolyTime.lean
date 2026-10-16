/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Tests for the polynomial-time calculus

Based on Christian Reitwiessner's `CslibTests/MultiTapePolyTime.lean` (branch `crei/tidy-universal`
@7f7c0696), and the change that branch makes to `CslibTests/MultiTapeComplexity.lean`, with tests
for encoding inference, list construction and indexing.
-/

namespace ComplexityTests.MultiTapePolyTime

open Turing.MultiTapeTM

-- `fun_prop` assembles polynomial-time computability from the closure properties.
example : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => (p.2, p.1 + 1 + 1))
    (encPair encNat encNat) (encPair encNat encNat) := by
  fun_prop

example {c : ℕ → Bool} (hc : ComputableTidilyInPolyTime c encNat encBool) :
    ComputableTidilyInPolyTime (fun n => if c n then n + 1 else n) encNat encNat := by
  fun_prop

example : ComputableTidilyInPolyTime (List.map (fun n : ℕ => n + 1))
    (encList encNat) (encList encNat) := by
  fun_prop

example : ComputableTidilyInPolyTime (fun p : List ℕ × ℕ => p.1.idxOf p.2)
    (encPair (encList encNat) encNat) encUnary := by
  fun_prop

example : ComputableTidilyInPolyTime (fun p : List Bool × ℕ => p.1.getD p.2 false)
    (encPair encBits encUnary) encBool := by
  fun_prop

-- Composition infers the unary index encoding from `idxOf` before applying lookup.
example : ComputableTidilyInPolyTime (fun p : List ℕ × ℕ => p.1.getD (p.1.idxOf p.2) 0)
    (encPair (encList encNat) encNat) encNat := by
  fun_prop

-- Scans, like folds, use an explicit rule for the captured parameter.
example : ComputableTidilyInPolyTime (fun p : List ℕ × ℕ => p.1.any fun n => decide (p.2 = n))
    (encPair (encList encNat) encNat) encBool :=
  ComputableTidilyInPolyTime.anyWith (ComputableTidilyInPolyTime.decide_eq encNat)
    (ComputableTidilyInPolyTime.snd (encList encNat) encNat)
    (ComputableTidilyInPolyTime.fst (encList encNat) encNat)

-- Both raw and framed lists infer the element encoding for unary lengths.
example : ComputableTidilyInPolyTime (fun w : List Bool => List.range w.length)
    encBits (encList encUnary) := by
  fun_prop

example : ComputableTidilyInPolyTime (fun l : List ℕ => List.range l.length)
    (encList encNat) (encList encUnary) := by
  fun_prop

-- The intermediate range has quadratic encoded length, so the parameterized map must
-- accept polynomial-sized lists, not just lists with a linear output bound.
example : ComputableTidilyInPolyTime (fun n => (List.range n).map fun i => (n, i))
    encUnary (encList (encPair encUnary encUnary)) :=
  ComputableTidilyInPolyTime.mapWith .id' .id' ComputableTidilyInPolyTime.range

example : ComputableTidilyInPolyTime (fun n => (List.range n).flatMap fun i => List.replicate i n)
    encUnary (encList encUnary) := by
  have hrep := (ComputableTidilyInDegree.replicate encUnary).computableTidilyInPolyTime.comp
    ((ComputableTidilyInPolyTime.snd encUnary encUnary).prod
      (ComputableTidilyInPolyTime.fst encUnary encUnary))
  exact ComputableTidilyInPolyTime.flatMapWith hrep .id' ComputableTidilyInPolyTime.range

private def finish (move : SignType) (symbol : Bool) : Turing.MultiTapeTM 0 Bool Unit :=
  ofTr () fun _ _ _ => ⟨move, Fin.elim0, some symbol, none⟩

private def bit : Bool ↪ List Bool := ⟨fun b => [b], by intro a b h; simpa using h⟩

-- A deterministic machine that has halted after `t` steps satisfies the time bound `t`.
example (symbol : Bool) :
    ComputableInTimeAndSpace (fun _ : Bool => symbol) bit bit
      (fun b => if b then 1 else 2) (fun _ => 0) := by
  refine ⟨0, Unit, inferInstance, finish 0 symbol, fun b ↦ ?_⟩
  have h : ((finish 0 symbol).runFrom ((finish 0 symbol).initCfg (bit b)) 1).Halted ∧
      ((finish 0 symbol).runFrom ((finish 0 symbol).initCfg (bit b)) 1).output = bit symbol := by
    rw [runFrom, Function.iterate_one, step_of_state rfl]
    simp [finish, Turing.Cfg.Halted]; rfl
  exact ⟨⟨1, h⟩, (runsInTime_iff_halted.mpr h.1).mono (by cases b <;> decide), by simp⟩


/-- `length_le_length_encList` holds in every universe. -/
example {α : Type 1} (enc : α ↪ List Bool) (l : List α) :
    l.length ≤ (Turing.MultiTapeTM.encList enc l).length :=
  Turing.MultiTapeTM.length_le_length_encList enc l

end ComplexityTests.MultiTapePolyTime
