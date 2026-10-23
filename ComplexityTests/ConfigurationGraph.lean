/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph

/-! Compact graph checks: native acceptance with zero tapes on every input, empty-input
boundaries, ternary blank gaps and erasure, absorbing rejecting output, and native routines. -/

namespace ComplexityTests.ConfigurationGraph

open Cslib.Turing Turing Turing.MultiTapeTM
open Turing.MultiTapeNTM.ConfigurationGraph

private def acceptAction : Action 0 Bool Unit :=
  { inputTape := 0, workTapes := Fin.elim0, output := some true, state := none }

private def acceptMachine : MultiTapeNTM 0 Bool Unit where
  q₀ := ()
  Tr _ _ _ a := a = acceptAction

private theorem accepts_acceptMachine (w : List Bool) : acceptMachine.Accepts w := by
  have hstep : acceptMachine.Step (acceptMachine.initCfg w)
      (acceptAction.apply (acceptMachine.initCfg w)) := ⟨acceptAction, rfl, rfl⟩
  refine ⟨⟨(RelSeries.singleton _ _).cons (acceptMachine.initCfg w) hstep, rfl⟩, ?_, ?_⟩ <;>
    simp [acceptAction]

/-- A concrete machine satisfies all hypotheses of the exact graph bridge, including at `[]`. -/
example (w : List Bool) : ∃ u,
    Relation.ReflTransGen (Edge acceptMachine (radixExponent Unit 0) w)
      (startID acceptMachine (radixExponent Unit 0) w.length) u ∧
      bad (k := 0) (State := Unit) (radixExponent Unit 0) w.length u = true :=
  (accepts_iff_reachable_bad_of_runsInSpace 0
    (MultiTapeNTM.runsInSpace_zero_tapes _ _ _)).mp (accepts_acceptMachine w)

/-- An out-of-range source ID cannot create an edge, even with an arbitrary supplied bit. -/
example (D n v : ℕ) (b : Option Bool) :
    edgeWithSymbol acceptMachine D n (vertexBound (k := 0) D n) v b = false := by
  cases h : edgeWithSymbol acceptMachine D n (vertexBound (k := 0) D n) v b with
  | false => rfl
  | true => have := (lt_vertexBound_of_edgeWithSymbol h).1; omega

example : inputSymbol 0 1 (some true) = none := by decide
example : inputSymbol 3 0 (some true) = none := by decide
example : inputSymbol 3 4 (some false) = none := by decide
example : inputSymbol 3 2 (some false) = some false := by decide

example : stackCode (StackTape.cons none (StackTape.cons (some false) StackTape.nil)) = 3 :=
  by decide
example : stackCode (StackTape.cons none (StackTape.nil : StackTape Bool)) = 0 := by decide
example : tapeStep (some none, .zero) (2, 17, 23) = (0, 17, 23) := by decide
example : tapeStep (none, .pos) (2, 1, 3) = (0, 5, 1) := by decide

example : outputStep 0 (some true) = 1 := by decide
example : outputStep 0 (some false) = 2 := by decide
example (b : Bool) : outputStep 1 (some b) = 2 := by cases b <;> decide
example (b : Option Bool) : outputStep 2 b = 2 := by rcases b with _ | _ | _ <;> decide

example (D : ℕ) : ComputableTidilyInSpace
    (fun a : ℕ × ℕ => queryIndex (k := 0) D a.1 a.2)
    encVertex encNat (fun a => (encVertex a).length) := queryIndex_inSpace D

example (D : ℕ) : ComputableTidilyInSpace
    (fun a : ℕ × ℕ × ℕ × Option Bool =>
      edgeWithSymbol acceptMachine D a.1 a.2.1 a.2.2.1 a.2.2.2)
    encEdge encBool (fun a => (encEdge a).length) := edgeWithSymbol_inSpace acceptMachine D

-- Legacy Nat-only interfaces retain their original arguments and remain definitionally equal.
set_option linter.deprecated false in
example : (packList : ℕ → List ℕ → ℕ) = Nat.ofDigits := rfl

set_option linter.deprecated false in
example (B x i : ℕ) : digit B x i = Cslib.Radix.digit B x i := rfl

set_option linter.deprecated false in
example (B : ℕ) (f : Bool → ℕ) : pack B f = Cslib.Radix.pack B f := rfl

set_option linter.deprecated false in
example (B x : ℕ) (i : Bool) : component B x i = Cslib.Radix.component B x i := rfl

set_option linter.deprecated false in
example {B : ℕ} (hB : 0 < B) (l : List ℕ) (hl : ∀ a ∈ l, a < B)
    (i : ℕ) (hi : i < l.length) : digit B (packList B l) i = l[i] :=
  digit_packList (hB := hB) l hl i hi

set_option linter.deprecated false in
example {B : ℕ} (hB : 0 < B) (l : List ℕ) (hl : ∀ a ∈ l, a < B) :
    packList B l < B ^ l.length := packList_lt (_hB := hB) l hl

set_option linter.deprecated false in
example {B : ℕ} (hB : 0 < B) {f : Bool → ℕ} (hf : ∀ i, f i < B) (i : Bool) :
    component B (pack B f) i = f i := component_pack (hB := hB) hf i

set_option linter.deprecated false in
example {B : ℕ} (hB : 0 < B) {f : Bool → ℕ} (hf : ∀ i, f i < B) :
    pack B f < B ^ Fintype.card Bool := pack_lt (hB := hB) hf

/--
info: 'Turing.MultiTapeNTM.ConfigurationGraph.accepts_iff_reachable_bad_of_runsInSpace'
depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeNTM.ConfigurationGraph.accepts_iff_reachable_bad_of_runsInSpace

/--
info: 'Turing.MultiTapeNTM.ConfigurationGraph.edgeWithSymbol_inSpace' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeNTM.ConfigurationGraph.edgeWithSymbol_inSpace

/--
info: 'Turing.MultiTapeNTM.ConfigurationGraph.reachable_lt_pow_of_runsInSpace' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeNTM.ConfigurationGraph.reachable_lt_pow_of_runsInSpace

end ComplexityTests.ConfigurationGraph
