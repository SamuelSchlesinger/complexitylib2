/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.VanEmdeBoas.Call
public import Complexity.Algorithms.Lean.VanEmdeBoas.Insert
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
Native membership boundary, adversarial-memory and calling-convention regressions.
Fixture installation below is test-harness code, not a charged initializer. Generic correctness
comes from the execution theorems, not these finite evaluations.
-/

@[expose] public section

namespace ComplexityTests.VanEmdeBoasRAM

open Cslib.WordRAM
open Cslib.Algorithms.Lean.VanEmdeBoas
open Cslib.Algorithms.WordRAM.VanEmdeBoas

/-- The test tree represents exactly the three keys zero, one and three. -/
def fixtureTree : Tree 1 := (((Tree.empty 1).insert 0).insert 1).insert 3

/-- Concrete headers for the represented test tree. -/
def fixtureWords : List ℕ :=
  [1, 0, 3, 2, 5, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0]

-- A fake occupied leaf immediately beyond the tree would make the old unguarded program
-- report key 4 as present. All other unowned cells are deliberately nonzero/stale.
/-- The fixture's tree region, a hostile fake leaf, and nonzero unowned memory. -/
def poisonedMemory (a : ℕ) : ℕ :=
  if 8 ≤ a ∧ a < 28 then fixtureWords[a - 8]!
  else if a = 28 then 1 else if a ∈ [29, 30, 31, 32] then 0 else 173

/-- A fully fitting eight-bit caller with nonzero stale scratch registers. -/
def caller (query : ℕ) : Data 32 where
  regs i := if i = root then 8 else if i = arg then query else if i = tag then 1 else 173
  mem := poisonedMemory

/-- A concrete valid represented instance, including deliberately hostile outside memory. -/
theorem fixture_valid : fixtureTree.Valid := by
  unfold fixtureTree
  iterate 3 apply Tree.valid_insert (hx := by decide)
  exact Tree.valid_empty 1

/-- The recursive memory hypothesis is inhabited by the finite nonzero-background fixture. -/
theorem fixture_represented : Rep fixtureTree 8 poisonedMemory := by
  refine ⟨?_, ?_, ?_⟩
  · change Header 1 (some (0, 3)) 8 poisonedMemory
    unfold Header
    decide
  · change Header 0 (some (0, 1)) 13 poisonedMemory
    unfold Header
    decide
  · intro i
    fin_cases i <;> change Header 0 (some (1, 1)) _ poisonedMemory <;>
      unfold Header <;> decide

/-- The represented fixture satisfies the machine's global bounded-memory hypothesis. -/
theorem caller_bounded (query : ℕ) (hq : Fits 8 query) : (caller query).Bounded 8 := by
  constructor
  · intro i
    simp only [caller]
    split_ifs <;> first | exact hq | decide
  · intro a
    simp only [caller, poisonedMemory]
    split_ifs with htree
    · obtain ⟨hlo, hhi⟩ := htree
      interval_cases a <;> decide
    · decide
    · decide
    · decide

/-- The complete flat-call theorem applies to every fitting query on hostile outside memory. -/
theorem fixture_call (query : ℕ) (hq : Fits 8 query) :
    ∃ n ≤ 74, Executes 8 (program.program out) ⟨0, caller query⟩
      (if fixtureTree.member query then 1 else 0) n :=
  member_executes (caller_bounded query hq) fixture_valid fixture_represented
    (by decide) (by simp +decide [caller]) (by simp +decide [caller])
    (by simp +decide [caller])

private def structuredAnswer (query : ℕ) : Option (ℕ × ℕ) :=
  (program.eval 8 3 (caller query)).map fun yn => (yn.1.regs out, yn.2 + 1)

private def flatAnswer (query : ℕ) : Option (ℕ × ℕ) :=
  Cslib.WordRAM.run 8 (program.program out) 1024 ⟨0, caller query⟩

-- Every fitting query word, including all 252 queries outside the four-key universe.
private def queriesAgree (start : ℕ) : Bool :=
  (List.range 64).all (fun offset =>
    let query := start + offset
    (structuredAnswer query).map Prod.fst == some (if query ∈ [0, 1, 3] then 1 else 0)) =
    true

example : queriesAgree 0 := by decide
example : queriesAgree 64 := by decide
example : queriesAgree 128 := by decide
example : queriesAgree 192 := by decide

example : flatAnswer 4 = structuredAnswer 4 := by decide
example : flatAnswer 255 = structuredAnswer 255 := by decide
example : flatAnswer 0 = structuredAnswer 0 := by decide
example : flatAnswer 1 = structuredAnswer 1 := by decide
example : flatAnswer 2 = structuredAnswer 2 := by decide
example : flatAnswer 3 = structuredAnswer 3 := by decide

-- The adversarial leaf remains outside the represented region.
example : poisonedMemory 28 = 1 ∧ poisonedMemory 29 = 0 ∧ poisonedMemory 1000 = 173 := by
  decide

private def adaptiveAnswers : Option (List ℕ) := do
  let (a, _) ← program.eval 8 3 (caller 1)
  let q := if a.regs out = 1 then 4 else 0
  let (b, _) ← program.eval 8 3 (a.set arg q)
  let q' := if b.regs out = 0 then 3 else 2
  let (c, _) ← program.eval 8 3 (b.set arg q')
  pure [a.regs out, b.regs out, c.regs out]

example : adaptiveAnswers = some [1, 0, 1] := by decide

-- Empty extrema may be stale even inside the represented interval.
private def staleEmptyMemory (a : ℕ) : ℕ :=
  if a ∈ [8, 13, 18, 23, 16, 17, 21, 22, 26, 27] then 0
  else if a = 11 then 2 else if a = 12 then 5 else 173

example : Rep (Tree.empty 1) 8 staleEmptyMemory := by
  refine ⟨?_, ?_, ?_⟩
  · change Header 1 none 8 staleEmptyMemory
    unfold Header
    decide
  · change Header 0 none 13 staleEmptyMemory
    unfold Header
    decide
  · intro i
    fin_cases i <;> change Header 0 none _ staleEmptyMemory <;> unfold Header <;> decide

example : ((program.eval 8 3 ⟨(caller 255).regs, staleEmptyMemory⟩).map
    (fun yn => yn.1.regs out)) = some 0 := by decide

/--
info: 'Cslib.Algorithms.WordRAM.VanEmdeBoas.member_descent_safe' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Algorithms.WordRAM.VanEmdeBoas.member_descent_safe
/--
info: 'Cslib.Algorithms.WordRAM.VanEmdeBoas.memberLoop_spec' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Algorithms.WordRAM.VanEmdeBoas.memberLoop_spec
/--
info: 'Cslib.Algorithms.WordRAM.VanEmdeBoas.member_call' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Algorithms.WordRAM.VanEmdeBoas.member_call
/--
info: 'Cslib.Algorithms.WordRAM.VanEmdeBoas.member_executes_generic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Algorithms.WordRAM.VanEmdeBoas.member_executes_generic

end ComplexityTests.VanEmdeBoasRAM
