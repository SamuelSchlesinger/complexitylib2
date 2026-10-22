/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.VanEmdeBoas.Member
public import Complexity.Computability.WordRAM.Compile
public import Complexity.Computability.WordRAM.Generic
public import Mathlib.Data.Nat.Log

/-!
# Complete native van Emde Boas membership calls

Membership uses the same fixed dispatcher as the other, as yet uncertified, operations.
The cost includes constant setup, dispatch branches, every loop instruction and the final
halt. The represented tree is supplied at entry: no initialization cost is claimed here.
The caller supplies a bounded register/memory state, hence its query word must fit even when
the query is outside the tree universe. External delivery/decoding is not charged.

## Main definitions

* `setupData`: a mathematical description of the twelve charged setup instructions.

## Main results

* `member_dispatch_spec`: complete structured membership call, excluding only halt.
* `member_call`: bounded-state and represented-memory preservation with the native result.
* `member_executes`: actual flat execution including halt.
* `member_executes_generic`: the same execution in the exact shared generic RAM model.

## References

* [E. Demaine, *Divide and conquer: van Emde Boas trees*, Lecture 4][Demaine2015VanEmdeBoas]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.VanEmdeBoas

open Cslib.WordRAM
open Cslib.Algorithms.Lean.VanEmdeBoas

/-- The state after the twelve actual setup instructions. -/
def setupData (s : Data 32) : Data 32 :=
  let a := (((((s.set zero 0).set one 1).set two 2).set three 3).set four 4).set five 5
  let b := (((a.set p (s.regs root)).set x (s.regs arg)).set out 0).set found 0
  (b.set sp (s.regs stackBase)).set runFlag 1

/-- Constant and traversal setup has exactly twelve native instructions. -/
theorem setup_exec {w : ℕ} {s : Data 32} (hw : Fits w 5) :
    Exec w setup s (setupData s) 12 := by
  have h₁ := hw.of_le (by decide : 1 ≤ 5)
  have h₂ := hw.of_le (by decide : 2 ≤ 5)
  have h₃ := hw.of_le (by decide : 3 ≤ 5)
  have h₄ := hw.of_le (by decide : 4 ≤ 5)
  ram_eval [setup, setupData, hw, h₁, h₂, h₃, h₄]

/-- Setup establishes membership's entry registers from the caller's root and argument. -/
theorem setup_memberEntry (s : Data 32) :
    MemberEntry (s.regs root) (s.regs arg) (setupData s) := by
  constructor <;> simp +decide [setupData]

/-- The single compiled program contains 212 ordinary instructions and a final halt. -/
theorem compiled_program_length : (program.program out).length = 213 := by
  simp only [Code.program, List.length_append, Code.length_assemble, program_size,
    List.length_cons, List.length_nil]

/-- Compiling the fixed dispatcher introduces no word-width instruction. -/
theorem compiled_program_not_readsWidth : ¬(program.program out).ReadsWidth :=
  Code.not_readsWidth_program program_not_readsWidth out

/-- A complete membership dispatch, including setup and all control flow but not final halt.
No query-universe restriction and no zero-filled outside-memory assumption are imposed. -/
theorem member_dispatch_spec {d w base query : ℕ} {tree : Tree d} {s : Data 32}
    (ht : tree.Valid) (hr : Rep tree base s.mem) (ha : Fits w (base + span d))
    (hroot : s.regs root = base) (harg : s.regs arg = query) (htag : s.regs tag = 1) :
    ∃ z, ExecWithin w program s z (28 * (d + 1) + 17) ∧
      z.regs out = (if tree.member query then 1 else 0) ∧ z.mem = s.mem := by
  have hw : Fits w 5 := ha.of_le (by have := five_le_span d; omega)
  have hentry : MemberEntry base query (setupData s) := by
    simpa only [hroot, harg] using setup_memberEntry s
  obtain ⟨z, hz, hout, hmem⟩ := memberLoop_spec hentry ht (by simpa [setupData] using hr) ha
  have h₀ : ¬(Cond.eq tag zero).Holds (setupData s) := by
    simp +decide [Cond.holds_eq, setupData, htag]
  have h₁ : (Cond.eq tag one).Holds (setupData s) := by
    simp +decide [Cond.holds_eq, setupData, htag]
  refine ⟨z, ?_, hout, ?_⟩
  · exact ((setup_exec hw).within.seq
      (ExecWithin.branch_neg h₀ (ExecWithin.branch_pos h₁ hz))).mono (by omega)
  · simpa only [setupData, Data.set_mem] using hmem

/-- A bounded caller obtains a bounded result, identical represented memory and an unchanged
persistent root. Its query fits the machine word because every caller register does. -/
theorem member_call {d w base query : ℕ} {tree : Tree d} {s : Data 32}
    (hs : s.Bounded w) (ht : tree.Valid) (hr : Rep tree base s.mem)
    (ha : Fits w (base + span d)) (hroot : s.regs root = base)
    (harg : s.regs arg = query) (htag : s.regs tag = 1) :
    ∃ z n, n + 1 ≤ 28 * (d + 1) + 18 ∧ Exec w program s z n ∧
      z.Bounded w ∧ Rep tree base z.mem ∧ z.regs root = base ∧
      z.regs out = (if tree.member query then 1 else 0) ∧ z.mem = s.mem := by
  obtain ⟨z, ⟨n, hn, he⟩, hout, hmem⟩ := member_dispatch_spec ht hr ha hroot harg htag
  refine ⟨z, n, by omega, he, he.bounded hs, ?_, ?_, hout, hmem⟩
  · simpa only [hmem] using hr
  · exact (he.regs_eq (by decide : program.Preserves root)).trans hroot

/-- Actual flat bounded-word execution, including its final halt, in `28 (d+1) + 18`
instructions. The selected fixed program has no depth or word-width parameter. -/
theorem member_executes {d w base query : ℕ} {tree : Tree d} {s : Data 32}
    (hs : s.Bounded w) (ht : tree.Valid) (hr : Rep tree base s.mem)
    (ha : Fits w (base + span d)) (hroot : s.regs root = base)
    (harg : s.regs arg = query) (htag : s.regs tag = 1) :
    ∃ n ≤ 28 * (d + 1) + 18,
      Executes w (program.program out) ⟨0, s⟩ (if tree.member query then 1 else 0) n := by
  obtain ⟨z, n, hn, he, _, _, _, hout, _⟩ := member_call hs ht hr ha hroot harg htag
  exact ⟨n + 1, hn, hout ▸ he.executes out⟩

/-- Exact transfer of the actual flat call into the shared generic RAM model; this adds no
semantic operation or uncharged oracle instruction. -/
theorem member_executes_generic {d w base query : ℕ} {tree : Tree d} {s : Data 32}
    (hs : s.Bounded w) (ht : tree.Valid) (hr : Rep tree base s.mem)
    (ha : Fits w (base + span d)) (hroot : s.regs root = base)
    (harg : s.regs arg = query) (htag : s.regs tag = 1) :
    ∃ n ≤ 28 * (d + 1) + 18,
      GenericRAM.Executes w (program.program out).toGeneric
        ((⟨0, s⟩ : State 32).toGeneric .standard) (if tree.member query then 1 else 0) n := by
  obtain ⟨n, hn, he⟩ := member_executes hs ht hr ha hroot harg htag
  exact ⟨n, hn, executes_toGeneric_iff.mpr he⟩

/-- The supported double-exponential universe has exactly `d` iterated binary logarithms. -/
theorem log_log_universeSize (d : ℕ) : Nat.log 2 (Nat.log 2 (universeSize d)) = d := by
  simp only [universeSize_eq_two_pow, Nat.log_pow Nat.one_lt_two]

/-- The charged native membership bound written directly in terms of the universe size. -/
theorem member_executes_log {d w base query : ℕ} {tree : Tree d} {s : Data 32}
    (hs : s.Bounded w) (ht : tree.Valid) (hr : Rep tree base s.mem)
    (ha : Fits w (base + span d)) (hroot : s.regs root = base)
    (harg : s.regs arg = query) (htag : s.regs tag = 1) :
    ∃ n ≤ 28 * (Nat.log 2 (Nat.log 2 (universeSize d)) + 1) + 18,
      Executes w (program.program out) ⟨0, s⟩ (if tree.member query then 1 else 0) n := by
  simpa only [log_log_universeSize] using member_executes hs ht hr ha hroot harg htag

end Cslib.Algorithms.WordRAM.VanEmdeBoas
