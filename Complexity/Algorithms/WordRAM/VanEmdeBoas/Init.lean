/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.VanEmdeBoas.Model
public import Complexity.Algorithms.WordRAM.VanEmdeBoas.Program
public import Complexity.Computability.WordRAM.Compile
public import Complexity.Computability.WordRAM.Generic
import Mathlib.Tactic.Linarith

/-!
# Charged uniform Word-RAM initialization of van Emde Boas trees

This module certifies a single fixed 32-register Word-RAM program (`initProgram`) that initializes
an empty recursive van Emde Boas tree of arbitrary depth `d` at base address `base`, together with
the scratch stack pointer at `base + span d`, without depth-dependent code generation, square-root
oracle instructions, or uncharged zero-memory assumptions.

The initializer executes in three phases:
1. Compute `(universeSize d, span d)` by `d` iterations of the layout recurrences.
2. Set `tableBase = stackBase = base + span d` and populate a `(splitSize k, childSpan k)` lookup
   table of `2 * (d + 1)` words at `[tableBase, tableBase + 2 * (d + 1))`.
3. Traverse the recursive layout in depth-first order using `d` words of per-depth cluster counters
   at `[tableBase + 2 * (d + 1) + 1, tableBase + 3 * d + 2]`, writing `0`, `splitSize k`, and
   `childSpan k` into every depth-`k` header while leaving empty minimum/maximum cells untouched.

## Main definitions

* `initProgram`: the fixed 32-register structured initializer program.

## Main results

* `init_dispatch_spec`: structured execution in at most `8 * span d + 20 * d + 24` instructions,
  establishing `Rep (Tree.empty d) base z.mem`, `z.regs root = base`, and
  `z.regs stackBase = base + span d`, while preserving all memory outside
  `[base, base + span d + 4 * (d + 1))`.
* `init_call`, `init_executes`, `init_executes_generic`: bounded-state, flat, and generic RAM
  initialization certificates.
* `init_space_le`: the total tree-plus-scratch footprint is at most
  `10 * universeSize d + 4 * (d + 1)` words.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.VanEmdeBoas

open Cslib.WordRAM
open Cslib.Algorithms.Lean.VanEmdeBoas

/-- Monotonicity of `universeSize` in the recursion depth. -/
theorem universeSize_mono {a b : ℕ} (hab : a ≤ b) : universeSize a ≤ universeSize b := by
  induction hab with
  | refl => exact le_rfl
  | @step m _ ih =>
    rw [universeSize_succ]
    have hpos := two_le_universeSize m
    nlinarith

/-- Monotonicity of `span` in the recursion depth. -/
theorem span_mono {a b : ℕ} (hab : a ≤ b) : span a ≤ span b := by
  induction hab with
  | refl => exact le_rfl
  | @step m _ ih => exact ih.trans (span_le_succ m)

/-- Every split size is bounded by its record span. -/
theorem splitSize_le_span (d : ℕ) : splitSize d ≤ span d := by
  cases d with
  | zero => decide
  | succ d =>
    dsimp only [splitSize]
    exact (universeSize_le_span d).trans (span_le_succ d)

/-- Every child span is bounded by its parent record span. -/
theorem childSpan_le_span (d : ℕ) : childSpan d ≤ span d := by
  cases d with
  | zero => decide
  | succ d => exact span_le_succ d

/-- The combined tree and scratch region of `span d + 4 * (d + 1)` words is bounded by
`10 * universeSize d + 4 * (d + 1)`. -/
theorem init_space_le (d : ℕ) :
    span d + 4 * (d + 1) ≤ 10 * universeSize d + 4 * (d + 1) :=
  Nat.add_le_add_right (span_le d) (4 * (d + 1))

/-! ## Structured initializer program -/

/-- Constant and recurrence-seed setup for Phase 1. -/
def initSetup : Code .standard 32 := ram[
  zero ← #0; one ← #1; two ← #2; three ← #3; four ← #4; five ← #5;
  q ← two; t ← five; high ← zero ]

/-- One step of the `(universeSize, span)` recurrence loop. -/
def sizeBody : Code .standard 32 := ram[
  tmp ← q + one; tmp ← tmp * t; tmp ← tmp + five;
  q ← q * q; t ← tmp; high ← high + one ]

/-- Phase 1 loop computing `(universeSize d, span d)`. -/
def sizeLoop : Code .standard 32 := ram[
  while high < depth do [ ⟪sizeBody⟫ ] ]

/-- Setup for the Phase 2 `(splitSize, childSpan)` table construction. -/
def tableSetup : Code .standard 32 := ram[
  payload ← root + t; tableBase ← payload; stackBase ← payload; sp ← tableBase;
  *sp ← zero; sp ← sp + one; *sp ← zero; sp ← sp + one;
  q ← two; t ← five; high ← zero ]

/-- One step of the Phase 2 table-population loop. -/
def tableBody : Code .standard 32 := ram[
  *sp ← q; sp ← sp + one; *sp ← t; sp ← sp + one;
  tmp ← q + one; tmp ← tmp * t; tmp ← tmp + five;
  q ← q * q; t ← tmp; high ← high + one ]

/-- Phase 2 loop writing `(splitSize (k + 1), childSpan (k + 1))` for `k < d`. -/
def tableLoop : Code .standard 32 := ram[
  while high < depth do [ ⟪tableBody⟫ ] ]

/-- Setup for the Phase 3 depth-first header initialization. -/
def dfsSetup : Code .standard 32 := ram[
  low ← sp; p ← root; x ← depth; kind ← zero; runFlag ← one ]

/-- Downward step of the DFS initializer: write the current node's empty header and either
turn around at a leaf or initialize the cluster counter and descend into the summary. -/
def dfsEnterBody : Code .standard 32 := ram[
  *p ← zero;
  tmp ← x * two; addr ← tableBase + tmp; q ← *addr;
  addr ← addr + one; t ← *addr;
  child ← p + three; *child ← q; child ← child + one; *child ← t;
  p ← p + five;
  if x = zero then [ kind ← one ] else [
    addr ← low + x; *addr ← q; x ← x - one
  ] ]

/-- Upward/sibling step of the DFS initializer: ascend to the parent level and either finish
when above `depth`, continue ascending when all clusters are done, or decrement the remaining
cluster counter and descend into the next cluster. -/
def dfsExitBody : Code .standard 32 := ram[
  x ← x + one;
  if depth < x then [ runFlag ← zero ] else [
    addr ← low + x; present ← *addr;
    if present = zero then [ kind ← kind ] else [
      present ← present - one; *addr ← present; x ← x - one; kind ← zero
    ]
  ] ]

/-- Full body of the Phase 3 DFS loop. -/
def dfsBody : Code .standard 32 := ram[
  if kind = zero then [ ⟪dfsEnterBody⟫ ] else [ ⟪dfsExitBody⟫ ] ]

/-- Phase 3 DFS traversal loop. -/
def dfsLoop : Code .standard 32 := ram[
  while zero < runFlag do [ ⟪dfsBody⟫ ] ]

/-- Fixed 32-register structured program initializing an empty van Emde Boas tree of depth
`depth` at `root` and placing `stackBase` at `root + span depth`. -/
def initProgram : Code .standard 32 := ram[
  ⟪initSetup⟫;
  ⟪sizeLoop⟫;
  ⟪tableSetup⟫;
  ⟪tableLoop⟫;
  ⟪dfsSetup⟫;
  ⟪dfsLoop⟫;
  out ← payload ]

theorem initProgram_not_readsWidth : ¬initProgram.ReadsWidth := by decide

theorem compiled_initProgram_not_readsWidth : ¬(initProgram.program out).ReadsWidth :=
  Code.not_readsWidth_program initProgram_not_readsWidth out

/-! ## Phase 1: computing `(universeSize d, span d)` -/

/-- State after `initSetup`. -/
def initSetupData (s : Data 32) : Data 32 :=
  ((((((((s.set zero 0).set one 1).set two 2).set three 3).set four 4).set five 5).set q 2).set
    t 5).set high 0

theorem initSetup_exec {w : ℕ} {s : Data 32} (hw : Fits w 5) :
    Exec w initSetup s (initSetupData s) 9 := by
  have h0 := hw.of_le (by decide : 0 ≤ 5)
  have h1 := hw.of_le (by decide : 1 ≤ 5)
  have h2 := hw.of_le (by decide : 2 ≤ 5)
  have h3 := hw.of_le (by decide : 3 ≤ 5)
  have h4 := hw.of_le (by decide : 4 ≤ 5)
  ram_eval [initSetup, initSetupData, h0, h1, h2, h3, h4, hw]

/-- State after one iteration of `sizeBody` at depth `k`. -/
def sizeBodyData (s : Data 32) (k : ℕ) : Data 32 :=
  (((((s.set tmp (universeSize k + 1)).set tmp ((universeSize k + 1) * span k)).set
    tmp ((universeSize k + 1) * span k + 5)).set q (universeSize k * universeSize k)).set
    t ((universeSize k + 1) * span k + 5)).set high (k + 1)

theorem sizeBody_exec {w d k : ℕ} {s : Data 32} (hk : k < d) (hspan : Fits w (span d))
    (hd : Fits w d) (h1 : s.regs one = 1) (h5 : s.regs five = 5)
    (hq : s.regs q = universeSize k) (ht : s.regs t = span k) (hhigh : s.regs high = k) :
    ExecWithin w sizeBody s (sizeBodyData s k) 6 := by
  have hle : span (k + 1) ≤ span d := span_mono (by omega)
  have hu_le : universeSize (k + 1) ≤ span (k + 1) := universeSize_le_span (k + 1)
  have huk_le : universeSize k + 1 ≤ universeSize (k + 1) := by
    have := two_le_universeSize k; rw [universeSize_succ]; nlinarith
  have h_prod_le : (universeSize k + 1) * span k + 5 = span (k + 1) := by
    rw [span_succ]; omega
  have hf1 : Fits w (universeSize k + 1) := hspan.of_le (by omega)
  have hf2 : Fits w ((universeSize k + 1) * span k) := hspan.of_le (by omega)
  have hf3 : Fits w ((universeSize k + 1) * span k + 5) := hspan.of_le (by omega)
  have hf4 : Fits w (universeSize k * universeSize k) :=
    hspan.of_le (by rw [← universeSize_succ]; omega)
  have hf5 : Fits w (k + 1) := hd.of_le (by omega)
  ram_eval [sizeBody, sizeBodyData, h1, h5, hq, ht, hhigh, hf1, hf2, hf3, hf4, hf5]

/-- `sizeLoop` advances `(q, t, high)` from `(universeSize k, span k, k)` to
`(universeSize d, span d, d)` in `8 * (d - k) + 2` instructions without modifying memory. -/
theorem sizeLoop_spec {w d : ℕ} (rem : ℕ) {k : ℕ} {s : Data 32} (hk : k + rem = d)
    (hspan : Fits w (span d)) (hd : Fits w d)
    (h0 : s.regs zero = 0) (h1 : s.regs one = 1) (h2 : s.regs two = 2)
    (h3 : s.regs three = 3) (h4 : s.regs four = 4) (h5 : s.regs five = 5)
    (hdepth : s.regs depth = d) (hq : s.regs q = universeSize k) (ht : s.regs t = span k)
    (hhigh : s.regs high = k) :
    ∃ z, ExecWithin w sizeLoop s z (8 * rem + 2) ∧
      z.regs zero = 0 ∧ z.regs one = 1 ∧ z.regs two = 2 ∧
      z.regs three = 3 ∧ z.regs four = 4 ∧ z.regs five = 5 ∧
      z.regs root = s.regs root ∧ z.regs depth = d ∧
      z.regs q = universeSize d ∧ z.regs t = span d ∧ z.mem = s.mem := by
  induction rem generalizing k s with
  | zero =>
    have hkd : k = d := by omega
    subst hkd
    have hc : ¬(Cond.lt high depth).Holds s := by
      simp +decide [Cond.holds_lt, hhigh, hdepth]
    exact ⟨s, ExecWithin.loop_exit hc, h0, h1, h2, h3, h4, h5, rfl, hdepth, hq, ht, rfl⟩
  | succ rem ih =>
    have hk_lt : k < d := by omega
    have hc : (Cond.lt high depth).Holds s := by
      simp +decide [Cond.holds_lt, hhigh, hdepth, hk_lt]
    have hbody := sizeBody_exec hk_lt hspan hd h1 h5 hq ht hhigh
    let s₁ := sizeBodyData s k
    have hs₁_t : s₁.regs t = span (k + 1) := by
      change (universeSize k + 1) * span k + 5 = span (k + 1)
      rw [span_succ]
      omega
    obtain ⟨z, hz, hz0, hz1, hz2, hz3, hz4, hz5, hzr, hzd, hzq, hzt, hzm⟩ :=
      ih (k := k + 1) (s := s₁) (by omega)
        (by simpa +decide [s₁, sizeBodyData] using h0)
        (by simpa +decide [s₁, sizeBodyData] using h1)
        (by simpa +decide [s₁, sizeBodyData] using h2)
        (by simpa +decide [s₁, sizeBodyData] using h3)
        (by simpa +decide [s₁, sizeBodyData] using h4)
        (by simpa +decide [s₁, sizeBodyData] using h5)
        (by simpa +decide [s₁, sizeBodyData] using hdepth)
        (by simp +decide [s₁, sizeBodyData, universeSize_succ])
        hs₁_t
        (by simp +decide [s₁, sizeBodyData])
    refine ⟨z, (ExecWithin.loop_iter hc hbody hz).mono (by omega),
      hz0, hz1, hz2, hz3, hz4, hz5, ?_, hzd, hzq, hzt, ?_⟩
    · simpa +decide [s₁, sizeBodyData] using hzr
    · simpa +decide [s₁, sizeBodyData] using hzm

/-! ## Phase 2: populating the `(splitSize, childSpan)` table -/

/-- State after `tableSetup`. -/
def tableSetupData (s : Data 32) (base d : ℕ) : Data 32 :=
  let tbl := base + span d
  ((((((((((s.set payload tbl).set tableBase tbl).set stackBase tbl).set sp tbl).write
    tbl 0).set sp (tbl + 1)).write (tbl + 1) 0).set sp (tbl + 1 + 1)).set q 2).set t 5).set high 0

theorem tableSetup_exec {w base d : ℕ} {s : Data 32} (ha : Fits w (base + span d + 4 * (d + 1)))
    (h0 : s.regs zero = 0) (h1 : s.regs one = 1) (h2 : s.regs two = 2) (h5 : s.regs five = 5)
    (hroot : s.regs root = base) (ht : s.regs t = span d) :
    Exec w tableSetup s (tableSetupData s base d) 11 := by
  have hf_tbl : Fits w (base + span d) := ha.of_le (by omega)
  have hf_tbl1 : Fits w (base + span d + 1) := ha.of_le (by omega)
  have hf_tbl2 : Fits w (base + span d + 1 + 1) := ha.of_le (by omega)
  ram_eval [tableSetup, tableSetupData, h0, h1, h2, h5, hroot, ht, hf_tbl, hf_tbl1, hf_tbl2]

/-- State after one iteration of `tableBody` at depth `k` and pointer `sp₀`. -/
def tableBodyData (s : Data 32) (sp₀ k : ℕ) : Data 32 :=
  (((((((((s.write sp₀ (universeSize k)).set sp (sp₀ + 1)).write (sp₀ + 1) (span k)).set
    sp (sp₀ + 1 + 1)).set tmp (universeSize k + 1)).set tmp ((universeSize k + 1) * span k)).set
    tmp ((universeSize k + 1) * span k + 5)).set q (universeSize k * universeSize k)).set
    t ((universeSize k + 1) * span k + 5)).set high (k + 1)

theorem tableBody_exec {w base d k : ℕ} {s : Data 32} (hk : k < d)
    (ha : Fits w (base + span d + 4 * (d + 1)))
    (h1 : s.regs one = 1) (h5 : s.regs five = 5)
    (hsp : s.regs sp = base + span d + 2 * (k + 1))
    (hq : s.regs q = universeSize k) (ht : s.regs t = span k) (hhigh : s.regs high = k) :
    ExecWithin w tableBody s (tableBodyData s (base + span d + 2 * (k + 1)) k) 10 := by
  have hle : span (k + 1) ≤ span d := span_mono (by omega)
  have hu_le : universeSize (k + 1) ≤ span (k + 1) := universeSize_le_span (k + 1)
  have huk_le : universeSize k + 1 ≤ universeSize (k + 1) := by
    have := two_le_universeSize k; rw [universeSize_succ]; nlinarith
  have h_prod_le : (universeSize k + 1) * span k + 5 = span (k + 1) := by
    rw [span_succ]; omega
  have hf_sp1 : Fits w (base + span d + 2 * (k + 1) + 1) := ha.of_le (by omega)
  have hf_sp2 : Fits w (base + span d + 2 * (k + 1) + 1 + 1) := ha.of_le (by omega)
  have hf1 : Fits w (universeSize k + 1) := ha.of_le (by omega)
  have hf2 : Fits w ((universeSize k + 1) * span k) := ha.of_le (by omega)
  have hf3 : Fits w ((universeSize k + 1) * span k + 5) := ha.of_le (by omega)
  have hf4 : Fits w (universeSize k * universeSize k) :=
    ha.of_le (by rw [← universeSize_succ]; omega)
  have hf5 : Fits w (k + 1) := ha.of_le (by omega)
  ram_eval [tableBody, tableBodyData, h1, h5, hsp, hq, ht, hhigh,
    hf_sp1, hf_sp2, hf1, hf2, hf3, hf4, hf5]

/-- Lookup-table invariant up to depth `m`: for all `j ≤ m`, `mem (tbl + 2 * j) = splitSize j`
and `mem (tbl + 2 * j + 1) = childSpan j`. -/
def TableInv (tbl m : ℕ) (mem : ℕ → ℕ) : Prop :=
  ∀ j ≤ m, mem (tbl + 2 * j) = splitSize j ∧ mem (tbl + 2 * j + 1) = childSpan j

/-- `tableLoop` populates the lookup table from depth `k` up to `d` in `12 * (d - k) + 2`
instructions, advancing `sp` to `base + span d + 2 * (d + 1)` and preserving all memory outside
`[base + span d + 2 * (k + 1), base + span d + 2 * (d + 1))`. -/
theorem tableLoop_spec {w base d : ℕ} (rem : ℕ) {k : ℕ} {s : Data 32} (hk : k + rem = d)
    (ha : Fits w (base + span d + 4 * (d + 1)))
    (h0 : s.regs zero = 0) (h1 : s.regs one = 1) (h2 : s.regs two = 2)
    (h3 : s.regs three = 3) (h4 : s.regs four = 4) (h5 : s.regs five = 5)
    (hroot : s.regs root = base) (hdepth : s.regs depth = d)
    (hpay : s.regs payload = base + span d)
    (htbl : s.regs tableBase = base + span d)
    (hstk : s.regs stackBase = base + span d)
    (hsp : s.regs sp = base + span d + 2 * (k + 1))
    (hq : s.regs q = universeSize k) (ht : s.regs t = span k) (hhigh : s.regs high = k)
    (hinv : TableInv (base + span d) k s.mem) :
    ∃ z, ExecWithin w tableLoop s z (12 * rem + 2) ∧
      z.regs zero = 0 ∧ z.regs one = 1 ∧ z.regs two = 2 ∧
      z.regs three = 3 ∧ z.regs four = 4 ∧ z.regs five = 5 ∧
      z.regs root = base ∧ z.regs depth = d ∧
      z.regs payload = base + span d ∧
      z.regs tableBase = base + span d ∧
      z.regs stackBase = base + span d ∧
      z.regs sp = base + span d + 2 * (d + 1) ∧
      TableInv (base + span d) d z.mem ∧
      (∀ a, a < base + span d + 2 * (k + 1) ∨ base + span d + 2 * (d + 1) ≤ a →
        z.mem a = s.mem a) := by
  induction rem generalizing k s with
  | zero =>
    have hkd : k = d := by omega
    subst hkd
    have hc : ¬(Cond.lt high depth).Holds s := by
      simp +decide [Cond.holds_lt, hhigh, hdepth]
    refine ⟨s, ExecWithin.loop_exit hc, h0, h1, h2, h3, h4, h5, hroot, hdepth,
      hpay, htbl, hstk, hsp, hinv, fun _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < d := by omega
    have hc : (Cond.lt high depth).Holds s := by
      simp +decide [Cond.holds_lt, hhigh, hdepth, hk_lt]
    have hbody := tableBody_exec hk_lt ha h1 h5 hsp hq ht hhigh
    let sp₀ := base + span d + 2 * (k + 1)
    let s₁ := tableBodyData s sp₀ k
    have hs₁_sp : s₁.regs sp = base + span d + 2 * (k + 1 + 1) := by
      change sp₀ + 1 + 1 = base + span d + 2 * (k + 1 + 1)
      dsimp only [sp₀]
      omega
    have hs₁_t : s₁.regs t = span (k + 1) := by
      change (universeSize k + 1) * span k + 5 = span (k + 1)
      rw [span_succ]
      omega
    have hs₁_mem_away : ∀ a, a ≠ sp₀ → a ≠ sp₀ + 1 → s₁.mem a = s.mem a := by
      intro a ha0 ha1
      simp only [s₁, tableBodyData, Data.set_mem, Data.write_mem]
      rw [Function.update_of_ne ha1, Function.update_of_ne ha0]
    have hs₁_inv : TableInv (base + span d) (k + 1) s₁.mem := by
      intro j hj
      by_cases hjk : j ≤ k
      · rw [hs₁_mem_away _ (by dsimp only [sp₀]; omega) (by dsimp only [sp₀]; omega),
          hs₁_mem_away _ (by dsimp only [sp₀]; omega) (by dsimp only [sp₀]; omega)]
        exact hinv j hjk
      · have hj_eq : j = k + 1 := by omega
        subst hj_eq
        simp only [s₁, sp₀, tableBodyData, Data.set_mem, Data.write_mem, splitSize, childSpan]
        constructor
        · rw [Function.update_of_ne (by omega), Function.update_self]
        · rw [Function.update_self]
    obtain ⟨z, hz, hz0, hz1, hz2, hz3, hz4, hz5, hzr, hzd, hzp, hztbl, hzstk, hzsp, hzinv,
        hzframe⟩ :=
      ih (k := k + 1) (s := s₁) (by omega)
        (by simpa +decide [s₁, tableBodyData] using h0)
        (by simpa +decide [s₁, tableBodyData] using h1)
        (by simpa +decide [s₁, tableBodyData] using h2)
        (by simpa +decide [s₁, tableBodyData] using h3)
        (by simpa +decide [s₁, tableBodyData] using h4)
        (by simpa +decide [s₁, tableBodyData] using h5)
        (by simpa +decide [s₁, tableBodyData] using hroot)
        (by simpa +decide [s₁, tableBodyData] using hdepth)
        (by simpa +decide [s₁, tableBodyData] using hpay)
        (by simpa +decide [s₁, tableBodyData] using htbl)
        (by simpa +decide [s₁, tableBodyData] using hstk)
        hs₁_sp
        (by simp +decide [s₁, tableBodyData, universeSize_succ])
        hs₁_t
        (by simp +decide [s₁, tableBodyData])
        hs₁_inv
    refine ⟨z, (ExecWithin.loop_iter hc hbody hz).mono (by omega),
      hz0, hz1, hz2, hz3, hz4, hz5, hzr, hzd, hzp, hztbl, hzstk, hzsp, hzinv, ?_⟩
    intro a ha_out
    have ha_out₁ : a < base + span d + 2 * (k + 1 + 1) ∨ base + span d + 2 * (d + 1) ≤ a := by
      omega
    rw [hzframe a ha_out₁,
      hs₁_mem_away a (by dsimp only [sp₀]; omega) (by dsimp only [sp₀]; omega)]

/-! ## Phase 3: depth-first empty-header initialization -/

/-- State after `dfsSetup`. -/
def dfsSetupData (s : Data 32) (base d : ℕ) : Data 32 :=
  let lw := base + span d + 2 * (d + 1)
  ((((s.set low lw).set p base).set x d).set kind 0).set runFlag 1

theorem dfsSetup_exec {w base d : ℕ} {s : Data 32}
    (h0 : s.regs zero = 0) (h1 : s.regs one = 1) (hroot : s.regs root = base)
    (hdepth : s.regs depth = d) (hsp : s.regs sp = base + span d + 2 * (d + 1)) :
    Exec w dfsSetup s (dfsSetupData s base d) 5 := by
  ram_eval [dfsSetup, dfsSetupData, h0, h1, hroot, hdepth, hsp]

/-- Constant registers and lookup-table invariant preserved throughout the Phase 3 DFS loop. -/
def DfsConst (base d : ℕ) (s : Data 32) : Prop :=
  s.regs zero = 0 ∧ s.regs one = 1 ∧ s.regs two = 2 ∧
    s.regs three = 3 ∧ s.regs four = 4 ∧ s.regs five = 5 ∧
    s.regs root = base ∧ s.regs depth = d ∧
    s.regs payload = base + span d ∧
    s.regs tableBase = base + span d ∧
    s.regs stackBase = base + span d ∧
    s.regs low = base + span d + 2 * (d + 1) ∧
    TableInv (base + span d) d s.mem

/-- Active DFS state at pointer `ptr`, subtree depth `k`, and phase `kindVal` (`0` = enter,
`1` = exit). -/
def DfsState (base d ptr k kindVal : ℕ) (s : Data 32) : Prop :=
  DfsConst base d s ∧
    s.regs p = ptr ∧ s.regs x = k ∧ s.regs kind = kindVal ∧ s.regs runFlag = 1

/-- State after `dfsBody` at a leaf (`kind = 0`, `x = 0`). -/
def dfsLeafData (s : Data 32) (base d ptr : ℕ) : Data 32 :=
  let tbl := base + span d
  (((((((((((s.write ptr 0).set tmp (0 * 2)).set addr (tbl + 0 * 2)).set q 0).set
    addr (tbl + 0 * 2 + 1)).set t 0).set child (ptr + 3)).write (ptr + 3) 0).set
    child (ptr + 3 + 1)).write (ptr + 3 + 1) 0).set p (ptr + 5)).set kind 1

theorem dfsBody_leaf_exec {w base d ptr : ℕ} {s : Data 32}
    (hs : DfsState base d ptr 0 0 s) (ha : Fits w (base + span d + 4 * (d + 1)))
    (hptr_end : ptr + 5 ≤ base + span d) :
    ExecWithin w dfsBody s (dfsLeafData s base d ptr) 14 := by
  obtain ⟨⟨h0, h1, h2, h3, _, h5, _, _, _, htbl, _, _, hinv⟩, hp, hx, hkind, _⟩ := hs
  have htbl0 := (hinv 0 (by omega)).1
  have htbl1 := (hinv 0 (by omega)).2
  dsimp only [splitSize, childSpan] at htbl0 htbl1
  have hm0 : (s.write ptr 0).mem (base + span d + 0 * 2) = 0 := by
    rw [Data.write_mem, Function.update_of_ne (by omega)]
    exact htbl0
  have hm1 : (s.write ptr 0).mem (base + span d + 0 * 2 + 1) = 0 := by
    rw [Data.write_mem, Function.update_of_ne (by omega)]
    exact htbl1
  have hf_tmp : Fits w (0 * 2) := ha.of_le (by omega)
  have hf_a0 : Fits w (base + span d + 0 * 2) := ha.of_le (by omega)
  have hf_a1 : Fits w (base + span d + 0 * 2 + 1) := ha.of_le (by omega)
  have hf_c3 : Fits w (ptr + 3) := ha.of_le (by omega)
  have hf_c4 : Fits w (ptr + 3 + 1) := ha.of_le (by omega)
  have hf_p5 : Fits w (ptr + 5) := ha.of_le (by omega)
  ram_eval [dfsBody, dfsEnterBody, dfsExitBody, dfsLeafData,
    h0, h1, h2, h3, h5, htbl, hp, hx, hkind, hm0, hm1,
    hf_tmp, hf_a0, hf_a1, hf_c3, hf_c4, hf_p5]

/-- State after `dfsBody` entering an internal node (`kind = 0`, `x = k + 1`). -/
def dfsEnterSuccData (s : Data 32) (base d ptr k : ℕ) : Data 32 :=
  let tbl := base + span d
  let lw := base + span d + 2 * (d + 1)
  (((((((((((((s.write ptr 0).set tmp ((k + 1) * 2)).set
    addr (tbl + (k + 1) * 2)).set q (universeSize k)).set
    addr (tbl + (k + 1) * 2 + 1)).set t (span k)).set
    child (ptr + 3)).write (ptr + 3) (universeSize k)).set
    child (ptr + 3 + 1)).write (ptr + 3 + 1) (span k)).set
    p (ptr + 5)).set addr (lw + (k + 1))).write (lw + (k + 1)) (universeSize k)).set
    x (k + 1 - 1)

theorem dfsBody_enter_succ_exec {w base d ptr k : ℕ} {s : Data 32}
    (hs : DfsState base d ptr (k + 1) 0 s) (hk : k + 1 ≤ d)
    (ha : Fits w (base + span d + 4 * (d + 1))) (hptr_end : ptr + span (k + 1) ≤ base + span d) :
    ExecWithin w dfsBody s (dfsEnterSuccData s base d ptr k) 17 := by
  obtain ⟨⟨h0, h1, h2, h3, _, h5, _, _, _, htbl, _, hlow, hinv⟩, hp, hx, hkind, _⟩ := hs
  have h5_le := five_le_span (k + 1)
  have htbl0 := (hinv (k + 1) hk).1
  have htbl1 := (hinv (k + 1) hk).2
  dsimp only [splitSize, childSpan] at htbl0 htbl1
  have hm0 : (s.write ptr 0).mem (base + span d + (k + 1) * 2) = universeSize k := by
    rw [Data.write_mem, Function.update_of_ne (by omega), Nat.mul_comm (k + 1) 2]
    exact htbl0
  have hm1 : (s.write ptr 0).mem (base + span d + (k + 1) * 2 + 1) = span k := by
    rw [Data.write_mem, Function.update_of_ne (by omega), Nat.mul_comm (k + 1) 2]
    exact htbl1
  have hf_tmp : Fits w ((k + 1) * 2) := ha.of_le (by omega)
  have hf_a0 : Fits w (base + span d + (k + 1) * 2) := ha.of_le (by omega)
  have hf_a1 : Fits w (base + span d + (k + 1) * 2 + 1) := ha.of_le (by omega)
  have hf_c3 : Fits w (ptr + 3) := ha.of_le (by omega)
  have hf_c4 : Fits w (ptr + 3 + 1) := ha.of_le (by omega)
  have hf_p5 : Fits w (ptr + 5) := ha.of_le (by omega)
  have hf_lw : Fits w (base + span d + 2 * (d + 1) + (k + 1)) := ha.of_le (by omega)
  have hf_x : Fits w (k + 1 - 1) := ha.of_le (by omega)
  have hne : k + 1 ≠ 0 := by omega
  ram_eval [dfsBody, dfsEnterBody, dfsExitBody, dfsEnterSuccData,
    h0, h1, h2, h3, h5, htbl, hlow, hp, hx, hkind, hm0, hm1, hne,
    hf_tmp, hf_a0, hf_a1, hf_c3, hf_c4, hf_p5, hf_lw, hf_x]

/-- State after `dfsBody` advancing from one child to the next cluster (`kind = 1`, `x = k`,
`mem (low + k + 1) = cnt + 1`). -/
def dfsNextClusterData (s : Data 32) (base d k cnt : ℕ) : Data 32 :=
  let lw := base + span d + 2 * (d + 1)
  s.set x (k + 1) |>.set addr (lw + (k + 1)) |>.set present (cnt + 1)
    |>.set present (cnt + 1 - 1) |>.write (lw + (k + 1)) (cnt + 1 - 1)
    |>.set x (k + 1 - 1) |>.set kind 0

theorem dfsBody_next_cluster_exec {w base d ptr k cnt : ℕ} {s : Data 32}
    (hs : DfsState base d ptr k 1 s) (hk : k + 1 ≤ d)
    (hcnt : s.mem (base + span d + 2 * (d + 1) + (k + 1)) = cnt + 1)
    (ha : Fits w (base + span d + 4 * (d + 1)))
    (hcnt_fit : Fits w (cnt + 1 - 1)) :
    ExecWithin w dfsBody s (dfsNextClusterData s base d k cnt) 13 := by
  obtain ⟨⟨h0, h1, _, _, _, _, _, hdepth, _, _, _, hlow, _⟩, _, hx, hkind, _⟩ := hs
  have hf_k1 : Fits w (k + 1) := ha.of_le (by omega)
  have hf_lw : Fits w (base + span d + 2 * (d + 1) + (k + 1)) := ha.of_le (by omega)
  have hf_k : Fits w (k + 1 - 1) := ha.of_le (by omega)
  have hnot_lt : ¬d < k + 1 := by omega
  have hne : cnt + 1 ≠ 0 := by omega
  ram_eval [dfsBody, dfsEnterBody, dfsExitBody, dfsNextClusterData,
    h0, h1, hdepth, hlow, hx, hkind, hcnt, hnot_lt, hne,
    hf_k1, hf_lw, hcnt_fit, hf_k]

/-- State after `dfsBody` finishing all clusters of a depth-`k + 1` node (`kind = 1`, `x = k`,
`mem (low + k + 1) = 0`). -/
def dfsExitNodeData (s : Data 32) (base d k : ℕ) : Data 32 :=
  let lw := base + span d + 2 * (d + 1)
  (((s.set x (k + 1)).set addr (lw + (k + 1))).set present 0).set kind 1

theorem dfsBody_exit_node_exec {w base d ptr k : ℕ} {s : Data 32}
    (hs : DfsState base d ptr k 1 s) (hk : k + 1 ≤ d)
    (hrem : s.mem (base + span d + 2 * (d + 1) + (k + 1)) = 0)
    (ha : Fits w (base + span d + 4 * (d + 1))) :
    ExecWithin w dfsBody s (dfsExitNodeData s base d k) 9 := by
  obtain ⟨⟨h0, h1, _, _, _, _, _, hdepth, _, _, _, hlow, _⟩, _, hx, hkind, _⟩ := hs
  have hf_k1 : Fits w (k + 1) := ha.of_le (by omega)
  have hf_lw : Fits w (base + span d + 2 * (d + 1) + (k + 1)) := ha.of_le (by omega)
  have hnot_lt : ¬d < k + 1 := by omega
  ram_eval [dfsBody, dfsEnterBody, dfsExitBody, dfsExitNodeData,
    h0, h1, hdepth, hlow, hx, hkind, hrem, hnot_lt, hf_k1, hf_lw]

/-- State after `dfsBody` exiting the root (`kind = 1`, `x = d`). -/
def dfsFinishData (s : Data 32) (d : ℕ) : Data 32 :=
  (s.set x (d + 1)).set runFlag 0

theorem dfsBody_finish_exec {w base d ptr : ℕ} {s : Data 32}
    (hs : DfsState base d ptr d 1 s) (ha : Fits w (base + span d + 4 * (d + 1))) :
    ExecWithin w dfsBody s (dfsFinishData s d) 5 := by
  obtain ⟨⟨h0, h1, _, _, _, _, _, hdepth, _, _, _, _, _⟩, _, hx, hkind, _⟩ := hs
  have hf_d1 : Fits w (d + 1) := ha.of_le (by omega)
  have hlt : d < d + 1 := by omega
  ram_eval [dfsBody, dfsEnterBody, dfsExitBody, dfsFinishData,
    h0, h1, hdepth, hx, hkind, hlt, hf_d1]

private theorem dfsState_cond_holds {base d ptr k kindVal : ℕ} {s : Data 32}
    (hs : DfsState base d ptr k kindVal s) : (Cond.lt zero runFlag).Holds s := by
  obtain ⟨⟨h0, _⟩, _, _, _, hrun⟩ := hs
  simp +decide [Cond.holds_lt, h0, hrun]

private theorem tableInv_congr {tbl d : ℕ} {m m' : ℕ → ℕ}
    (hinv : TableInv tbl d m)
    (h : ∀ a, tbl ≤ a → a < tbl + 2 * (d + 1) → m' a = m a) :
    TableInv tbl d m' := by
  intro j hj
  rw [h (tbl + 2 * j) (by omega) (by omega), h (tbl + 2 * j + 1) (by omega) (by omega)]
  exact hinv j hj

/-- Cluster-iteration helper for `dfs_subtree_spec` at depth `k + 1`: given the induction
hypothesis `ih` at depth `k`, initializes the remaining `cnt` clusters starting at index `m`
(where `m + cnt = universeSize k`) in `cnt * (8 * span k)` loop instructions. -/
theorem dfs_clusters_spec {w base d ptr k : ℕ}
    (hk : k + 1 ≤ d) (ha : Fits w (base + span d + 4 * (d + 1)))
    (hptr_end : ptr + span (k + 1) ≤ base + span d)
    (ih : ∀ {p₀ : ℕ} {s₀ : Data 32},
      DfsState base d p₀ k 0 s₀ → p₀ + span k ≤ base + span d →
      ∃ s₁, DfsState base d (p₀ + span k) k 1 s₁ ∧
        Rep (Tree.empty k) p₀ s₁.mem ∧
        (∀ a, (a < p₀ ∨ p₀ + span k ≤ a) →
          (a < base + span d + 2 * (d + 1) + 1 ∨
            base + span d + 2 * (d + 1) + k < a) →
          s₁.mem a = s₀.mem a) ∧
        (∀ z T_cont, ExecWithin w dfsLoop s₁ z T_cont →
          ExecWithin w dfsLoop s₀ z (8 * span k - 15 + T_cont)))
    (cnt : ℕ) {m : ℕ} {s : Data 32} (hm : m + cnt = universeSize k)
    (hs : DfsState base d (ptr + 5 + (m + 1) * span k) k 1 s)
    (hcnt : s.mem (base + span d + 2 * (d + 1) + (k + 1)) = cnt)
    (hprev : ∀ i : Fin (universeSize k), i.val < m →
      Rep (Tree.empty k) (ptr + clusterOffset k i.val) s.mem) :
    ∃ s', DfsState base d (ptr + span (k + 1)) k 1 s' ∧
      s'.mem (base + span d + 2 * (d + 1) + (k + 1)) = 0 ∧
      (∀ i : Fin (universeSize k),
        Rep (Tree.empty k) (ptr + clusterOffset k i.val) s'.mem) ∧
      (∀ a, (a < ptr + 5 + (m + 1) * span k ∨ ptr + span (k + 1) ≤ a) →
        (a < base + span d + 2 * (d + 1) + 1 ∨
          base + span d + 2 * (d + 1) + (k + 1) < a) →
        s'.mem a = s.mem a) ∧
      (∀ z T_cont, ExecWithin w dfsLoop s' z T_cont →
        ExecWithin w dfsLoop s z (cnt * (8 * span k) + T_cont)) := by
  induction cnt generalizing m s with
  | zero =>
    have hm_eq : m = universeSize k := by omega
    have hptr_eq : ptr + 5 + (m + 1) * span k = ptr + span (k + 1) := by
      rw [hm_eq, span_succ]; omega
    refine ⟨s, hptr_eq ▸ hs, hcnt, fun i => hprev i (hm_eq ▸ i.isLt),
      fun _ _ _ => rfl, fun z T_cont hcont => by
        simpa only [Nat.zero_mul, Nat.zero_add] using hcont⟩
  | succ cnt ih_cnt =>
    have hm_lt : m < universeSize k := by omega
    have hu_le : universeSize k ≤ span d :=
      (universeSize_le_span k).trans (span_mono (by omega))
    have hcnt_fit : Fits w (cnt + 1 - 1) := ha.of_le (by omega)
    have hstep := dfsBody_next_cluster_exec hs hk hcnt ha hcnt_fit
    let p_m := ptr + 5 + (m + 1) * span k
    let lw := base + span d + 2 * (d + 1)
    let s₁ := dfsNextClusterData s base d k cnt
    have hs₁_away : ∀ a, a ≠ lw + (k + 1) → s₁.mem a = s.mem a := by
      intro a ha_ne
      simp only [s₁, dfsNextClusterData, Data.set_mem, Data.write_mem]
      exact Function.update_of_ne ha_ne _ _
    have hp_m_end : p_m + span k ≤ ptr + span (k + 1) := by
      have : p_m = ptr + clusterOffset k m := by dsimp only [p_m, clusterOffset]; omega
      have hce := cluster_end_le_span k hm_lt
      omega
    have hs₁_state : DfsState base d p_m k 0 s₁ := by
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
      · simpa +decide [s₁, dfsNextClusterData] using hs.1.1
      · simpa +decide [s₁, dfsNextClusterData] using hs.1.2.1
      · simpa +decide [s₁, dfsNextClusterData] using hs.1.2.2.1
      · simpa +decide [s₁, dfsNextClusterData] using hs.1.2.2.2.1
      · simpa +decide [s₁, dfsNextClusterData] using hs.1.2.2.2.2.1
      · simpa +decide [s₁, dfsNextClusterData] using hs.1.2.2.2.2.2.1
      · simpa +decide [s₁, dfsNextClusterData] using hs.1.2.2.2.2.2.2.1
      · simpa +decide [s₁, dfsNextClusterData] using hs.1.2.2.2.2.2.2.2.1
      · simpa +decide [s₁, dfsNextClusterData] using hs.1.2.2.2.2.2.2.2.2.1
      · simpa +decide [s₁, dfsNextClusterData] using hs.1.2.2.2.2.2.2.2.2.2.1
      · simpa +decide [s₁, dfsNextClusterData] using hs.1.2.2.2.2.2.2.2.2.2.2.1
      · simpa +decide [s₁, dfsNextClusterData] using hs.1.2.2.2.2.2.2.2.2.2.2.2.1
      · apply tableInv_congr hs.1.2.2.2.2.2.2.2.2.2.2.2.2
        intro a _ ha_hi
        exact hs₁_away a (by dsimp only [lw]; omega)
      · simpa +decide [s₁, dfsNextClusterData] using hs.2.1
      · change k + 1 - 1 = k; omega
      · rfl
      · simpa +decide [s₁, dfsNextClusterData] using hs.2.2.2.2
    obtain ⟨s₂, hs₂_state, hs₂_rep, hs₂_frame, hs₂_cps⟩ :=
      ih hs₁_state (hp_m_end.trans hptr_end)
    have hs₂_p_eq : p_m + span k = ptr + 5 + (m + 1 + 1) * span k := by
      dsimp only [p_m]; ring
    have hs₂_cnt : s₂.mem (lw + (k + 1)) = cnt := by
      rw [hs₂_frame (lw + (k + 1))
        (Or.inr (by have := hp_m_end.trans hptr_end; dsimp only [lw]; omega))
        (Or.inr (by dsimp only [lw]; omega))]
      simp only [s₁, lw, dfsNextClusterData, Data.set_mem, Data.write_mem, Function.update_self]
      omega
    have hs₂_prev : ∀ i : Fin (universeSize k), i.val < m + 1 →
        Rep (Tree.empty k) (ptr + clusterOffset k i.val) s₂.mem := by
      intro i hi
      by_cases him : i.val < m
      · apply rep_frame (hprev i him)
        intro a ha_lo ha_hi
        have hce := cluster_end_le_clusterOffset k him
        have hce_span := cluster_end_le_span k i.isLt
        have hp_m_eq : p_m = ptr + clusterOffset k m := by dsimp only [p_m, clusterOffset]; omega
        rw [hs₂_frame a (Or.inl (by omega)) (Or.inl (by omega))]
        exact hs₁_away a (by omega)
      · have hi_eq : i.val = m := by omega
        have hp_eq : ptr + clusterOffset k i.val = p_m := by
          dsimp only [p_m, clusterOffset]; rw [hi_eq]; omega
        simpa only [hp_eq] using hs₂_rep
    obtain ⟨s', hs'_state, hs'_cnt, hs'_all, hs'_frame, hs'_cps⟩ :=
      ih_cnt (m := m + 1) (s := s₂) (by omega)
        (hs₂_p_eq ▸ hs₂_state) hs₂_cnt hs₂_prev
    refine ⟨s', hs'_state, hs'_cnt, hs'_all, ?_, ?_⟩
    · intro a ha_tree ha_cnt
      have ha_tree₂ : a < ptr + 5 + (m + 1 + 1) * span k ∨ ptr + span (k + 1) ≤ a := by
        rcases ha_tree with hlt | hge
        · exact Or.inl (by omega)
        · exact Or.inr hge
      rw [hs'_frame a ha_tree₂ ha_cnt]
      have ha_tree₁ : a < p_m ∨ p_m + span k ≤ a := by
        rcases ha_tree with hlt | hge
        · exact Or.inl hlt
        · exact Or.inr (hp_m_end.trans hge)
      have ha_cnt₁ : a < lw + 1 ∨ lw + k < a := by omega
      rw [hs₂_frame a ha_tree₁ ha_cnt₁]
      exact hs₁_away a (by omega)
    · intro z T_cont hcont
      have h1 := hs'_cps z T_cont hcont
      have h2 := hs₂_cps z (cnt * (8 * span k) + T_cont) h1
      have h3 := ExecWithin.loop_iter (dfsState_cond_holds hs) hstep h2
      have h5_le := five_le_span k
      have hmul : (cnt + 1) * (8 * span k) = cnt * (8 * span k) + 8 * span k :=
        Nat.succ_mul cnt (8 * span k)
      exact h3.mono (by omega)

/-- Subtree initialization theorem: from `DfsState base d ptr k 0 s` with `k ≤ d` and
`ptr + span k ≤ base + span d`, the DFS loop initializes `Rep (Tree.empty k) ptr s'.mem`
and reaches `DfsState base d (ptr + span k) k 1 s'` in at most `8 * span k - 15` instructions,
modifying only `[ptr, ptr + span k)` and counters `[low + 1, low + k]`. -/
theorem dfs_subtree_spec {w base d : ℕ} (k : ℕ) (hk : k ≤ d)
    (ha : Fits w (base + span d + 4 * (d + 1))) :
    ∀ {ptr : ℕ} {s : Data 32},
      DfsState base d ptr k 0 s → ptr + span k ≤ base + span d →
      ∃ s', DfsState base d (ptr + span k) k 1 s' ∧
        Rep (Tree.empty k) ptr s'.mem ∧
        (∀ a, (a < ptr ∨ ptr + span k ≤ a) →
          (a < base + span d + 2 * (d + 1) + 1 ∨
            base + span d + 2 * (d + 1) + k < a) →
          s'.mem a = s.mem a) ∧
        (∀ z T_cont, ExecWithin w dfsLoop s' z T_cont →
          ExecWithin w dfsLoop s z (8 * span k - 15 + T_cont)) := by
  induction k with
  | zero =>
    intro ptr s hs hptr_end
    have hstep := dfsBody_leaf_exec hs ha hptr_end
    let s' := dfsLeafData s base d ptr
    have hs'_away : ∀ a, a < ptr ∨ ptr + 5 ≤ a → s'.mem a = s.mem a := by
      intro a ha_out
      simp only [s', dfsLeafData, Data.set_mem, Data.write_mem]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
    have hs'_state : DfsState base d (ptr + span 0) 0 1 s' := by
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
      · simpa +decide [s', dfsLeafData] using hs.1.1
      · simpa +decide [s', dfsLeafData] using hs.1.2.1
      · simpa +decide [s', dfsLeafData] using hs.1.2.2.1
      · simpa +decide [s', dfsLeafData] using hs.1.2.2.2.1
      · simpa +decide [s', dfsLeafData] using hs.1.2.2.2.2.1
      · simpa +decide [s', dfsLeafData] using hs.1.2.2.2.2.2.1
      · simpa +decide [s', dfsLeafData] using hs.1.2.2.2.2.2.2.1
      · simpa +decide [s', dfsLeafData] using hs.1.2.2.2.2.2.2.2.1
      · simpa +decide [s', dfsLeafData] using hs.1.2.2.2.2.2.2.2.2.1
      · simpa +decide [s', dfsLeafData] using hs.1.2.2.2.2.2.2.2.2.2.1
      · simpa +decide [s', dfsLeafData] using hs.1.2.2.2.2.2.2.2.2.2.2.1
      · simpa +decide [s', dfsLeafData] using hs.1.2.2.2.2.2.2.2.2.2.2.2.1
      · apply tableInv_congr hs.1.2.2.2.2.2.2.2.2.2.2.2.2
        intro a ha_lo _
        exact hs'_away a (Or.inr (by dsimp only [span] at hptr_end; omega))
      · rfl
      · simpa +decide [s', dfsLeafData] using hs.2.2.1
      · rfl
      · simpa +decide [s', dfsLeafData] using hs.2.2.2.2
    have hs'_rep : Rep (Tree.empty 0) ptr s'.mem := by
      change Header 0 none ptr s'.mem
      simp only [Header, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, splitSize, childSpan,
        s', dfsLeafData, Data.set_mem, Data.write_mem]
      refine ⟨?_, trivial, ?_, ?_⟩
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_self]
      · rw [Function.update_of_ne (by omega), Function.update_self]
      · rw [Function.update_self]
    refine ⟨s', hs'_state, hs'_rep, fun a ha_tree _ => hs'_away a ha_tree, ?_⟩
    intro z T_cont hcont
    exact (ExecWithin.loop_iter (dfsState_cond_holds hs) hstep hcont).mono
      (by dsimp only [span]; omega)
  | succ k ih =>
    intro ptr s hs hptr_end
    have ih' {p₀ : ℕ} {s₀ : Data 32} := ih (by omega) (ptr := p₀) (s := s₀)
    have hstep_enter := dfsBody_enter_succ_exec hs hk ha hptr_end
    let lw := base + span d + 2 * (d + 1)
    let s₀ := dfsEnterSuccData s base d ptr k
    have hs₀_away : ∀ a, (a < ptr ∨ ptr + 5 ≤ a) → a ≠ lw + (k + 1) → s₀.mem a = s.mem a := by
      intro a ha_ptr ha_lw
      simp only [s₀, dfsEnterSuccData, Data.set_mem, Data.write_mem]
      rw [Function.update_of_ne ha_lw, Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    have hs₀_hdr : Header (k + 1) none ptr s₀.mem := by
      simp only [Header, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, splitSize, childSpan,
        s₀, dfsEnterSuccData, Data.set_mem, Data.write_mem]
      have h5_le := five_le_span (k + 1)
      refine ⟨?_, trivial, ?_, ?_⟩
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_self]
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_self]
      · rw [Function.update_of_ne (by omega), Function.update_self]
    have hs₀_cnt : s₀.mem (lw + (k + 1)) = universeSize k := by
      simp only [s₀, dfsEnterSuccData, Data.set_mem, Data.write_mem]
      rw [Function.update_self]
    have hs₀_state : DfsState base d (ptr + 5) k 0 s₀ := by
      have h5_le := five_le_span (k + 1)
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
      · simpa +decide [s₀, dfsEnterSuccData] using hs.1.1
      · simpa +decide [s₀, dfsEnterSuccData] using hs.1.2.1
      · simpa +decide [s₀, dfsEnterSuccData] using hs.1.2.2.1
      · simpa +decide [s₀, dfsEnterSuccData] using hs.1.2.2.2.1
      · simpa +decide [s₀, dfsEnterSuccData] using hs.1.2.2.2.2.1
      · simpa +decide [s₀, dfsEnterSuccData] using hs.1.2.2.2.2.2.1
      · simpa +decide [s₀, dfsEnterSuccData] using hs.1.2.2.2.2.2.2.1
      · simpa +decide [s₀, dfsEnterSuccData] using hs.1.2.2.2.2.2.2.2.1
      · simpa +decide [s₀, dfsEnterSuccData] using hs.1.2.2.2.2.2.2.2.2.1
      · simpa +decide [s₀, dfsEnterSuccData] using hs.1.2.2.2.2.2.2.2.2.2.1
      · simpa +decide [s₀, dfsEnterSuccData] using hs.1.2.2.2.2.2.2.2.2.2.2.1
      · simpa +decide [s₀, dfsEnterSuccData] using hs.1.2.2.2.2.2.2.2.2.2.2.2.1
      · apply tableInv_congr hs.1.2.2.2.2.2.2.2.2.2.2.2.2
        intro a ha_lo ha_hi
        exact hs₀_away a (Or.inr (by omega)) (by omega)
      · rfl
      · change k + 1 - 1 = k; omega
      · simpa +decide [s₀, dfsEnterSuccData] using hs.2.2.2.1
      · simpa +decide [s₀, dfsEnterSuccData] using hs.2.2.2.2
    have hsum_end : (ptr + 5) + span k ≤ base + span d := by
      have := summary_end_le_span k
      dsimp only [summaryOffset] at this
      omega
    obtain ⟨s₁, hs₁_state, hs₁_sum_rep, hs₁_frame, hs₁_cps⟩ := ih' hs₀_state hsum_end
    have hs₁_p_eq : ptr + 5 + span k = ptr + 5 + (0 + 1) * span k := by ring
    have hs₁_cnt : s₁.mem (lw + (k + 1)) = universeSize k := by
      rw [hs₁_frame (lw + (k + 1)) (Or.inr (by omega)) (Or.inr (by omega))]
      exact hs₀_cnt
    obtain ⟨s₂, hs₂_state, hs₂_cnt, hs₂_clusters, hs₂_frame, hs₂_cps⟩ :=
      dfs_clusters_spec hk ha hptr_end ih' (universeSize k) (m := 0) (s := s₁)
        (by omega) (hs₁_p_eq ▸ hs₁_state) hs₁_cnt (fun i hi => by omega)
    have hstep_exit := dfsBody_exit_node_exec hs₂_state hk hs₂_cnt ha
    let s' := dfsExitNodeData s₂ base d k
    have hs'_mem : s'.mem = s₂.mem := rfl
    have hs'_state : DfsState base d (ptr + span (k + 1)) (k + 1) 1 s' := by
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
      · simpa +decide [s', dfsExitNodeData] using hs₂_state.1.1
      · simpa +decide [s', dfsExitNodeData] using hs₂_state.1.2.1
      · simpa +decide [s', dfsExitNodeData] using hs₂_state.1.2.2.1
      · simpa +decide [s', dfsExitNodeData] using hs₂_state.1.2.2.2.1
      · simpa +decide [s', dfsExitNodeData] using hs₂_state.1.2.2.2.2.1
      · simpa +decide [s', dfsExitNodeData] using hs₂_state.1.2.2.2.2.2.1
      · simpa +decide [s', dfsExitNodeData] using hs₂_state.1.2.2.2.2.2.2.1
      · simpa +decide [s', dfsExitNodeData] using hs₂_state.1.2.2.2.2.2.2.2.1
      · simpa +decide [s', dfsExitNodeData] using hs₂_state.1.2.2.2.2.2.2.2.2.1
      · simpa +decide [s', dfsExitNodeData] using hs₂_state.1.2.2.2.2.2.2.2.2.2.1
      · simpa +decide [s', dfsExitNodeData] using hs₂_state.1.2.2.2.2.2.2.2.2.2.2.1
      · simpa +decide [s', dfsExitNodeData] using hs₂_state.1.2.2.2.2.2.2.2.2.2.2.2.1
      · exact hs₂_state.1.2.2.2.2.2.2.2.2.2.2.2.2
      · simpa +decide [s', dfsExitNodeData] using hs₂_state.2.1
      · rfl
      · rfl
      · simpa +decide [s', dfsExitNodeData] using hs₂_state.2.2.2.2
    have hs'_hdr : Header (k + 1) none ptr s'.mem := by
      have h5_le := five_le_span (k + 1)
      apply (header_congr ?_).mp hs₀_hdr
      intro a ha_lt5
      rw [hs'_mem,
        hs₂_frame (ptr + a) (Or.inl (by omega)) (Or.inl (by omega)),
        hs₁_frame (ptr + a) (Or.inl (by omega)) (Or.inl (by omega))]
    have hs'_sum : Rep (Tree.empty k) (ptr + summaryOffset) s'.mem := by
      have hsum_le := summary_end_le_span k
      have hso : summaryOffset = 5 := rfl
      apply rep_frame hs₁_sum_rep
      intro a ha_lo ha_hi
      rw [hs'_mem]
      exact hs₂_frame a (Or.inl (by omega)) (Or.inl (by omega))
    refine ⟨s', hs'_state, ⟨hs'_hdr, hs'_sum, hs₂_clusters⟩, ?_, ?_⟩
    · intro a ha_tree ha_cnt
      have h5_le := five_le_span k
      have hsum_le := summary_end_le_span k
      dsimp only [summaryOffset] at hsum_le
      rw [hs'_mem,
        hs₂_frame a (by omega) ha_cnt,
        hs₁_frame a (by omega) (by omega),
        hs₀_away a (by omega) (by omega)]
    · intro z T_cont hcont
      have h_exit := ExecWithin.loop_iter (dfsState_cond_holds hs₂_state) hstep_exit hcont
      have h_clus := hs₂_cps z (9 + T_cont + 2) h_exit
      have h_sum := hs₁_cps z (universeSize k * (8 * span k) + (9 + T_cont + 2)) h_clus
      have h_enter := ExecWithin.loop_iter (dfsState_cond_holds hs) hstep_enter h_sum
      have h5_le := five_le_span k
      apply h_enter.mono
      rw [span_succ]
      have h_alg : universeSize k * (8 * span k) + 8 * span k =
        8 * ((universeSize k + 1) * span k) := by ring
      omega

/-- Complete Phase 3 DFS loop specification: from `DfsState base d base d 0 s`, `dfsLoop`
terminates in at most `8 * span d - 6` instructions, establishing `Rep (Tree.empty d) base z.mem`,
 preserving `root`, `payload`, and `stackBase`, and modifying only `[base, base + span d)` and
`[base + span d + 2 * (d + 1) + 1, base + span d + 3 * d + 2]`. -/
theorem dfsLoop_spec {w base d : ℕ} {s : Data 32}
    (hs : DfsState base d base d 0 s) (ha : Fits w (base + span d + 4 * (d + 1))) :
    ∃ z, ExecWithin w dfsLoop s z (8 * span d - 6) ∧
      Rep (Tree.empty d) base z.mem ∧
      z.regs root = base ∧
      z.regs payload = base + span d ∧
      z.regs stackBase = base + span d ∧
      (∀ a, (a < base ∨ base + span d ≤ a) →
        (a < base + span d + 2 * (d + 1) + 1 ∨
          base + span d + 2 * (d + 1) + d < a) →
        z.mem a = s.mem a) := by
  obtain ⟨s', hs'_state, hs'_rep, hs'_frame, hs'_cps⟩ :=
    dfs_subtree_spec d le_rfl ha hs le_rfl
  have hfinish := dfsBody_finish_exec hs'_state ha
  let z := dfsFinishData s' d
  have hc_exit : ¬(Cond.lt zero runFlag).Holds z := by
    simp +decide [z, dfsFinishData, Cond.holds_lt]
  have hcont := ExecWithin.loop_iter (dfsState_cond_holds hs'_state) hfinish
    (ExecWithin.loop_exit hc_exit)
  have h5_le := five_le_span d
  have hrun : ExecWithin w dfsLoop s z (8 * span d - 6) :=
    (hs'_cps z (5 + 2 + 2) hcont).mono (by omega)
  refine ⟨z, hrun, hs'_rep, ?_, ?_, ?_, hs'_frame⟩
  · simpa +decide [z, dfsFinishData] using hs'_state.1.2.2.2.2.2.2.1
  · simpa +decide [z, dfsFinishData] using hs'_state.1.2.2.2.2.2.2.2.2.1
  · simpa +decide [z, dfsFinishData] using hs'_state.1.2.2.2.2.2.2.2.2.2.2.1

/-! ## Complete initializer specifications -/

/-- Complete structured execution of `initProgram` (excluding only the final flat `halt`):
from any state with `s.regs root = base` and `s.regs depth = d`, `initProgram` executes in at
most `8 * span d + 20 * d + 24` instructions, establishes `Rep (Tree.empty d) base z.mem`,
preserves `z.regs root = base`, sets `z.regs stackBase = base + span d` and
`z.regs out = base + span d`, and modifies no memory outside `[base, base + span d + 4 * (d + 1))`.
-/
theorem init_dispatch_spec {w base d : ℕ} {s : Data 32}
    (ha : Fits w (base + span d + 4 * (d + 1)))
    (hroot : s.regs root = base) (hdepth : s.regs depth = d) :
    ∃ z, ExecWithin w initProgram s z (8 * span d + 20 * d + 24) ∧
      Rep (Tree.empty d) base z.mem ∧
      z.regs root = base ∧
      z.regs stackBase = base + span d ∧
      z.regs out = base + span d ∧
      (∀ a, a < base ∨ base + span d + 4 * (d + 1) ≤ a → z.mem a = s.mem a) := by
  have h5_le := five_le_span d
  have hw5 : Fits w 5 := ha.of_le (by omega)
  have hspan : Fits w (span d) := ha.of_le (by omega)
  have hd : Fits w d := ha.of_le (by omega)
  have h1 := (initSetup_exec (s := s) hw5).within
  let s₁ := initSetupData s
  obtain ⟨s₂, h2, hs₂0, hs₂1, hs₂2, hs₂3, hs₂4, hs₂5, hs₂r, hs₂d, hs₂q, hs₂t, hs₂m⟩ :=
    sizeLoop_spec d (k := 0) (s := s₁) (by omega) hspan hd
      (by simp +decide [s₁, initSetupData])
      (by simp +decide [s₁, initSetupData])
      (by simp +decide [s₁, initSetupData])
      (by simp +decide [s₁, initSetupData])
      (by simp +decide [s₁, initSetupData])
      (by simp +decide [s₁, initSetupData])
      (by simpa +decide [s₁, initSetupData] using hdepth)
      (by simp +decide [s₁, initSetupData, universeSize])
      (by simp +decide [s₁, initSetupData, span])
      (by simp +decide [s₁, initSetupData])
  have hs₂_root : s₂.regs root = base := by
    simpa +decide [s₁, initSetupData, hroot] using hs₂r
  have h3 := (tableSetup_exec ha hs₂0 hs₂1 hs₂2 hs₂5 hs₂_root hs₂t).within
  let s₃ := tableSetupData s₂ base d
  have hs₃_sp : s₃.regs sp = base + span d + 2 * (0 + 1) := by
    change base + span d + 1 + 1 = base + span d + 2 * (0 + 1)
    omega
  have hs₃_inv : TableInv (base + span d) 0 s₃.mem := by
    intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    simp only [s₃, tableSetupData, Data.set_mem, Data.write_mem, splitSize, childSpan,
      Nat.mul_zero, Nat.add_zero]
    constructor
    · rw [Function.update_of_ne (by omega), Function.update_self]
    · rw [Function.update_self]
  have hs₃_away : ∀ a, a < base + span d ∨ base + span d + 2 ≤ a → s₃.mem a = s.mem a := by
    intro a ha_out
    simp only [s₃, tableSetupData, Data.set_mem, Data.write_mem]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hs₂m]
    rfl
  obtain ⟨s₄, h4, hs₄0, hs₄1, hs₄2, hs₄3, hs₄4, hs₄5, hs₄r, hs₄d, hs₄p, hs₄tbl, hs₄stk,
      hs₄sp, hs₄inv, hs₄frame⟩ :=
    tableLoop_spec d (k := 0) (s := s₃) (by omega) ha
      (by simpa +decide [s₃, tableSetupData] using hs₂0)
      (by simpa +decide [s₃, tableSetupData] using hs₂1)
      (by simpa +decide [s₃, tableSetupData] using hs₂2)
      (by simpa +decide [s₃, tableSetupData] using hs₂3)
      (by simpa +decide [s₃, tableSetupData] using hs₂4)
      (by simpa +decide [s₃, tableSetupData] using hs₂5)
      (by simpa +decide [s₃, tableSetupData] using hs₂_root)
      (by simpa +decide [s₃, tableSetupData] using hs₂d)
      (by simp +decide [s₃, tableSetupData])
      (by simp +decide [s₃, tableSetupData])
      (by simp +decide [s₃, tableSetupData])
      hs₃_sp
      (by simp +decide [s₃, tableSetupData, universeSize])
      (by simp +decide [s₃, tableSetupData, span])
      (by simp +decide [s₃, tableSetupData])
      hs₃_inv
  have h5 := (dfsSetup_exec (w := w) hs₄0 hs₄1 hs₄r hs₄d hs₄sp).within
  let s₅ := dfsSetupData s₄ base d
  have hs₅_state : DfsState base d base d 0 s₅ := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · simpa +decide [s₅, dfsSetupData] using hs₄0
    · simpa +decide [s₅, dfsSetupData] using hs₄1
    · simpa +decide [s₅, dfsSetupData] using hs₄2
    · simpa +decide [s₅, dfsSetupData] using hs₄3
    · simpa +decide [s₅, dfsSetupData] using hs₄4
    · simpa +decide [s₅, dfsSetupData] using hs₄5
    · simpa +decide [s₅, dfsSetupData] using hs₄r
    · simpa +decide [s₅, dfsSetupData] using hs₄d
    · simpa +decide [s₅, dfsSetupData] using hs₄p
    · simpa +decide [s₅, dfsSetupData] using hs₄tbl
    · simpa +decide [s₅, dfsSetupData] using hs₄stk
    · rfl
    · exact hs₄inv
    · rfl
    · rfl
    · rfl
    · rfl
  obtain ⟨s₆, h6, hs₆_rep, hs₆r, hs₆p, hs₆stk, hs₆frame⟩ := dfsLoop_spec hs₅_state ha
  have h7 : ExecWithin w (ram[out ← payload] : Code .standard 32) s₆
      (s₆.set out (s₆.regs payload)) 1 := ExecWithin.copy
  let z := s₆.set out (s₆.regs payload)
  have hrun : ExecWithin w initProgram s z (8 * span d + 20 * d + 24) :=
    (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq h7)))))).mono (by omega)
  refine ⟨z, hrun, hs₆_rep, ?_, ?_, ?_, ?_⟩
  · simpa +decide [z] using hs₆r
  · simpa +decide [z] using hs₆stk
  · simpa +decide [z] using hs₆p
  · intro a ha_out
    change s₆.mem a = s.mem a
    rw [hs₆frame a (by omega) (by omega)]
    change s₄.mem a = s.mem a
    rw [hs₄frame a (by omega)]
    exact hs₃_away a (by omega)

/-- Bounded-caller initialization certificate: from any bounded state with `s.regs root = base`
and `s.regs depth = d`, `initProgram` executes in at most `8 * span d + 20 * d + 25` instructions
(including the final halt), preserves boundedness, establishes `Rep (Tree.empty d) base z.mem`,
and sets `z.regs root = base` and `z.regs stackBase = base + span d`. -/
theorem init_call {w base d : ℕ} {s : Data 32}
    (hs : s.Bounded w) (ha : Fits w (base + span d + 4 * (d + 1)))
    (hroot : s.regs root = base) (hdepth : s.regs depth = d) :
    ∃ z n, n + 1 ≤ 8 * span d + 20 * d + 25 ∧ Exec w initProgram s z n ∧
      z.Bounded w ∧ Rep (Tree.empty d) base z.mem ∧
      z.regs root = base ∧ z.regs stackBase = base + span d ∧
      z.regs out = base + span d ∧
      (∀ a, a < base ∨ base + span d + 4 * (d + 1) ≤ a → z.mem a = s.mem a) := by
  obtain ⟨z, ⟨n, hn, he⟩, hrep, hr, hstk, hout, hframe⟩ :=
    init_dispatch_spec ha hroot hdepth
  exact ⟨z, n, by omega, he, he.bounded hs, hrep, hr, hstk, hout, hframe⟩

/-- Flat bounded-word execution of `initProgram.program out`, including the final halt, in at
most `8 * span d + 20 * d + 25` instructions. -/
theorem init_executes {w base d : ℕ} {s : Data 32}
    (hs : s.Bounded w) (ha : Fits w (base + span d + 4 * (d + 1)))
    (hroot : s.regs root = base) (hdepth : s.regs depth = d) :
    ∃ n ≤ 8 * span d + 20 * d + 25,
      Executes w (initProgram.program out) ⟨0, s⟩ (base + span d) n := by
  obtain ⟨z, n, hn, he, _, _, _, _, hout, _⟩ := init_call hs ha hroot hdepth
  exact ⟨n + 1, hn, hout ▸ he.executes out⟩

/-- Exact transfer of the flat initializer execution into the shared generic RAM model. -/
theorem init_executes_generic {w base d : ℕ} {s : Data 32}
    (hs : s.Bounded w) (ha : Fits w (base + span d + 4 * (d + 1)))
    (hroot : s.regs root = base) (hdepth : s.regs depth = d) :
    ∃ n ≤ 8 * span d + 20 * d + 25,
      GenericRAM.Executes w (initProgram.program out).toGeneric
        ((⟨0, s⟩ : State 32).toGeneric .standard) (base + span d) n := by
  obtain ⟨n, hn, he⟩ := init_executes hs ha hroot hdepth
  exact ⟨n, hn, executes_toGeneric_iff.mpr he⟩

/-- The flat initializer instruction bound written directly in terms of `universeSize d`. -/
theorem init_executes_universe {w base d : ℕ} {s : Data 32}
    (hs : s.Bounded w) (ha : Fits w (base + span d + 4 * (d + 1)))
    (hroot : s.regs root = base) (hdepth : s.regs depth = d) :
    ∃ n ≤ 80 * universeSize d + 20 * d,
      Executes w (initProgram.program out) ⟨0, s⟩ (base + span d) n := by
  obtain ⟨n, hn, he⟩ := init_executes hs ha hroot hdepth
  have hsp := span_add_fifteen_le d
  exact ⟨n, by omega, he⟩

end Cslib.Algorithms.WordRAM.VanEmdeBoas
