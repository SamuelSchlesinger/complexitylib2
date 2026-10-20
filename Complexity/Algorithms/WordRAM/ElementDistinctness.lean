/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Allocation
public import Complexity.Computability.WordRAM.Compile

/-!
# Element distinctness in linear time on the word RAM

Deciding whether `n` numbers are pairwise distinct needs `Ω(n log n)` comparisons, but on the
word RAM numbers are also addresses. When the numbers are below `n`, a table of `n` flags decides
distinctness in linear time: allocate the table zeroed, then for each number check its flag,
answering *no* if it is set and setting it otherwise.

`Cslib.Algorithms.WordRAM.ElementDistinctness.linearTime_nodup` formalizes this: on lists of
naturals whose entries are below their length, `List.Nodup` is decided in linear time, at every
word size of at least twice the number of binary digits of the length. The program allocates
its table with `Cslib.WordRAM.alloc`, reads and writes it with `Cslib.WordRAM.readAt` and
`Cslib.WordRAM.writeAt`, and executes at most `16 (n + 1)` instructions, the final `halt`
included.

## Main definitions

* `Cslib.Algorithms.WordRAM.ElementDistinctness.program`: the program.

## Main results

* `Cslib.Algorithms.WordRAM.ElementDistinctness.answers`: the program answers whether its input
  list has no duplicates within `14 n + 15` instructions.
* `Cslib.Algorithms.WordRAM.ElementDistinctness.linearTime_nodup`: element distinctness for
  entries below the length is in linear time on the word RAM.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ElementDistinctness

open Cslib.WordRAM

/-! ## The program -/

/-- Register holding `0`, as all registers do initially. -/
abbrev zero : Fin 12 := 0
/-- Register holding `1`. -/
abbrev one : Fin 12 := 1
/-- Register holding the length `n` of the input. -/
abbrev len : Fin 12 := 2
/-- The allocation frontier. -/
abbrev front : Fin 12 := 3
/-- The number of cells to allocate. -/
abbrev cnt : Fin 12 := 4
/-- The address `n + 1` of the table of flags, just past the input. -/
abbrev base : Fin 12 := 5
/-- Scratch register of the allocator. -/
abbrev cur : Fin 12 := 6
/-- The address `i + 1` of the next input entry `l[i]`. -/
abbrev idx : Fin 12 := 7
/-- The current input entry. -/
abbrev val : Fin 12 := 8
/-- Scratch register for table accesses. -/
abbrev tmp : Fin 12 := 9
/-- The flag of the current entry. -/
abbrev seen : Fin 12 := 10
/-- The answer. -/
abbrev ans : Fin 12 := 11

/-- Read the length, allocate a zeroed table of `n` flags just past the input, and start at the
first entry with answer `1`. -/
def setup : Code 12 := ram[
  len ← *zero;
  one ← #1;
  front ← len + one;
  cnt ← len;
  ⟪alloc front cnt base cur zero one⟫;
  ans ← #1;
  idx ← one ]

/-- Process one entry: if its flag is set, answer `0` and stop; otherwise set its flag and
advance. -/
def body : Code 12 := ram[
  val ← *idx;
  ⟪readAt tmp seen base val⟫;
  if seen = one then [ ans ← #0; idx ← base ] else [ ⟪writeAt tmp base val one⟫; idx ← idx + one ] ]

/-- Element distinctness: the answer is left in register `ans`. -/
def program : Code 12 := ram[ ⟪setup⟫; while idx < base do [ ⟪body⟫ ] ]

/-! ## Correctness -/

variable {l : List ℕ} {w : ℕ}

/-- The loop invariant, after the first `t = idx - 1` entries: the input is intact; either no
duplicate has been found, the first `t` entries are distinct and the table flags exactly them, or
a duplicate has been found, the answer is `0` and the loop is about to stop. -/
structure Inv (l : List ℕ) (y : Data 12) : Prop where
  one_eq : y.regs one = 1
  base_eq : y.regs base = l.length + 1
  idx_pos : 1 ≤ y.regs idx
  idx_le : y.regs idx ≤ l.length + 1
  input : ∀ j (hj : j < l.length), y.mem (j + 1) = l[j]
  state : (y.regs ans = 1 ∧ (l.take (y.regs idx - 1)).Nodup ∧
      ∀ v < l.length, y.mem (l.length + 1 + v) = if v ∈ l.take (y.regs idx - 1) then 1 else 0) ∨
    (y.regs ans = 0 ∧ ¬l.Nodup ∧ y.regs idx = l.length + 1)

/-- Words of twice the number of binary digits of `n` hold `2 n + 1`. -/
theorem fits_two_mul_add_one {n : ℕ} (hw : logWords 2 n ≤ w) : Fits w (2 * n + 1) := by
  refine Fits.mono ?_ hw
  have hn : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two n
  have hP : 2 ≤ 2 ^ (Nat.log 2 n + 1) := Nat.le_self_pow (Nat.succ_ne_zero _) 2
  rw [fits_iff, logWords, show 2 * (Nat.log 2 n + 1) = (Nat.log 2 n + 1) + (Nat.log 2 n + 1) by
    omega, pow_add]
  nlinarith

theorem setup_spec (hw : Fits w (2 * l.length + 1)) (h1 : Fits w 1) :
    ∃ y, ExecWithin w setup (.init l) y (4 * l.length + 13) ∧ Inv l y := by
  have e := (Exec.load (w := w) (d := len) (a := zero) (x := .init l)).seq <|
    (Exec.const (d := one) h1).seq <|
    (Exec.bin (f := .add) (d := front) (i := len) (j := one)
      (by simpa +decide using hw.of_le (show l.length + 1 ≤ 2 * l.length + 1 by omega))).seq <|
    Exec.copy (d := cnt) (s := len) |>.seq <|
    (alloc_exec (frontier := front) (count := cnt) (result := base) (cur := cur) (zero := zero)
      (one := one) (by decide) h1
      (by simpa +decide using hw.of_le (show l.length + 1 + l.length ≤ 2 * l.length + 1 by
        omega))).seq <|
    (Exec.const (d := ans) h1).seq <| Exec.copy (d := idx) (s := one)
  refine ⟨_, e.within.mono (by simp +decide; omega), ⟨by simp +decide, by simp +decide,
    by simp +decide, by simp +decide, fun j hj => ?_, Or.inl ⟨by simp +decide, by simp +decide,
      fun v hv => by simp +decide [clear, hv]⟩⟩⟩
  simp +decide [clear, Nat.not_le.mpr hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

/-- An entry that occurs among the entries before it is a duplicate. -/
theorem not_nodup_of_mem_take {t : ℕ} (ht : t < l.length) (h : l[t] ∈ l.take t) : ¬l.Nodup := by
  intro hn
  obtain ⟨j, hj, hjt⟩ := List.mem_iff_getElem.1 h
  rw [List.getElem_take] at hjt
  rw [List.length_take] at hj
  have := hn.getElem_inj_iff.1 hjt
  omega

theorem take_add_one_eq {t : ℕ} (ht : t < l.length) : l.take (t + 1) = l.take t ++ [l[t]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem ht, Option.toList_some]

/-- One iteration of the loop takes at most `8` instructions, preserves the invariant, and
either processes the next entry or stops. -/
theorem body_spec (hl : ∀ v ∈ l, v < l.length) (hw : Fits w (2 * l.length + 1)) {y : Data 12}
    (hy : Inv l y) (hc : (Cond.lt idx base).Holds y) :
    ∃ y', ExecWithin w body y y' 8 ∧ Inv l y' ∧
      l.length + 1 - y'.regs idx < l.length + 1 - y.regs idx := by
  have hbase := hy.base_eq
  have hone := hy.one_eq
  obtain ⟨t, ht⟩ : ∃ t, y.regs idx = t + 1 := ⟨y.regs idx - 1, by have := hy.idx_pos; omega⟩
  have htn : t < l.length := by simp only [Cond.holds_lt] at hc; omega
  obtain ⟨hans, hnd, hseen⟩ : y.regs ans = 1 ∧ (l.take t).Nodup ∧
      ∀ v < l.length, y.mem (l.length + 1 + v) = if v ∈ l.take t then 1 else 0 := by
    rcases hy.state with h | h
    · simpa [ht] using h
    · omega
  have hv : l[t] < l.length := hl _ (List.getElem_mem htn)
  have hyv : y.mem (y.regs idx) = l[t] := by rw [ht]; exact hy.input t htn
  have hfit : Fits w (l.length + 1 + l[t]) := hw.of_le (by omega)
  set y₁ := y.set val (y.mem (y.regs idx))
  set y₂ := (y₁.set tmp (y₁.regs base + y₁.regs val)).set seen (y₁.mem (y₁.regs base + y₁.regs val))
  have e₁ : Exec w (.op (.load val idx)) y y₁ 1 := Exec.load
  have e₂ : Exec w (readAt tmp seen base val) y₁ y₂ 2 :=
    readAt_exec (by simpa +decide [y₁, hbase, hyv] using hfit)
  by_cases hfound : l[t] ∈ l.take t
  · -- A duplicate: answer `0` and move the index past the end.
    have e₃ := (Exec.const (w := w) (d := ans) (x := y₂) (fits_zero w)).seq
      (Exec.copy (d := idx) (s := base))
    have e := e₁.seq <| e₂.seq <| Exec.branch_pos (c := .eq seen one)
      (neg := ram[⟪writeAt tmp base val one⟫; idx ← idx + one])
      (by simp +decide [y₂, y₁, hbase, hyv, hseen _ hv, hfound, hone]) e₃
    refine ⟨_, e.within.mono (by omega), ⟨by simp +decide [y₂, y₁, hone],
      by simp +decide [y₂, y₁, hbase], by simp +decide [y₂, y₁, hbase],
      by simp +decide [y₂, y₁, hbase], by simpa [y₂, y₁] using hy.input,
      Or.inr ⟨by simp +decide [y₂, y₁], not_nodup_of_mem_take htn hfound,
        by simp +decide [y₂, y₁, hbase]⟩⟩, ?_⟩
    · simp +decide [y₂, y₁, hbase]
      omega
  · -- A new entry: set its flag and advance.
    have hseen0 : y.mem (l.length + 1 + l[t]) = 0 := by simp [hseen _ hv, hfound]
    have e₃ := (writeAt_exec (w := w) (tmp := tmp) (ptr := base) (idx := val) (src := one)
      (x := y₂) (by decide) (by simpa +decide [y₂, y₁, hbase, hyv] using hfit)).seq
      (Exec.bin (f := .add) (d := idx) (i := idx) (j := one) ?hinc)
    case hinc =>
      simpa +decide [y₂, y₁, ht, hone] using
        hw.of_le (show t + 1 + 1 ≤ 2 * l.length + 1 by omega)
    have e := e₁.seq <| e₂.seq <| Exec.branch_neg (c := .eq seen one)
      (pos := ram[ans ← #0; idx ← base]) (by simp +decide [y₂, y₁, hbase, hyv, hseen0, hone]) e₃
    have hyt : y.mem (t + 1) = l[t] := hy.input t htn
    refine ⟨_, e.within.mono (by omega),
      ⟨?one, ?base, ?pos, ?le, ?input, Or.inl ⟨?ans, ?nodup, ?seen⟩⟩, ?measure⟩
    all_goals simp +decide only [y₂, y₁, Data.set_regs, Data.set_mem, Data.write_regs,
      Data.write_mem, Function.update_self, Function.update_apply, BinOp.eval, hbase, hone, ht,
      hyt, hans, Nat.add_sub_cancel, ↓reduceIte]
    all_goals try omega
    case input =>
      intro j hj
      simp only [show j + 1 ≠ l.length + 1 + l[t] by omega, ↓reduceIte]
      exact hy.input j hj
    case nodup =>
      rw [take_add_one_eq htn, List.nodup_append]
      refine ⟨hnd, List.nodup_singleton _, fun a ha b hb => ?_⟩
      rw [List.mem_singleton] at hb
      subst hb
      exact fun hab => hfound (hab ▸ ha)
    case seen =>
      intro u hu
      rw [take_add_one_eq htn]
      by_cases hu' : u = l[t]
      · subst hu'
        simp only [List.mem_append, List.mem_singleton, or_true, ↓reduceIte]
      · simp only [show l.length + 1 + u ≠ l.length + 1 + l[t] by omega, ↓reduceIte, hseen u hu,
          List.mem_append, List.mem_singleton, hu', or_false]

/-- When the loop stops, the answer is `1` exactly if the input has no duplicates. -/
theorem exit_spec {y : Data 12} (hy : Inv l y) (hc : ¬(Cond.lt idx base).Holds y) :
    y.regs ans ≤ 1 ∧ (y.regs ans = 1 ↔ l.Nodup) := by
  have hidx : y.regs idx = l.length + 1 := by
    have := hy.idx_le
    have := hy.base_eq
    simp only [Cond.holds_lt] at hc
    omega
  rcases hy.state with ⟨hans, hnd, -⟩ | ⟨hans, hnd, -⟩
  · rw [hidx, Nat.add_sub_cancel, List.take_length] at hnd
    simp [hans, hnd]
  · simp [hans, hnd]

/-- **Correctness and running time.** On a list whose entries are below its length, at a word
size that holds `2 n + 1`, the program leaves in register `ans` the answer to whether the list has
no duplicates, within `14 n + 15` instructions. -/
theorem answers (hl : ∀ v ∈ l, v < l.length) (hw : Fits w (2 * l.length + 1)) (h1 : Fits w 1) :
    program.Answers ans w l l.Nodup (14 * l.length + 15) := by
  obtain ⟨y, hy, hI⟩ := setup_spec hw h1
  obtain ⟨z, hz, hIz, hcz⟩ := ExecWithin.loop_invariant (cond := .lt idx base) (body := body)
    (Inv l) (fun y => l.length + 1 - y.regs idx) (B := 8)
    (fun x hx hc => body_spec hl hw hx hc) hI
  refine ⟨z, (hy.seq hz).mono ?_, exit_spec hIz hcz⟩
  have := hI.idx_pos
  have := Nat.mul_le_mul_right (8 + 2) (show l.length + 1 - y.regs idx ≤ l.length by omega)
  omega

/-- **Element distinctness in linear time.** On lists of naturals whose entries are below their
length, deciding whether there are no duplicates takes linear time on the word RAM, at every
word size of at least twice the number of binary digits of the length. -/
theorem linearTime_nodup :
    LinearTime (fun l : {l : List ℕ // ∀ v ∈ l, v < l.length} => l.1) (fun l => l.1.length)
      (fun l => l.1.Nodup) := by
  refine ⟨16, 2, (DecidesInTime.of_code (time := fun l => 14 * l.1.length + 15)
    (bits := fun l => logWords 2 l.1.length) program ans fun a w hw _ =>
      answers a.2 (fits_two_mul_add_one hw) (fits_one ?_)).mono (fun a => by dsimp only; omega)
      fun _ => le_rfl⟩
  have : 2 ≤ logWords 2 a.1.length := Nat.le_mul_of_pos_right 2 (Nat.succ_pos _)
  omega

end Cslib.Algorithms.WordRAM.ElementDistinctness

end
