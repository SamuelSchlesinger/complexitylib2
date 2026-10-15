/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.DepthClasses
public import Complexity.Computability.Circuit.Boolean.Formula
public import Complexity.Computability.Circuit.MapLines
public import Complexity.Computability.Circuit.SimulationDepth
import Complexity.Computability.Circuit.Simulation

/-!
# Simulating unbounded fan-in with fan-in two

A disjunction of `k ≥ 1` arguments is a balanced tree of `k - 1` disjunctions of fan-in two, of
depth `⌈log₂ k⌉` (`Formula.size_orList_add_one`, `Formula.depth_orList_le`), and a conjunction is
such a tree between negations. Replacing every gate of a circuit over the unbounded fan-in basis
by such a tree gives a De Morgan circuit for the same function. A gate may read one wire many
times, so its fan-in is not bounded by the size of the circuit; but a conjunction or a disjunction
keeps its value when it reads each of its wires once, so every circuit with `n` inputs and `s`
gates has an equivalent circuit of the same size and no larger depth whose gates have fan-in at
most `n + s` (`Unbounded.dedup`). Replacing its gates gives a De Morgan circuit with
`O(s (n + s))` gates and depth `O(d log (n + s))` (`Unbounded.exists_deMorgan_simulation`).

For circuits of polynomial size `log (n + s)` is `O(log n)`, so polynomial-size circuits of depth
`O((log n) ^ i)` and unbounded fan-in become polynomial-size circuits of fan-in two and depth
`O((log n) ^ (i + 1))`: **ACⁱ ⊆ NCⁱ⁺¹** (`AC_subset_NC_succ`)
[Arora and Barak, Section 6.7][AroraBarak09], [Vollmer, Chapter 4][Vollmer1999]. With
`NCⁱ ⊆ ACⁱ`, the two hierarchies have the same union (`iUnion_NC_eq_iUnion_AC`).

## Main definitions

* `Cslib.Circuits.Boolean.Unbounded.dedup`: the circuit whose gates read their distinct wires.
* `Cslib.Circuits.Boolean.Unbounded.Op.deMorganFormula`: a De Morgan formula for each operation of
  the unbounded fan-in basis.

## Main results

* `Cslib.Circuits.Boolean.Unbounded.eval_dedup`, `Cslib.Circuits.Boolean.Unbounded.depth_dedup_le`,
  `Cslib.Circuits.Boolean.Unbounded.fanInAtMost_dedup`: reading every wire once keeps the function
  and the size, makes no gate deeper, and bounds the fan-in by the number of inputs and gates.
* `Cslib.Circuits.Boolean.Unbounded.exists_deMorgan_simulation`: a circuit of unbounded fan-in
  with `n` inputs, `s` gates and depth `d` has an equivalent De Morgan circuit with at most
  `s (2 (n + s) + 2)` gates and depth at most `(⌈log₂ (n + s)⌉ + 2) d`.
* `Cslib.Circuits.Boolean.AC_subset_NC_succ`: **ACⁱ ⊆ NCⁱ⁺¹**.
* `Cslib.Circuits.Boolean.AC0_subset_NC_one`: **AC⁰ ⊆ NC¹**.
* `Cslib.Circuits.Boolean.iUnion_NC_eq_iUnion_AC`: **NC = AC**.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [H. Vollmer, *Introduction to Circuit Complexity*][Vollmer1999]
-/

@[expose] public section

namespace Cslib.Circuits

namespace Boolean

namespace Unbounded

variable {n g m : ℕ}

/-! ### Reading every wire once -/

private theorem forall_get_dedup_ofFn_iff {α : Type*} [DecidableEq α] {k : ℕ} (w : Fin k → α)
    (P : α → Prop) : (∀ j, P ((List.ofFn w).dedup.get j)) ↔ ∀ j, P (w j) := by
  rw [← List.forall_mem_iff_get, ← List.forall_mem_ofFn_iff]
  simp only [List.mem_dedup]

private theorem exists_get_dedup_ofFn_iff {α : Type*} [DecidableEq α] {k : ℕ} (w : Fin k → α)
    (P : α → Prop) : (∃ j, P ((List.ofFn w).dedup.get j)) ↔ ∃ j, P (w j) := by
  rw [← List.exists_mem_iff_get]
  simp [List.mem_dedup, List.mem_ofFn']

/-- The line reading the distinct wires of `line`, each once. A conjunction or a disjunction does
not depend on how often it reads a wire, so this keeps the value of the line. -/
def dedupLine : Line signature n g → Line signature n g
  | ⟨.not, w⟩ => ⟨.not, w⟩
  | ⟨.and _, w⟩ => ⟨.and (List.ofFn w).dedup.length, (List.ofFn w).dedup.get⟩
  | ⟨.or _, w⟩ => ⟨.or (List.ofFn w).dedup.length, (List.ofFn w).dedup.get⟩

/-- Reading every wire once keeps the value of a line. -/
theorem eval_dedupLine (line : Line signature n g) (x : Fin n → Bool) (gates : Fin g → Bool) :
    (dedupLine line).eval interpretation x gates = line.eval interpretation x gates := by
  obtain ⟨op, w⟩ := line
  cases op with
  | not => rfl
  | and k =>
    exact decide_eq_decide.2 (forall_get_dedup_ofFn_iff w fun a => Wire.elim x gates a = true)
  | or k =>
    exact decide_eq_decide.2 (exists_get_dedup_ofFn_iff w fun a => Wire.elim x gates a = true)

/-- Reading every wire once makes no line deeper. -/
theorem depth_dedupLine_le (line : Line signature n g) (depths : Wire n g → ℕ) :
    (dedupLine line).depth depths ≤ line.depth depths := by
  have hpos := line.depth_pos depths
  have hle : ∀ a, depths (line.wires a) ≤ line.depth depths - 1 := fun a => by
    have := line.wireDepth_lt_depth depths a
    omega
  refine ((Line.depth_le_add_one_iff _ depths (d := line.depth depths - 1)).2 ?_).trans
    (by omega)
  obtain ⟨op, w⟩ := line
  cases op with
  | not => exact hle
  | and k => exact (forall_get_dedup_ofFn_iff w fun a => depths a ≤ _).2 hle
  | or k => exact (forall_get_dedup_ofFn_iff w fun a => depths a ≤ _).2 hle

/-- A line reading every wire once reads at most all `n + g` wires. -/
theorem arity_dedupLine_le (line : Line signature n g) :
    signature.Arity (dedupLine line).op ≤ n + g := by
  obtain ⟨op, w⟩ := line
  cases op with
  | not => exact (Fintype.card_pos_iff.2 ⟨w 0⟩).trans_eq Wire.card
  | and k => exact (List.nodup_dedup _).length_le_card.trans_eq Wire.card
  | or k => exact (List.nodup_dedup _).length_le_card.trans_eq Wire.card

/-- The gates of a program reading every wire once read at most all wires. -/
private theorem arity_lines_mapLines_dedupLine_le (p : Program signature n g) (k : Fin g) :
    signature.Arity ((p.mapLines dedupLine).lines k).op ≤ n + g := by
  induction p with
  | empty => exact k.elim0
  | @gate g p line ih =>
    induction k using Fin.lastCases with
    | last =>
      rw [Program.mapLines_gate, Program.lines_gate_last, Line.mapWires_op]
      exact (arity_dedupLine_le line).trans (Nat.le_succ _)
    | cast k =>
      rw [Program.mapLines_gate, Program.lines_gate_castSucc, Line.mapWires_op]
      exact (ih k).trans (Nat.le_succ _)

/-- The circuit whose gates read their distinct wires, each once. It computes the same function
(`eval_dedup`) with the same size and no larger depth (`depth_dedup_le`), and its gates have
fan-in at most the number of inputs and gates (`fanInAtMost_dedup`). -/
def dedup (C : Circuit signature n m) : Circuit signature n m :=
  C.mapLines dedupLine

/-- Reading every wire once keeps the size. -/
@[simp] theorem size_dedup (C : Circuit signature n m) : (dedup C).size = C.size :=
  rfl

/-- Reading every wire once keeps the function computed. -/
@[simp] theorem eval_dedup (C : Circuit signature n m) :
    (dedup C).eval interpretation = C.eval interpretation :=
  Circuit.eval_mapLines eval_dedupLine C

/-- Reading every wire once makes no gate deeper. -/
theorem depth_dedup_le (C : Circuit signature n m) : (dedup C).depth ≤ C.depth :=
  Circuit.depth_mapLines_le depth_dedupLine_le C

/-- Every gate of `dedup C` reads at most all `n + C.size` wires. -/
theorem arity_lines_dedup_le (C : Circuit signature n m) (k : Fin C.size) :
    signature.Arity ((dedup C).program.lines k).op ≤ n + C.size :=
  arity_lines_mapLines_dedupLine_le C.program k

/-- **Fan-in reduction**: the gates of `dedup C` have fan-in at most the number of inputs and
gates of `C`. -/
theorem fanInAtMost_dedup (C : Circuit signature n m) : (dedup C).FanInAtMost (n + C.size) := by
  suffices h : ∀ {g : ℕ} (p : Program signature n g) {r : ℕ}, n + g ≤ r →
      (p.mapLines dedupLine).FanInAtMost r from h C.program le_rfl
  intro g p r hr
  induction p with
  | empty => trivial
  | gate p line ih => exact ⟨ih (by omega), (arity_dedupLine_le line).trans (by omega)⟩

/-! ### Balanced trees for the gates -/

/-- A De Morgan formula for each operation of the unbounded fan-in basis: the negation of the
input, and the balanced conjunction and disjunction of the inputs. -/
def Op.deMorganFormula : (op : Op) → Formula Boolean.signature op.arity
  | .not => (Formula.input 0).not
  | .and _ => Formula.andList (List.ofFn Formula.input)
  | .or _ => Formula.orList (List.ofFn Formula.input)

/-- The De Morgan formula of an operation computes it. -/
theorem Op.computes_deMorganFormula (op : Op) :
    op.deMorganFormula.Computes Boolean.interpretation (interpretation op) := fun x => by
  cases op with
  | not => rfl
  | and k =>
    rw [deMorganFormula, Formula.eval_andList, interpretation_and, Bool.eq_iff_iff,
      List.all_eq_true]
    simp
  | or k =>
    rw [deMorganFormula, Formula.eval_orList, interpretation_or, Bool.eq_iff_iff,
      List.any_eq_true]
    simp

/-- The De Morgan formula of an operation of `k` arguments has at most `2 k + 2` nodes. -/
theorem Op.size_deMorganFormula_le (op : Op) : op.deMorganFormula.size ≤ 2 * op.arity + 2 := by
  cases op with
  | not => simp [deMorganFormula]
  | and k =>
    rcases k.eq_zero_or_pos with rfl | hk
    · simp [deMorganFormula, Formula.andList]
    · rw [deMorganFormula, Formula.size_andList (by simpa using hk.ne')]
      simp [List.sum_ofFn]
  | or k =>
    change (Formula.orList (List.ofFn Formula.input)).size ≤ 2 * k + 2
    rcases k.eq_zero_or_pos with rfl | hk
    · simp
    · have := Formula.size_orList_add_one
        (l := List.ofFn (Formula.input (σ := Boolean.signature) (n := k))) (by simpa using hk.ne')
      simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply, Formula.size_input,
        Finset.sum_const_zero, List.length_ofFn] at this
      omega

/-- The De Morgan formula of an operation of `k` arguments has depth at most `⌈log₂ k⌉ + 2`. -/
theorem Op.depth_deMorganFormula_le (op : Op) :
    op.deMorganFormula.depth ≤ Nat.clog 2 op.arity + 2 := by
  cases op with
  | not => simp [deMorganFormula]
  | and k =>
    have := Formula.depth_andList_le (List.ofFn (Formula.input (σ := Boolean.signature) (n := k)))
      (d := 0) (by simp)
    rw [List.length_ofFn, zero_add] at this
    exact this
  | or k =>
    have := Formula.depth_orList_le (List.ofFn (Formula.input (σ := Boolean.signature) (n := k)))
      (d := 0) (by simp)
    rw [List.length_ofFn] at this
    change (Formula.orList (List.ofFn Formula.input)).depth ≤ Nat.clog 2 k + 2
    omega

/-! ### Simulation -/

/-- **Fan-in two simulates unbounded fan-in** [Arora and Barak, Section 6.7][AroraBarak09]: a
circuit of unbounded fan-in with `n` inputs, `s` gates and depth `d` has an equivalent De Morgan
circuit with at most `s (2 (n + s) + 2)` gates and depth at most `(⌈log₂ (n + s)⌉ + 2) d`. Its
gates are first made to read every wire once (`dedup`), and then replaced by balanced trees. -/
theorem exists_deMorgan_simulation (C : Circuit signature n m) :
    ∃ D : Circuit Boolean.signature n m, D.eval Boolean.interpretation = C.eval interpretation ∧
      D.size ≤ C.size * (2 * (n + C.size) + 2) ∧
      D.depth ≤ (Nat.clog 2 (n + C.size) + 2) * C.depth := by
  refine ⟨(dedup C).simulate fun op => op.deMorganFormula.toCircuit, ?_, ?_, ?_⟩
  · rw [Circuit.eval_simulate _ _ fun op => (Op.computes_deMorganFormula op).toCircuit, eval_dedup]
  · rw [Circuit.size_simulate, Program.cost_eq_sum]
    refine (Finset.sum_le_sum (g := fun _ => 2 * (n + C.size) + 2) fun k _ => ?_).trans_eq
      (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, size_dedup])
    rw [Formula.size_toCircuit]
    exact (Op.size_deMorganFormula_le _).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (arity_lines_dedup_le C k)) 2)
  · refine (Circuit.depth_simulate_le _ _).trans
      ((Circuit.depthWith_le_mul_depth _ fun k => ?_).trans
        (Nat.mul_le_mul_left _ (depth_dedup_le C)))
    exact (Formula.depth_toCircuit_le _).trans ((Op.depth_deMorganFormula_le _).trans
      (Nat.add_le_add_right (Nat.clog_mono_right 2 (arity_lines_dedup_le C k)) 2))

end Unbounded

/-! ### ACⁱ ⊆ NCⁱ⁺¹ -/

/-- With `t ≤ a (n + 1) ^ e` gates, the depth of the balanced trees is `O(log n)`. -/
private theorem clog_add_add_two_le {a e n t : ℕ} (ht : t ≤ a * (n + 1) ^ e) :
    Nat.clog 2 (n + t) + 2 ≤ (a + e + 4) * (Nat.log 2 n + 1) := by
  set L := Nat.log 2 n + 1
  have hL : 1 ≤ L := Nat.le_add_left 1 _
  have hn : n + 1 ≤ 2 ^ L := Nat.lt_pow_succ_log_self one_lt_two n
  have h₁ : n + t ≤ (a + 1) * (n + 1) ^ (e + 1) := by
    have h : n + 1 ≤ (n + 1) ^ (e + 1) := Nat.le_self_pow (by omega) _
    have h' : a * (n + 1) ^ e ≤ a * (n + 1) ^ (e + 1) :=
      Nat.mul_le_mul_left a (Nat.pow_le_pow_right (by omega) (by omega))
    rw [add_mul, one_mul]
    omega
  have h₂ : a + 1 ≤ 2 ^ ((a + 1) * L) :=
    Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right two_pos (Nat.le_mul_of_pos_right _ hL))
  have h₃ : (n + 1) ^ (e + 1) ≤ 2 ^ (L * (e + 1)) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left hn _
  have h₄ : n + t ≤ 2 ^ ((a + e + 2) * L) :=
    calc n + t ≤ (a + 1) * (n + 1) ^ (e + 1) := h₁
      _ ≤ 2 ^ ((a + 1) * L) * 2 ^ (L * (e + 1)) := Nat.mul_le_mul h₂ h₃
      _ = 2 ^ ((a + e + 2) * L) := by rw [← pow_add]; congr 1; ring
  have h₅ := Nat.clog_le_of_le_pow h₄
  have h₆ : (a + e + 4) * L = (a + e + 2) * L + 2 * L := by ring
  omega

/-- **ACⁱ ⊆ NCⁱ⁺¹** [Arora and Barak, Section 6.7][AroraBarak09], [Vollmer, Chapter 4][Vollmer1999]:
polynomial-size circuits of depth `O((log n) ^ i)` and unbounded fan-in are simulated by
polynomial-size circuits of depth `O((log n) ^ (i + 1))` and fan-in two. -/
theorem AC_subset_NC_succ (i : ℕ) : AC i ⊆ NC (i + 1) := by
  rintro L ⟨c, s, hs, hC⟩
  obtain ⟨a, e, hse⟩ := polynomiallyBounded_iff_le.1 hs
  refine ⟨c * (a + e + 4), fun n => s n * (2 * (n + s n) + 2), by fun_prop, fun n => ?_⟩
  obtain ⟨C, hCc, hCd, hCs⟩ := hC n
  obtain ⟨D, hDe, hDs, hDd⟩ := Unbounded.exists_deMorgan_simulation C
  refine ⟨D, fun x => (congrFun hDe x).trans (hCc x), ?_, ?_⟩
  · calc D.depth ≤ (Nat.clog 2 (n + C.size) + 2) * C.depth := hDd
      _ ≤ ((a + e + 4) * (Nat.log 2 n + 1)) * (c * (Nat.log 2 n + 1) ^ i) :=
          Nat.mul_le_mul (clog_add_add_two_le (hCs.trans (hse n))) hCd
      _ = c * (a + e + 4) * (Nat.log 2 n + 1) ^ (i + 1) := by ring
  · calc D.size ≤ C.size * (2 * (n + C.size) + 2) := hDs
      _ ≤ s n * (2 * (n + s n) + 2) := by gcongr

/-- **AC⁰ ⊆ NC¹.** -/
theorem AC0_subset_NC_one : AC0 ⊆ NC 1 :=
  AC_zero.symm.subset.trans (AC_subset_NC_succ 0)

/-- **NC = AC**: the NC and AC hierarchies have the same union. -/
theorem iUnion_NC_eq_iUnion_AC : ⋃ i, NC i = ⋃ i, AC i :=
  (Set.iUnion_mono NC_subset_AC).antisymm <| Set.iUnion_subset fun i =>
    (AC_subset_NC_succ i).trans (Set.subset_iUnion NC (i + 1))

end Boolean

end Cslib.Circuits
