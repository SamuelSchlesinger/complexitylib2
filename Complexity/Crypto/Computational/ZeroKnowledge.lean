/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.IP
public import Complexity.Computability.Complexity.Problems.ThreeSAT
public import Complexity.Computability.Probabilistic.OracleSimulation
public import Complexity.Crypto.Computational.Commitment
public import Complexity.Languages.Probabilistic.Oracle.Simulation
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Probabilistic.Oracle.Composition
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Logics.Propositional.CNF.PolyTime
import Complexity.Tactic.PPT

/-!
# Computational zero-knowledge interactive proofs for NP

Goldreich, Micali, and Wigderson [GoldreichMicaliWigderson1991] proved that if one-way functions
exist, then every language in `NP` has a computational zero-knowledge interactive proof system.
This module formalizes computational zero-knowledge interactive proofs secure against uniform
strict oracle PPT malicious verifiers with auxiliary input, and constructs such a proof system for
`ThreeSAT` and hence for every language in `NP` via `ThreeSAT_npHard` and Naor's bit commitment
scheme (`Complexity.Crypto.Computational.Commitment`).

## Main definitions

* `Cslib.Crypto.ZeroKnowledgeProof`: an interactive proof system for a language `A` with a uniform
  strict oracle PPT verifier, completeness `2 / 3`, soundness `1 / 3` against unbounded provers,
  and a uniform strict PPT simulator producing views computationally indistinguishable from the
  real interaction for every uniform strict oracle PPT malicious verifier and auxiliary input.

## Main results

* `Cslib.Crypto.PseudorandomGenerator.exists_zeroKnowledgeProof_of_mem_NP`: any pseudorandom
  generator with stretch `fun n => 3 * n + 1` yields a computational zero-knowledge proof system
  for every language in `NP`.
* `Cslib.Crypto.OneWay.exists_zeroKnowledgeProof_of_mem_NP`: if a one-way function exists, every
  language in `NP` has a computational zero-knowledge proof system.

## References

* [O. Goldreich, S. Micali, A. Wigderson, *Proofs that Yield Nothing But Their Validity, or All
  Languages in NP Have Zero-Knowledge Proof Systems*][GoldreichMicaliWigderson1991]
* [M. Naor, *Bit Commitment Using Pseudorandomness*][Naor1991]
* [O. Goldreich, *Foundations of Cryptography: Volume 1, Basic Tools*][Goldreich2001], Chapter 4.
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 9.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Complexity Logic.PL Turing.MultiTapeTM ComputableTidilyInPolyTime
open scoped NNReal ENNReal

namespace GMW

/-! ### Masked 3SAT truth-table gadgets -/

/-- Bit 0 of an index `t < 8`. -/
def bit0Of8 (t : ℕ) : Bool :=
  (t == 1) || (t == 3) || (t == 5) || (t == 7)

/-- Bit 1 of an index `t < 8`. -/
def bit1Of8 (t : ℕ) : Bool :=
  (t == 2) || (t == 3) || (t == 6) || (t == 7)

/-- Bit 2 of an index `t < 8`. -/
def bit2Of8 (t : ℕ) : Bool :=
  (t == 4) || (t == 5) || (t == 6) || (t == 7)

/-- Pack three bits into an index in `0..7`. -/
def activeIdx (b₀ b₁ b₂ : Bool) : ℕ :=
  (if b₀ then 1 else 0) + 2 * (if b₁ then 1 else 0) + 4 * (if b₂ then 1 else 0)

theorem activeIdx_lt_eight (b₀ b₁ b₂ : Bool) : activeIdx b₀ b₁ b₂ < 8 := by
  cases b₀ <;> cases b₁ <;> cases b₂ <;> decide

@[simp] theorem bit0Of8_activeIdx (b₀ b₁ b₂ : Bool) : bit0Of8 (activeIdx b₀ b₁ b₂) = b₀ := by
  cases b₀ <;> cases b₁ <;> cases b₂ <;> decide

@[simp] theorem bit1Of8_activeIdx (b₀ b₁ b₂ : Bool) : bit1Of8 (activeIdx b₀ b₁ b₂) = b₁ := by
  cases b₀ <;> cases b₁ <;> cases b₂ <;> decide

@[simp] theorem bit2Of8_activeIdx (b₀ b₁ b₂ : Bool) : bit2Of8 (activeIdx b₀ b₁ b₂) = b₂ := by
  cases b₀ <;> cases b₁ <;> cases b₂ <;> decide

/-- Evaluate a clause of length at most 3 given the truth values of its first three literals'
variables. -/
def clauseEvalBits (c : Clause ℕ) (b₀ b₁ b₂ : Bool) : Bool :=
  (decide (0 < c.length) && (b₀ == (c.getD 0 (0, false)).2)) ||
  (decide (1 < c.length) && (b₁ == (c.getD 1 (0, false)).2)) ||
  (decide (2 < c.length) && (b₂ == (c.getD 2 (0, false)).2))

theorem clauseEvalBits_eq_eval {c : Clause ℕ} (hc : c.length ≤ 3) (σ : ℕ → Bool) :
    clauseEvalBits c
      (σ (c.getD 0 (0, false)).1)
      (σ (c.getD 1 (0, false)).1)
      (σ (c.getD 2 (0, false)).1) = c.eval σ := by
  rcases c with _ | ⟨⟨v₀, p₀⟩, _ | ⟨⟨v₁, p₁⟩, _ | ⟨⟨v₂, p₂⟩, _ | ⟨_, _⟩⟩⟩⟩
  · rfl
  · simp [clauseEvalBits, Clause.eval, Literal.eval]
  · simp [clauseEvalBits, Clause.eval, Literal.eval]
  · simp [clauseEvalBits, Clause.eval, Literal.eval, Bool.or_assoc]
  · simp only [List.length_cons] at hc; omega

/-- Look up the bit for variable `v` in `vec` at its first occurrence in `φ.vars`, returning
`false` when `v ∉ φ.vars`. -/
def varBit (φ : CNF ℕ) (vec : List Bool) (v : ℕ) : Bool :=
  if φ.vars.idxOf v < φ.vars.length then vec.getD (φ.vars.idxOf v) false else false

theorem varBit_eq_assignment {φ : CNF ℕ} (vec : List Bool) {v : ℕ} (hv : v ∈ φ.vars) :
    varBit φ vec v = SAT.assignment φ vec v := by
  have hlt : φ.vars.idxOf v < φ.vars.length := List.idxOf_lt_length_iff.mpr hv
  simp [varBit, SAT.assignment, hlt]

theorem eval_varBit_eq (φ : CNF ℕ) (vec : List Bool) :
    φ.eval (varBit φ vec) = φ.eval (SAT.assignment φ vec) :=
  CNF.eval_congr (fun _ hv => varBit_eq_assignment vec hv)

@[simp] theorem varBit_listXor (φ : CNF ℕ) (w m : List Bool) (v : ℕ) :
    varBit φ (BitString.listXor φ.vars.length [w, m]) v = (varBit φ w v ^^ varBit φ m v) := by
  unfold varBit
  split_ifs with hlt
  · exact getD_listXor_pair φ.vars.length w m (φ.vars.idxOf v) hlt
  · rfl

@[simp] theorem varBit_listRow (φ : CNF ℕ) (vec : List Bool) (v : ℕ) :
    varBit φ (BitString.listRow φ.vars.length 0 vec) v = varBit φ vec v := by
  unfold varBit
  split_ifs with hlt
  · exact getD_listRow_zero φ.vars.length vec (φ.vars.idxOf v) hlt
  · rfl

/-- The 8-bit masked truth table of clause `c` under variable mask `m`. -/
def clauseTableRow (φ : CNF ℕ) (m : List Bool) (c : Clause ℕ) : List Bool :=
  let m₀ := varBit φ m (c.getD 0 (0, false)).1
  let m₁ := varBit φ m (c.getD 1 (0, false)).1
  let m₂ := varBit φ m (c.getD 2 (0, false)).1
  (List.range 8).map fun t =>
    clauseEvalBits c (bit0Of8 t ^^ m₀) (bit1Of8 t ^^ m₁) (bit2Of8 t ^^ m₂)

/-- The 8-bit indicator of the active row of clause `c` under masked assignment `v`. -/
def clauseActiveRow (φ : CNF ℕ) (v : List Bool) (c : Clause ℕ) : List Bool :=
  let v₀ := varBit φ v (c.getD 0 (0, false)).1
  let v₁ := varBit φ v (c.getD 1 (0, false)).1
  let v₂ := varBit φ v (c.getD 2 (0, false)).1
  let active := activeIdx v₀ v₁ v₂
  (List.range 8).map fun t => decide (t = active)

@[simp] theorem length_clauseTableRow (φ : CNF ℕ) (m : List Bool) (c : Clause ℕ) :
    (clauseTableRow φ m c).length = 8 := by
  simp [clauseTableRow]

@[simp] theorem length_clauseActiveRow (φ : CNF ℕ) (v : List Bool) (c : Clause ℕ) :
    (clauseActiveRow φ v c).length = 8 := by
  simp [clauseActiveRow]

@[simp] theorem clauseTableRow_listRow (φ : CNF ℕ) (m : List Bool) (c : Clause ℕ) :
    clauseTableRow φ (BitString.listRow φ.vars.length 0 m) c = clauseTableRow φ m c := by
  simp [clauseTableRow]

@[simp] theorem clauseActiveRow_listRow (φ : CNF ℕ) (v : List Bool) (c : Clause ℕ) :
    clauseActiveRow φ (BitString.listRow φ.vars.length 0 v) c = clauseActiveRow φ v c := by
  simp [clauseActiveRow]

theorem naorMaskBits_eq_self_of_imp {openFlags bits : List Bool}
    (hlen : openFlags.length = bits.length)
    (himp : ∀ i, openFlags.getD i false = true → bits.getD i false = true) :
    naorMaskBits openFlags bits = openFlags := by
  apply List.ext_getElem (by simp [hlen])
  intro i hi hi'
  have hlt : i < bits.length := by simpa [hlen] using hi
  have h := getD_naorMaskBits openFlags bits i
  have hopen : openFlags.getD i false = openFlags[i] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
  have hbit : bits.getD i false = bits[i]'hlt := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
  have hmask : (naorMaskBits openFlags bits).getD i false = (naorMaskBits openFlags bits)[i] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rw [← hmask, h, hopen]
  cases hflag : openFlags[i]
  · simp
  · simpa [List.getD_eq_getElem?_getD] using himp i (hopen.trans hflag)

theorem getD_clauseTableRow (φ : CNF ℕ) (m : List Bool) (c : Clause ℕ) {t : ℕ} (ht : t < 8) :
    (clauseTableRow φ m c).getD t false =
      clauseEvalBits c
        (bit0Of8 t ^^ varBit φ m (c.getD 0 (0, false)).1)
        (bit1Of8 t ^^ varBit φ m (c.getD 1 (0, false)).1)
        (bit2Of8 t ^^ varBit φ m (c.getD 2 (0, false)).1) := by
  simp [clauseTableRow, List.getD_eq_getElem?_getD, ht]

theorem getD_clauseActiveRow (φ : CNF ℕ) (v : List Bool) (c : Clause ℕ) {t : ℕ} (ht : t < 8) :
    (clauseActiveRow φ v c).getD t false =
      decide (t = activeIdx
        (varBit φ v (c.getD 0 (0, false)).1)
        (varBit φ v (c.getD 1 (0, false)).1)
        (varBit φ v (c.getD 2 (0, false)).1)) := by
  simp [clauseActiveRow, List.getD_eq_getElem?_getD, ht]

theorem naorMaskBits_clauseActiveRow {φ : CNF ℕ} {w m : List Bool} {c : Clause ℕ}
    (hc_len : c.length ≤ 3) (hc_eval : c.eval (varBit φ w) = true) :
    naorMaskBits (clauseActiveRow φ (BitString.listXor φ.vars.length [w, m]) c)
      (clauseTableRow φ m c) =
      clauseActiveRow φ (BitString.listXor φ.vars.length [w, m]) c := by
  apply naorMaskBits_eq_self_of_imp (by simp)
  intro t ht
  by_cases hlt : t < 8
  · rw [getD_clauseActiveRow φ _ c hlt, decide_eq_true_eq] at ht
    rw [getD_clauseTableRow φ m c hlt, ht, bit0Of8_activeIdx, bit1Of8_activeIdx, bit2Of8_activeIdx]
    simp only [varBit_listXor, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
    rw [clauseEvalBits_eq_eval hc_len (varBit φ w), hc_eval]
  · have hge : (clauseActiveRow φ (BitString.listXor φ.vars.length [w, m]) c).length ≤ t := by
      simp; omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at ht

/-- The `8 * φ.length`-bit concatenation of all clause truth tables of `φ` under mask `m`. -/
def tableBits (φ : CNF ℕ) (m : List Bool) : List Bool :=
  (φ.map (clauseTableRow φ m)).flatten

/-- The `8 * φ.length`-bit concatenation of all active-row indicators of `φ` under `v`. -/
def activeTableFlags (φ : CNF ℕ) (v : List Bool) : List Bool :=
  (φ.map (clauseActiveRow φ v)).flatten

private theorem length_flatten_map_eight {α : Type} (xs : List α) (f : α → List Bool)
    (hf : ∀ x ∈ xs, (f x).length = 8) : (xs.map f).flatten.length = 8 * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons,
      hf x List.mem_cons_self, ih (fun y hy => hf y (List.mem_cons_of_mem _ hy))]
    omega

@[simp] theorem length_tableBits (φ : CNF ℕ) (m : List Bool) :
    (tableBits φ m).length = 8 * φ.length :=
  length_flatten_map_eight φ (clauseTableRow φ m) (fun _ _ => length_clauseTableRow _ _ _)

@[simp] theorem length_activeTableFlags (φ : CNF ℕ) (v : List Bool) :
    (activeTableFlags φ v).length = 8 * φ.length :=
  length_flatten_map_eight φ (clauseActiveRow φ v) (fun _ _ => length_clauseActiveRow _ _ _)

@[simp] theorem tableBits_listRow (φ : CNF ℕ) (m : List Bool) :
    tableBits φ (BitString.listRow φ.vars.length 0 m) = tableBits φ m := by
  have h : clauseTableRow φ (BitString.listRow φ.vars.length 0 m) = clauseTableRow φ m := by
    funext c
    exact clauseTableRow_listRow φ m c
  simp [tableBits, h]

@[simp] theorem activeTableFlags_listRow (φ : CNF ℕ) (v : List Bool) :
    activeTableFlags φ (BitString.listRow φ.vars.length 0 v) = activeTableFlags φ v := by
  have h : clauseActiveRow φ (BitString.listRow φ.vars.length 0 v) = clauseActiveRow φ v := by
    funext c
    exact clauseActiveRow_listRow φ v c
  simp [activeTableFlags, h]

theorem naorMaskBits_activeTableFlags {φ : CNF ℕ} {w m : List Bool}
    (hw : ThreeSAT.verifier (φ, w) = true) :
    naorMaskBits (activeTableFlags φ (BitString.listXor φ.vars.length [w, m]))
      (tableBits φ m) =
      activeTableFlags φ (BitString.listXor φ.vars.length [w, m]) := by
  simp only [ThreeSAT.verifier, SAT.verifier, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, ← eval_varBit_eq, CNF.eval_eq_true_iff] at hw
  rcases hw with ⟨hlen, heval⟩
  unfold activeTableFlags tableBits
  have hrec : ∀ cs : List (Clause ℕ),
      (∀ c ∈ cs, c.length ≤ 3) → (∀ c ∈ cs, c.eval (varBit φ w) = true) →
      naorMaskBits (cs.map (clauseActiveRow φ (BitString.listXor φ.vars.length [w, m]))).flatten
        (cs.map (clauseTableRow φ m)).flatten =
        (cs.map (clauseActiveRow φ (BitString.listXor φ.vars.length [w, m]))).flatten := by
    intro cs hcs_len hcs_eval
    induction cs with
    | nil => rfl
    | cons c cs ih =>
      simp only [List.map_cons, List.flatten_cons]
      rw [naorMaskBits_append (by simp),
        naorMaskBits_clauseActiveRow (hcs_len c List.mem_cons_self)
          (hcs_eval c List.mem_cons_self),
        ih (fun c' hc' => hcs_len c' (List.mem_cons_of_mem _ hc'))
          (fun c' hc' => hcs_eval c' (List.mem_cons_of_mem _ hc'))]
  exact hrec φ hlen heval

/-! ### Single-copy and three-copy bit layouts -/

theorem getD_take (l : List Bool) (w i : ℕ) (hi : i < w) :
    (l.take w).getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]

theorem getD_take_drop (l : List Bool) (d w i : ℕ) (hi : i < w) :
    ((l.drop d).take w).getD i false = l.getD (d + i) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi, List.getElem?_drop]

theorem take_three_0 {w : ℕ} {a b c : List Bool} (ha : a.length = w) :
    (a ++ b ++ c).take w = a := by
  rw [List.append_assoc, List.take_left' ha]

theorem take_drop_three_1 {w : ℕ} {a b c : List Bool} (ha : a.length = w) (hb : b.length = w) :
    ((a ++ b ++ c).drop w).take w = b := by
  rw [List.append_assoc, List.drop_left' ha, List.take_left' hb]

theorem take_drop_three_2 {w u : ℕ} {a b c : List Bool} (ha : a.length = w) (hb : b.length = w)
    (hc : c.length = u) :
    ((a ++ b ++ c).drop (2 * w)).take u = c := by
  have hab : (a ++ b).length = 2 * w := by simp [ha, hb, Nat.two_mul]
  rw [List.drop_left' hab, List.take_of_length_le hc.le]

/-- Number of committed bits in one copy of the masked 3SAT gadget:
`φ.vars.length` mask bits, `φ.vars.length` masked assignment bits, and `8 * φ.length` table bits. -/
def copyLen (φ : CNF ℕ) : ℕ := 2 * φ.vars.length + 8 * φ.length

/-- Number of committed bits across all three parallel copies. -/
def totalLen (φ : CNF ℕ) : ℕ := 3 * copyLen φ

/-- Extract the `m` segment (first `φ.vars.length` bits) of a copy. -/
def mPart (φ : CNF ℕ) (copy : List Bool) : List Bool :=
  copy.take φ.vars.length

/-- Extract the `v` segment (second `φ.vars.length` bits) of a copy. -/
def vPart (φ : CNF ℕ) (copy : List Bool) : List Bool :=
  (copy.drop φ.vars.length).take φ.vars.length

/-- Extract the truth-table segment (`8 * φ.length` bits) of a copy. -/
def tablePart (φ : CNF ℕ) (copy : List Bool) : List Bool :=
  (copy.drop (2 * φ.vars.length)).take (8 * φ.length)

/-- Honest committed bits for one copy given witness `w` and mask `m`. -/
def realCopyBits (φ : CNF ℕ) (w m : List Bool) : List Bool :=
  BitString.listRow φ.vars.length 0 m ++
    BitString.listXor φ.vars.length [w, m] ++
    tableBits φ m

/-- Simulated (and selectively opened) bits for one copy given challenge bit `b` and random word
`rand` of length `φ.vars.length`. -/
def simCopyBits (φ : CNF ℕ) (b : Bool) (rand : List Bool) : List Bool :=
  if b then
    List.replicate φ.vars.length false ++
      BitString.listRow φ.vars.length 0 rand ++
      activeTableFlags φ rand
  else
    BitString.listRow φ.vars.length 0 rand ++
      List.replicate φ.vars.length false ++
      tableBits φ rand

/-- Selective-opening flags for one copy under challenge bit `b`. -/
def copyOpenFlags (φ : CNF ℕ) (b : Bool) (copy : List Bool) : List Bool :=
  if b then
    List.replicate φ.vars.length false ++
      List.replicate φ.vars.length true ++
      activeTableFlags φ (vPart φ copy)
  else
    List.replicate φ.vars.length true ++
      List.replicate φ.vars.length false ++
      List.replicate (8 * φ.length) true

@[simp] theorem length_realCopyBits (φ : CNF ℕ) (w m : List Bool) :
    (realCopyBits φ w m).length = copyLen φ := by
  simp [realCopyBits, copyLen, Nat.two_mul, Nat.add_assoc]

@[simp] theorem length_simCopyBits (φ : CNF ℕ) (b : Bool) (rand : List Bool) :
    (simCopyBits φ b rand).length = copyLen φ := by
  cases b <;> simp [simCopyBits, copyLen, Nat.two_mul, Nat.add_assoc]

@[simp] theorem length_copyOpenFlags (φ : CNF ℕ) (b : Bool) (copy : List Bool) :
    (copyOpenFlags φ b copy).length = copyLen φ := by
  cases b <;> simp [copyOpenFlags, copyLen, Nat.two_mul, Nat.add_assoc]

@[simp] theorem vPart_realCopyBits (φ : CNF ℕ) (w m : List Bool) :
    vPart φ (realCopyBits φ w m) = BitString.listXor φ.vars.length [w, m] :=
  take_drop_three_1 (by simp) (by simp)

@[simp] theorem mPart_simCopyBits_false (φ : CNF ℕ) (rand : List Bool) :
    mPart φ (simCopyBits φ false rand) = BitString.listRow φ.vars.length 0 rand :=
  take_three_0 (by simp)

@[simp] theorem vPart_simCopyBits_true (φ : CNF ℕ) (rand : List Bool) :
    vPart φ (simCopyBits φ true rand) = BitString.listRow φ.vars.length 0 rand :=
  take_drop_three_1 (by simp) (by simp)

@[simp] theorem tablePart_simCopyBits_false (φ : CNF ℕ) (rand : List Bool) :
    tablePart φ (simCopyBits φ false rand) = tableBits φ rand :=
  take_drop_three_2 (by simp) (by simp) (by simp)

@[simp] theorem tablePart_simCopyBits_true (φ : CNF ℕ) (rand : List Bool) :
    tablePart φ (simCopyBits φ true rand) = activeTableFlags φ rand :=
  take_drop_three_2 (by simp) (by simp) (by simp)

@[simp] theorem naorMaskBits_replicate_true {bits : List Bool} {n : ℕ} (h : bits.length = n) :
    naorMaskBits (List.replicate n true) bits = bits := by
  subst n
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [naorMaskBits, List.replicate_succ, ih]

@[simp] theorem naorMaskBits_replicate_false {bits : List Bool} {n : ℕ} (h : bits.length = n) :
    naorMaskBits (List.replicate n false) bits = List.replicate n false := by
  subst n
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [naorMaskBits, List.replicate_succ, ih]

theorem naorMaskBits_realCopyBits_false (φ : CNF ℕ) (w m : List Bool) :
    naorMaskBits (copyOpenFlags φ false (realCopyBits φ w m)) (realCopyBits φ w m) =
      simCopyBits φ false m := by
  simp only [copyOpenFlags, Bool.false_eq_true, ↓reduceIte, realCopyBits, simCopyBits]
  rw [naorMaskBits_append (by simp), naorMaskBits_append (by simp),
    naorMaskBits_replicate_true (by simp), naorMaskBits_replicate_false (by simp),
    naorMaskBits_replicate_true (by simp)]

theorem naorMaskBits_realCopyBits_true {φ : CNF ℕ} {w m : List Bool}
    (hw : ThreeSAT.verifier (φ, w) = true) :
    naorMaskBits (copyOpenFlags φ true (realCopyBits φ w m)) (realCopyBits φ w m) =
      simCopyBits φ true (BitString.listXor φ.vars.length [w, m]) := by
  have hlen_xor : (BitString.listXor φ.vars.length [w, m]).length = φ.vars.length := by simp
  have hrow_xor : BitString.listRow φ.vars.length 0 (BitString.listXor φ.vars.length [w, m]) =
      BitString.listXor φ.vars.length [w, m] := by
    simp [BitString.listRow, List.take_left' hlen_xor]
  simp only [copyOpenFlags, ↓reduceIte, vPart_realCopyBits]
  simp only [realCopyBits, simCopyBits, ↓reduceIte, hrow_xor]
  rw [naorMaskBits_append (by simp), naorMaskBits_append (by simp),
    naorMaskBits_replicate_false (by simp), naorMaskBits_replicate_true (by simp),
    naorMaskBits_activeTableFlags hw]

theorem copyOpenFlags_simCopyBits (φ : CNF ℕ) (b : Bool) (rand : List Bool) :
    copyOpenFlags φ b (simCopyBits φ b rand) =
      if b then
        List.replicate φ.vars.length false ++
          List.replicate φ.vars.length true ++
          activeTableFlags φ rand
      else
        List.replicate φ.vars.length true ++
          List.replicate φ.vars.length false ++
          List.replicate (8 * φ.length) true := by
  cases b <;> simp [copyOpenFlags]

theorem copyOpenFlags_realCopyBits (φ : CNF ℕ) (b : Bool) (w m : List Bool) :
    copyOpenFlags φ b (realCopyBits φ w m) =
      copyOpenFlags φ b
        (simCopyBits φ b (if b then BitString.listXor φ.vars.length [w, m] else m)) := by
  cases b <;> simp [copyOpenFlags]

@[simp] theorem naorMaskBits_simCopyBits (φ : CNF ℕ) (b : Bool) (rand : List Bool) :
    naorMaskBits (copyOpenFlags φ b (simCopyBits φ b rand)) (simCopyBits φ b rand) =
      simCopyBits φ b rand := by
  rw [copyOpenFlags_simCopyBits]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, simCopyBits]
    rw [naorMaskBits_append (by simp), naorMaskBits_append (by simp),
      naorMaskBits_replicate_true (by simp), naorMaskBits_replicate_false (by simp),
      naorMaskBits_replicate_true (by simp)]
  · simp only [↓reduceIte, simCopyBits]
    rw [naorMaskBits_append (by simp), naorMaskBits_append (by simp),
      naorMaskBits_replicate_false (by simp), naorMaskBits_replicate_true (by simp),
      naorMaskBits_eq_self_of_imp (by simp) (fun _ h => h)]

/-- Check the opened bits of one copy against challenge bit `b`. -/
def verifyCopyBits (φ : CNF ℕ) (b : Bool) (copy : List Bool) : Bool :=
  if b then
    (List.range (8 * φ.length)).all fun i =>
      !(activeTableFlags φ (vPart φ copy)).getD i false || (tablePart φ copy).getD i false
  else
    tablePart φ copy == tableBits φ (mPart φ copy)

@[simp] theorem verifyCopyBits_simCopyBits (φ : CNF ℕ) (b : Bool) (rand : List Bool) :
    verifyCopyBits φ b (simCopyBits φ b rand) = true := by
  cases b
  · simp [verifyCopyBits]
  · simp only [verifyCopyBits, ↓reduceIte, vPart_simCopyBits_true, activeTableFlags_listRow,
      tablePart_simCopyBits_true, List.all_eq_true]
    intro i _
    cases (activeTableFlags φ rand).getD i false <;> rfl

theorem getD_append_right {u v : List Bool} {d i : ℕ} (hu : u.length = d) :
    (u ++ v).getD (d + i) false = v.getD i false := by
  subst d
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right u.length i)]

theorem getD_listRow_of_lt {width row t : ℕ} {word : List Bool} (ht : t < width)
    (hlen : row * width + t < word.length) :
    (BitString.listRow width row word).getD t false = word.getD (row * width + t) false := by
  have hdrop : t < (word.drop (row * width)).length := by simp; omega
  simp [BitString.listRow, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt ht,
    List.getElem?_append_left hdrop, List.getElem?_drop]

theorem satisfiable_of_verifyCopyBits {φ : CNF ℕ} {copy₀ copy₁ : List Bool}
    (hwidth : ∀ c ∈ φ, c.length ≤ 3)
    (h₀ : verifyCopyBits φ false copy₀ = true)
    (h₁ : verifyCopyBits φ true copy₁ = true)
    (hagree : ∀ i < copyLen φ,
      (copyOpenFlags φ false copy₀).getD i false = true →
      (copyOpenFlags φ true copy₁).getD i false = true →
      copy₀.getD i false = copy₁.getD i false) :
    φ.Satisfiable := by
  let m := mPart φ copy₀
  let v := vPart φ copy₁
  have htab₀ : tablePart φ copy₀ = tableBits φ m := by
    simpa [verifyCopyBits, m] using h₀
  have htab₁ : ∀ j < 8 * φ.length,
      (activeTableFlags φ v).getD j false = true → (tablePart φ copy₁).getD j false = true := by
    simp only [verifyCopyBits, ↓reduceIte, List.all_eq_true, List.mem_range,
      Bool.or_eq_true, Bool.not_eq_true'] at h₁
    intro j hj hact
    rcases h₁ j hj with hfalse | htrue
    · rw [hact] at hfalse; contradiction
    · exact htrue
  have htab_eq : ∀ j < 8 * φ.length,
      (activeTableFlags φ v).getD j false = true → (tableBits φ m).getD j false = true := by
    intro j hj hact
    have hj_len : 2 * φ.vars.length + j < copyLen φ := by unfold copyLen; omega
    have hflag₀ : (copyOpenFlags φ false copy₀).getD (2 * φ.vars.length + j) false = true := by
      simp only [copyOpenFlags, Bool.false_eq_true, ↓reduceIte]
      rw [getD_append_right (by simp [Nat.two_mul])]
      simp [List.getD_eq_getElem?_getD, hj]
    have hflag₁ : (copyOpenFlags φ true copy₁).getD (2 * φ.vars.length + j) false = true := by
      simp only [copyOpenFlags, ↓reduceIte]
      rw [getD_append_right (by simp [Nat.two_mul])]
      exact hact
    have hcopy_eq := hagree (2 * φ.vars.length + j) hj_len hflag₀ hflag₁
    have hpart₀ := getD_take_drop copy₀ (2 * φ.vars.length) (8 * φ.length) j hj
    have hpart₁ := getD_take_drop copy₁ (2 * φ.vars.length) (8 * φ.length) j hj
    rw [← htab₀]
    change ((copy₀.drop (2 * φ.vars.length)).take (8 * φ.length)).getD j false = true
    rw [hpart₀, hcopy_eq, ← hpart₁]
    exact htab₁ j hj hact
  refine ⟨fun x => varBit φ v x ^^ varBit φ m x, CNF.eval_eq_true_iff _ _ |>.mpr ?_⟩
  intro c hc
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
  let t := activeIdx
    (varBit φ v (φ[k].getD 0 (0, false)).1)
    (varBit φ v (φ[k].getD 1 (0, false)).1)
    (varBit φ v (φ[k].getD 2 (0, false)).1)
  have ht : t < 8 := activeIdx_lt_eight _ _ _
  have hkt : k * 8 + t < 8 * φ.length := by omega
  have hrow_act : BitString.listRow 8 k (activeTableFlags φ v) = clauseActiveRow φ v φ[k] := by
    unfold activeTableFlags
    rw [listRow_flatten (by intro w hw; obtain ⟨_, _, rfl⟩ := List.mem_map.mp hw; simp)
      (by simpa using hk)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  have hrow_tab : BitString.listRow 8 k (tableBits φ m) = clauseTableRow φ m φ[k] := by
    unfold tableBits
    rw [listRow_flatten (by intro w hw; obtain ⟨_, _, rfl⟩ := List.mem_map.mp hw; simp)
      (by simpa using hk)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  have hact_true : (activeTableFlags φ v).getD (k * 8 + t) false = true := by
    rw [← getD_listRow_of_lt ht (by simpa using hkt), hrow_act, getD_clauseActiveRow φ v φ[k] ht]
    simp [t]
  have htab_true := htab_eq (k * 8 + t) hkt hact_true
  rw [← getD_listRow_of_lt ht (by simpa using hkt), hrow_tab,
    getD_clauseTableRow φ m φ[k] ht] at htab_true
  simp only [t, bit0Of8_activeIdx, bit1Of8_activeIdx, bit2Of8_activeIdx] at htab_true
  rw [← clauseEvalBits_eq_eval (hwidth φ[k] hc) (fun x => varBit φ v x ^^ varBit φ m x)]
  exact htab_true

/-! ### Three-copy protocol messages and verification -/

/-- Extract copy 0 (`copyLen φ` bits) from a 3-copy bit vector. -/
def copy0 (φ : CNF ℕ) (bits : List Bool) : List Bool :=
  bits.take (copyLen φ)

/-- Extract copy 1 (`copyLen φ` bits) from a 3-copy bit vector. -/
def copy1 (φ : CNF ℕ) (bits : List Bool) : List Bool :=
  (bits.drop (copyLen φ)).take (copyLen φ)

/-- Extract copy 2 (`copyLen φ` bits) from a 3-copy bit vector. -/
def copy2 (φ : CNF ℕ) (bits : List Bool) : List Bool :=
  (bits.drop (2 * copyLen φ)).take (copyLen φ)

/-- Honest committed bits across all three copies. -/
def realBits (φ : CNF ℕ) (w m₀ m₁ m₂ : List Bool) : List Bool :=
  realCopyBits φ w m₀ ++ realCopyBits φ w m₁ ++ realCopyBits φ w m₂

/-- Simulated (and selectively opened) bits across all three copies. -/
def simBits (φ : CNF ℕ) (ch r₀ r₁ r₂ : List Bool) : List Bool :=
  simCopyBits φ (ch.getD 0 false) r₀ ++
    simCopyBits φ (ch.getD 1 false) r₁ ++
    simCopyBits φ (ch.getD 2 false) r₂

/-- Selective-opening flags across all three copies under challenge word `ch`. -/
def allOpenFlags (φ : CNF ℕ) (ch bits : List Bool) : List Bool :=
  copyOpenFlags φ (ch.getD 0 false) (copy0 φ bits) ++
    copyOpenFlags φ (ch.getD 1 false) (copy1 φ bits) ++
    copyOpenFlags φ (ch.getD 2 false) (copy2 φ bits)

@[simp] theorem length_realBits (φ : CNF ℕ) (w m₀ m₁ m₂ : List Bool) :
    (realBits φ w m₀ m₁ m₂).length = totalLen φ := by
  simp [realBits, totalLen]
  omega

@[simp] theorem length_simBits (φ : CNF ℕ) (ch r₀ r₁ r₂ : List Bool) :
    (simBits φ ch r₀ r₁ r₂).length = totalLen φ := by
  simp [simBits, totalLen]
  omega

@[simp] theorem length_allOpenFlags (φ : CNF ℕ) (ch bits : List Bool) :
    (allOpenFlags φ ch bits).length = totalLen φ := by
  simp [allOpenFlags, totalLen]
  omega

@[simp] theorem copy0_realBits (φ : CNF ℕ) (w m₀ m₁ m₂ : List Bool) :
    copy0 φ (realBits φ w m₀ m₁ m₂) = realCopyBits φ w m₀ :=
  take_three_0 (by simp)

@[simp] theorem copy1_realBits (φ : CNF ℕ) (w m₀ m₁ m₂ : List Bool) :
    copy1 φ (realBits φ w m₀ m₁ m₂) = realCopyBits φ w m₁ :=
  take_drop_three_1 (by simp) (by simp)

@[simp] theorem copy2_realBits (φ : CNF ℕ) (w m₀ m₁ m₂ : List Bool) :
    copy2 φ (realBits φ w m₀ m₁ m₂) = realCopyBits φ w m₂ :=
  take_drop_three_2 (by simp) (by simp) (by simp)

@[simp] theorem copy0_simBits (φ : CNF ℕ) (ch r₀ r₁ r₂ : List Bool) :
    copy0 φ (simBits φ ch r₀ r₁ r₂) = simCopyBits φ (ch.getD 0 false) r₀ :=
  take_three_0 (by simp)

@[simp] theorem copy1_simBits (φ : CNF ℕ) (ch r₀ r₁ r₂ : List Bool) :
    copy1 φ (simBits φ ch r₀ r₁ r₂) = simCopyBits φ (ch.getD 1 false) r₁ :=
  take_drop_three_1 (by simp) (by simp)

@[simp] theorem copy2_simBits (φ : CNF ℕ) (ch r₀ r₁ r₂ : List Bool) :
    copy2 φ (simBits φ ch r₀ r₁ r₂) = simCopyBits φ (ch.getD 2 false) r₂ :=
  take_drop_three_2 (by simp) (by simp) (by simp)

theorem naorMaskBits_realCopyBits {φ : CNF ℕ} {w m : List Bool} (b : Bool)
    (hw : ThreeSAT.verifier (φ, w) = true) :
    naorMaskBits (copyOpenFlags φ b (realCopyBits φ w m)) (realCopyBits φ w m) =
      simCopyBits φ b (if b then BitString.listXor φ.vars.length [w, m] else m) := by
  cases b
  · exact naorMaskBits_realCopyBits_false φ w m
  · exact naorMaskBits_realCopyBits_true hw

theorem naorMaskBits_realBits {φ : CNF ℕ} {w m₀ m₁ m₂ : List Bool} (ch : List Bool)
    (hw : ThreeSAT.verifier (φ, w) = true) :
    naorMaskBits (allOpenFlags φ ch (realBits φ w m₀ m₁ m₂)) (realBits φ w m₀ m₁ m₂) =
      simBits φ ch
        (if ch.getD 0 false then BitString.listXor φ.vars.length [w, m₀] else m₀)
        (if ch.getD 1 false then BitString.listXor φ.vars.length [w, m₁] else m₁)
        (if ch.getD 2 false then BitString.listXor φ.vars.length [w, m₂] else m₂) := by
  simp only [allOpenFlags, copy0_realBits, copy1_realBits, copy2_realBits]
  simp only [realBits, simBits]
  rw [naorMaskBits_append (by simp), naorMaskBits_append (by simp),
    naorMaskBits_realCopyBits _ hw, naorMaskBits_realCopyBits _ hw, naorMaskBits_realCopyBits _ hw]

theorem allOpenFlags_realBits (φ : CNF ℕ) (ch w m₀ m₁ m₂ : List Bool) :
    allOpenFlags φ ch (realBits φ w m₀ m₁ m₂) =
      allOpenFlags φ ch
        (simBits φ ch
          (if ch.getD 0 false then BitString.listXor φ.vars.length [w, m₀] else m₀)
          (if ch.getD 1 false then BitString.listXor φ.vars.length [w, m₁] else m₁)
          (if ch.getD 2 false then BitString.listXor φ.vars.length [w, m₂] else m₂)) := by
  simp only [allOpenFlags, copy0_realBits, copy1_realBits, copy2_realBits,
    copy0_simBits, copy1_simBits, copy2_simBits, copyOpenFlags_realCopyBits]

@[simp] theorem naorMaskBits_simBits (φ : CNF ℕ) (ch r₀ r₁ r₂ : List Bool) :
    naorMaskBits (allOpenFlags φ ch (simBits φ ch r₀ r₁ r₂)) (simBits φ ch r₀ r₁ r₂) =
      simBits φ ch r₀ r₁ r₂ := by
  simp only [allOpenFlags, copy0_simBits, copy1_simBits, copy2_simBits]
  simp only [simBits]
  rw [naorMaskBits_append (by simp), naorMaskBits_append (by simp),
    naorMaskBits_simCopyBits, naorMaskBits_simCopyBits, naorMaskBits_simCopyBits]

/-- Prover's first-round message: flat list of `totalLen φ` Naor commitments. -/
def proverReply1 (generator : List Bool → List Bool) (m : ℕ)
    (r openFlags bits : List Bool) (seeds pads : List (List Bool)) : List Bool :=
  ((naorCommitSplit generator (BitString.listRow m 0 r) openFlags bits seeds pads).flatten).take
    (bits.length * m)

/-- Prover's second-round message: masked bits followed by flat selected seeds. -/
def proverReply2 (s : ℕ) (φ : CNF ℕ) (ch bits : List Bool)
    (seeds : List (List Bool)) : List Bool :=
  let flags := allOpenFlags φ ch bits
  naorMaskBits flags bits ++ (naorSelectSeeds s flags bits seeds).flatten

/-- Check that every active position `i < totalLen φ` opens to the committed word in
`commitReply`. -/
def verifyCommitments (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (r flags commitReply openedBits openSeedsFlat : List Bool) : Bool :=
  (List.range (totalLen φ)).all fun i =>
    !flags.getD i false ||
      (naorCommit generator (BitString.listRow m 0 r) (openedBits.getD i false)
        (BitString.listRow s i openSeedsFlat) ==
        BitString.listRow m i commitReply)

/-- Verifier's complete check on the two-round interaction transcript. -/
def verifyTranscript (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (r commitReply ch openReply : List Bool) : Bool :=
  let K := totalLen φ
  let openedBits := openReply.take K
  let openSeedsFlat := openReply.drop K
  let flags := allOpenFlags φ ch openedBits
  (φ.all fun c => decide (c.length ≤ 3)) &&
  verifyCopyBits φ (ch.getD 0 false) (copy0 φ openedBits) &&
  verifyCopyBits φ (ch.getD 1 false) (copy1 φ openedBits) &&
  verifyCopyBits φ (ch.getD 2 false) (copy2 φ openedBits) &&
  verifyCommitments generator s m φ r flags commitReply openedBits openSeedsFlat

theorem length_mem_naorCommitSplit_true {generator : List Bool → List Bool} {m : ℕ}
    {r bits : List Bool} {seeds : List (List Bool)}
    (hseeds : seeds.length = bits.length)
    (hgen : ∀ seed ∈ seeds, (generator seed).length = m) :
    ∀ u ∈ naorCommitSplit generator r (List.replicate bits.length true) bits seeds [],
      u.length = m := by
  rw [naorCommitSplit_eq_map]
  intro u hu
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hu
  rw [List.mem_range] at hi
  have hflag : (List.replicate bits.length true).getD i false = true := by
    simp [List.getD, hi]
  have hi_seeds : i < seeds.length := hseeds ▸ hi
  have hmem : seeds.getD i [] ∈ seeds := by
    simp [List.getD, List.getElem?_eq_getElem hi_seeds]
  rw [hflag, naorCommitAt_true, length_naorCommit, hgen _ hmem]

theorem length_proverReply1_le (generator : List Bool → List Bool) (m : ℕ)
    (r openFlags bits : List Bool) (seeds pads : List (List Bool)) :
    (proverReply1 generator m r openFlags bits seeds pads).length ≤ bits.length * m :=
  List.length_take_le _ _

theorem proverReply1_true_eq_flatten {generator : List Bool → List Bool} {m : ℕ}
    (r : List Bool) {bits : List Bool} {seeds : List (List Bool)}
    (hseeds : seeds.length = bits.length)
    (hgen : ∀ seed ∈ seeds, (generator seed).length = m) :
    proverReply1 generator m r (List.replicate bits.length true) bits seeds [] =
      (naorCommitSplit generator (BitString.listRow m 0 r)
        (List.replicate bits.length true) bits seeds []).flatten := by
  have hmem := length_mem_naorCommitSplit_true (r := BitString.listRow m 0 r) hseeds hgen
  have hmap :
      List.map List.length
        (naorCommitSplit generator (BitString.listRow m 0 r)
          (List.replicate bits.length true) bits seeds []) =
        List.replicate bits.length m := by
    apply List.ext_getElem (by simp)
    intro i hi hi'
    simp only [List.getElem_map, List.getElem_replicate]
    exact hmem _ (List.getElem_mem _)
  have hlen :
      (naorCommitSplit generator (BitString.listRow m 0 r)
        (List.replicate bits.length true) bits seeds []).flatten.length = bits.length * m := by
    simp [List.length_flatten, hmap]
  simp [proverReply1, List.take_of_length_le hlen.le]

theorem length_proverReply1_true {generator : List Bool → List Bool} {m : ℕ}
    {r bits : List Bool} {seeds : List (List Bool)}
    (hseeds : seeds.length = bits.length)
    (hgen : ∀ seed ∈ seeds, (generator seed).length = m) :
    (proverReply1 generator m r (List.replicate bits.length true) bits seeds []).length =
      bits.length * m := by
  have hmem := length_mem_naorCommitSplit_true (r := BitString.listRow m 0 r) hseeds hgen
  have hmap :
      List.map List.length
        (naorCommitSplit generator (BitString.listRow m 0 r)
          (List.replicate bits.length true) bits seeds []) =
        List.replicate bits.length m := by
    apply List.ext_getElem (by simp)
    intro i hi hi'
    simp only [List.getElem_map, List.getElem_replicate]
    exact hmem _ (List.getElem_mem _)
  simp [proverReply1_true_eq_flatten r hseeds hgen, List.length_flatten, hmap]

theorem length_proverReply2_any (s : ℕ) (φ : CNF ℕ) (ch bits : List Bool)
    (seeds : List (List Bool)) :
    (proverReply2 s φ ch bits seeds).length = bits.length * (s + 1) := by
  have hmap :
      List.map List.length (naorSelectSeeds s (allOpenFlags φ ch bits) bits seeds) =
        List.replicate bits.length s := by
    apply List.ext_getElem (by simp)
    intro i hi hi'
    simp only [List.getElem_map, List.getElem_replicate]
    exact length_mem_naorSelectSeeds (List.getElem_mem _)
  simp only [proverReply2, List.length_append, length_naorMaskBits,
    List.length_flatten, hmap, List.sum_replicate, smul_eq_mul]
  ring

theorem length_proverReply2 (s : ℕ) (φ : CNF ℕ) {ch bits : List Bool}
    (seeds : List (List Bool)) (hbits : bits.length = totalLen φ) :
    (proverReply2 s φ ch bits seeds).length = totalLen φ * (s + 1) := by
  rw [length_proverReply2_any, hbits]

theorem verifyTranscript_honest {generator : List Bool → List Bool} {s m : ℕ}
    {φ : CNF ℕ} {w m₀ m₁ m₂ r ch : List Bool} {seeds : List (List Bool)}
    (hw : ThreeSAT.verifier (φ, w) = true)
    (hseeds : seeds.length = totalLen φ)
    (hseed_len : ∀ seed ∈ seeds, seed.length = s)
    (hgen_len : ∀ seed ∈ seeds, (generator seed).length = m) :
    verifyTranscript generator s m φ r
      (proverReply1 generator m r (List.replicate (totalLen φ) true)
        (realBits φ w m₀ m₁ m₂) seeds [])
      ch
      (proverReply2 s φ ch (realBits φ w m₀ m₁ m₂) seeds) = true := by
  let K := totalLen φ
  let bits := realBits φ w m₀ m₁ m₂
  have hbits_len : bits.length = K := length_realBits φ w m₀ m₁ m₂
  let flags := allOpenFlags φ ch bits
  have hmask_len :
      (naorMaskBits (allOpenFlags φ ch (realBits φ w m₀ m₁ m₂))
        (realBits φ w m₀ m₁ m₂)).length = totalLen φ := by
    simp
  have htake :
      (proverReply2 s φ ch (realBits φ w m₀ m₁ m₂) seeds).take (totalLen φ) =
        naorMaskBits (allOpenFlags φ ch (realBits φ w m₀ m₁ m₂))
          (realBits φ w m₀ m₁ m₂) := by
    simp [proverReply2, List.take_left' hmask_len]
  have hdrop :
      (proverReply2 s φ ch (realBits φ w m₀ m₁ m₂) seeds).drop (totalLen φ) =
        (naorSelectSeeds s (allOpenFlags φ ch (realBits φ w m₀ m₁ m₂))
          (realBits φ w m₀ m₁ m₂) seeds).flatten := by
    simp [proverReply2, List.drop_left' hmask_len]
  have hmask_eq := naorMaskBits_realBits (m₀ := m₀) (m₁ := m₁) (m₂ := m₂) ch hw
  have hflags_eq :
      allOpenFlags φ ch
        (naorMaskBits (allOpenFlags φ ch (realBits φ w m₀ m₁ m₂))
          (realBits φ w m₀ m₁ m₂)) =
        allOpenFlags φ ch (realBits φ w m₀ m₁ m₂) := by
    rw [hmask_eq]
    exact (allOpenFlags_realBits φ ch w m₀ m₁ m₂).symm
  have h3sat : (φ.all fun c => decide (c.length ≤ 3)) = true := by
    simp only [ThreeSAT.verifier, Bool.and_eq_true] at hw
    exact hw.1
  dsimp only [verifyTranscript]
  rw [htake, hdrop, hflags_eq, h3sat]
  have hcopy :
      verifyCopyBits φ (ch.getD 0 false) (copy0 φ (naorMaskBits flags bits)) = true ∧
      verifyCopyBits φ (ch.getD 1 false) (copy1 φ (naorMaskBits flags bits)) = true ∧
      verifyCopyBits φ (ch.getD 2 false) (copy2 φ (naorMaskBits flags bits)) = true := by
    dsimp only [flags, bits]
    rw [hmask_eq]
    simp [copy0_simBits, copy1_simBits, copy2_simBits, verifyCopyBits_simCopyBits]
  change
    (true &&
      verifyCopyBits φ (ch.getD 0 false) (copy0 φ (naorMaskBits flags bits)) &&
      verifyCopyBits φ (ch.getD 1 false) (copy1 φ (naorMaskBits flags bits)) &&
      verifyCopyBits φ (ch.getD 2 false) (copy2 φ (naorMaskBits flags bits)) &&
      verifyCommitments generator s m φ r flags
        (proverReply1 generator m r (List.replicate K true) bits seeds [])
        (naorMaskBits flags bits) (naorSelectSeeds s flags bits seeds).flatten) = true
  simp only [hcopy.1, hcopy.2.1, hcopy.2.2, Bool.true_and, verifyCommitments, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq]
  intro i hi
  by_cases hfi : flags.getD i false = true
  · right
    have hbit_i : (naorMaskBits flags bits).getD i false = bits.getD i false := by
      rw [getD_naorMaskBits, hfi, Bool.true_and]
    have hi_bits : i < bits.length := hbits_len ▸ hi
    have hi_seeds : i < seeds.length := hseeds ▸ hi
    have hseed_mem : seeds.getD i [] ∈ seeds := by
      simp [List.getD, List.getElem?_eq_getElem hi_seeds]
    have hseed_i :
        BitString.listRow s i (naorSelectSeeds s flags bits seeds).flatten =
          seeds.getD i [] := by
      rw [listRow_flatten (fun w hw => length_mem_naorSelectSeeds hw) (by simp [hi_bits]),
        getD_naorSelectSeeds s flags bits seeds i hi_bits, hfi]
      simp only [↓reduceIte, BitString.listRow, Nat.zero_mul, List.drop_zero,
        List.take_left' (hseed_len _ hseed_mem)]
    have hcommit_i :
        BitString.listRow m i
          (proverReply1 generator m r (List.replicate K true) bits seeds []) =
          naorCommit generator (BitString.listRow m 0 r) (bits.getD i false)
            (seeds.getD i []) := by
      have hmem := length_mem_naorCommitSplit_true
        (r := BitString.listRow m 0 r) (hseeds.trans hbits_len.symm) hgen_len
      rw [← hbits_len, proverReply1_true_eq_flatten r (hseeds.trans hbits_len.symm) hgen_len,
        listRow_flatten hmem (by simp [hi_bits]),
        getD_naorCommitSplit _ _ _ _ _ _ i hi_bits]
      have hrep : (List.replicate bits.length true).getD i false = true := by
        simp [List.getD, hi_bits]
      rw [hrep, naorCommitAt_true]
    rw [hbit_i, hseed_i, hcommit_i]
  · left
    exact Bool.eq_false_iff.mpr hfi

theorem getD_append_left {u v : List Bool} {i : ℕ} (hi : i < u.length) :
    (u ++ v).getD i false = u.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_drop_take {xs : List Bool} {d L i : ℕ} (hi : i < L) :
    ((xs.drop d).take L).getD i false = xs.getD (d + i) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi, List.getElem?_drop]

theorem getD_allOpenFlags_copy0 (φ : CNF ℕ) (ch bits : List Bool) {i : ℕ} (hi : i < copyLen φ) :
    (allOpenFlags φ ch bits).getD i false =
      (copyOpenFlags φ (ch.getD 0 false) (copy0 φ bits)).getD i false := by
  simp only [allOpenFlags, List.append_assoc]
  exact getD_append_left (by simpa using hi)

theorem getD_allOpenFlags_copy1 (φ : CNF ℕ) (ch bits : List Bool) {i : ℕ} (hi : i < copyLen φ) :
    (allOpenFlags φ ch bits).getD (copyLen φ + i) false =
      (copyOpenFlags φ (ch.getD 1 false) (copy1 φ bits)).getD i false := by
  simp only [allOpenFlags, List.append_assoc]
  rw [getD_append_right (by simp), getD_append_left (by simpa using hi)]

theorem getD_allOpenFlags_copy2 (φ : CNF ℕ) (ch bits : List Bool) (i : ℕ) :
    (allOpenFlags φ ch bits).getD (2 * copyLen φ + i) false =
      (copyOpenFlags φ (ch.getD 2 false) (copy2 φ bits)).getD i false := by
  have hlen :
      (copyOpenFlags φ (ch.getD 0 false) (copy0 φ bits) ++
        copyOpenFlags φ (ch.getD 1 false) (copy1 φ bits)).length = 2 * copyLen φ := by
    simp; omega
  simp only [allOpenFlags]
  exact getD_append_right hlen

theorem verifyCommitments_eq_of_true {generator : List Bool → List Bool} {s m : ℕ} {φ : CNF ℕ}
    {r flags₀ flags₁ commitReply opened₀ opened₁ seeds₀ seeds₁ : List Bool}
    (hbind : NaorBinding generator s (BitString.listRow m 0 r))
    (hc₀ : verifyCommitments generator s m φ r flags₀ commitReply opened₀ seeds₀ = true)
    (hc₁ : verifyCommitments generator s m φ r flags₁ commitReply opened₁ seeds₁ = true)
    {idx : ℕ} (hidx : idx < totalLen φ)
    (hf₀ : flags₀.getD idx false = true) (hf₁ : flags₁.getD idx false = true) :
    opened₀.getD idx false = opened₁.getD idx false := by
  simp only [verifyCommitments, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', beq_iff_eq] at hc₀ hc₁
  have h₀ := (hc₀ idx hidx).resolve_left (by rw [hf₀]; decide)
  have h₁ := (hc₁ idx hidx).resolve_left (by rw [hf₁]; decide)
  exact hbind.eq_of_naorCommit_eq (BitString.length_listRow s idx seeds₀)
    (BitString.length_listRow s idx seeds₁) (h₀.trans h₁.symm)

theorem mem_ThreeSAT_of_verifyTranscript_false_true
    {generator : List Bool → List Bool} {s m : ℕ} {φ : CNF ℕ}
    {r commitReply ch₀ ch₁ openReply₀ openReply₁ : List Bool}
    (hbind : NaorBinding generator s (BitString.listRow m 0 r))
    (hv₀ : verifyTranscript generator s m φ r commitReply ch₀ openReply₀ = true)
    (hv₁ : verifyTranscript generator s m φ r commitReply ch₁ openReply₁ = true)
    (hdiff :
      (ch₀.getD 0 false = false ∧ ch₁.getD 0 false = true) ∨
      (ch₀.getD 1 false = false ∧ ch₁.getD 1 false = true) ∨
      (ch₀.getD 2 false = false ∧ ch₁.getD 2 false = true)) :
    φ ∈ ThreeSAT := by
  let K := totalLen φ
  let opened₀ := openReply₀.take K
  let opened₁ := openReply₁.take K
  simp only [verifyTranscript, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hv₀ hv₁
  obtain ⟨⟨⟨⟨hwidth, hv₀_0⟩, hv₀_1⟩, hv₀_2⟩, hc₀⟩ := hv₀
  obtain ⟨⟨⟨⟨_, hv₁_0⟩, hv₁_1⟩, hv₁_2⟩, hc₁⟩ := hv₁
  refine ⟨hwidth, ?_⟩
  rcases hdiff with ⟨hb₀, hb₁⟩ | ⟨hb₀, hb₁⟩ | ⟨hb₀, hb₁⟩
  · rw [hb₀] at hv₀_0
    rw [hb₁] at hv₁_0
    refine satisfiable_of_verifyCopyBits hwidth hv₀_0 hv₁_0 fun i hi hf₀ hf₁ => ?_
    have hidx : i < totalLen φ := by simp [totalLen]; omega
    have hf₀' : (allOpenFlags φ ch₀ opened₀).getD i false = true := by
      rw [getD_allOpenFlags_copy0 φ ch₀ opened₀ hi, hb₀]
      exact hf₀
    have hf₁' : (allOpenFlags φ ch₁ opened₁).getD i false = true := by
      rw [getD_allOpenFlags_copy0 φ ch₁ opened₁ hi, hb₁]
      exact hf₁
    have heq := verifyCommitments_eq_of_true hbind hc₀ hc₁ hidx hf₀' hf₁'
    simpa [copy0, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi] using heq
  · rw [hb₀] at hv₀_1
    rw [hb₁] at hv₁_1
    refine satisfiable_of_verifyCopyBits hwidth hv₀_1 hv₁_1 fun i hi hf₀ hf₁ => ?_
    have hidx : copyLen φ + i < totalLen φ := by simp [totalLen]; omega
    have hf₀' : (allOpenFlags φ ch₀ opened₀).getD (copyLen φ + i) false = true := by
      rw [getD_allOpenFlags_copy1 φ ch₀ opened₀ hi, hb₀]
      exact hf₀
    have hf₁' : (allOpenFlags φ ch₁ opened₁).getD (copyLen φ + i) false = true := by
      rw [getD_allOpenFlags_copy1 φ ch₁ opened₁ hi, hb₁]
      exact hf₁
    have heq := verifyCommitments_eq_of_true hbind hc₀ hc₁ hidx hf₀' hf₁'
    simp only [copy1, getD_drop_take hi]
    exact heq
  · rw [hb₀] at hv₀_2
    rw [hb₁] at hv₁_2
    refine satisfiable_of_verifyCopyBits hwidth hv₀_2 hv₁_2 fun i hi hf₀ hf₁ => ?_
    have hidx : 2 * copyLen φ + i < totalLen φ := by simp [totalLen]; omega
    have hf₀' : (allOpenFlags φ ch₀ opened₀).getD (2 * copyLen φ + i) false = true := by
      rw [getD_allOpenFlags_copy2 φ ch₀ opened₀ i, hb₀]
      exact hf₀
    have hf₁' : (allOpenFlags φ ch₁ opened₁).getD (2 * copyLen φ + i) false = true := by
      rw [getD_allOpenFlags_copy2 φ ch₁ opened₁ i, hb₁]
      exact hf₁
    have heq := verifyCommitments_eq_of_true hbind hc₀ hc₁ hidx hf₀' hf₁'
    simp only [copy2, getD_drop_take hi]
    exact heq

theorem mem_ThreeSAT_of_verifyTranscript_ne
    {generator : List Bool → List Bool} {s m : ℕ} {φ : CNF ℕ}
    {r commitReply openReply₁ openReply₂ : List Bool} {x₁ x₂ : BitString 3}
    (hbind : NaorBinding generator s (BitString.listRow m 0 r))
    (hne : x₁ ≠ x₂)
    (hv₁ : verifyTranscript generator s m φ r commitReply (List.ofFn x₁) openReply₁ = true)
    (hv₂ : verifyTranscript generator s m φ r commitReply (List.ofFn x₂) openReply₂ = true) :
    φ ∈ ThreeSAT := by
  have hdiff :
      (List.ofFn x₁).getD 0 false ≠ (List.ofFn x₂).getD 0 false ∨
      (List.ofFn x₁).getD 1 false ≠ (List.ofFn x₂).getD 1 false ∨
      (List.ofFn x₁).getD 2 false ≠ (List.ofFn x₂).getD 2 false := by
    by_contra h
    push Not at h
    apply hne
    funext j
    fin_cases j
    · simpa using h.1
    · simpa using h.2.1
    · simpa using h.2.2
  rcases hdiff with h0 | h1 | h2
  · cases h10 : (List.ofFn x₁).getD 0 false <;> cases h20 : (List.ofFn x₂).getD 0 false
    · exact False.elim (h0 (h10.trans h20.symm))
    · exact mem_ThreeSAT_of_verifyTranscript_false_true hbind hv₁ hv₂ (Or.inl ⟨h10, h20⟩)
    · exact mem_ThreeSAT_of_verifyTranscript_false_true hbind hv₂ hv₁ (Or.inl ⟨h20, h10⟩)
    · exact False.elim (h0 (h10.trans h20.symm))
  · cases h11 : (List.ofFn x₁).getD 1 false <;> cases h21 : (List.ofFn x₂).getD 1 false
    · exact False.elim (h1 (h11.trans h21.symm))
    · exact mem_ThreeSAT_of_verifyTranscript_false_true hbind hv₁ hv₂ (Or.inr (Or.inl ⟨h11, h21⟩))
    · exact mem_ThreeSAT_of_verifyTranscript_false_true hbind hv₂ hv₁ (Or.inr (Or.inl ⟨h21, h11⟩))
    · exact False.elim (h1 (h11.trans h21.symm))
  · cases h12 : (List.ofFn x₁).getD 2 false <;> cases h22 : (List.ofFn x₂).getD 2 false
    · exact False.elim (h2 (h12.trans h22.symm))
    · exact mem_ThreeSAT_of_verifyTranscript_false_true hbind hv₁ hv₂ (Or.inr (Or.inr ⟨h12, h22⟩))
    · exact mem_ThreeSAT_of_verifyTranscript_false_true hbind hv₂ hv₁ (Or.inr (Or.inr ⟨h22, h12⟩))
    · exact False.elim (h2 (h12.trans h22.symm))

/-! ### Two-round deterministic state handler and honest prover -/

/-- Deterministic two-round state transition answering the first query with `reply1 q`, the second
query with `reply2 (BitString.listRow 3 0 q)` while recording the 3-bit challenge in the state, and
subsequent queries with `[]`. -/
def twoRoundStep (reply1 reply2 : List Bool → List Bool) (q : List Bool)
    (s : ℕ × List Bool) : List Bool × (ℕ × List Bool) :=
  if s.1 == 0 then (reply1 q, (1, s.2))
  else if s.1 == 1 then (reply2 (BitString.listRow 3 0 q), (2, BitString.listRow 3 0 q))
  else ([], s)

/-- Run a `WordOracleComp Unit` program against `twoRoundStep` inside `ProbComp`. -/
noncomputable def runTwoRound {α : Type} (reply1 reply2 : List Bool → List Bool)
    (prog : WordOracleComp Unit α) (s : ℕ × List Bool) :
    ProbComp (α × (ℕ × List Bool)) :=
  (OracleComp.interpret
    (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifFin n))
      (fun q state => pure (twoRoundStep reply1 reply2 q.2 state)))
    prog).run s

@[simp] theorem runTwoRound_pure {α : Type} (reply1 reply2 : List Bool → List Bool)
    (a : α) (s : ℕ × List Bool) :
    runTwoRound reply1 reply2 (pure a) s = pure (a, s) := rfl

theorem runTwoRound_bind {α β : Type} (reply1 reply2 : List Bool → List Bool)
    (prog : WordOracleComp Unit α) (next : α → WordOracleComp Unit β) (s : ℕ × List Bool) :
    runTwoRound reply1 reply2 (prog >>= next) s =
      (runTwoRound reply1 reply2 prog s >>= fun x => runTwoRound reply1 reply2 (next x.1) x.2) := by
  simp only [runTwoRound, OracleComp.interpret_bind, StateT.run_bind]

theorem runTwoRound_map {α β : Type} (reply1 reply2 : List Bool → List Bool)
    (f : α → β) (prog : WordOracleComp Unit α) (s : ℕ × List Bool) :
    runTwoRound reply1 reply2 (f <$> prog) s =
      Prod.map f id <$> runTwoRound reply1 reply2 prog s := by
  simp only [runTwoRound, OracleComp.interpret_map, StateT.run_map]
  rfl

@[simp] theorem runTwoRound_sample {α : Type} (reply1 reply2 : List Bool → List Bool)
    (prog : ProbComp α) (s : ℕ × List Bool) :
    runTwoRound reply1 reply2 (ProbOracleComp.sample prog) s = (·, s) <$> prog := by
  simp only [runTwoRound, ProbOracleComp.interpret_sample, OracleComp.run_interpret_lift,
    ProbComp.unifFin, OracleComp.interpret_query_eq_self]

@[simp] theorem runTwoRound_query (reply1 reply2 : List Bool → List Bool)
    (q : Unit × List Bool) (s : ℕ × List Bool) :
    runTwoRound reply1 reply2 (ProbOracleComp.query q) s =
      pure (twoRoundStep reply1 reply2 q.2 s) := by
  simp only [runTwoRound, ProbOracleComp.interpret_query]
  rfl

theorem eval_runTwoRound {α : Type} (reply1 reply2 : List Bool → List Bool)
    (prog : WordOracleComp Unit α) (s : ℕ × List Bool) :
    ProbComp.eval (runTwoRound reply1 reply2 prog s) =
      ProbOracleComp.runWith
        (fun q state => PMF.pure (twoRoundStep reply1 reply2 q.2 state))
        prog s := by
  simpa [runTwoRound, ProbOracleComp.runWith] using
    ProbOracleComp.eval_run_interpret
      (fun q state => pure (twoRoundStep reply1 reply2 q.2 state)) prog s

/-- Sample the honest prover's random masks and commitment seeds, returning `(bits, seeds)`. -/
noncomputable def sampleHonestCoins (s : ℕ) (φ : CNF ℕ) (w : List Bool) :
    ProbComp (List Bool × List (List Bool)) := do
  let m₀ ← BitString.sampleList φ.vars.length
  let m₁ ← BitString.sampleList φ.vars.length
  let m₂ ← BitString.sampleList φ.vars.length
  let seeds ← OracleComp.replicate (totalLen φ) (BitString.sampleList s)
  return (realBits φ w m₀ m₁ m₂, seeds)

/-- Honest first-round reply function for pre-sampled `(bits, seeds)`. -/
def honestReply1 (generator : List Bool → List Bool) (m : ℕ) (φ : CNF ℕ)
    (coins : List Bool × List (List Bool)) (r : List Bool) : List Bool :=
  proverReply1 generator m r (List.replicate (totalLen φ) true) coins.1 coins.2 []

/-- Honest second-round reply function for pre-sampled `(bits, seeds)`. -/
def honestReply2 (s : ℕ) (φ : CNF ℕ)
    (coins : List Bool × List (List Bool)) (ch : List Bool) : List Bool :=
  proverReply2 s φ ch coins.1 coins.2

/-- The honest GMW prover for a 3SAT formula `φ` and witness `w`. It samples its masks and
commitment seeds on the first query and answers the two rounds via `honestReply1` and
`honestReply2`. -/
noncomputable def gmwProver (generator : List Bool → List Bool) (s m : ℕ)
    (φ : CNF ℕ) (w : List Bool) : Prover Unit where
  State := (ℕ × List Bool) × Option (List Bool × List (List Bool))
  init := ((0, [false, false, false]), none)
  respond q state :=
    match state.2 with
    | none =>
      (ProbComp.eval (sampleHonestCoins s φ w)).map fun coins =>
        let step := twoRoundStep (honestReply1 generator m φ coins)
          (honestReply2 s φ coins) q.2 state.1
        (step.1, (step.2, some coins))
    | some coins =>
      let step := twoRoundStep (honestReply1 generator m φ coins)
        (honestReply2 s φ coins) q.2 state.1
      PMF.pure (step.1, (step.2, some coins))

theorem run_gmwProver_fst {α : Type} (generator : List Bool → List Bool) (s m : ℕ)
    (φ : CNF ℕ) (w : List Bool) (prog : WordOracleComp Unit α) :
    ((gmwProver generator s m φ w).run prog (gmwProver generator s m φ w).init).map Prod.fst =
      ProbComp.eval (do
        let coins ← sampleHonestCoins s φ w
        Prod.fst <$> runTwoRound (honestReply1 generator m φ coins)
          (honestReply2 s φ coins) prog (0, [false, false, false])) := by
  let P := gmwProver generator s m φ w
  let State' := (ℕ × List Bool) × (List Bool × List (List Bool))
  let relate : P.State → PMF State' := fun state =>
    match state.2 with
    | none => (ProbComp.eval (sampleHonestCoins s φ w)).map (state.1, ·)
    | some coins => PMF.pure (state.1, coins)
  let oracle' : Unit × List Bool → StateT State' PMF (List Bool) := fun q state =>
    let step := twoRoundStep (honestReply1 generator m φ state.2)
      (honestReply2 s φ state.2) q.2 state.1
    PMF.pure (step.1, (step.2, state.2))
  have hsim := ProbOracleComp.run_interpret_simulation P.respond oracle' relate
    (fun q state => by
      rcases state with ⟨st, _ | coins⟩ <;>
        simp [P, gmwProver, relate, oracle', PMF.bind_map, Function.comp_def])
    prog P.init
  have hmap := congrArg (PMF.map Prod.fst) hsim
  have hlhs :
      (((OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) P.respond)
        prog).run P.init).bind (fun (a, s') => (relate s').map (a, ·))).map Prod.fst =
      (P.run prog P.init).map Prod.fst := by
    simp only [Prover.run, PMF.map_bind, PMF.map_comp, Function.comp_def]
    have hconst : ∀ x : α × P.State, PMF.map (fun _ : State' => x.1) (relate x.2) = PMF.pure x.1 :=
      fun _ => PMF.map_const _ _
    simp only [hconst]
    rfl
  rw [hlhs] at hmap
  rw [hmap]
  simp only [P, gmwProver, relate, ProbComp.eval_bind, ProbComp.eval_map,
    PMF.map_bind, PMF.bind_map, Function.comp_def]
  congr 1
  funext coins
  have hstate := ProbOracleComp.run_interpret_map_state
    (fun q (st : ℕ × List Bool) =>
      PMF.pure (twoRoundStep (honestReply1 generator m φ coins)
        (honestReply2 s φ coins) q.2 st))
    oracle' (fun st => (st, coins))
    (fun q st => by simp [oracle'])
    prog (0, [false, false, false])
  have hstate_fst := congrArg (PMF.map Prod.fst) hstate
  simp only [PMF.map_comp, Function.comp_def] at hstate_fst
  rw [← hstate_fst, eval_runTwoRound]
  rfl

/-! ### GMW verifier: completeness and soundness -/

/-- The two-round GMW verifier for a problem reduced to `ThreeSAT` by `f`, at security parameter
`n` (using Naor commitments with seed length `n + 7`). -/
noncomputable def gmwVerifier {α : Type} (generator : List Bool → List Bool) (length : ℕ → ℕ)
    (f : α → CNF ℕ) (n : ℕ) (a : α) : WordOracleComp Unit Bool := do
  let φ := f a
  let s := n + 7
  let m := length s
  let K := totalLen φ
  let r ← ProbOracleComp.sample (BitString.sampleList m)
  let commitReply ← List.take (K * m) <$> ProbOracleComp.query ((), r)
  let ch ← ProbOracleComp.sample (BitString.sampleList 3)
  let openReply ← List.take (K * (s + 1)) <$> ProbOracleComp.query ((), ch)
  return verifyTranscript generator s m φ r commitReply ch openReply

theorem length_mem_support_replicate_sampleList {K s : ℕ} {seeds : List (List Bool)}
    (hseeds : seeds ∈ (ProbComp.eval (OracleComp.replicate K (BitString.sampleList s))).support) :
    seeds.length = K ∧ ∀ seed ∈ seeds, seed.length = s := by
  induction K generalizing seeds with
  | zero =>
    simp only [OracleComp.replicate_zero, ProbComp.eval_pure, PMF.support_pure,
      Set.mem_singleton_iff] at hseeds
    subst hseeds
    simp
  | succ K ih =>
    simp only [OracleComp.replicate_succ, ProbComp.eval_map, ProbComp.eval_bind,
      BitString.eval_sampleList, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hseeds
    obtain ⟨seed, hseed, rest, hrest, rfl⟩ := hseeds
    obtain ⟨hrest_len, hrest_mem⟩ := ih hrest
    refine ⟨by simp [hrest_len], ?_⟩
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact BitString.length_of_mem_support_uniformList hseed
    · exact hrest_mem u hu

/-- **Completeness of the GMW protocol.** When `ThreeSAT.verifier (f a, w) = true`, the honest
prover `gmwProver` makes `gmwVerifier` accept with probability `1`. -/
theorem acceptProb_gmwVerifier_gmwProver {α : Type} {generator : List Bool → List Bool}
    {length : ℕ → ℕ} (hlen : ∀ seed, (generator seed).length = length seed.length)
    (f : α → CNF ℕ) (n : ℕ) (a : α) {w : List Bool}
    (hw : ThreeSAT.verifier (f a, w) = true) :
    acceptProb (gmwVerifier generator length f n a)
      (gmwProver generator (n + 7) (length (n + 7)) (f a) w) = 1 := by
  let φ := f a
  let s := n + 7
  let m := length s
  let K := totalLen φ
  rw [acceptProb, run_gmwProver_fst]
  let prog : ProbComp Bool := do
    let coins ← sampleHonestCoins s φ w
    Prod.fst <$> runTwoRound (honestReply1 generator m φ coins)
      (honestReply2 s φ coins) (gmwVerifier generator length f n a) (0, [false, false, false])
  change ProbComp.eval prog true = 1
  have hfalse : ProbComp.eval prog false = 0 := by
    rw [PMF.apply_eq_zero_iff]
    intro hmem
    simp only [prog, ProbComp.eval_bind, ProbComp.eval_map, PMF.mem_support_bind_iff,
      PMF.mem_support_map_iff] at hmem
    obtain ⟨coins, hcoins, ⟨b, finalState⟩, hrun, hfst⟩ := hmem
    simp only at hfst
    subst hfst
    simp only [sampleHonestCoins, ProbComp.eval_bind, ProbComp.eval_pure,
      BitString.eval_sampleList, PMF.mem_support_bind_iff, PMF.support_pure,
      Set.mem_singleton_iff] at hcoins
    obtain ⟨m₀, _, m₁, _, m₂, _, seeds, hseeds, rfl⟩ := hcoins
    simp only [gmwVerifier, runTwoRound_bind, runTwoRound_sample, runTwoRound_map,
      runTwoRound_query, runTwoRound_pure, ProbComp.eval_bind, ProbComp.eval_map,
      ProbComp.eval_pure, BitString.eval_sampleList, PMF.mem_support_bind_iff,
      PMF.mem_support_map_iff, PMF.support_pure, Set.mem_singleton_iff] at hrun
    obtain ⟨⟨r, s₁⟩, ⟨r', _, hr1⟩, ⟨commitReply, s₂⟩, ⟨⟨q1, s₁'⟩, hq1, hmap1⟩,
      ⟨ch, s₃⟩, ⟨ch', hch, hch1⟩, ⟨openReply, s₄⟩, ⟨⟨q2, s₃'⟩, hq2, hmap2⟩, hfinal⟩ := hrun
    cases hr1
    cases hq1
    cases hmap1
    cases hch1
    cases hq2
    cases hmap2
    obtain ⟨hseeds_len, hseeds_mem⟩ := length_mem_support_replicate_sampleList hseeds
    have hch_len : ch.length = 3 := BitString.length_of_mem_support_uniformList hch
    have hch_row : BitString.listRow 3 0 ch = ch := by
      simp [BitString.listRow, List.take_left' hch_len]
    have hgen_len : ∀ seed ∈ seeds, (generator seed).length = m := by
      intro seed hseed
      rw [hlen, hseeds_mem seed hseed]
    have hr1_len :
        (honestReply1 generator m φ (realBits φ w m₀ m₁ m₂, seeds) r).length = K * m := by
      simpa [honestReply1, K, length_realBits] using
        length_proverReply1_true (r := r)
          (hseeds_len.trans (length_realBits φ w m₀ m₁ m₂).symm) hgen_len
    have hr2_len :
        (honestReply2 s φ (realBits φ w m₀ m₁ m₂, seeds) ch).length = K * (s + 1) := by
      simpa [honestReply2, K] using length_proverReply2 s φ seeds (length_realBits φ w m₀ m₁ m₂)
    have htake1 :
        List.take (K * m) (honestReply1 generator m φ (realBits φ w m₀ m₁ m₂, seeds) r) =
          honestReply1 generator m φ (realBits φ w m₀ m₁ m₂, seeds) r :=
      List.take_of_length_le hr1_len.le
    have htake2 :
        List.take (K * (s + 1)) (honestReply2 s φ (realBits φ w m₀ m₁ m₂, seeds) ch) =
          honestReply2 s φ (realBits φ w m₀ m₁ m₂, seeds) ch :=
      List.take_of_length_le hr2_len.le
    have hfalse_eq := congrArg Prod.fst hfinal
    dsimp only at hfalse_eq
    change false =
      verifyTranscript generator s m φ r
        (List.take (K * m) (honestReply1 generator m φ (realBits φ w m₀ m₁ m₂, seeds) r)) ch
        (List.take (K * (s + 1))
          (honestReply2 s φ (realBits φ w m₀ m₁ m₂, seeds) (BitString.listRow 3 0 ch))) at hfalse_eq
    rw [hch_row, htake1, htake2] at hfalse_eq
    have htrue := verifyTranscript_honest (m₀ := m₀) (m₁ := m₁) (m₂ := m₂)
      (r := r) (ch := ch) hw hseeds_len hseeds_mem hgen_len
    exact Bool.false_ne_true (hfalse_eq.trans htrue)
  have hsum := PMF.tsum_coe (ProbComp.eval prog)
  rw [tsum_bool, hfalse, zero_add] at hsum
  exact hsum

private theorem sum_le_of_subsingleton_support {ι : Type*} [Fintype ι]
    {f : ι → ℝ≥0∞} {c : ℝ≥0∞} (hle : ∀ i, f i ≤ c)
    (hsub : ∀ i₁ i₂, f i₁ ≠ 0 → f i₂ ≠ 0 → i₁ = i₂) :
    ∑ i, f i ≤ c := by
  classical
  by_cases hex : ∃ i₀, f i₀ ≠ 0
  · obtain ⟨i₀, hi₀⟩ := hex
    rw [Finset.sum_eq_single i₀
      (fun i _ hne => Decidable.byContradiction fun hfi => hne (hsub i i₀ hfi hi₀))
      (fun h => False.elim (h (Finset.mem_univ i₀)))]
    exact hle i₀
  · push Not at hex
    simp [hex]

/-- **Soundness of the GMW protocol.** When `f a ∉ ThreeSAT` and `3 * k + 1 ≤ length k` for all `k`,
no unbounded stateful prover `P` makes `gmwVerifier` accept with probability greater than
`1 / 3`. -/
theorem acceptProb_gmwVerifier_le {α : Type} {generator : List Bool → List Bool}
    {length : ℕ → ℕ} (hlen : ∀ seed, (generator seed).length = length seed.length)
    (hstretch : ∀ k, 3 * k + 1 ≤ length k)
    (f : α → CNF ℕ) (n : ℕ) (a : α) (hnot : f a ∉ ThreeSAT) (P : Prover Unit) :
    acceptProb (gmwVerifier generator length f n a) P ≤ 1 / 3 := by
  let φ := f a
  let s := n + 7
  let m := length s
  let K := totalLen φ
  let step3 (r commitReply ch : List Bool) : WordOracleComp Unit Bool :=
    (List.take (K * (s + 1)) <$> ProbOracleComp.query ((), ch)) >>= fun openReply =>
      pure (verifyTranscript generator s m φ r commitReply ch openReply)
  let step2 (r commitReply : List Bool) : WordOracleComp Unit Bool :=
    ProbOracleComp.sample (BitString.sampleList 3) >>= step3 r commitReply
  let step1 (r : List Bool) : WordOracleComp Unit Bool :=
    (List.take (K * m) <$> ProbOracleComp.query ((), r)) >>= step2 r
  have hverifier : gmwVerifier generator length f n a =
      (ProbOracleComp.sample (BitString.sampleList m) >>= step1) := rfl
  have hstep2_le : ∀ r commitReply state₁,
      NaorBinding generator s (BitString.listRow m 0 r) →
      ProbOracleComp.acceptProbWith P.respond (step2 r commitReply) state₁ ≤ 1 / 8 := by
    intro r commitReply state₁ hbind
    have heq :
        ProbOracleComp.acceptProbWith P.respond (step2 r commitReply) state₁ =
          ∑ x : BitString 3, (1 / 8 : ℝ≥0∞) *
            ProbOracleComp.acceptProbWith P.respond (step3 r commitReply (List.ofFn x)) state₁ := by
      rw [ProbOracleComp.acceptProbWith, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample,
        BitString.eval_sampleList, BitString.uniformList, PMF.bind_map, PMF.map_bind,
        PMF.bind_map, PMF.bind_apply, tsum_fintype]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Probability.PMF.uniformOfFintype_apply]
      simp [ProbOracleComp.acceptProbWith]
    rw [heq]
    refine sum_le_of_subsingleton_support
      (fun x => by
        calc (1 / 8 : ℝ≥0∞) *
              ProbOracleComp.acceptProbWith P.respond (step3 r commitReply (List.ofFn x)) state₁
          _ ≤ (1 / 8 : ℝ≥0∞) * 1 :=
              mul_le_mul_right (ProbOracleComp.acceptProbWith_le_one _ _ _) (1 / 8)
          _ = 1 / 8 := mul_one _)
      (fun x₁ x₂ hx₁ hx₂ => ?_)
    by_contra hne
    have hpos₁ :
        ProbOracleComp.acceptProbWith P.respond (step3 r commitReply (List.ofFn x₁)) state₁ ≠ 0 :=
      right_ne_zero_of_mul hx₁
    have hpos₂ :
        ProbOracleComp.acceptProbWith P.respond (step3 r commitReply (List.ofFn x₂)) state₁ ≠ 0 :=
      right_ne_zero_of_mul hx₂
    rw [ProbOracleComp.acceptProbWith, Ne, PMF.apply_eq_zero_iff,
      PMF.mem_support_map_iff, not_exists] at hpos₁ hpos₂
    push Not at hpos₁ hpos₂
    obtain ⟨⟨b₁, s₁'⟩, hmem₁, hfst₁⟩ := hpos₁
    obtain ⟨⟨b₂, s₂'⟩, hmem₂, hfst₂⟩ := hpos₂
    simp only [step3, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_map,
      ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure, PMF.mem_support_bind_iff,
      PMF.mem_support_map_iff, PMF.support_pure, Set.mem_singleton_iff] at hmem₁ hmem₂
    obtain ⟨⟨openReply₁, _⟩, ⟨⟨reply₁, _⟩, _, hmap₁⟩, heq₁⟩ := hmem₁
    obtain ⟨⟨openReply₂, _⟩, ⟨⟨reply₂, _⟩, _, hmap₂⟩, heq₂⟩ := hmem₂
    cases hmap₁
    cases hmap₂
    have hv₁ : verifyTranscript generator s m φ r commitReply (List.ofFn x₁)
        (List.take (K * (s + 1)) reply₁) = true := by
      have h := (congrArg Prod.fst heq₁).symm.trans hfst₁
      simpa using h
    have hv₂ : verifyTranscript generator s m φ r commitReply (List.ofFn x₂)
        (List.take (K * (s + 1)) reply₂) = true := by
      have h := (congrArg Prod.fst heq₂).symm.trans hfst₂
      simpa using h
    exact hnot (mem_ThreeSAT_of_verifyTranscript_ne hbind hne hv₁ hv₂)
  have hstep1_le : ∀ r, NaorBinding generator s (BitString.listRow m 0 r) →
      acceptProb (step1 r) P ≤ 1 / 8 := by
    intro r hbind
    rw [acceptProb_eq_acceptProbWith, ProbOracleComp.acceptProbWith_bind]
    calc
      ∑' x, ProbOracleComp.runWith P.respond (List.take (K * m) <$> ProbOracleComp.query ((), r))
          P.init x * ProbOracleComp.acceptProbWith P.respond (step2 r x.1) x.2
        ≤ ∑' x, ProbOracleComp.runWith P.respond
            (List.take (K * m) <$> ProbOracleComp.query ((), r)) P.init x * (1 / 8) :=
          ENNReal.tsum_le_tsum fun x => mul_le_mul_right (hstep2_le r x.1 x.2 hbind) _
      _ = (∑' x, ProbOracleComp.runWith P.respond
            (List.take (K * m) <$> ProbOracleComp.query ((), r)) P.init x) * (1 / 8) :=
          ENNReal.tsum_mul_right
      _ = 1 / 8 := by rw [PMF.tsum_coe, one_mul]
  rw [hverifier, acceptProb_sample_bind, BitString.eval_sampleList]
  have hterm_le : ∀ r,
      BitString.uniformList m r * acceptProb (step1 r) P ≤
        ({r | ¬ NaorBinding generator s r}.indicator (BitString.uniformList m) r) +
          BitString.uniformList m r * (1 / 8) := by
    intro r
    by_cases hbind : NaorBinding generator s r
    · rw [Set.indicator_of_notMem (by simp [hbind]), zero_add]
      by_cases hr : r ∈ (BitString.uniformList m).support
      · have hr_len : r.length = m := BitString.length_of_mem_support_uniformList hr
        have hrow : BitString.listRow m 0 r = r := by
          simp [BitString.listRow, List.take_left' hr_len]
        exact mul_le_mul_right (hstep1_le r (hrow.symm ▸ hbind)) _
      · rw [(PMF.apply_eq_zero_iff _ _).mpr hr, zero_mul, zero_mul]
    · rw [Set.indicator_of_mem (by simp [hbind])]
      calc
        BitString.uniformList m r * acceptProb (step1 r) P
          ≤ BitString.uniformList m r * 1 :=
            mul_le_mul_right (ProbOracleComp.acceptProbWith_le_one _ _ _) _
        _ = BitString.uniformList m r := mul_one _
        _ ≤ BitString.uniformList m r + BitString.uniformList m r * (1 / 8) := le_self_add
  calc
    ∑' r, BitString.uniformList m r * acceptProb (step1 r) P
      ≤ ∑' r, (({r | ¬ NaorBinding generator s r}.indicator (BitString.uniformList m) r) +
          BitString.uniformList m r * (1 / 8)) := ENNReal.tsum_le_tsum hterm_le
    _ = (∑' r, {r | ¬ NaorBinding generator s r}.indicator (BitString.uniformList m) r) +
          ∑' r, BitString.uniformList m r * (1 / 8) := ENNReal.tsum_add
    _ = naorBindingProb generator length s + 1 / 8 := by
        rw [← PMF.toOuterMeasure_apply, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
        rfl
    _ ≤ (1 / 2 : ℝ≥0∞) ^ (n + 8) + 1 / 8 := by
        gcongr
        exact naorBindingProb_le_of_three_mul_add_one hlen (n + 7) (hstretch (n + 7))
    _ ≤ 1 / 8 + 1 / 8 := by
        gcongr
        rw [one_div, ← ENNReal.inv_pow, one_div]
        exact ENNReal.inv_le_inv.mpr
          ((by norm_num : (8 : ℝ≥0∞) ≤ 2 ^ 3).trans
            (pow_le_pow_right' (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by omega)))
    _ ≤ 1 / 3 := by
        rw [← two_mul,
          ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num)),
          one_div, mul_comm (2 : ℝ≥0∞), mul_assoc]
        calc
          (8 : ℝ≥0∞)⁻¹ * (2 * 3) ≤ (8 : ℝ≥0∞)⁻¹ * 8 := by gcongr; norm_num
          _ = 1 := ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

/-! ### Polynomial-time certificates for protocol gadgets -/

@[fun_prop]
theorem computableTidilyInPolyTime_clauseLength {α : Type} {input : α ↪ List Bool}
    {c : α → Clause ℕ}
    (hc : ComputableTidilyInPolyTime c input (encList (encPair encNat encBool))) :
    ComputableTidilyInPolyTime (fun a => (c a).length) input encUnary :=
  (length (encPair encNat encBool)).comp hc

@[fun_prop]
theorem computableTidilyInPolyTime_cnfLength {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ}
    (hφ : ComputableTidilyInPolyTime φ input encCNF) :
    ComputableTidilyInPolyTime (fun a => (φ a).length) input encUnary := by
  rw [encCNF] at hφ
  exact (length (encList (encPair encNat encBool))).comp hφ

theorem computableTidilyInPolyTime_clauseLitVar (i : ℕ) {α : Type} {input : α ↪ List Bool}
    {c : α → Clause ℕ}
    (hc : ComputableTidilyInPolyTime c input (encList (encPair encNat encBool))) :
    ComputableTidilyInPolyTime (fun a => ((c a).getD i (0, false)).1) input encNat := by
  have hget : ComputableTidilyInPolyTime (fun a => (c a).getD i (0, false))
      input (encPair encNat encBool) :=
    (listGetD (0, false)).comp (hc.prod (const i))
  exact (fst encNat encBool).comp hget

theorem computableTidilyInPolyTime_clauseLitPol (i : ℕ) {α : Type} {input : α ↪ List Bool}
    {c : α → Clause ℕ}
    (hc : ComputableTidilyInPolyTime c input (encList (encPair encNat encBool))) :
    ComputableTidilyInPolyTime (fun a => ((c a).getD i (0, false)).2) input encBool := by
  have hget : ComputableTidilyInPolyTime (fun a => (c a).getD i (0, false))
      input (encPair encNat encBool) :=
    (listGetD (0, false)).comp (hc.prod (const i))
  exact (snd encNat encBool).comp hget

@[fun_prop]
theorem computableTidilyInPolyTime_varsLength {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ}
    (hφ : ComputableTidilyInPolyTime φ input encCNF) :
    ComputableTidilyInPolyTime (fun a => (φ a).vars.length) input encUnary :=
  (length encNat).comp (SAT.computableTidilyInPolyTime_vars.comp hφ)

@[fun_prop]
theorem computableTidilyInPolyTime_bit0Of8 {α : Type} {input : α ↪ List Bool} {t : α → ℕ}
    (ht : ComputableTidilyInPolyTime t input encUnary) :
    ComputableTidilyInPolyTime (fun a => bit0Of8 (t a)) input encBool := by
  dsimp only [bit0Of8]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_bit1Of8 {α : Type} {input : α ↪ List Bool} {t : α → ℕ}
    (ht : ComputableTidilyInPolyTime t input encUnary) :
    ComputableTidilyInPolyTime (fun a => bit1Of8 (t a)) input encBool := by
  dsimp only [bit1Of8]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_bit2Of8 {α : Type} {input : α ↪ List Bool} {t : α → ℕ}
    (ht : ComputableTidilyInPolyTime t input encUnary) :
    ComputableTidilyInPolyTime (fun a => bit2Of8 (t a)) input encBool := by
  dsimp only [bit2Of8]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_activeIdx {α : Type} {input : α ↪ List Bool}
    {b₀ b₁ b₂ : α → Bool}
    (hb₀ : ComputableTidilyInPolyTime b₀ input encBool)
    (hb₁ : ComputableTidilyInPolyTime b₁ input encBool)
    (hb₂ : ComputableTidilyInPolyTime b₂ input encBool) :
    ComputableTidilyInPolyTime (fun a => activeIdx (b₀ a) (b₁ a) (b₂ a)) input encUnary := by
  dsimp only [activeIdx]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_clauseEvalBits {α : Type} {input : α ↪ List Bool}
    {c : α → Clause ℕ} {b₀ b₁ b₂ : α → Bool}
    (hc : ComputableTidilyInPolyTime c input (encList (encPair encNat encBool)))
    (hb₀ : ComputableTidilyInPolyTime b₀ input encBool)
    (hb₁ : ComputableTidilyInPolyTime b₁ input encBool)
    (hb₂ : ComputableTidilyInPolyTime b₂ input encBool) :
    ComputableTidilyInPolyTime (fun a => clauseEvalBits (c a) (b₀ a) (b₁ a) (b₂ a))
      input encBool := by
  have hp0 := computableTidilyInPolyTime_clauseLitPol 0 hc
  have hp1 := computableTidilyInPolyTime_clauseLitPol 1 hc
  have hp2 := computableTidilyInPolyTime_clauseLitPol 2 hc
  dsimp only [clauseEvalBits]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_varBit {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {vec : α → List Bool} {v : α → ℕ}
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hvec : ComputableTidilyInPolyTime vec input encBits)
    (hv : ComputableTidilyInPolyTime v input encNat) :
    ComputableTidilyInPolyTime (fun a => varBit (φ a) (vec a) (v a)) input encBool := by
  dsimp only [varBit]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_clauseTableRow {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {m : α → List Bool} {c : α → Clause ℕ}
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hm : ComputableTidilyInPolyTime m input encBits)
    (hc : ComputableTidilyInPolyTime c input (encList (encPair encNat encBool))) :
    ComputableTidilyInPolyTime (fun a => clauseTableRow (φ a) (m a) (c a)) input encBits := by
  have hv0 : ComputableTidilyInPolyTime (fun p : α × ℕ => ((c p.1).getD 0 (0, false)).1)
      (encPair input encUnary) encNat :=
    computableTidilyInPolyTime_clauseLitVar 0 (hc.comp (fst input encUnary))
  have hv1 : ComputableTidilyInPolyTime (fun p : α × ℕ => ((c p.1).getD 1 (0, false)).1)
      (encPair input encUnary) encNat :=
    computableTidilyInPolyTime_clauseLitVar 1 (hc.comp (fst input encUnary))
  have hv2 : ComputableTidilyInPolyTime (fun p : α × ℕ => ((c p.1).getD 2 (0, false)).1)
      (encPair input encUnary) encNat :=
    computableTidilyInPolyTime_clauseLitVar 2 (hc.comp (fst input encUnary))
  dsimp only [clauseTableRow]
  exact mapToBitsWithInput (range.comp (const 8)) (by fun_prop)

@[fun_prop]
theorem computableTidilyInPolyTime_clauseActiveRow {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {v : α → List Bool} {c : α → Clause ℕ}
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hv : ComputableTidilyInPolyTime v input encBits)
    (hc : ComputableTidilyInPolyTime c input (encList (encPair encNat encBool))) :
    ComputableTidilyInPolyTime (fun a => clauseActiveRow (φ a) (v a) (c a)) input encBits := by
  have hv0 : ComputableTidilyInPolyTime (fun p : α × ℕ => ((c p.1).getD 0 (0, false)).1)
      (encPair input encUnary) encNat :=
    computableTidilyInPolyTime_clauseLitVar 0 (hc.comp (fst input encUnary))
  have hv1 : ComputableTidilyInPolyTime (fun p : α × ℕ => ((c p.1).getD 1 (0, false)).1)
      (encPair input encUnary) encNat :=
    computableTidilyInPolyTime_clauseLitVar 1 (hc.comp (fst input encUnary))
  have hv2 : ComputableTidilyInPolyTime (fun p : α × ℕ => ((c p.1).getD 2 (0, false)).1)
      (encPair input encUnary) encNat :=
    computableTidilyInPolyTime_clauseLitVar 2 (hc.comp (fst input encUnary))
  have heq (x y : ℕ) : decide (x = y) = (x == y) := Bool.eq_iff_iff.mpr (by simp)
  dsimp only [clauseActiveRow]
  simp only [heq]
  exact mapToBitsWithInput (range.comp (const 8)) (by fun_prop)

@[fun_prop]
theorem computableTidilyInPolyTime_tableBits {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {m : α → List Bool}
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hm : ComputableTidilyInPolyTime m input encBits) :
    ComputableTidilyInPolyTime (fun a => tableBits (φ a) (m a)) input encBits := by
  dsimp only [tableBits]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_activeTableFlags {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {v : α → List Bool}
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hv : ComputableTidilyInPolyTime v input encBits) :
    ComputableTidilyInPolyTime (fun a => activeTableFlags (φ a) (v a)) input encBits := by
  dsimp only [activeTableFlags]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_copyLen {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} (hφ : ComputableTidilyInPolyTime φ input encCNF) :
    ComputableTidilyInPolyTime (fun a => copyLen (φ a)) input encUnary := by
  dsimp only [copyLen]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_totalLen {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} (hφ : ComputableTidilyInPolyTime φ input encCNF) :
    ComputableTidilyInPolyTime (fun a => totalLen (φ a)) input encUnary := by
  dsimp only [totalLen]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_mPart {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {copy : α → List Bool}
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hcopy : ComputableTidilyInPolyTime copy input encBits) :
    ComputableTidilyInPolyTime (fun a => mPart (φ a) (copy a)) input encBits := by
  dsimp only [mPart]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_vPart {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {copy : α → List Bool}
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hcopy : ComputableTidilyInPolyTime copy input encBits) :
    ComputableTidilyInPolyTime (fun a => vPart (φ a) (copy a)) input encBits := by
  dsimp only [vPart]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_tablePart {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {copy : α → List Bool}
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hcopy : ComputableTidilyInPolyTime copy input encBits) :
    ComputableTidilyInPolyTime (fun a => tablePart (φ a) (copy a)) input encBits := by
  dsimp only [tablePart]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_realCopyBits {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {w m : α → List Bool}
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hw : ComputableTidilyInPolyTime w input encBits)
    (hm : ComputableTidilyInPolyTime m input encBits) :
    ComputableTidilyInPolyTime (fun a => realCopyBits (φ a) (w a) (m a)) input encBits := by
  dsimp only [realCopyBits]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_simCopyBits {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {b : α → Bool} {rand : α → List Bool}
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hb : ComputableTidilyInPolyTime b input encBool)
    (hrand : ComputableTidilyInPolyTime rand input encBits) :
    ComputableTidilyInPolyTime (fun a => simCopyBits (φ a) (b a) (rand a)) input encBits := by
  dsimp only [simCopyBits]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_copyOpenFlags {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {b : α → Bool} {copy : α → List Bool}
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hb : ComputableTidilyInPolyTime b input encBool)
    (hcopy : ComputableTidilyInPolyTime copy input encBits) :
    ComputableTidilyInPolyTime (fun a => copyOpenFlags (φ a) (b a) (copy a)) input encBits := by
  dsimp only [copyOpenFlags]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_verifyCopyBits {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {b : α → Bool} {copy : α → List Bool}
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hb : ComputableTidilyInPolyTime b input encBool)
    (hcopy : ComputableTidilyInPolyTime copy input encBits) :
    ComputableTidilyInPolyTime (fun a => verifyCopyBits (φ a) (b a) (copy a)) input encBool := by
  dsimp only [verifyCopyBits]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_copy0 {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {bits : α → List Bool}
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hbits : ComputableTidilyInPolyTime bits input encBits) :
    ComputableTidilyInPolyTime (fun a => copy0 (φ a) (bits a)) input encBits := by
  dsimp only [copy0]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_copy1 {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {bits : α → List Bool}
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hbits : ComputableTidilyInPolyTime bits input encBits) :
    ComputableTidilyInPolyTime (fun a => copy1 (φ a) (bits a)) input encBits := by
  dsimp only [copy1]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_copy2 {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {bits : α → List Bool}
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hbits : ComputableTidilyInPolyTime bits input encBits) :
    ComputableTidilyInPolyTime (fun a => copy2 (φ a) (bits a)) input encBits := by
  dsimp only [copy2]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_realBits {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {w m₀ m₁ m₂ : α → List Bool}
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hw : ComputableTidilyInPolyTime w input encBits)
    (hm₀ : ComputableTidilyInPolyTime m₀ input encBits)
    (hm₁ : ComputableTidilyInPolyTime m₁ input encBits)
    (hm₂ : ComputableTidilyInPolyTime m₂ input encBits) :
    ComputableTidilyInPolyTime (fun a => realBits (φ a) (w a) (m₀ a) (m₁ a) (m₂ a))
      input encBits := by
  dsimp only [realBits]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_simBits {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {ch r₀ r₁ r₂ : α → List Bool}
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hch : ComputableTidilyInPolyTime ch input encBits)
    (hr₀ : ComputableTidilyInPolyTime r₀ input encBits)
    (hr₁ : ComputableTidilyInPolyTime r₁ input encBits)
    (hr₂ : ComputableTidilyInPolyTime r₂ input encBits) :
    ComputableTidilyInPolyTime (fun a => simBits (φ a) (ch a) (r₀ a) (r₁ a) (r₂ a))
      input encBits := by
  dsimp only [simBits]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_allOpenFlags {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {ch bits : α → List Bool}
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hch : ComputableTidilyInPolyTime ch input encBits)
    (hbits : ComputableTidilyInPolyTime bits input encBits) :
    ComputableTidilyInPolyTime (fun a => allOpenFlags (φ a) (ch a) (bits a))
      input encBits := by
  dsimp only [allOpenFlags]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_proverReply1 {α : Type} {input : α ↪ List Bool}
    {generator : List Bool → List Bool} {m : α → ℕ}
    {r openFlags bits : α → List Bool} {seeds pads : α → List (List Bool)}
    (hg : ComputableTidilyInPolyTime generator encBits encBits)
    (hm : ComputableTidilyInPolyTime m input encUnary)
    (hr : ComputableTidilyInPolyTime r input encBits)
    (hopen : ComputableTidilyInPolyTime openFlags input encBits)
    (hbits : ComputableTidilyInPolyTime bits input encBits)
    (hseeds : ComputableTidilyInPolyTime seeds input (encList encBits))
    (hpads : ComputableTidilyInPolyTime pads input (encList encBits)) :
    ComputableTidilyInPolyTime
      (fun a => proverReply1 generator (m a) (r a) (openFlags a) (bits a) (seeds a) (pads a))
      input encBits := by
  dsimp only [proverReply1]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_proverReply2 {α : Type} {input : α ↪ List Bool}
    {s : α → ℕ} {φ : α → CNF ℕ} {ch bits : α → List Bool} {seeds : α → List (List Bool)}
    (hs : ComputableTidilyInPolyTime s input encUnary)
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hch : ComputableTidilyInPolyTime ch input encBits)
    (hbits : ComputableTidilyInPolyTime bits input encBits)
    (hseeds : ComputableTidilyInPolyTime seeds input (encList encBits)) :
    ComputableTidilyInPolyTime
      (fun a => proverReply2 (s a) (φ a) (ch a) (bits a) (seeds a))
      input encBits := by
  dsimp only [proverReply2]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_verifyCommitments {α : Type} {input : α ↪ List Bool}
    {generator : List Bool → List Bool} {s m : α → ℕ} {φ : α → CNF ℕ}
    {r flags commitReply openedBits openSeedsFlat : α → List Bool}
    (hg : ComputableTidilyInPolyTime generator encBits encBits)
    (hs : ComputableTidilyInPolyTime s input encUnary)
    (hm : ComputableTidilyInPolyTime m input encUnary)
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hr : ComputableTidilyInPolyTime r input encBits)
    (hflags : ComputableTidilyInPolyTime flags input encBits)
    (hcommit : ComputableTidilyInPolyTime commitReply input encBits)
    (hopened : ComputableTidilyInPolyTime openedBits input encBits)
    (hseeds : ComputableTidilyInPolyTime openSeedsFlat input encBits) :
    ComputableTidilyInPolyTime
      (fun a => verifyCommitments generator (s a) (m a) (φ a) (r a) (flags a)
        (commitReply a) (openedBits a) (openSeedsFlat a))
      input encBool := by
  dsimp only [verifyCommitments]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_verifyTranscript {α : Type} {input : α ↪ List Bool}
    {generator : List Bool → List Bool} {s m : α → ℕ} {φ : α → CNF ℕ}
    {r commitReply ch openReply : α → List Bool}
    (hg : ComputableTidilyInPolyTime generator encBits encBits)
    (hs : ComputableTidilyInPolyTime s input encUnary)
    (hm : ComputableTidilyInPolyTime m input encUnary)
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hr : ComputableTidilyInPolyTime r input encBits)
    (hcommit : ComputableTidilyInPolyTime commitReply input encBits)
    (hch : ComputableTidilyInPolyTime ch input encBits)
    (hopen : ComputableTidilyInPolyTime openReply input encBits) :
    ComputableTidilyInPolyTime
      (fun a => verifyTranscript generator (s a) (m a) (φ a) (r a)
        (commitReply a) (ch a) (openReply a))
      input encBool := by
  dsimp only [verifyTranscript]
  fun_prop

@[fun_prop]
theorem isOraclePPTOn_gmwVerifier {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ} {f : α → CNF ℕ}
    (hg : ComputableTidilyInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length)
    (hf : ComputableTidilyInPolyTime f enc encCNF) :
    IsOraclePPTOn (encPair encUnary enc) encBool
      (fun p : ℕ × α => gmwVerifier generator length f p.1 p.2) := by
  have hlength : ComputableTidilyInPolyTime length encUnary encUnary := by
    have h : length = fun n => (generator (List.replicate n true)).length := by
      funext n
      rw [hlen, List.length_replicate]
    rw [h]
    fun_prop
  dsimp only [gmwVerifier]
  fun_prop

/-- Extract the payload of the first successful simulation attempt (`true :: out`), or `[]` if all
attempts failed (`[]`). -/
def firstSuccess (attempts : List (List Bool)) : List Bool :=
  ((attempts.filter (fun w => w.headD false)).headD []).tail

@[fun_prop]
theorem computableTidilyInPolyTime_firstSuccess {α : Type} {input : α ↪ List Bool}
    {attempts : α → List (List Bool)}
    (ha : ComputableTidilyInPolyTime attempts input (encList encBits)) :
    ComputableTidilyInPolyTime (fun a => firstSuccess (attempts a)) input encBits := by
  dsimp only [firstSuccess]
  fun_prop

theorem isPPTOn_runTwoRound {α Caller : Type} {enc : α ↪ List Bool} {input : Caller ↪ List Bool}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    {prepare : Caller → ℕ × α × List Bool}
    {reply1 reply2 : Caller × List Bool → List Bool}
    {bound : Caller → ℕ}
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun p => Vstar p.1 p.2.1 p.2.2))
    (hprep : ComputableTidilyInPolyTime prepare input (encPair encUnary (encPair enc encBits)))
    (hr1 : ComputableTidilyInPolyTime reply1 (encPair input encBits) encBits)
    (hr2 : ComputableTidilyInPolyTime reply2 (encPair input encBits) encBits)
    (hbound : ComputableTidilyInPolyTime bound input encUnary)
    (hle1 : ∀ c q, (reply1 (c, q)).length ≤ bound c)
    (hle2 : ∀ c q, (reply2 (c, q)).length ≤ bound c) :
    IsPPTOn input (encPair encBits (encPair encUnary encBits))
      (fun c => runTwoRound (fun q => reply1 (c, q)) (fun q => reply2 (c, q))
        (Vstar (prepare c).1 (prepare c).2.1 (prepare c).2.2) (0, [false, false, false])) := by
  let stateEncoding : ℕ × List Bool ↪ List Bool := encPair encUnary encBits
  have hlen_state : ∀ s : ℕ × List Bool, s.1 ≤ 2 → s.2.length = 3 →
      (stateEncoding s).length ≤ 9 := by
    intro s hs1 hs2
    simp only [stateEncoding, length_encPair, encUnary_apply, List.length_replicate,
      encBits_apply, hs2]
    omega
  refine hV.run_interpret_preprocess (stateEncoding := stateEncoding)
    (handler := fun c q s =>
      pure (twoRoundStep (fun x => reply1 (c, x)) (fun x => reply2 (c, x)) q.2 s))
    (prepare := prepare)
    (initial := fun _ => (0, [false, false, false]))
    (resources := fun c _ => bound c + 9)
    hprep
    (by dsimp only [twoRoundStep, stateEncoding]; fun_prop)
    (by dsimp only [stateEncoding]; fun_prop)
    (fun _ s => s.1 ≤ 2 ∧ s.2.length = 3)
    (fun _ => ⟨by omega, rfl⟩)
    (by fun_prop)
    (fun c request state hstate result hresult => ?_)
  simp only [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hresult
  subst hresult
  dsimp only [twoRoundStep]
  split_ifs with h0 h1
  · dsimp only
    refine ⟨⟨by omega, hstate.2⟩, (hle1 c request.2).trans (by omega), ?_⟩
    exact (hlen_state (1, state.2) (by omega) hstate.2).trans (by omega)
  · dsimp only
    refine ⟨⟨by omega, BitString.length_listRow 3 0 request.2⟩,
      (hle2 c _).trans (by omega), ?_⟩
    exact (hlen_state (2, BitString.listRow 3 0 request.2)
      (by omega) (BitString.length_listRow 3 0 request.2)).trans (by omega)
  · dsimp only
    refine ⟨hstate, by simp, ?_⟩
    exact (hlen_state state hstate.1 hstate.2).trans (by omega)

/-! ### Step 1: Replacing the verifier's challenge in `runTwoRound` by a random guess -/

theorem runTwoRound_query_inl {α β : Type} (reply1 reply2 : List Bool → List Bool)
    (n : ℕ) (k : Fin (n + 1) → WordOracleComp Unit α) (s : ℕ × List Bool)
    (f : α × (ℕ × List Bool) → β) :
    f <$> runTwoRound reply1 reply2 (OracleComp.query (Sum.inl n) >>= k) s =
      (ProbComp.unifFin n >>= fun u => f <$> runTwoRound reply1 reply2 (k u) s) := by
  simp only [runTwoRound, OracleComp.interpret_bind, OracleComp.interpret_query,
    ProbOracleComp.handler, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]

theorem runTwoRound_query_inr {α β : Type} (reply1 reply2 : List Bool → List Bool)
    (q : Unit × List Bool) (k : List Bool → WordOracleComp Unit α) (s : ℕ × List Bool)
    (f : α × (ℕ × List Bool) → β) :
    f <$> runTwoRound reply1 reply2 (OracleComp.query (Sum.inr q) >>= k) s =
      let step := twoRoundStep reply1 reply2 q.2 s
      f <$> runTwoRound reply1 reply2 (k step.1) step.2 := by
  simp only [runTwoRound, OracleComp.interpret_bind, OracleComp.interpret_query,
    ProbOracleComp.handler, StateT.run_bind]
  rfl

theorem eval_runTwoRound_of_two_le (r1 r2 : List Bool → List Bool) (ch_guess : List Bool)
    (prog : WordOracleComp Unit (List Bool)) {s : ℕ × List Bool}
    (hs1 : 2 ≤ s.1) (hs2 : (s.2 == ch_guess) = false) :
    ProbComp.eval ((fun p => if p.2.2 == ch_guess then true :: p.1 else []) <$>
      runTwoRound r1 r2 prog s) = PMF.pure [] := by
  induction prog using PFunctor.FreeM.induction generalizing s with
  | pure x =>
    simp [beq_eq_false_iff_ne.mp hs2]
  | lift_bind q k ih =>
    cases q with
    | inl n =>
      change ProbComp.eval (_ <$> runTwoRound r1 r2 (OracleComp.query (Sum.inl n) >>= k) s) = _
      rw [runTwoRound_query_inl, ProbComp.eval_bind]
      have hconst : (fun u => ProbComp.eval
          ((fun p => if p.2.2 == ch_guess then true :: p.1 else []) <$>
            runTwoRound r1 r2 (k u) s)) = fun _ => PMF.pure [] := by
        funext u
        exact ih u hs1 hs2
      rw [hconst, PMF.bind_const]
    | inr q =>
      change ProbComp.eval (_ <$> runTwoRound r1 r2 (OracleComp.query (Sum.inr q) >>= k) s) = _
      rw [runTwoRound_query_inr]
      have h0 : (s.1 == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
      have h1 : (s.1 == 1) = false := beq_eq_false_iff_ne.mpr (by omega)
      have hstep : twoRoundStep r1 r2 q.2 s = ([], s) := by
        simp [twoRoundStep, h0, h1]
      rw [hstep]
      exact ih [] hs1 hs2

theorem eval_runTwoRound_guess (r1 r2 : List Bool → List Bool) (ch_guess : List Bool)
    (prog : WordOracleComp Unit (List Bool)) (s : ℕ × List Bool) :
    ProbComp.eval ((fun p => if p.2.2 == ch_guess then true :: p.1 else []) <$>
      runTwoRound r1 r2 prog s) =
    ProbComp.eval ((fun p => if p.2.2 == ch_guess then true :: p.1 else []) <$>
      runTwoRound r1 (fun _ => r2 ch_guess) prog s) := by
  induction prog using PFunctor.FreeM.induction generalizing s with
  | pure x => rfl
  | lift_bind q k ih =>
    cases q with
    | inl n =>
      change ProbComp.eval (_ <$> runTwoRound r1 r2 (OracleComp.query (Sum.inl n) >>= k) s) =
        ProbComp.eval (_ <$> runTwoRound r1 _ (OracleComp.query (Sum.inl n) >>= k) s)
      rw [runTwoRound_query_inl, runTwoRound_query_inl, ProbComp.eval_bind, ProbComp.eval_bind]
      congr 1
      funext u
      exact ih u s
    | inr q =>
      change ProbComp.eval (_ <$> runTwoRound r1 r2 (OracleComp.query (Sum.inr q) >>= k) s) =
        ProbComp.eval (_ <$> runTwoRound r1 _ (OracleComp.query (Sum.inr q) >>= k) s)
      rw [runTwoRound_query_inr, runTwoRound_query_inr]
      dsimp only [twoRoundStep]
      split_ifs with h0 h1
      · exact ih (r1 q.2) (1, s.2)
      · by_cases hch : (BitString.listRow 3 0 q.2 == ch_guess) = true
        · have heq : BitString.listRow 3 0 q.2 = ch_guess := beq_iff_eq.mp hch
          rw [heq]
          exact ih (r2 ch_guess) (2, ch_guess)
        · have hfalse : (BitString.listRow 3 0 q.2 == ch_guess) = false :=
            Bool.eq_false_iff.mpr hch
          rw [eval_runTwoRound_of_two_le r1 r2 ch_guess (k (r2 (BitString.listRow 3 0 q.2)))
              (le_refl 2) hfalse,
            eval_runTwoRound_of_two_le r1 (fun _ => r2 ch_guess) ch_guess (k (r2 ch_guess))
              (le_refl 2) hfalse]
      · exact ih [] s

theorem length_snd_mem_support_runTwoRound {α : Type} (r1 r2 : List Bool → List Bool)
    (prog : WordOracleComp Unit α) {s : ℕ × List Bool} (hs : s.2.length = 3)
    {p : α × (ℕ × List Bool)}
    (hp : p ∈ (ProbComp.eval (runTwoRound r1 r2 prog s)).support) :
    p.2.2.length = 3 := by
  induction prog using PFunctor.FreeM.induction generalizing s with
  | pure x =>
    simp only [runTwoRound_pure, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hp
    rw [hp]
    exact hs
  | lift_bind q k ih =>
    cases q with
    | inl n =>
      have hq := runTwoRound_query_inl r1 r2 n k s id
      simp only [id_map] at hq
      change p ∈ (ProbComp.eval (runTwoRound r1 r2 (OracleComp.query (Sum.inl n) >>= k) s)).support
        at hp
      rw [hq, ProbComp.eval_bind, PMF.mem_support_bind_iff] at hp
      obtain ⟨u, _, hu⟩ := hp
      exact ih u hs hu
    | inr q =>
      have hq := runTwoRound_query_inr r1 r2 q k s id
      simp only [id_map] at hq
      change p ∈ (ProbComp.eval (runTwoRound r1 r2 (OracleComp.query (Sum.inr q) >>= k) s)).support
        at hp
      rw [hq] at hp
      have hstep : (twoRoundStep r1 r2 q.2 s).2.2.length = 3 := by
        dsimp only [twoRoundStep]
        split_ifs <;> simp [hs]
      exact ih _ hstep hp

theorem uniformList_map_guess_eq {ch₀ : List Bool} (hch₀ : ch₀.length = 3) (out : List Bool) :
    (BitString.uniformList 3).map (fun ch_guess => if ch₀ == ch_guess then true :: out else []) =
      (BitString.uniformList 3).map
        (fun ch_guess => if [false, false, false] == ch_guess then true :: out else []) := by
  conv_lhs => rw [← uniformList_map_listXor 3 ch₀]
  rw [PMF.map_comp]
  simp only [PMF.map]
  refine Probability.PMF.bind_congr_on_support (BitString.uniformList 3) _ _ fun u hu => ?_
  have hu_len : u.length = 3 := BitString.length_of_mem_support_uniformList hu
  have hzero : BitString.ofList 3 [false, false, false] = 0 := by
    funext i
    fin_cases i <;> rfl
  have hiff : (ch₀ = BitString.listXor 3 [u, ch₀]) ↔ ([false, false, false] = u) := by
    constructor
    · intro h
      have h1 := congrArg (fun l => BitString.ofList 3 l + BitString.ofList 3 ch₀) h
      simp only [ofList_listXor_pair 3 u ch₀, add_assoc, BitString.add_self, add_zero] at h1
      have h2 := congrArg List.ofFn h1
      rw [← hzero, BitString.ofFn_ofList (by simp), BitString.ofFn_ofList hu_len] at h2
      exact h2
    · rintro rfl
      have h1 : BitString.ofList 3 (BitString.listXor 3 [[false, false, false], ch₀]) =
          BitString.ofList 3 ch₀ := by
        rw [ofList_listXor_pair, hzero, zero_add]
      have h2 := congrArg List.ofFn h1
      rw [BitString.ofFn_ofList (by simp), BitString.ofFn_ofList hch₀] at h2
      exact h2.symm
  simp [Function.comp_def, hiff]

@[simp] theorem firstSuccess_nil : firstSuccess [] = [] := rfl

@[simp] theorem firstSuccess_cons (x : List Bool) (xs : List (List Bool)) :
    firstSuccess (x :: xs) = if x.headD false then x.tail else firstSuccess xs := by
  simp only [firstSuccess, List.filter_cons]
  cases x.headD false <;> rfl

/-- Single-attempt hybrid 0: guess a 3-bit challenge `ch_guess`, sample honest prover coins
`(bits, seeds)`, run `prog` against `honestReply1` and `fun _ => honestReply2 ... ch_guess`, and
return `true :: out` when the verifier's challenge equals `ch_guess`, or `[]` otherwise. -/
noncomputable def game0 (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ) (w : List Bool)
    (prog : WordOracleComp Unit (List Bool)) : ProbComp (List Bool) := do
  let ch_guess ← BitString.sampleList 3
  let coins ← sampleHonestCoins s φ w
  let p ← runTwoRound
    (honestReply1 generator m φ coins)
    (fun _ => honestReply2 s φ coins ch_guess)
    prog (0, [false, false, false])
  return if p.2.2 == ch_guess then true :: p.1 else []

/-- Tag `out` with `true :: out` when a uniform 3-bit challenge equals `[false, false, false]`,
and return `[]` otherwise. -/
noncomputable def bernoulliAttempt (out : List Bool) : PMF (List Bool) :=
  (BitString.uniformList 3).map
    (fun ch_guess => if [false, false, false] == ch_guess then true :: out else [])

/-- Choose `p` when a uniform 3-bit challenge equals `[false, false, false]`, and `q` otherwise. -/
noncomputable def mixThree {α : Type} (p q : PMF α) : PMF α :=
  (BitString.uniformList 3).bind
    (fun ch_guess => if [false, false, false] == ch_guess then p else q)

/-- Distribution of `firstSuccess` after `k` independent attempts from `μ.bind bernoulliAttempt`. -/
noncomputable def repeatAttempt (μ : PMF (List Bool)) : ℕ → PMF (List Bool)
  | 0 => PMF.pure []
  | k + 1 => mixThree μ (repeatAttempt μ k)

theorem eval_game0_eq_bind_bernoulliAttempt (generator : List Bool → List Bool) (s m : ℕ)
    (φ : CNF ℕ) (w : List Bool) (prog : WordOracleComp Unit (List Bool)) :
    ProbComp.eval (game0 generator s m φ w prog) =
      (((gmwProver generator s m φ w).run prog
        (gmwProver generator s m φ w).init).map Prod.fst).bind bernoulliAttempt := by
  rw [run_gmwProver_fst]
  have hguess (ch_guess : List Bool) (coins : List Bool × List (List Bool)) :
      ProbComp.eval (do
        let p ← runTwoRound
          (honestReply1 generator m φ coins)
          (fun _ => honestReply2 s φ coins ch_guess)
          prog (0, [false, false, false])
        return if p.2.2 == ch_guess then true :: p.1 else []) =
      ProbComp.eval (do
        let p ← runTwoRound
          (honestReply1 generator m φ coins)
          (honestReply2 s φ coins)
          prog (0, [false, false, false])
        return if p.2.2 == ch_guess then true :: p.1 else []) := by
    simpa only [ bind_pure_comp] using
      (eval_runTwoRound_guess
        (honestReply1 generator m φ coins)
        (honestReply2 s φ coins)
        ch_guess prog (0, [false, false, false])).symm
  simp only [game0, ProbComp.eval_bind, BitString.eval_sampleList, hguess]
  simp only [ProbComp.eval_map, ProbComp.eval_pure, PMF.bind_bind,
    PMF.bind_map, Function.comp_def]
  rw [PMF.bind_comm]
  refine Probability.PMF.bind_congr_on_support _ _ _ fun coins _ => ?_
  rw [PMF.bind_comm]
  refine Probability.PMF.bind_congr_on_support _ _ _ fun p hp => ?_
  have hlen : p.2.2.length = 3 := length_snd_mem_support_runTwoRound _ _ prog rfl hp
  simpa only [bernoulliAttempt, PMF.map, Function.comp_def] using
    uniformList_map_guess_eq hlen p.1

theorem bind_bernoulliAttempt_ite (μ ν : PMF (List Bool)) :
    (μ.bind bernoulliAttempt).bind
      (fun x => if x.headD false then PMF.pure x.tail else ν) = mixThree μ ν := by
  simp only [bernoulliAttempt, mixThree, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  rw [PMF.bind_comm]
  congr 1
  funext ch_guess
  by_cases h : ([false, false, false] == ch_guess) = true
  · simp [h]
  · have hfalse : ([false, false, false] == ch_guess) = false := Bool.eq_false_iff.mpr h
    simp [hfalse, PMF.bind_const]

theorem eval_firstSuccess_replicate_eq_repeatAttempt {g : ProbComp (List Bool)}
    {μ : PMF (List Bool)} (hg : ProbComp.eval g = μ.bind bernoulliAttempt) (k : ℕ) :
    ProbComp.eval (firstSuccess <$> OracleComp.replicate k g) = repeatAttempt μ k := by
  induction k with
  | zero =>
    simp [repeatAttempt]
  | succ k ih =>
    simp only [OracleComp.replicate_succ, map_bind, ProbComp.eval_bind, ProbComp.eval_map,
      PMF.map_comp, Function.comp_def, firstSuccess_cons, repeatAttempt]
    have hstep (x : List Bool) :
        (ProbComp.eval (OracleComp.replicate k g)).map
          (fun xs => if x.headD false then x.tail else firstSuccess xs) =
        if x.headD false then PMF.pure x.tail else repeatAttempt μ k := by
      cases x.headD false
      · simpa only [Bool.false_eq_true, ↓reduceIte, ProbComp.eval_map] using ih
      · simp only [↓reduceIte]
        exact PMF.map_const _ _
    simp only [hstep, hg]
    exact bind_bernoulliAttempt_ite μ (repeatAttempt μ k)

theorem distinguishingGame_mixThree (p q : PMF (List Bool))
    (adv : List Bool → ProbComp Bool) :
    distinguishingGame (mixThree p q) adv =
      mixThree (distinguishingGame p adv) (distinguishingGame q adv) := by
  simp only [distinguishingGame, mixThree, PMF.bind_bind]
  congr 1
  funext ch_guess
  split_ifs <;> rfl

theorem advantage_mixThree (g1 g2 : Game) :
    Game.advantage (mixThree g1 g2) g1 = (7 / 8 : ℝ≥0) * Game.advantage g2 g1 := by
  have hunif : mixThree g1 g2 =
      (PMF.uniformOfFintype (BitString 3)).bind
        (fun v => if v = 0 then g1 else g2) := by
    simp only [mixThree, BitString.uniformList, PMF.bind_map, Function.comp_def]
    congr 1
    funext v
    by_cases hv : v = 0
    · subst hv; rfl
    · simp only [hv, ↓reduceIte, beq_iff_eq, ite_eq_right_iff]
      intro h
      refine False.elim (hv (funext fun i => ?_))
      have hi := congrArg (fun l => l.getD i.val false) h.symm
      fin_cases i <;> exact hi
  have hsucc : (Game.succProbability (mixThree g1 g2) : ℝ) - Game.succProbability g1 =
      (7 / 8 : ℝ) * ((Game.succProbability g2 : ℝ) - Game.succProbability g1) := by
    rw [hunif, Game.succProbability_uniform]
    simp only [NNReal.coe_div, NNReal.coe_sum, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
    have hterm (v : BitString 3) :
        (Game.succProbability (if v = 0 then g1 else g2) : ℝ) =
          (Game.succProbability g2 : ℝ) +
            if v = 0 then (Game.succProbability g1 : ℝ) - Game.succProbability g2 else 0 := by
      split_ifs <;> ring
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul, Nat.cast_pow,
      Nat.cast_ofNat, Fintype.sum_ite_eq']
    norm_num
    ring
  apply NNReal.eq
  rw [NNReal.coe_mul, Game.coe_advantage, Game.coe_advantage, hsucc, abs_mul]
  norm_num

theorem advantage_repeatAttempt_le (μ : PMF (List Bool)) (adv : List Bool → ProbComp Bool)
    (k : ℕ) :
    Game.advantage (distinguishingGame (repeatAttempt μ k) adv) (distinguishingGame μ adv) ≤
      (7 / 8 : ℝ≥0) ^ k := by
  induction k with
  | zero =>
    simpa [repeatAttempt] using Game.advantage_le_one _ _
  | succ k ih =>
    rw [repeatAttempt, distinguishingGame_mixThree, advantage_mixThree, pow_succ']
    gcongr

theorem firstSuccess_replicate_game0_indistinguishable (generator : List Bool → List Bool)
    (s m : ℕ → ℕ) (φ : ℕ → CNF ℕ) (w : ℕ → List Bool)
    (prog : ℕ → WordOracleComp Unit (List Bool)) :
    ComputationallyIndistinguishable
      (fun n => ((gmwProver generator (s n) (m n) (φ n) (w n)).run (prog n)
        (gmwProver generator (s n) (m n) (φ n) (w n)).init).map Prod.fst)
      (fun n => ProbComp.eval
        (firstSuccess <$> OracleComp.replicate (n + 1)
          (game0 generator (s n) (m n) (φ n) (w n) (prog n)))) := by
  refine ComputationallyIndistinguishable.symm fun adv _ => ?_
  refine negligible_of_le
    ((negligible_geometric (by norm_num : (7 / 8 : ℝ≥0) < 1)).shift 1) fun n => ?_
  dsimp only
  rw [eval_firstSuccess_replicate_eq_repeatAttempt
    (eval_game0_eq_bind_bernoulliAttempt generator (s n) (m n) (φ n) (w n) (prog n)) (n + 1)]
  exact advantage_repeatAttempt_le _ (adv n) (n + 1)

/-! ### Step 2: Introducing unopened pads via `naorSelectPads` -/

@[fun_prop]
theorem isPPTOn_runTwoRound_prover {α Caller : Type} {enc : α ↪ List Bool}
    {input : Caller ↪ List Bool}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    {generator : List Bool → List Bool}
    {n s m : Caller → ℕ} {a : Caller → α} {z : Caller → List Bool}
    {φ : Caller → CNF ℕ}
    {openFlags bits ch_guess : Caller → List Bool}
    {seeds pads : Caller → List (List Bool)}
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun p => Vstar p.1 p.2.1 p.2.2))
    (hg : ComputableTidilyInPolyTime generator encBits encBits)
    (hn : ComputableTidilyInPolyTime n input encUnary)
    (hs : ComputableTidilyInPolyTime s input encUnary)
    (hm : ComputableTidilyInPolyTime m input encUnary)
    (ha : ComputableTidilyInPolyTime a input enc)
    (hz : ComputableTidilyInPolyTime z input encBits)
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hopen : ComputableTidilyInPolyTime openFlags input encBits)
    (hbits : ComputableTidilyInPolyTime bits input encBits)
    (hch : ComputableTidilyInPolyTime ch_guess input encBits)
    (hseeds : ComputableTidilyInPolyTime seeds input (encList encBits))
    (hpads : ComputableTidilyInPolyTime pads input (encList encBits)) :
    IsPPTOn input (encPair encBits (encPair encUnary encBits))
      (fun c => runTwoRound
        (fun r => proverReply1 generator (m c) r (openFlags c) (bits c) (seeds c) (pads c))
        (fun _ => proverReply2 (s c) (φ c) (ch_guess c) (bits c) (seeds c))
        (Vstar (n c) (a c) (z c))
        (0, [false, false, false])) := by
  refine isPPTOn_runTwoRound hV
    (prepare := fun c => (n c, a c, z c))
    (reply1 := fun p => proverReply1 generator (m p.1) p.2 (openFlags p.1)
      (bits p.1) (seeds p.1) (pads p.1))
    (reply2 := fun p => proverReply2 (s p.1) (φ p.1) (ch_guess p.1) (bits p.1) (seeds p.1))
    (bound := fun c => (bits c).length * m c + (bits c).length * (s c + 1))
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (fun c q => by dsimp only; exact (List.length_take_le _ _).trans (by omega))
    (fun c q => by dsimp only; rw [length_proverReply2_any]; omega)

/-- Run one attempt with pre-sampled unopened pads `pads` and active flags
`allOpenFlags φ ch_guess bits`. -/
noncomputable def gameWithPads (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (w : List Bool) (prog : WordOracleComp Unit (List Bool)) (pads : List (List Bool)) :
    ProbComp (List Bool) := do
  let ch_guess ← BitString.sampleList 3
  let m₀ ← BitString.sampleList φ.vars.length
  let m₁ ← BitString.sampleList φ.vars.length
  let m₂ ← BitString.sampleList φ.vars.length
  let bits := realBits φ w m₀ m₁ m₂
  let openFlags := allOpenFlags φ ch_guess bits
  let seeds ← OracleComp.replicate (totalLen φ) (BitString.sampleList s)
  let p ← runTwoRound
    (fun r => proverReply1 generator m r openFlags bits seeds pads)
    (fun _ => proverReply2 s φ ch_guess bits seeds)
    prog (0, [false, false, false])
  return if p.2.2 == ch_guess then true :: p.1 else []

/-- Single-attempt hybrid with pseudorandom unopened pads. -/
noncomputable def game0Pads (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (w : List Bool) (prog : WordOracleComp Unit (List Bool)) : ProbComp (List Bool) :=
  OracleComp.replicate (totalLen φ) (generator <$> BitString.sampleList s) >>=
    gameWithPads generator s m φ w prog

/-- Single-attempt hybrid with uniform unopened pads. -/
noncomputable def game1 (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (w : List Bool) (prog : WordOracleComp Unit (List Bool)) : ProbComp (List Bool) :=
  OracleComp.replicate (totalLen φ) (BitString.sampleList m) >>=
    gameWithPads generator s m φ w prog

theorem eval_bind_gameWithPads (d_pads : ProbComp (List (List Bool)))
    (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ) (w : List Bool)
    (prog : WordOracleComp Unit (List Bool)) :
    ProbComp.eval (d_pads >>= gameWithPads generator s m φ w prog) =
      ProbComp.eval (do
        let ch_guess ← BitString.sampleList 3
        let m₀ ← BitString.sampleList φ.vars.length
        let m₁ ← BitString.sampleList φ.vars.length
        let m₂ ← BitString.sampleList φ.vars.length
        let bits := realBits φ w m₀ m₁ m₂
        let openFlags := allOpenFlags φ ch_guess bits
        let seeds ← OracleComp.replicate (totalLen φ) (BitString.sampleList s)
        let pads ← d_pads
        let p ← runTwoRound
          (fun r => proverReply1 generator m r openFlags bits seeds pads)
          (fun _ => proverReply2 s φ ch_guess bits seeds)
          prog (0, [false, false, false])
        return if p.2.2 == ch_guess then true :: p.1 else []) := by
  simp only [gameWithPads, ProbComp.eval_bind, BitString.eval_sampleList]
  rw [PMF.bind_comm]
  congr 1; funext ch_guess
  rw [PMF.bind_comm]
  congr 1; funext m₀
  rw [PMF.bind_comm]
  congr 1; funext m₁
  rw [PMF.bind_comm]
  congr 1; funext m₂
  rw [PMF.bind_comm]

theorem proverReply1_eq_naorSelectPads (generator : List Bool → List Bool) (m : ℕ)
    (r openFlags bits : List Bool) (seeds pads : List (List Bool)) :
    proverReply1 generator m r openFlags bits seeds pads =
      proverReply1 id m r (List.replicate bits.length false) bits []
        (naorSelectPads generator openFlags bits seeds pads) := by
  unfold proverReply1
  rw [naorCommitSplit_eq_naorSelectPads]

theorem eval_game0Pads_eq_eval_game0 (generator : List Bool → List Bool) (s m : ℕ)
    (φ : CNF ℕ) (w : List Bool) (prog : WordOracleComp Unit (List Bool)) :
    ProbComp.eval (game0Pads generator s m φ w prog) =
      ProbComp.eval (game0 generator s m φ w prog) := by
  rw [game0Pads, eval_bind_gameWithPads]
  simp only [game0, sampleHonestCoins, bind_assoc, pure_bind, ProbComp.eval_bind]
  congr 1; funext ch_guess
  congr 1; funext m₀
  congr 1; funext m₁
  congr 1; funext m₂
  let bits := realBits φ w m₀ m₁ m₂
  have hbits : bits.length = totalLen φ := length_realBits φ w m₀ m₁ m₂
  let openFlags := allOpenFlags φ ch_guess bits
  let cont (q : List (List Bool) × List (List Bool)) : PMF (List Bool) :=
    ProbComp.eval (do
      let p ← runTwoRound
        (fun r => proverReply1 id m r (List.replicate bits.length false) bits [] q.1)
        (fun _ => naorMaskBits openFlags bits ++ q.2.flatten)
        prog (0, [false, false, false])
      return if p.2.2 == ch_guess then true :: p.1 else [])
  have hselect := congrArg (fun d => d.bind cont)
    (eval_replicate_naorSelectPads s generator openFlags bits)
  simp only [hbits, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure, PMF.bind_bind,
    PMF.bind_map, PMF.pure_bind, Function.comp_def, cont] at hselect
  have hhon1 (seeds : List (List Bool)) :
      honestReply1 generator m φ (realBits φ w m₀ m₁ m₂, seeds) =
        fun r => proverReply1 generator m r (List.replicate (totalLen φ) true)
          (realBits φ w m₀ m₁ m₂) seeds [] := rfl
  simp only [hhon1, honestReply2, proverReply2, ProbComp.eval_pure,
    proverReply1_eq_naorSelectPads generator m, length_realBits]
  exact hselect

/-! ### Step 3: Pseudorandom unopened pads to uniform unopened pads -/

theorem isPPTOn_gameWithPads {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ} {f : α → CNF ℕ}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    {a : ℕ → α} {w z : ℕ → List Bool}
    (hg : ComputableTidilyInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length)
    (hf : ComputableTidilyInPolyTime f enc encCNF)
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun p => Vstar p.1 p.2.1 p.2.2))
    (ha : ComputableTidilyInPolyTime a encUnary enc)
    (hw : ComputableTidilyInPolyTime w encUnary encBits)
    (hz : ComputableTidilyInPolyTime z encUnary encBits) :
    IsPPTOn (encPair encUnary (encList encBits)) encBits
      (fun p : ℕ × List (List Bool) =>
        gameWithPads generator (p.1 + 7) (length (p.1 + 7))
          (f (a p.1)) (w p.1) (Vstar p.1 (a p.1) (z p.1)) p.2) := by
  have hlength := PRG.polyTime_length hg hlen
  dsimp only [gameWithPads]
  ppt

theorem isPPTOn_game0 {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ} {f : α → CNF ℕ}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    {a : ℕ → α} {w z : ℕ → List Bool}
    (hg : ComputableTidilyInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length)
    (hf : ComputableTidilyInPolyTime f enc encCNF)
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun p => Vstar p.1 p.2.1 p.2.2))
    (ha : ComputableTidilyInPolyTime a encUnary enc)
    (hw : ComputableTidilyInPolyTime w encUnary encBits)
    (hz : ComputableTidilyInPolyTime z encUnary encBits) :
    IsPPTOn encUnary encBits
      (fun n => game0 generator (n + 7) (length (n + 7))
        (f (a n)) (w n) (Vstar n (a n) (z n))) := by
  have hlength := PRG.polyTime_length hg hlen
  dsimp only [game0, sampleHonestCoins, honestReply1, honestReply2]
  ppt

theorem isPPTOn_game1 {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ} {f : α → CNF ℕ}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    {a : ℕ → α} {w z : ℕ → List Bool}
    (hg : ComputableTidilyInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length)
    (hf : ComputableTidilyInPolyTime f enc encCNF)
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun p => Vstar p.1 p.2.1 p.2.2))
    (ha : ComputableTidilyInPolyTime a encUnary enc)
    (hw : ComputableTidilyInPolyTime w encUnary encBits)
    (hz : ComputableTidilyInPolyTime z encUnary encBits) :
    IsPPTOn encUnary encBits
      (fun n => game1 generator (n + 7) (length (n + 7))
        (f (a n)) (w n) (Vstar n (a n) (z n))) := by
  have hlength := PRG.polyTime_length hg hlen
  have hpad := isPPTOn_gameWithPads hg hlen hf hV ha hw hz
  dsimp only [game1]
  ppt

theorem game0_indistinguishable_game1 {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    {f : α → CNF ℕ} (hf : ComputableTidilyInPolyTime f enc encCNF)
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun p => Vstar p.1 p.2.1 p.2.2))
    {a : ℕ → α} {w z : ℕ → List Bool}
    (ha : ComputableTidilyInPolyTime a encUnary enc)
    (hw : ComputableTidilyInPolyTime w encUnary encBits)
    (hz : ComputableTidilyInPolyTime z encUnary encBits) :
    ComputationallyIndistinguishable
      (fun n => ProbComp.eval
        (game0 generator (n + 7) (length (n + 7)) (f (a n)) (w n) (Vstar n (a n) (z n))))
      (fun n => ProbComp.eval
        (game1 generator (n + 7) (length (n + 7)) (f (a n)) (w n) (Vstar n (a n) (z n)))) := by
  have hlength := hG.polyTime_length
  have hg := hG.polyTime
  have horig : IsPPTOn encUnary encBits (fun n => generator <$> BitString.sampleList (n + 7)) := by
    ppt
  have hrepl : IsPPTOn encUnary encBits (fun n => BitString.sampleList (length (n + 7))) := by
    ppt
  have hind_pad : ComputationallyIndistinguishable
      (fun n => ProbComp.eval (generator <$> BitString.sampleList (n + 7)))
      (fun n => ProbComp.eval (BitString.sampleList (length (n + 7)))) := by
    simpa only [ProbComp.eval_map, BitString.eval_sampleList, generatorEnsemble] using
      hG.indistinguishable.shift 7
  have hrep := ComputationallyIndistinguishable.replicate_bind horig hrepl hind_pad
    (count := fun n => totalLen (f (a n)))
    (process := fun n pads =>
      gameWithPads generator (n + 7) (length (n + 7))
        (f (a n)) (w n) (Vstar n (a n) (z n)) pads)
    (by fun_prop)
    (isPPTOn_gameWithPads hg hG.length_eq hf hV ha hw hz)
  change ComputationallyIndistinguishable
    (fun n => ProbComp.eval (game0Pads generator (n + 7) (length (n + 7))
      (f (a n)) (w n) (Vstar n (a n) (z n))))
    (fun n => ProbComp.eval (game1 generator (n + 7) (length (n + 7))
      (f (a n)) (w n) (Vstar n (a n) (z n)))) at hrep
  simpa only [eval_game0Pads_eq_eval_game0] using hrep

/-! ### Step 4: Masking unopened committed bits and eliminating the witness -/

theorem runTwoRound_congr_reply1_of_one_le {α : Type} (r1 r1' r2 : List Bool → List Bool)
    (prog : WordOracleComp Unit α) {s : ℕ × List Bool} (hs : 1 ≤ s.1) :
    runTwoRound r1 r2 prog s = runTwoRound r1' r2 prog s := by
  induction prog using PFunctor.FreeM.induction generalizing s with
  | pure x => rfl
  | lift_bind q k ih =>
    cases q with
    | inl n =>
      have h1 := runTwoRound_query_inl r1 r2 n k s id
      have h2 := runTwoRound_query_inl r1' r2 n k s id
      simp only [id_map] at h1 h2
      change runTwoRound r1 r2 (OracleComp.query (Sum.inl n) >>= k) s =
        runTwoRound r1' r2 (OracleComp.query (Sum.inl n) >>= k) s
      rw [h1, h2]
      congr 1; funext u
      exact ih u hs
    | inr q =>
      have h1 := runTwoRound_query_inr r1 r2 q k s id
      have h2 := runTwoRound_query_inr r1' r2 q k s id
      simp only [id_map] at h1 h2
      change runTwoRound r1 r2 (OracleComp.query (Sum.inr q) >>= k) s =
        runTwoRound r1' r2 (OracleComp.query (Sum.inr q) >>= k) s
      rw [h1, h2]
      have h0 : (s.1 == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
      have hstep : twoRoundStep r1 r2 q.2 s = twoRoundStep r1' r2 q.2 s := by
        simp [twoRoundStep, h0]
      have hs' : 1 ≤ (twoRoundStep r1' r2 q.2 s).2.1 := by
        dsimp only [twoRoundStep]
        split_ifs <;> simp [hs]
      rw [hstep]
      exact ih _ hs'

theorem eval_bind_runTwoRound_reply1 {α β : Type} (μ : ProbComp β)
    (f₁ f₂ : β → List Bool → List Bool) (r2 : List Bool → List Bool)
    (hf : ∀ r, ProbComp.eval ((fun b => f₁ b r) <$> μ) =
      ProbComp.eval ((fun b => f₂ b r) <$> μ))
    (prog : WordOracleComp Unit α) (ch₀ : List Bool) :
    ProbComp.eval (μ >>= fun b => runTwoRound (f₁ b) r2 prog (0, ch₀)) =
      ProbComp.eval (μ >>= fun b => runTwoRound (f₂ b) r2 prog (0, ch₀)) := by
  induction prog using PFunctor.FreeM.induction with
  | pure x => rfl
  | lift_bind q k ih =>
    cases q with
    | inl n =>
      have h1 (b : β) := runTwoRound_query_inl (f₁ b) r2 n k (0, ch₀) id
      have h2 (b : β) := runTwoRound_query_inl (f₂ b) r2 n k (0, ch₀) id
      simp only [id_map] at h1 h2
      change ProbComp.eval (μ >>= fun b =>
          runTwoRound (f₁ b) r2 (OracleComp.query (Sum.inl n) >>= k) (0, ch₀)) =
        ProbComp.eval (μ >>= fun b =>
          runTwoRound (f₂ b) r2 (OracleComp.query (Sum.inl n) >>= k) (0, ch₀))
      simp only [h1, h2, ProbComp.eval_bind]
      rw [PMF.bind_comm (ProbComp.eval μ), PMF.bind_comm (ProbComp.eval μ)]
      congr 1; funext u
      simpa only [ProbComp.eval_bind] using ih u
    | inr q =>
      have h1 (b : β) := runTwoRound_query_inr (f₁ b) r2 q k (0, ch₀) id
      have h2 (b : β) := runTwoRound_query_inr (f₂ b) r2 q k (0, ch₀) id
      simp only [id_map, twoRoundStep, beq_self_eq_true, ↓reduceIte] at h1 h2
      have hcongr1 (b : β) :
          runTwoRound (f₁ b) r2 (k (f₁ b q.2)) (1, ch₀) =
            runTwoRound (fun _ => []) r2 (k (f₁ b q.2)) (1, ch₀) :=
        runTwoRound_congr_reply1_of_one_le _ _ r2 _ (le_refl 1)
      have hcongr2 (b : β) :
          runTwoRound (f₂ b) r2 (k (f₂ b q.2)) (1, ch₀) =
            runTwoRound (fun _ => []) r2 (k (f₂ b q.2)) (1, ch₀) :=
        runTwoRound_congr_reply1_of_one_le _ _ r2 _ (le_refl 1)
      change ProbComp.eval (μ >>= fun b =>
          runTwoRound (f₁ b) r2 (OracleComp.query (Sum.inr q) >>= k) (0, ch₀)) =
        ProbComp.eval (μ >>= fun b =>
          runTwoRound (f₂ b) r2 (OracleComp.query (Sum.inr q) >>= k) (0, ch₀))
      simp only [h1, h2, hcongr1, hcongr2]
      have hmap := congrArg
        (fun d => d.bind (fun ans => ProbComp.eval (runTwoRound (fun _ => []) r2 (k ans) (1, ch₀))))
        (hf q.2)
      simpa only [ProbComp.eval_bind, ProbComp.eval_map, PMF.bind_map, Function.comp_def]
        using hmap

theorem listXor_pair_comm (d : ℕ) (w m : List Bool) :
    BitString.listXor d [w, m] = BitString.listXor d [m, w] := by
  have h : BitString.ofList d (BitString.listXor d [w, m]) =
      BitString.ofList d (BitString.listXor d [m, w]) := by
    rw [ofList_listXor_pair, ofList_listXor_pair, add_comm]
  have h2 := congrArg List.ofFn h
  rwa [BitString.ofFn_ofList (by simp), BitString.ofFn_ofList (by simp)] at h2

theorem uniformList_bind_ite_listXor {α : Type} (d : ℕ) (b : Bool) (w : List Bool)
    (k : List Bool → PMF α) :
    ((BitString.uniformList d).bind
      fun m => k (if b then BitString.listXor d [w, m] else m)) =
      (BitString.uniformList d).bind k := by
  have hmap : (BitString.uniformList d).map
      (fun m => if b then BitString.listXor d [w, m] else m) = BitString.uniformList d := by
    cases b
    · exact PMF.map_id _
    · simp only [↓reduceIte, listXor_pair_comm d w]
      exact uniformList_map_listXor d w
  conv_rhs => rw [← hmap]
  simp only [PMF.bind_map, Function.comp_def]

theorem uniformList_bind_ite_listXor_three {α : Type} (d : ℕ) (b₀ b₁ b₂ : Bool) (w : List Bool)
    (f : List Bool → List Bool → List Bool → PMF α) :
    ((BitString.uniformList d).bind fun m₀ =>
      (BitString.uniformList d).bind fun m₁ =>
        (BitString.uniformList d).bind fun m₂ =>
          f (if b₀ then BitString.listXor d [w, m₀] else m₀)
            (if b₁ then BitString.listXor d [w, m₁] else m₁)
            (if b₂ then BitString.listXor d [w, m₂] else m₂)) =
    ((BitString.uniformList d).bind fun r₀ =>
      (BitString.uniformList d).bind fun r₁ =>
        (BitString.uniformList d).bind fun r₂ =>
          f r₀ r₁ r₂) := by
  rw [uniformList_bind_ite_listXor d b₀ w (fun r₀ =>
    (BitString.uniformList d).bind fun m₁ =>
      (BitString.uniformList d).bind fun m₂ =>
        f r₀ (if b₁ then BitString.listXor d [w, m₁] else m₁)
          (if b₂ then BitString.listXor d [w, m₂] else m₂))]
  congr 1; funext r₀
  rw [uniformList_bind_ite_listXor d b₁ w (fun r₁ =>
    (BitString.uniformList d).bind fun m₂ =>
      f r₀ r₁ (if b₂ then BitString.listXor d [w, m₂] else m₂))]
  congr 1; funext r₁
  exact uniformList_bind_ite_listXor d b₂ w (fun r₂ => f r₀ r₁ r₂)

theorem naorSelectSeeds_congr_length (s : ℕ) (openFlags bits₁ bits₂ : List Bool)
    (seeds : List (List Bool)) (hlen : bits₁.length = bits₂.length) :
    naorSelectSeeds s openFlags bits₁ seeds = naorSelectSeeds s openFlags bits₂ seeds := by
  rw [naorSelectSeeds_eq_map, naorSelectSeeds_eq_map, hlen]

/-- Sample the simulator's random strings and commitment seeds for a guessed challenge `ch_guess`,
returning `(simBits φ ch_guess r₀ r₁ r₂, seeds)`. -/
noncomputable def sampleSimCoins (s : ℕ) (φ : CNF ℕ) (ch_guess : List Bool) :
    ProbComp (List Bool × List (List Bool)) := do
  let r₀ ← BitString.sampleList φ.vars.length
  let r₁ ← BitString.sampleList φ.vars.length
  let r₂ ← BitString.sampleList φ.vars.length
  let seeds ← OracleComp.replicate (totalLen φ) (BitString.sampleList s)
  return (simBits φ ch_guess r₀ r₁ r₂, seeds)

@[fun_prop]
theorem isPPTOn_sampleSimCoins {α : Type} {input : α ↪ List Bool}
    {s : α → ℕ} {φ : α → CNF ℕ} {ch_guess : α → List Bool}
    (hs : ComputableTidilyInPolyTime s input encUnary)
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hch : ComputableTidilyInPolyTime ch_guess input encBits) :
    IsPPTOn input (encPair encBits (encList encBits))
      (fun a => sampleSimCoins (s a) (φ a) (ch_guess a)) := by
  dsimp only [sampleSimCoins]
  ppt

/-- Run one simulated attempt with pre-sampled unopened pads `pads` (without the witness `w`). -/
noncomputable def simWithPads (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (prog : WordOracleComp Unit (List Bool)) (pads : List (List Bool)) :
    ProbComp (List Bool) := do
  let ch_guess ← BitString.sampleList 3
  let coins ← sampleSimCoins s φ ch_guess
  let p ← runTwoRound
    (fun r => proverReply1 generator m r (allOpenFlags φ ch_guess coins.1) coins.1 coins.2 pads)
    (fun _ => proverReply2 s φ ch_guess coins.1 coins.2)
    prog (0, [false, false, false])
  return if p.2.2 == ch_guess then true :: p.1 else []

/-- One attempt of the GMW zero-knowledge simulator (without the witness `w`). -/
noncomputable def simAttempt (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (prog : WordOracleComp Unit (List Bool)) : ProbComp (List Bool) :=
  OracleComp.replicate (totalLen φ) (BitString.sampleList m) >>=
    simWithPads generator s m φ prog

/-- The GMW zero-knowledge simulator: repeat `simAttempt` `n + 1` times and return the first
successful output (`firstSuccess`). -/
noncomputable def gmwSimulator {α : Type} (generator : List Bool → List Bool) (length : ℕ → ℕ)
    (f : α → CNF ℕ) (Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool))
    (n : ℕ) (a : α) (z : List Bool) : ProbComp (List Bool) :=
  firstSuccess <$> OracleComp.replicate (n + 1)
    (simAttempt generator (n + 7) (length (n + 7)) (f a) (Vstar n a z))

theorem eval_bind_simWithPads (d_pads : ProbComp (List (List Bool)))
    (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (prog : WordOracleComp Unit (List Bool)) :
    ProbComp.eval (d_pads >>= simWithPads generator s m φ prog) =
      ProbComp.eval (do
        let ch_guess ← BitString.sampleList 3
        let r₀ ← BitString.sampleList φ.vars.length
        let r₁ ← BitString.sampleList φ.vars.length
        let r₂ ← BitString.sampleList φ.vars.length
        let bits := simBits φ ch_guess r₀ r₁ r₂
        let openFlags := allOpenFlags φ ch_guess bits
        let seeds ← OracleComp.replicate (totalLen φ) (BitString.sampleList s)
        let pads ← d_pads
        let p ← runTwoRound
          (fun r => proverReply1 generator m r openFlags bits seeds pads)
          (fun _ => proverReply2 s φ ch_guess bits seeds)
          prog (0, [false, false, false])
        return if p.2.2 == ch_guess then true :: p.1 else []) := by
  simp only [simWithPads, sampleSimCoins, bind_assoc, pure_bind,
    ProbComp.eval_bind, BitString.eval_sampleList]
  rw [PMF.bind_comm]
  congr 1; funext ch_guess
  rw [PMF.bind_comm]
  congr 1; funext r₀
  rw [PMF.bind_comm]
  congr 1; funext r₁
  rw [PMF.bind_comm]
  congr 1; funext r₂
  rw [PMF.bind_comm]

theorem eval_pads_runTwoRound_mask (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (ch_guess openFlags bits : List Bool) (seeds : List (List Bool))
    (prog : WordOracleComp Unit (List Bool)) :
    ProbComp.eval (do
      let pads ← OracleComp.replicate bits.length (BitString.sampleList m)
      let p ← runTwoRound
        (fun r => proverReply1 generator m r openFlags bits seeds pads)
        (fun _ => proverReply2 s φ ch_guess bits seeds)
        prog (0, [false, false, false])
      return if p.2.2 == ch_guess then true :: p.1 else []) =
    ProbComp.eval (do
      let pads ← OracleComp.replicate bits.length (BitString.sampleList m)
      let p ← runTwoRound
        (fun r => proverReply1 generator m r openFlags (naorMaskBits openFlags bits) seeds pads)
        (fun _ => proverReply2 s φ ch_guess bits seeds)
        prog (0, [false, false, false])
      return if p.2.2 == ch_guess then true :: p.1 else []) := by
  have h1 := eval_bind_runTwoRound_reply1
    (OracleComp.replicate bits.length (BitString.sampleList m))
    (fun pads r => proverReply1 generator m r openFlags bits seeds pads)
    (fun pads r => proverReply1 generator m r openFlags (naorMaskBits openFlags bits) seeds pads)
    (fun _ => proverReply2 s φ ch_guess bits seeds)
    (fun r => by
      have hsplit := congrArg
        (PMF.map fun xs : List (List Bool) => xs.flatten.take (bits.length * m))
        (eval_replicate_map_naorCommitSplit m generator (BitString.listRow m 0 r)
          openFlags bits seeds)
      simpa only [ProbComp.eval_map, PMF.map_comp, Function.comp_def,
        proverReply1, length_naorMaskBits] using hsplit)
    prog [false, false, false]
  have hmap := congrArg
    (PMF.map (fun p : List Bool × (ℕ × List Bool) =>
      if p.2.2 == ch_guess then true :: p.1 else [])) h1
  simpa only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind, PMF.pure_map,
    PMF.map, PMF.bind_bind, Function.comp_def] using hmap

theorem eval_game1_eq_eval_simAttempt (generator : List Bool → List Bool) {s m : ℕ}
    {φ : CNF ℕ} {w : List Bool} (hw : ThreeSAT.verifier (φ, w) = true)
    (prog : WordOracleComp Unit (List Bool)) :
    ProbComp.eval (game1 generator s m φ w prog) =
      ProbComp.eval (simAttempt generator s m φ prog) := by
  rw [game1, eval_bind_gameWithPads, simAttempt, eval_bind_simWithPads]
  let simCont (ch_guess r₀ r₁ r₂ : List Bool) : PMF (List Bool) :=
    let sbits := simBits φ ch_guess r₀ r₁ r₂
    let sflags := allOpenFlags φ ch_guess sbits
    ProbComp.eval (do
      let seeds ← OracleComp.replicate (totalLen φ) (BitString.sampleList s)
      let pads ← OracleComp.replicate (totalLen φ) (BitString.sampleList m)
      let p ← runTwoRound
        (fun r => proverReply1 generator m r sflags sbits seeds pads)
        (fun _ => proverReply2 s φ ch_guess sbits seeds)
        prog (0, [false, false, false])
      return if p.2.2 == ch_guess then true :: p.1 else [])
  have hinner (ch_guess m₀ m₁ m₂ : List Bool) :
      ProbComp.eval (do
        let bits := realBits φ w m₀ m₁ m₂
        let openFlags := allOpenFlags φ ch_guess bits
        let seeds ← OracleComp.replicate (totalLen φ) (BitString.sampleList s)
        let pads ← OracleComp.replicate (totalLen φ) (BitString.sampleList m)
        let p ← runTwoRound
          (fun r => proverReply1 generator m r openFlags bits seeds pads)
          (fun _ => proverReply2 s φ ch_guess bits seeds)
          prog (0, [false, false, false])
        return if p.2.2 == ch_guess then true :: p.1 else []) =
      simCont ch_guess
        (if ch_guess.getD 0 false then BitString.listXor φ.vars.length [w, m₀] else m₀)
        (if ch_guess.getD 1 false then BitString.listXor φ.vars.length [w, m₁] else m₁)
        (if ch_guess.getD 2 false then BitString.listXor φ.vars.length [w, m₂] else m₂) := by
    let bits := realBits φ w m₀ m₁ m₂
    let openFlags := allOpenFlags φ ch_guess bits
    let r₀ := if ch_guess.getD 0 false then BitString.listXor φ.vars.length [w, m₀] else m₀
    let r₁ := if ch_guess.getD 1 false then BitString.listXor φ.vars.length [w, m₁] else m₁
    let r₂ := if ch_guess.getD 2 false then BitString.listXor φ.vars.length [w, m₂] else m₂
    let sbits := simBits φ ch_guess r₀ r₁ r₂
    have hbits_len : bits.length = totalLen φ := length_realBits φ w m₀ m₁ m₂
    have hsbits_len : sbits.length = totalLen φ := length_simBits φ ch_guess r₀ r₁ r₂
    have hmask : naorMaskBits openFlags bits = sbits := naorMaskBits_realBits ch_guess hw
    have hflags : openFlags = allOpenFlags φ ch_guess sbits :=
      allOpenFlags_realBits φ ch_guess w m₀ m₁ m₂
    have hrep2 (seeds : List (List Bool)) :
        proverReply2 s φ ch_guess bits seeds = proverReply2 s φ ch_guess sbits seeds := by
      simp only [proverReply2]
      change naorMaskBits openFlags bits ++ (naorSelectSeeds s openFlags bits seeds).flatten =
        naorMaskBits (allOpenFlags φ ch_guess sbits) sbits ++
          (naorSelectSeeds s (allOpenFlags φ ch_guess sbits) sbits seeds).flatten
      rw [hmask, naorMaskBits_simBits, hflags,
        naorSelectSeeds_congr_length s _ bits sbits seeds (hbits_len.trans hsbits_len.symm)]
    dsimp only [simCont]
    simp only [ProbComp.eval_bind]
    congr 1; funext seeds
    have hpad := eval_pads_runTwoRound_mask generator s m φ ch_guess openFlags bits seeds prog
    rw [hbits_len] at hpad
    have hpad_rhs :
        ProbComp.eval (do
          let pads ← OracleComp.replicate (totalLen φ) (BitString.sampleList m)
          let p ← runTwoRound
            (fun r => proverReply1 generator m r openFlags (naorMaskBits openFlags bits) seeds pads)
            (fun _ => proverReply2 s φ ch_guess bits seeds)
            prog (0, [false, false, false])
          return if p.2.2 == ch_guess then true :: p.1 else []) =
        ProbComp.eval (do
          let pads ← OracleComp.replicate (totalLen φ) (BitString.sampleList m)
          let p ← runTwoRound
            (fun r => proverReply1 generator m r (allOpenFlags φ ch_guess sbits) sbits seeds pads)
            (fun _ => proverReply2 s φ ch_guess sbits seeds)
            prog (0, [false, false, false])
          return if p.2.2 == ch_guess then true :: p.1 else []) := by
      rw [hmask, hflags, hrep2 seeds]
    simpa only [ProbComp.eval_bind] using hpad.trans hpad_rhs
  simp only [ProbComp.eval_bind, BitString.eval_sampleList, hinner]
  congr 1; funext ch_guess
  simpa only [simCont, ProbComp.eval_bind] using
    uniformList_bind_ite_listXor_three φ.vars.length
      (ch_guess.getD 0 false) (ch_guess.getD 1 false) (ch_guess.getD 2 false) w
      (simCont ch_guess)

theorem isPPTOn_simWithPads {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ} {f : α → CNF ℕ}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    (hg : ComputableTidilyInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length)
    (hf : ComputableTidilyInPolyTime f enc encCNF)
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun p => Vstar p.1 p.2.1 p.2.2)) :
    IsPPTOn (encPair (encPair encUnary (encPair enc encBits)) (encList encBits)) encBits
      (fun p : (ℕ × α × List Bool) × List (List Bool) =>
        simWithPads generator (p.1.1 + 7) (length (p.1.1 + 7))
          (f p.1.2.1) (Vstar p.1.1 p.1.2.1 p.1.2.2) p.2) := by
  have hlength := PRG.polyTime_length hg hlen
  dsimp only [simWithPads]
  ppt

theorem isPPTOn_simAttempt {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ} {f : α → CNF ℕ}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    (hg : ComputableTidilyInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length)
    (hf : ComputableTidilyInPolyTime f enc encCNF)
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun p => Vstar p.1 p.2.1 p.2.2)) :
    IsPPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun p : ℕ × α × List Bool =>
        simAttempt generator (p.1 + 7) (length (p.1 + 7)) (f p.2.1) (Vstar p.1 p.2.1 p.2.2)) := by
  have hlength := PRG.polyTime_length hg hlen
  have hpad := isPPTOn_simWithPads hg hlen hf hV
  dsimp only [simAttempt]
  ppt

theorem isPPTOn_gmwSimulator {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ} {f : α → CNF ℕ}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    (hg : ComputableTidilyInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length)
    (hf : ComputableTidilyInPolyTime f enc encCNF)
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun p => Vstar p.1 p.2.1 p.2.2)) :
    IsPPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun p : ℕ × α × List Bool =>
        gmwSimulator generator length f Vstar p.1 p.2.1 p.2.2) := by
  have hattempt := isPPTOn_simAttempt hg hlen hf hV
  dsimp only [gmwSimulator]
  ppt

theorem gmwView_indistinguishable_gmwSimulator {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    {f : α → CNF ℕ} (hf : ComputableTidilyInPolyTime f enc encCNF)
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun p => Vstar p.1 p.2.1 p.2.2))
    {a : ℕ → α} {w z : ℕ → List Bool}
    (ha : ComputableTidilyInPolyTime a encUnary enc)
    (hw_comp : ComputableTidilyInPolyTime w encUnary encBits)
    (hz : ComputableTidilyInPolyTime z encUnary encBits)
    (hw_sat : ∀ n, ThreeSAT.verifier (f (a n), w n) = true) :
    ComputationallyIndistinguishable
      (fun n => ((gmwProver generator (n + 7) (length (n + 7)) (f (a n)) (w n)).run
        (Vstar n (a n) (z n))
        (gmwProver generator (n + 7) (length (n + 7)) (f (a n)) (w n)).init).map Prod.fst)
      (fun n => ProbComp.eval (gmwSimulator generator length f Vstar n (a n) (z n))) := by
  have hstep1 := firstSuccess_replicate_game0_indistinguishable generator
    (fun n => n + 7) (fun n => length (n + 7)) (fun n => f (a n)) w
    (fun n => Vstar n (a n) (z n))
  have hg := hG.polyTime
  have hstep23 := ComputationallyIndistinguishable.replicate_bind
    (isPPTOn_game0 hg hG.length_eq hf hV ha hw_comp hz)
    (isPPTOn_game1 hg hG.length_eq hf hV ha hw_comp hz)
    (game0_indistinguishable_game1 hG hf hV ha hw_comp hz)
    (count := fun n => n + 1)
    (process := fun _ xs => pure (firstSuccess xs))
    (by fun_prop)
    (by ppt)
  have hstep23' :
      ComputationallyIndistinguishable
        (fun n => ProbComp.eval
          (firstSuccess <$> OracleComp.replicate (n + 1)
            (game0 generator (n + 7) (length (n + 7)) (f (a n)) (w n) (Vstar n (a n) (z n)))))
        (fun n => ProbComp.eval
          (firstSuccess <$> OracleComp.replicate (n + 1)
            (game1 generator (n + 7) (length (n + 7)) (f (a n)) (w n) (Vstar n (a n) (z n))))) := by
    simpa only [bind_pure_comp] using hstep23
  have hstep4 :
      (fun n => ProbComp.eval
        (firstSuccess <$> OracleComp.replicate (n + 1)
          (game1 generator (n + 7) (length (n + 7)) (f (a n)) (w n) (Vstar n (a n) (z n))))) =
      (fun n => ProbComp.eval (gmwSimulator generator length f Vstar n (a n) (z n))) := by
    funext n
    have h1 := eval_game1_eq_eval_simAttempt generator (s := n + 7) (m := length (n + 7))
      (hw_sat n) (Vstar n (a n) (z n))
    simp only [gmwSimulator, ProbComp.eval_map, ProbComp.eval_replicate_congr h1]
  rw [← hstep4]
  exact hstep1.trans hstep23'

/-! ### Efficient honest prover interaction -/

/-- The PPT program realizing the honest GMW prover's interaction with a verifier `prog`. -/
noncomputable def gmwInteract (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (w : List Bool) (prog : WordOracleComp Unit (List Bool)) : ProbComp (List Bool) := do
  let coins ← sampleHonestCoins s φ w
  let p ← runTwoRound (honestReply1 generator m φ coins)
    (honestReply2 s φ coins) prog (0, [false, false, false])
  return p.1

theorem eval_gmwInteract (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (w : List Bool) (prog : WordOracleComp Unit (List Bool)) :
    ProbComp.eval (gmwInteract generator s m φ w prog) =
      ((gmwProver generator s m φ w).run prog
        (gmwProver generator s m φ w).init).map Prod.fst := by
  simpa only [gmwInteract, bind_pure_comp] using (run_gmwProver_fst generator s m φ w prog).symm

@[fun_prop]
theorem computableTidilyInPolyTime_honestReply1 {α : Type} {input : α ↪ List Bool}
    {generator : List Bool → List Bool} {m : α → ℕ} {φ : α → CNF ℕ}
    {coins : α → List Bool × List (List Bool)} {r : α → List Bool}
    (hg : ComputableTidilyInPolyTime generator encBits encBits)
    (hm : ComputableTidilyInPolyTime m input encUnary)
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hcoins : ComputableTidilyInPolyTime coins input (encPair encBits (encList encBits)))
    (hr : ComputableTidilyInPolyTime r input encBits) :
    ComputableTidilyInPolyTime
      (fun a => honestReply1 generator (m a) (φ a) (coins a) (r a))
      input encBits := by
  dsimp only [honestReply1]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_honestReply2 {α : Type} {input : α ↪ List Bool}
    {s : α → ℕ} {φ : α → CNF ℕ}
    {coins : α → List Bool × List (List Bool)} {ch : α → List Bool}
    (hs : ComputableTidilyInPolyTime s input encUnary)
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hcoins : ComputableTidilyInPolyTime coins input (encPair encBits (encList encBits)))
    (hch : ComputableTidilyInPolyTime ch input encBits) :
    ComputableTidilyInPolyTime
      (fun a => honestReply2 (s a) (φ a) (coins a) (ch a))
      input encBits := by
  dsimp only [honestReply2]
  fun_prop

@[fun_prop]
theorem isPPTOn_runTwoRound_honest {α Caller : Type} {enc : α ↪ List Bool}
    {input : Caller ↪ List Bool}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    {generator : List Bool → List Bool}
    {n s m : Caller → ℕ} {a : Caller → α} {z : Caller → List Bool}
    {φ : Caller → CNF ℕ} {coins : Caller → List Bool × List (List Bool)}
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun p => Vstar p.1 p.2.1 p.2.2))
    (hg : ComputableTidilyInPolyTime generator encBits encBits)
    (hn : ComputableTidilyInPolyTime n input encUnary)
    (hs : ComputableTidilyInPolyTime s input encUnary)
    (hm : ComputableTidilyInPolyTime m input encUnary)
    (ha : ComputableTidilyInPolyTime a input enc)
    (hz : ComputableTidilyInPolyTime z input encBits)
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hcoins : ComputableTidilyInPolyTime coins input (encPair encBits (encList encBits))) :
    IsPPTOn input (encPair encBits (encPair encUnary encBits))
      (fun c => runTwoRound
        (honestReply1 generator (m c) (φ c) (coins c))
        (honestReply2 (s c) (φ c) (coins c))
        (Vstar (n c) (a c) (z c))
        (0, [false, false, false])) := by
  refine isPPTOn_runTwoRound hV
    (prepare := fun c => (n c, a c, z c))
    (reply1 := fun p => honestReply1 generator (m p.1) (φ p.1) (coins p.1) p.2)
    (reply2 := fun p => honestReply2 (s p.1) (φ p.1) (coins p.1) p.2)
    (bound := fun c => (coins c).1.length * m c + (coins c).1.length * (s c + 1))
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (fun c q => by dsimp only [honestReply1]; exact (List.length_take_le _ _).trans (by omega))
    (fun c q => by dsimp only [honestReply2]; rw [length_proverReply2_any]; omega)

theorem isPPTOn_gmwInteract {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ} {f : α → CNF ℕ}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    (hg : ComputableTidilyInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length)
    (hf : ComputableTidilyInPolyTime f enc encCNF)
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun p => Vstar p.1 p.2.1 p.2.2)) :
    IsPPTOn (encPair encUnary (encPair enc (encPair encBits encBits))) encBits
      (fun p : ℕ × α × List Bool × List Bool =>
        gmwInteract generator (p.1 + 7) (length (p.1 + 7)) (f p.2.1) p.2.2.1
          (Vstar p.1 p.2.1 p.2.2.2)) := by
  have hlength : ComputableTidilyInPolyTime length encUnary encUnary := by
    have h : length = fun n => (generator (List.replicate n true)).length := by
      funext n
      rw [hlen, List.length_replicate]
    rw [h]
    fun_prop
  dsimp only [gmwInteract, sampleHonestCoins]
  ppt

end GMW

/-! ## Public Zero-Knowledge Proof API -/

/-- A computational zero-knowledge interactive proof system for a language `A : Set α` (with
instance encoding `enc : α ↪ List Bool`), indexed by a security parameter `n : ℕ` [Goldreich,
Micali, and Wigderson][GoldreichMicaliWigderson1991].

* `verifier n a`: the honest verifier's interactive program on security parameter `n` and
  instance `a`, certified uniform strict oracle PPT in `(1^n, a)` by `isOraclePPT_verifier`.
* `prover n a w`: the honest prover strategy on security parameter `n`, instance `a`, and
  witness `w`, certified efficient by `interact`, `eval_interact`, and `isPPT_interact`.
* `isWitness a w`: the polynomial-time witness check characterizing membership in `A`
  (`mem_iff_exists_witness`).
* `complete` and `sound`: completeness `1` for valid witnesses and soundness error at most `1 / 3`
  against all computationally unbounded stateful provers `P : Prover Unit`.
* `zero_knowledge`: for every uniform strict oracle PPT malicious verifier `Vstar` (taking
  security parameter `n`, instance `a`, and auxiliary input `z`), there is a uniform strict PPT
  simulator `S` (taking `(1^n, a, z)` without any witness) whose output ensemble is
  computationally indistinguishable from the real interaction output across all polynomial-time
  families of instances, valid witnesses, and auxiliary inputs. -/
structure ZeroKnowledgeProof {α : Type} (enc : α ↪ List Bool) (A : Set α) where
  /-- The honest verifier, indexed by security parameter `n` and instance `a`. -/
  verifier : ℕ → α → WordOracleComp Unit Bool
  /-- The honest prover strategy, taking security parameter `n`, instance `a`, and witness `w`. -/
  prover : ℕ → α → List Bool → Prover Unit
  /-- The polynomial-time witness check used by the honest prover. -/
  isWitness : α → List Bool → Bool
  /-- `isWitness` is computable in polynomial time. -/
  polyTime_isWitness :
    ComputableTidilyInPolyTime (fun p : α × List Bool => isWitness p.1 p.2)
      (encPair enc encBits) encBool
  /-- `a ∈ A` if and only if some witness `w` satisfies `isWitness a w = true`. -/
  mem_iff_exists_witness : ∀ a, a ∈ A ↔ ∃ w, isWitness a w = true
  /-- The honest verifier is uniform strict oracle PPT in `(1^n, a)`. -/
  isOraclePPT_verifier :
    IsOraclePPTOn (encPair encUnary enc) encBool (fun p : ℕ × α => verifier p.1 p.2)
  /-- The PPT program realizing the honest prover's interaction with a verifier program. -/
  interact : ℕ → α → List Bool → WordOracleComp Unit (List Bool) → ProbComp (List Bool)
  /-- `interact` has the exact output distribution of `prover.run`. -/
  eval_interact : ∀ n a w prog,
    ProbComp.eval (interact n a w prog) =
      ((prover n a w).run prog (prover n a w).init).map Prod.fst
  /-- Running any uniform strict oracle PPT verifier against the honest prover is uniform strict
  PPT in `(1^n, a, w, z)`. -/
  isPPT_interact :
    ∀ Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool),
      IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
        (fun p : ℕ × α × List Bool => Vstar p.1 p.2.1 p.2.2) →
      IsPPTOn (encPair encUnary (encPair enc (encPair encBits encBits))) encBits
        (fun p : ℕ × α × List Bool × List Bool =>
          interact p.1 p.2.1 p.2.2.1 (Vstar p.1 p.2.1 p.2.2.2))
  /-- Perfect completeness: for every valid witness `w` of `a`, the honest prover convinces the
  honest verifier with probability `1`. -/
  complete : ∀ n a w, isWitness a w = true → acceptProb (verifier n a) (prover n a w) = 1
  /-- Soundness: for every `a ∉ A` and every computationally unbounded stateful prover `P`, the
  verifier accepts with probability at most `1 / 3`. -/
  sound : ∀ n, ∀ a ∉ A, ∀ P : Prover Unit, acceptProb (verifier n a) P ≤ 1 / 3
  /-- Computational zero-knowledge with auxiliary input against all uniform strict oracle PPT
  malicious verifiers. -/
  zero_knowledge :
    ∀ Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool),
      IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
        (fun p : ℕ × α × List Bool => Vstar p.1 p.2.1 p.2.2) →
      ∃ S : ℕ → α → List Bool → ProbComp (List Bool),
        IsPPTOn (encPair encUnary (encPair enc encBits)) encBits
          (fun p : ℕ × α × List Bool => S p.1 p.2.1 p.2.2) ∧
        ∀ (a : ℕ → α) (w z : ℕ → List Bool),
          ComputableTidilyInPolyTime a encUnary enc →
          ComputableTidilyInPolyTime w encUnary encBits →
          ComputableTidilyInPolyTime z encUnary encBits →
          (∀ n, isWitness (a n) (w n) = true) →
          ComputationallyIndistinguishable
            (fun n => ((prover n (a n) (w n)).run (Vstar n (a n) (z n))
              (prover n (a n) (w n)).init).map Prod.fst)
            (fun n => ProbComp.eval (S n (a n) (z n)))

namespace ZeroKnowledgeProof

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- At every security parameter `n`, the honest verifier of a zero-knowledge proof system is an
interactive proof for `A` with completeness `2 / 3` and soundness `1 / 3`. -/
theorem isInteractiveProof (zk : ZeroKnowledgeProof enc A) (n : ℕ) :
    IsInteractiveProof (zk.verifier n) A (2 / 3) (1 / 3) where
  complete a ha := by
    obtain ⟨w, hw⟩ := (zk.mem_iff_exists_witness a).mp ha
    refine ⟨zk.prover n a w, ?_⟩
    rw [zk.complete n a w hw]
    exact ENNReal.div_le_of_le_mul (by norm_num)
  sound a ha P := zk.sound n a ha P

/-- Every language with a zero-knowledge interactive proof system belongs to `IP`. -/
theorem mem_IP (zk : ZeroKnowledgeProof enc A) : A ∈ IP enc := by
  refine ⟨zk.verifier 0, ?_, zk.isInteractiveProof 0⟩
  have h := zk.isOraclePPT_verifier
  fun_prop

/-- Fixed-instance computational zero-knowledge: for every fixed instance `a` and valid witness `w`
(`zk.isWitness a w = true`), and every polynomial-time auxiliary input family `z : ℕ → List Bool`,
the real interaction output and simulator output are computationally indistinguishable. -/
theorem zero_knowledge_const (zk : ZeroKnowledgeProof enc A)
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun p : ℕ × α × List Bool => Vstar p.1 p.2.1 p.2.2)) :
    ∃ S : ℕ → α → List Bool → ProbComp (List Bool),
      IsPPTOn (encPair encUnary (encPair enc encBits)) encBits
        (fun p : ℕ × α × List Bool => S p.1 p.2.1 p.2.2) ∧
      ∀ a w (z : ℕ → List Bool),
        zk.isWitness a w = true →
        ComputableTidilyInPolyTime z encUnary encBits →
        ComputationallyIndistinguishable
          (fun n => ((zk.prover n a w).run (Vstar n a (z n))
            (zk.prover n a w).init).map Prod.fst)
          (fun n => ProbComp.eval (S n a (z n))) := by
  obtain ⟨S, hS_ppt, hS_zk⟩ := zk.zero_knowledge Vstar hV
  exact ⟨S, hS_ppt, fun a w z hw hz =>
    hS_zk (fun _ => a) (fun _ => w) z (const a) (const w) hz (fun _ => hw)⟩

end ZeroKnowledgeProof

/-- Construct the Goldreich–Micali–Wigderson zero-knowledge proof system for any language `A` with
a polynomial-time many-one reduction `f : α → CNF ℕ` to `ThreeSAT`, using a pseudorandom generator
with stretch at least `3 * k + 1`. -/
noncomputable def PseudorandomGenerator.zeroKnowledgeProofOfReduction
    {α : Type} {enc : α ↪ List Bool} {A : Set α}
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    (hstretch : ∀ k, 3 * k + 1 ≤ length k)
    {f : α → CNF ℕ} (hf : ComputableTidilyInPolyTime f enc encCNF)
    (hred : ∀ a, a ∈ A ↔ f a ∈ ThreeSAT) :
    ZeroKnowledgeProof enc A where
  verifier := GMW.gmwVerifier generator length f
  prover n a w := GMW.gmwProver generator (n + 7) (length (n + 7)) (f a) w
  isWitness a w := ThreeSAT.verifier (f a, w)
  polyTime_isWitness := by fun_prop
  mem_iff_exists_witness a := by
    rw [hred a]
    refine ⟨fun ha => ?_, fun ⟨w, hw⟩ => ?_⟩
    · obtain ⟨w, _, hw⟩ := (ThreeSAT.isVerifier (f a)).mp ha
      exact ⟨w, hw⟩
    · simp only [ThreeSAT.verifier, SAT.verifier, Bool.and_eq_true, List.all_eq_true,
        decide_eq_true_eq] at hw
      exact ⟨hw.1, SAT.assignment (f a) w, hw.2⟩
  isOraclePPT_verifier := GMW.isOraclePPTOn_gmwVerifier hG.polyTime hG.length_eq hf
  interact n a w prog := GMW.gmwInteract generator (n + 7) (length (n + 7)) (f a) w prog
  eval_interact n a w prog := GMW.eval_gmwInteract generator (n + 7) (length (n + 7)) (f a) w prog
  isPPT_interact _ hV := GMW.isPPTOn_gmwInteract hG.polyTime hG.length_eq hf hV
  complete n a _ hw := GMW.acceptProb_gmwVerifier_gmwProver hG.length_eq f n a hw
  sound n a ha P :=
    GMW.acceptProb_gmwVerifier_le hG.length_eq hstretch f n a (mt (hred a).mpr ha) P
  zero_knowledge Vstar hV :=
    ⟨GMW.gmwSimulator generator length f Vstar,
      GMW.isPPTOn_gmwSimulator hG.polyTime hG.length_eq hf hV,
      fun _ _ _ ha hw_comp hz hw_sat =>
        GMW.gmwView_indistinguishable_gmwSimulator hG hf hV ha hw_comp hz hw_sat⟩

/-- The Goldreich–Micali–Wigderson computational zero-knowledge proof system for `ThreeSAT`, built
from any pseudorandom generator with stretch at least `3 * k + 1`. -/
noncomputable def PseudorandomGenerator.zeroKnowledgeProofThreeSAT
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    (hstretch : ∀ k, 3 * k + 1 ≤ length k) :
    ZeroKnowledgeProof encCNF ThreeSAT :=
  hG.zeroKnowledgeProofOfReduction hstretch (by fun_prop) (fun _ => Iff.rfl)

/-- **Goldreich–Micali–Wigderson theorem (from a pseudorandom generator).** Given a pseudorandom
generator with stretch at least `3 * k + 1` (such as `fun k => 3 * k + 1`), every language
`A ∈ NP enc` has a computational zero-knowledge interactive proof system
[Goldreich, Micali, and Wigderson][GoldreichMicaliWigderson1991]. -/
theorem PseudorandomGenerator.exists_zeroKnowledgeProof_of_mem_NP
    {α : Type} {enc : α ↪ List Bool} {A : Set α}
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    (hstretch : ∀ k, 3 * k + 1 ≤ length k)
    (hA : A ∈ NP enc) :
    Nonempty (ZeroKnowledgeProof enc A) := by
  obtain ⟨f, hf, hred⟩ := ThreeSAT_npHard enc A hA
  exact ⟨hG.zeroKnowledgeProofOfReduction hstretch hf hred⟩

/-- **Goldreich–Micali–Wigderson theorem (from a one-way function).** If a one-way function exists,
then every language `A ∈ NP enc` has a computational zero-knowledge interactive proof system
[Goldreich, Micali, and Wigderson][GoldreichMicaliWigderson1991]. -/
theorem OneWay.exists_zeroKnowledgeProof_of_mem_NP
    {α : Type} {enc : α ↪ List Bool} {A : Set α}
    {f : List Bool → List Bool} (hf : OneWay f) (hA : A ∈ NP enc) :
    Nonempty (ZeroKnowledgeProof enc A) := by
  obtain ⟨G, hG⟩ := hf.exists_pseudorandomGenerator_three_mul
  exact hG.exists_zeroKnowledgeProof_of_mem_NP (fun _ => le_rfl) hA

end Cslib.Crypto
