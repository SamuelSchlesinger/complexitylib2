/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (spike for #739, not for merge)

public import Complexity.Computability.WordRAM.Native
public import Complexity.Computability.WordRAM.Function
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Tactic.PolyTime.Init

/-!
# Word-RAM polynomial time implies Turing-machine polynomial time (spike, #739)

A fixed word-RAM program that runs in polynomially many instructions at every admissible word
size, on inputs whose word encoding is computable in polynomial time from a bit-string encoding,
gives a multi-tape Turing machine computing the same function in polynomial time
(`Turing.MultiTapeTM.ComputableInPolyTime`).

The simulating machine

* computes the word list `encode a` and stores it as a sparse memory `0 ↦ n, i + 1 ↦ xᵢ`
  (initialization);
* chooses a word size `w = Q (|encIn a|)` for a fixed polynomial `Q`, large enough for the
  logarithmic threshold and for every input word (charged configuration selection, unary);
* runs the existing clocked finite-state simulator `GenericRAM.FiniteState.run` for
  `S (|encIn a|)` steps, where `S` bounds the RAM time (clocked iteration);
* extracts the halted value (output decoding).

Each simulated step costs time polynomial in `w` and in the number of stored cells, since all
registers and memory cells stay below `2 ^ w` (`FiniteState.WordBounded`). Cost model: unit-cost
instructions on `w`-bit words with `w` polynomial in the input length, as in the trans-dichotomous
word RAM; this is the regime of the invariance thesis of Slot and van Emde Boas.

## Main definitions

* `Cslib.WordRAM.Basis.PolyTimeOps`: every checked operation of a basis is polynomial-time on
  a unary word size and binary operands (plain statement).
* `Cslib.WordRAM.initMemory`: the sparse memory of `State.init`.

## Main results

* `Cslib.WordRAM.Program.ComputesInTime.computableInPolyTime`: RAM ⇒ TM for a fixed program.
* `Cslib.WordRAM.UniformComputableInPolyTime.computableInPolyTime`: the same for the library's
  uniform polynomial-time predicate.
* `Cslib.WordRAM.Basis.polyTimeOps_additive`, `Cslib.WordRAM.Basis.polyTimeOps_arithmetic`:
  primitive obligations for the additive and arithmetic bases.

## References

* [S. A. Cook and R. A. Reckhow, *Time bounded random access machines*][CookReckhow1973]
-/

@[expose] public section

namespace Cslib.WordRAM

open Turing.MultiTapeTM

/-! ## Primitive operations -/

/-- The encodings used to simulate a word RAM: binary words and addresses, unary word size. -/
abbrev wordEncoding (B : Basis) : B.genericModel.Encoding := ⟨encNat, encNat, encUnary⟩

/-- Every operation of the basis, followed by the machine's word-fit check, is computable in
polynomial time from a unary word size and binary operands. -/
def Basis.PolyTimeOps (B : Basis) : Prop :=
  ∀ f : B.Op, Turing.MultiTapeTM.ComputableInPolyTime (B.genericModel.checkedOp f)
    (encPair encUnary (encPi encNat)) (encOption encNat)

section Primitives

open ComputableTidilyInPolyTime

/-- A checked binary operation from a polynomial-time binary implementation of its value. -/
private theorem checkedBin_polyTime {g : ℕ → ℕ → ℕ}
    (hg : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => g p.1 p.2) (encPair encNat encNat) encNat) :
    ComputableTidilyInPolyTime
      (fun p : ℕ × (Fin 2 → ℕ) =>
        if decide (Fits p.1 (g (p.2 0) (p.2 1))) then some (g (p.2 0) (p.2 1)) else none)
      (encPair encUnary (encPi encNat)) (encOption encNat) := by
  have hx := (pi_apply encNat (0 : Fin 2)).comp (snd encUnary (encPi encNat))
  have hy := (pi_apply encNat (1 : Fin 2)).comp (snd encUnary (encPi encNat))
  have hv := hg.comp (hx.prod hy)
  have hpow := binary_two_pow.comp (fst encUnary (encPi encNat (Index := Fin 2)))
  simp only [decide_eq_true_eq, fits_iff]
  exact (binary_lt.comp (hv.prod hpow)).ite_decide ((optionSome encNat).comp hv) (const none)

/-- The checked binary operations of the standard basis with a binary implementation. -/
private theorem checkedStandardBin_polyTime (f : BinOp)
    (hf : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => f.eval p.1 p.2)
      (encPair encNat encNat) encNat) :
    ComputableTidilyInPolyTime (Basis.standard.genericModel.checkedOp (.bin f))
      (encPair encUnary (encPi encNat)) (encOption encNat) := by
  have h := checkedBin_polyTime hf
  have heq : Basis.standard.genericModel.checkedOp (.bin f) = fun p : ℕ × (Fin 2 → ℕ) =>
      if decide (Fits p.1 (f.eval (p.2 0) (p.2 1))) then some (f.eval (p.2 0) (p.2 1))
      else none := by
    funext p
    simp only [GenericRAM.Model.checkedOp, Basis.genericModel, StandardOp.eval, bind,
      Option.bind_some, decide_eq_true_eq]
  rw [heq]
  exact h

/-- Reading the word size: a unary width converted to binary always fits. -/
private theorem checkedWidth_polyTime :
    ComputableTidilyInPolyTime (Basis.standard.genericModel.checkedOp .width)
      (encPair encUnary (encPi encNat)) (encOption encNat) := by
  have heq : Basis.standard.genericModel.checkedOp .width =
      fun p : ℕ × (Fin 0 → ℕ) => some p.1 := by
    funext p
    simp only [GenericRAM.Model.checkedOp, Basis.genericModel, StandardOp.eval, bind,
      Option.bind_some, decide_eq_true_eq, fits_self, ite_true]
  rw [heq]
  exact (optionSome encNat).comp (unary_to_binary.comp (fst encUnary (encPi encNat)))

/-- The arithmetic operations of the standard basis and the word size are polynomial-time. -/
theorem Basis.standard_checkedOp_polyTime (f : StandardOp)
    (hf : f ∈ [.bin .add, .bin .sub, .bin .mul, .bin .div, .bin .mod, .width]) :
    Turing.MultiTapeTM.ComputableInPolyTime (Basis.standard.genericModel.checkedOp f)
      (encPair encUnary (encPi encNat)) (encOption encNat) := by
  refine .of_tidy ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkedStandardBin_polyTime .add binary_add
  · exact checkedStandardBin_polyTime .sub binary_sub
  · exact checkedStandardBin_polyTime .mul binary_mul
  · exact checkedStandardBin_polyTime .div binary_div
  · exact checkedStandardBin_polyTime .mod binary_mod
  · exact checkedWidth_polyTime

/-- A sub-basis inherits the primitive obligation for its own operations. -/
theorem Basis.PolyTimeOps.restrict {B : Basis} {P : B.Op → Prop}
    (h : ∀ f, P f → Turing.MultiTapeTM.ComputableInPolyTime (B.genericModel.checkedOp f)
      (encPair encUnary (encPi encNat)) (encOption encNat)) :
    (B.restrict P).PolyTimeOps :=
  fun f => h f.1 f.2

/-- Addition and truncated subtraction meet the primitive obligation. -/
theorem Basis.polyTimeOps_additive : Basis.additive.PolyTimeOps :=
  Basis.PolyTimeOps.restrict fun f hf => Basis.standard_checkedOp_polyTime f (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf ⊢
    tauto)

/-- The arithmetic basis meets the primitive obligation. -/
theorem Basis.polyTimeOps_arithmetic : Basis.arithmetic.PolyTimeOps :=
  Basis.PolyTimeOps.restrict fun f hf => Basis.standard_checkedOp_polyTime f (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf ⊢
    tauto)

/-- **Spike gap.** The standard basis also needs bitwise `and`, `or`, `xor` on binary naturals
(absent from the machine library; each a bitwise zip of the two binary words, roughly 100 lines)
and checked shifts. A checked shift must compare the shift amount with the unary width before
materializing `2 ^ y`, since `y` may be exponential in the input length (roughly 150 lines). -/
theorem Basis.polyTimeOps_standard : Basis.standard.PolyTimeOps := by
  intro f
  by_cases hf : f ∈ [.bin .add, .bin .sub, .bin .mul, .bin .div, .bin .mod, .width]
  · exact Basis.standard_checkedOp_polyTime f hf
  · sorry

/-! ### Internal: the native primitive bundle -/

private theorem checkedConstant_polyTime (B : Basis) (c : ℕ) :
    ComputableTidilyInPolyTime (B.genericModel.checkedConstant c) encUnary (encOption encNat) := by
  have heq : B.genericModel.checkedConstant c = fun w => if c < 2 ^ w then some c else none := by
    funext w
    simp only [GenericRAM.Model.checkedConstant, Basis.genericModel, bind, Option.bind_some,
      decide_eq_true_eq, fits_iff]
  rw [heq]
  exact (binary_lt.comp ((const c).prod binary_two_pow)).ite_decide (const (some c)) (const none)

private theorem test_polyTime (B : Basis) (t : Bool) :
    ComputableTidilyInPolyTime (fun p : ℕ × (Fin 2 → ℕ) => B.genericModel.evalTest p.1 t p.2)
      (encPair encUnary (encPi encNat)) (encOption encBool) := by
  have hx := (pi_apply encNat (0 : Fin 2)).comp (snd encUnary (encPi encNat))
  have hy := (pi_apply encNat (1 : Fin 2)).comp (snd encUnary (encPi encNat))
  cases t
  · exact (optionSome encBool).comp ((decide_eq encNat).comp (hx.prod hy))
  · exact (optionSome encBool).comp (binary_lt.comp (hx.prod hy))

/-- The native primitive bundle of a basis meeting the primitive obligation. -/
private noncomputable def nativePrimitives {B : Basis} (hB : B.PolyTimeOps) :
    B.genericModel.NativePrimitives (wordEncoding B) where
  constant c := .ofPolyTime (checkedConstant_polyTime B c)
  operation f := .ofPolyTime (hB f).tidy
  test t := .ofPolyTime (test_polyTime B t)
  address := .ofPolyTime ((optionSome encNat).comp (snd encUnary encNat))
  validMove := .ofPolyTime (const true)
  validPC := .ofPolyTime (const true)

private theorem nativePrimitives_isPolynomial {B : Basis} (hB : B.PolyTimeOps) :
    (nativePrimitives hB).IsPolynomial where
  constant c := GenericRAM.NativeCertificate.ofPolyTime_isPolynomial
    (checkedConstant_polyTime B c)
  operation f := GenericRAM.NativeCertificate.ofPolyTime_isPolynomial (hB f).tidy
  test t := GenericRAM.NativeCertificate.ofPolyTime_isPolynomial (test_polyTime B t)
  address := GenericRAM.NativeCertificate.ofPolyTime_isPolynomial
    ((optionSome encNat).comp (snd encUnary encNat))
  validMove := GenericRAM.NativeCertificate.ofPolyTime_isPolynomial (const true)
  validPC := GenericRAM.NativeCertificate.ofPolyTime_isPolynomial (const true)

end Primitives

/-! ## Word bounds on finite simulation states -/

section Invariant

open GenericRAM GenericRAM.FiniteState

variable {B : Basis} {r w L : ℕ}

/-- The jump or branch target of an instruction, and `0` otherwise. -/
def instrTarget : GenericRAM.Instr B.genericModel r → ℕ
  | .jump t => t
  | .branch _ t => t
  | _ => 0

/-- An upper bound on every control label a run from label `0` can reach. -/
def labelBound (p : GenericRAM.Program B.genericModel r) : ℕ :=
  p.length + (p.map instrTarget).sum

/-- Registers, memory default and stored cells (addresses and values) are `w`-bit words. -/
structure DataBounded (w : ℕ) (s : FiniteState B.genericModel r) : Prop where
  regs_lt : ∀ i, s.regs i < 2 ^ w
  default_lt : s.default < 2 ^ w
  entries_lt : ∀ e ∈ SparseMemory.entries s.memory, e.1 < 2 ^ w ∧ e.2 < 2 ^ w

namespace DataBounded

variable {s t : FiniteState B.genericModel r}

theorem read_lt (h : DataBounded w s) (a : ℕ) :
    SparseMemory.read s.default a s.memory < 2 ^ w := by
  rw [SparseMemory.read_eq_find]
  cases hf : (SparseMemory.entries s.memory).find? (fun e => decide (a = e.1)) with
  | none => simpa using h.default_lt
  | some e => simpa using (h.entries_lt e (List.mem_of_find?_eq_some hf)).2

theorem set (h : DataBounded w s) (d : Fin r) {v : ℕ} (hv : v < 2 ^ w) :
    DataBounded w (s.set d v) where
  regs_lt i := by
    simp only [FiniteState.set]
    rcases eq_or_ne i d with rfl | hi
    · simpa using hv
    · simpa [Function.update_of_ne hi] using h.regs_lt i
  default_lt := h.default_lt
  entries_lt := h.entries_lt

theorem write (h : DataBounded w s) {a v : ℕ} (ha : a < 2 ^ w) (hv : v < 2 ^ w) :
    DataBounded w (s.write a v) where
  regs_lt := h.regs_lt
  default_lt := h.default_lt
  entries_lt e he := by
    rcases SparseMemory.mem_entries_insert.mp he with rfl | ⟨he, -⟩
    · exact ⟨ha, hv⟩
    · exact h.entries_lt e he

theorem withPC (h : DataBounded w s) (pc : ℕ) : DataBounded w { s with pc := pc } where
  regs_lt := h.regs_lt
  default_lt := h.default_lt
  entries_lt := h.entries_lt

theorem lt_of_checkedConstant {c v : ℕ} (h : B.genericModel.checkedConstant c w = some v) :
    v < 2 ^ w := by
  simp only [GenericRAM.Model.checkedConstant, Basis.genericModel, bind, Option.bind_some] at h
  split at h
  · next hc => cases h; simpa [fits_iff] using hc
  · cases h

theorem lt_of_checkedOp {f : B.Op} {args : Fin (B.Arity f) → ℕ} {v : ℕ}
    (h : B.genericModel.checkedOp f (w, args) = some v) : v < 2 ^ w := by
  simp only [GenericRAM.Model.checkedOp, Basis.genericModel, bind, Option.bind_eq_some_iff] at h
  obtain ⟨u, -, hu⟩ := h
  split at hu
  · next hc => cases hu; simpa [fits_iff] using hc
  · cases hu

/-- A data operation keeps every register and stored cell a word. -/
theorem evalOp (h : DataBounded w s) {o : GenericRAM.Op B.genericModel r}
    (ho : FiniteState.evalOp w o s = some t) : DataBounded w t := by
  cases o with
  | const d c =>
    simp only [FiniteState.evalOp, Option.map_eq_some_iff] at ho
    obtain ⟨v, hv, rfl⟩ := ho
    exact h.set d (lt_of_checkedConstant hv)
  | copy d src =>
    simp only [FiniteState.evalOp, FiniteState.move, Basis.genericModel, ite_true,
      Option.some.injEq] at ho
    subst ho
    exact h.set d (h.regs_lt src)
  | alu f d args =>
    simp only [FiniteState.evalOp, Option.map_eq_some_iff] at ho
    obtain ⟨v, hv, rfl⟩ := ho
    exact h.set d (lt_of_checkedOp hv)
  | load d a =>
    simp only [FiniteState.evalOp, FiniteState.move, Basis.genericModel, bind,
      Option.bind_some, ite_true, Option.some.injEq] at ho
    subst ho
    exact h.set d (h.read_lt _)
  | store a src =>
    simp only [FiniteState.evalOp, Basis.genericModel, bind, Option.bind_some, ite_true,
      Option.some.injEq] at ho
    subst ho
    exact h.write (h.regs_lt a) (h.regs_lt src)

end DataBounded

private theorem le_sum_of_mem {p : GenericRAM.Program B.genericModel r}
    {i : GenericRAM.Instr B.genericModel r} (hi : i ∈ p) :
    instrTarget i ≤ (p.map instrTarget).sum :=
  List.le_sum_of_mem (List.mem_map_of_mem hi)

/-- A continuing step keeps word bounds and stays below the label bound. -/
theorem DataBounded.step {p : GenericRAM.Program B.genericModel r}
    {s t : FiniteState B.genericModel r} (h : DataBounded w s)
    (hs : FiniteState.step w p s = some (.inl t)) :
    DataBounded w t ∧ t.pc ≤ labelBound p := by
  unfold FiniteState.step at hs
  simp only [Basis.genericModel, ite_true] at hs
  rw [dispatch_eq_getElem? w p 0 s (Nat.zero_le _), Nat.sub_zero] at hs
  simp only [bind, Option.bind_eq_some_iff] at hs
  obtain ⟨i, hi, hs⟩ := hs
  have hmem : i ∈ p := List.mem_of_getElem? hi
  have hlt : s.pc < p.length := (List.getElem?_eq_some_iff.mp hi).1
  have htarget := le_sum_of_mem hmem
  cases i with
  | op o =>
    simp only [evalInstr, bind, Option.bind_eq_some_iff] at hs
    obtain ⟨u, ho, hr⟩ := hs
    simp only [resume, Basis.genericModel, ite_true, Option.some.injEq, Sum.inl.injEq] at hr
    subst hr
    exact ⟨(h.evalOp ho).withPC _, by simp [labelBound]; omega⟩
  | jump target =>
    simp only [evalInstr, resume, Basis.genericModel, ite_true, Option.some.injEq,
      Sum.inl.injEq] at hs
    subst hs
    exact ⟨h.withPC _, by simp only [labelBound, instrTarget] at htarget ⊢; omega⟩
  | branch c target =>
    cases c with
    | test f args =>
      simp only [evalInstr, bind, Option.bind_eq_some_iff] at hs
      obtain ⟨b, -, hr⟩ := hs
      simp only [resume, Basis.genericModel, ite_true, Option.some.injEq, Sum.inl.injEq] at hr
      subst hr
      refine ⟨h.withPC _, ?_⟩
      simp only [labelBound, instrTarget] at htarget ⊢
      split <;> omega
  | halt idx =>
    simp only [evalInstr, Basis.genericModel, ite_true] at hs
    cases hs

/-- A halting step returns a word. -/
theorem DataBounded.step_halt {p : GenericRAM.Program B.genericModel r}
    {s : FiniteState B.genericModel r} {v : ℕ} (h : DataBounded w s)
    (hs : FiniteState.step w p s = some (.inr v)) : v < 2 ^ w := by
  unfold FiniteState.step at hs
  simp only [Basis.genericModel, ite_true] at hs
  rw [dispatch_eq_getElem? w p 0 s (Nat.zero_le _), Nat.sub_zero] at hs
  simp only [bind, Option.bind_eq_some_iff] at hs
  obtain ⟨i, -, hs⟩ := hs
  cases i with
  | op o =>
    simp only [evalInstr, bind, Option.bind_eq_some_iff] at hs
    obtain ⟨u, -, hr⟩ := hs
    simp [resume, Basis.genericModel] at hr
  | jump target => simp [evalInstr, resume, Basis.genericModel] at hs
  | branch c target =>
    cases c with
    | test f args =>
      simp only [evalInstr, bind, Option.bind_eq_some_iff] at hs
      obtain ⟨b, -, hr⟩ := hs
      simp [resume, Basis.genericModel] at hr
  | halt idx =>
    simp only [evalInstr, Basis.genericModel, ite_true, Option.some.injEq, Sum.inr.injEq] at hs
    subst hs
    exact h.regs_lt idx

/-- Every outcome of a clocked run from a word-bounded state is word-bounded: continuing states
keep their words and labels, halted values are words. -/
theorem DataBounded.run {p : GenericRAM.Program B.genericModel r}
    {s : FiniteState B.genericModel r} (h : DataBounded w s) (hpc : s.pc ≤ labelBound p) :
    ∀ n, (∀ t, FiniteState.run w p n s = some (.inl t) → DataBounded w t ∧ t.pc ≤ labelBound p) ∧
      (∀ v, FiniteState.run w p n s = some (.inr v) → v < 2 ^ w) := by
  intro n
  induction n generalizing s with
  | zero =>
    refine ⟨fun t ht => ?_, fun v hv => by simp at hv⟩
    simp only [FiniteState.run_zero, Option.some.injEq, Sum.inl.injEq] at ht
    subst ht
    exact ⟨h, hpc⟩
  | succ n ih =>
    rw [FiniteState.run_succ]
    cases hs : FiniteState.step w p s with
    | none => simp
    | some u =>
      cases u with
      | inl u =>
        obtain ⟨hu, hupc⟩ := h.step hs
        exact ih hu hupc
      | inr v =>
        refine ⟨fun t ht => by simp at ht, fun v' hv => ?_⟩
        simp only [Option.some.injEq, Sum.inr.injEq] at hv
        subst hv
        exact h.step_halt hs

private theorem listMax_le {α : Type*} {f : α → ℕ} {l : List α} {m : ℕ}
    (h : ∀ a ∈ l, f a ≤ m) : listMax f l ≤ m := by
  induction l with
  | nil => simp [listMax]
  | cons a l ih =>
    simp only [listMax, List.map_cons, List.foldr_cons] at ih ⊢
    exact max_le (h a (List.mem_cons_self ..)) (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

private theorem length_encNat_le_of_lt {v : ℕ} (hv : v < 2 ^ w) : (encNat v).length ≤ w := by
  rw [encNat_apply, Nat.size_eq_bits_len]
  exact Nat.size_le.mpr hv

/-- A bound on the encoded outcome of a simulation step: `r` registers, labels at most `L`,
`w`-bit words and at most `E` stored cells. -/
def stateBound (r L w E : ℕ) : ℕ :=
  2 * (encNat L).length + 2 * r * (2 * w + 1) + 2 * w + E * (6 * w + 3) + w + 5

/-- Encoded outcomes along a clocked run from a word-bounded state are bounded by `stateBound`,
with one stored cell per step. -/
theorem DataBounded.length_resultEncoding_run_le {p : GenericRAM.Program B.genericModel r}
    {s : FiniteState B.genericModel r} (h : DataBounded w s) (hpc : s.pc ≤ labelBound p)
    (n : ℕ) :
    (resultEncoding (wordEncoding B) (FiniteState.run w p n s)).length ≤
      stateBound r (labelBound p) w ((SparseMemory.entries s.memory).length + n) := by
  obtain ⟨hinl, hinr⟩ := h.run hpc n
  cases hrun : FiniteState.run w p n s with
  | none => simp [resultEncoding, encOption_none]
  | some u =>
    cases u with
    | inr v =>
      have hv := length_encNat_le_of_lt (hinr v hrun)
      simp only [resultEncoding, encOption_some, encSum_inr, List.length_cons, wordEncoding,
        stateBound]
      omega
    | inl t =>
      obtain ⟨ht, htpc⟩ := hinl t hrun
      have hE := length_entries_run_le hrun
      have hlen := FiniteState.length_encoding_le (wordEncoding B) t
        (bound := w) fun i => length_encNat_le_of_lt (ht.regs_lt i)
      have hpcl : (encNat t.pc).length ≤ (encNat (labelBound p)).length := by
        simp only [encNat_apply, Nat.size_eq_bits_len]
        exact Nat.size_le_size htpc
      have hdef : ((wordEncoding B).value t.default).length ≤ w :=
        length_encNat_le_of_lt ht.default_lt
      have hkey : SparseMemory.maxKeyLength (wordEncoding B).address t.memory ≤ w :=
        listMax_le fun e he => length_encNat_le_of_lt (ht.entries_lt e he).1
      have hval : SparseMemory.maxValueLength (wordEncoding B).value t.memory ≤ w :=
        listMax_le fun e he => length_encNat_le_of_lt (ht.entries_lt e he).2
      have hmul : (SparseMemory.entries t.memory).length *
            (4 * SparseMemory.maxKeyLength (wordEncoding B).address t.memory +
              2 * SparseMemory.maxValueLength (wordEncoding B).value t.memory + 3) ≤
          ((SparseMemory.entries s.memory).length + n) * (6 * w + 3) :=
        Nat.mul_le_mul hE (by omega)
      simp only [resultEncoding, encOption_some, encSum_inl, List.length_cons, stateBound]
      omega

end Invariant

/-! ## Initialization -/

section Init

open GenericRAM

/-- The stored cells of `State.init input`: the length at address `0`, word `i` at `i + 1`. -/
def initEntries (input : List ℕ) : List (ℕ × ℕ) :=
  (0, input.length) :: input.zipIdx.map fun e => (e.2 + 1, e.1)

private theorem keys_zipIdx (l : List ℕ) (n : ℕ) :
    ((l.zipIdx n).map fun e => (e.2 + 1, e.1)).map Prod.fst = List.range' (n + 1) l.length := by
  induction l generalizing n with
  | nil => rfl
  | cons v l ih =>
    simp only [List.zipIdx_cons, List.map_cons, List.length_cons, List.range'_succ, ih]

private theorem nodup_keys_initEntries (input : List ℕ) :
    ((initEntries input).map Prod.fst).Nodup := by
  simp only [initEntries, List.map_cons, keys_zipIdx]
  refine List.nodup_cons.mpr ⟨?_, List.nodup_range'⟩
  simp

/-- The sparse memory of `State.init input`. -/
def initMemory (input : List ℕ) : SparseMemory ℕ ℕ :=
  ⟨(initEntries input).map fun e => ⟨e.1, e.2⟩, by
    unfold List.NodupKeys List.keys
    simpa [List.map_map, Function.comp_def] using nodup_keys_initEntries input⟩

theorem entries_initMemory (input : List ℕ) :
    SparseMemory.entries (initMemory input) = initEntries input := by
  simp [SparseMemory.entries, initMemory, List.map_map, Function.comp_def]

private theorem find_zipIdx (l : List ℕ) (n a : ℕ) :
    (((l.zipIdx n).map fun e => (e.2 + 1, e.1)).find? (fun e => decide (a = e.1))).map
        Prod.snd = if n < a then l[a - n - 1]? else none := by
  induction l generalizing n with
  | nil => split <;> simp
  | cons v l ih =>
    simp only [List.zipIdx_cons, List.map_cons, List.find?_cons]
    by_cases ha : a = n + 1
    · subst ha
      simp
    · simp only [ha, decide_false]
      rw [ih]
      by_cases h1 : n + 1 < a
      · have he : a - n - 1 = a - (n + 1) - 1 + 1 := by omega
        simp [h1, show n < a by omega, he]
      · simp [h1, show ¬n < a by omega]

/-- The sparse memory denotes the input convention of `State.init`. -/
theorem read_initMemory (input : List ℕ) (a : ℕ) :
    SparseMemory.read 0 a (initMemory input) =
      if a = 0 then input.length else input.getD (a - 1) 0 := by
  rw [SparseMemory.read_eq_find, entries_initMemory, initEntries, List.find?_cons]
  rcases a with _ | a
  · simp
  · have h := find_zipIdx input 0 (a + 1)
    simp only [Nat.add_one_ne_zero, decide_false, ite_false, Nat.zero_lt_succ, ite_true,
      Nat.sub_zero, Nat.add_sub_cancel] at h ⊢
    rw [h, List.getD_eq_getElem?_getD]

/-- The initial finite state of a run on `input`. -/
def initState (B : Basis) (r : ℕ) (input : List ℕ) : FiniteState B.genericModel r :=
  FiniteState.initConst 0 0 (initMemory input)

/-- The initial finite state denotes `State.init`. -/
theorem denote_initState {B : Basis} {r : ℕ} (input : List ℕ) :
    (initState B r input).denote = (State.init input : State r).toGeneric B := by
  simp only [FiniteState.denote, initState, FiniteState.initConst, FiniteState.init,
    State.toGeneric, State.init, Data.toGeneric, Data.init]
  congr 2
  funext a
  exact read_initMemory input a

/-- From an input that fits, the initial state holds only words. -/
theorem dataBounded_initState {B : Basis} {r w : ℕ} {input : List ℕ}
    (h : InputFits w input) : DataBounded w (initState B r input) where
  regs_lt _ := Nat.two_pow_pos w
  default_lt := Nat.two_pow_pos w
  entries_lt e he := by
    simp only [initState, FiniteState.initConst, FiniteState.init, entries_initMemory,
      initEntries, List.mem_cons, List.mem_map] at he
    rcases he with rfl | ⟨⟨v, i⟩, hvi, rfl⟩
    · exact ⟨Nat.two_pow_pos w, h.1⟩
    · obtain ⟨hi, hv⟩ := List.mem_zipIdx' hvi
      refine ⟨lt_of_le_of_lt (show i + 1 ≤ input.length by omega) h.1, ?_⟩
      simpa [hv, fits_iff] using h.2 _ (List.getElem_mem hi)

theorem initState_pc {B : Basis} {r : ℕ} (input : List ℕ) : (initState B r input).pc = 0 := rfl

theorem length_entries_initState {B : Basis} {r : ℕ} (input : List ℕ) :
    (SparseMemory.entries (initState B r input).memory).length = input.length + 1 := by
  simp [initState, FiniteState.initConst, FiniteState.init, entries_initMemory, initEntries]

open ComputableTidilyInPolyTime in
/-- Building the initial memory is polynomial-time on framed lists of binary words. -/
theorem initMemory_polyTime :
    ComputableTidilyInPolyTime initMemory (encList encNat)
      (SparseMemory.encoding encNat encNat) := by
  have hlen : ComputableTidilyInPolyTime (fun l : List ℕ => l.length) (encList encNat) encNat :=
    unary_to_binary.comp (length_list encNat)
  have hstep : ComputableTidilyInPolyTime (fun e : ℕ × ℕ => (e.2 + 1, e.1))
      (encPair encNat encUnary) (encPair encNat encNat) :=
    (computableTidilyInPolyTime_succ.comp (unary_to_binary.comp (snd encNat encUnary))).prod
      (fst encNat encUnary)
  have hentries : ComputableTidilyInPolyTime initEntries (encList encNat)
      (encList (encPair encNat encNat)) :=
    cons' ((const 0).prod hlen)
      ((ComputableTidilyInPolyTime.map hstep).comp (ComputableTidilyInPolyTime.zipIdx encNat))
  exact hentries.of_enc_eq fun l => by
    simp only [SparseMemory.encoding_apply, entries_initMemory]

end Init

/-! ## Word RAM ⇒ Turing machine -/

section Main

open GenericRAM GenericRAM.NativeCertificate ComputableTidilyInPolyTime Polynomial

variable {B : Basis} {r : ℕ} {α : Type} {encIn : α ↪ List Bool}

/-- **Word-RAM polynomial time gives Turing-machine polynomial time.**

Let `p` be a fixed program over a basis whose checked operations are polynomial-time on binary
words (`Basis.PolyTimeOps`). Suppose that on every input `a` whose words fit, at every word size
above `logWidth k (size a)`, `p` halts with `f a` from `State.init (encode a)` within
`T (size a)` instructions, where `T` is polynomially bounded. If the word list `encode a` is
computable in polynomial time from the bit-string encoding `encIn a`, and `size a` is
polynomially bounded in `|encIn a|`, then `f` is computable in polynomial time with binary
output.

The simulation chooses the word size `Q (|encIn a|)` for a fixed polynomial `Q`, so its cost per
instruction is polynomial; the input words and their count are part of the charged input. -/
theorem Program.ComputesInTime.computableInPolyTime (hB : B.PolyTimeOps) {p : Program B r}
    {encode : α → List ℕ} {size f : α → ℕ} {T : ℕ → ℕ} {k : ℕ}
    (hT : PolynomiallyBounded T)
    (hsize : PolyBounded (fun a => (encIn a).length) size)
    (hencode : Turing.MultiTapeTM.ComputableInPolyTime encode encIn (encList encNat))
    (h : p.ComputesInTime (fun _ => encode) (fun a _ => T (size a))
      (fun a w => logWidth k (size a) ≤ w) f) :
    Turing.MultiTapeTM.ComputableInPolyTime f encIn encNat := by
  have hencT := hencode.tidy
  obtain ⟨c₁, d₁, h₁⟩ := hencT.polyBounded_length.exists_le
  obtain ⟨c₂, d₂, h₂⟩ := hsize.exists_le
  obtain ⟨c₃, d₃, h₃⟩ := Cslib.polynomiallyBounded_iff_le.mp hT
  -- Polynomials in the encoded input length: `S` bounds `size a + 1`, `Qw` the word size and
  -- `Qs` the number of simulated instructions.
  let S : Polynomial ℕ := C c₂ * (X + 1) ^ d₂ + 1
  let Qw : Polynomial ℕ := C k * S + C c₁ * (X + 1) ^ d₁
  let Qs : Polynomial ℕ := C c₃ * S ^ d₃
  let width : α → ℕ := fun a => Qw.eval (encIn a).length
  let steps : α → ℕ := fun a => Qs.eval (encIn a).length
  have hS (a : α) : size a + 1 ≤ S.eval (encIn a).length := by
    simp only [S, eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_one]
    have := h₂ a
    omega
  have hwidth_size (a : α) : logWidth k (size a) ≤ width a := by
    have hlog := Nat.log_le_self 2 (size a)
    have : k * (Nat.log 2 (size a) + 1) ≤ k * S.eval (encIn a).length :=
      Nat.mul_le_mul_left k ((Nat.add_le_add_right hlog 1).trans (hS a))
    simp only [width, Qw, logWidth, eval_add, eval_mul, eval_C] at this ⊢
    omega
  have hwidth_enc (a : α) : (encList encNat (encode a)).length ≤ width a := by
    simp only [width, Qw, eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_one]
    have := h₁ a
    omega
  have hfits (a : α) : InputFits (width a) (encode a) := by
    have hlen := (length_le_length_encList encNat (encode a)).trans (hwidth_enc a)
    refine ⟨lt_of_le_of_lt hlen Nat.lt_two_pow_self, fun v hv => ?_⟩
    have hsum :=
      (List.le_sum_of_mem (List.mem_map_of_mem (f := fun x => (encNat x).length) hv)).trans
      (sum_length_le_length_encList encNat (encode a))
    have hsize_v : v.size ≤ width a := by
      rw [← Nat.size_eq_bits_len, ← encNat_apply] at *
      exact hsum.trans (hwidth_enc a)
    exact lt_of_lt_of_le (Nat.lt_size_self v) (Nat.pow_le_pow_right (by norm_num) hsize_v)
  have hsteps (a : α) : T (size a) ≤ steps a := by
    have hpow := Nat.pow_le_pow_left (hS a) d₃
    simp only [steps, Qs, eval_mul, eval_C, eval_pow] at hpow ⊢
    exact (h₃ (size a)).trans (Nat.mul_le_mul_left c₃ hpow)
  have hExec (a : α) : ∃ m ≤ steps a, Executes (width a) p (State.init (encode a)) (f a) m := by
    obtain ⟨m, hm, hle⟩ := h a (width a) (hwidth_size a) (hfits a)
    exact ⟨m, hle.trans (hsteps a), hm⟩
  -- Native certificates for configuration selection, the clock and initialization.
  have hwidthT : ComputableTidilyInPolyTime width encIn encUnary :=
    (unary_eval Qw).comp (encoding_length encIn)
  have hstepsU : ComputableTidilyInPolyTime steps encIn encUnary :=
    (unary_eval Qs).comp (encoding_length encIn)
  have hstepsT : ComputableTidilyInPolyTime steps encIn encNat := unary_to_binary.comp hstepsU
  have hmemT : ComputableTidilyInPolyTime (fun a => initMemory (encode a)) encIn
      (SparseMemory.encoding encNat encNat) := initMemory_polyTime.comp hencT
  let cInit := FiniteState.initConstCertificate (r := r) (wordEncoding B)
    (NativeCertificate.const (ei := encIn) 0) (NativeCertificate.const 0) (ofPolyTime hmemT)
  have hInit : cInit.IsPolynomial :=
    FiniteState.initConstCertificate_isPolynomial _ _ _ _ (const_isPolynomial 0)
      (const_isPolynomial 0) (ofPolyTime_isPolynomial hmemT)
  -- Every simulated outcome is bounded by a polynomial in the input length.
  let bound : α → ℕ := fun a =>
    stateBound r (labelBound p.toGeneric) (width a) ((encode a).length + 1 + steps a)
  have hbound : PolyBounded (fun a => (encIn a).length) bound := by
    have hw := hwidthT.polyBounded
    have hE : PolyBounded (fun a => (encIn a).length)
        (fun a => (encode a).length + 1 + steps a) :=
      ((hencT.polyBounded_length.mono fun a => length_le_length_encList encNat (encode a)).add
        (.const 1)).add hstepsU.polyBounded
    exact (((((PolyBounded.const _).add ((PolyBounded.const (2 * r)).mul
      (((PolyBounded.const 2).mul hw).add (.const 1)))).add ((PolyBounded.const 2).mul hw)).add
      (hE.mul (((PolyBounded.const 6).mul hw).add (.const 3)))).add hw).add (.const 5)
  have hOutLen (a : α) (j : ℕ) (hj : j ≤ steps a) :
      (FiniteState.resultEncoding (wordEncoding B)
        (FiniteState.run (width a) p.toGeneric j (initState B r (encode a)))).length ≤
        bound a := by
    have hrun := (dataBounded_initState (B := B) (r := r) (hfits a)).length_resultEncoding_run_le
      (p := p.toGeneric) (by simp [initState_pc]) j
    rw [length_entries_initState] at hrun
    refine hrun.trans ?_
    simp only [bound, stateBound]
    have := Nat.mul_le_mul_right (6 * width a + 3)
      (show (encode a).length + 1 + j ≤ (encode a).length + 1 + steps a by omega)
    omega
  exact .of_tidy (WordRAM.transport_polyTime (wordEncoding B) (nativePrimitives hB) p
    (ofPolyTime hstepsT) (ofPolyTime hwidthT) cInit (u := fun a => State.init (encode a))
    (fun a => denote_initState (encode a)) hExec (nativePrimitives_isPolynomial hB)
    (ofPolyTime_isPolynomial hstepsT) (ofPolyTime_isPolynomial hwidthT) hInit
    hstepsU.polyBounded hbound hOutLen)

end Main

end Cslib.WordRAM
