/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.InnerSize
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Complexity.Computability.Circuit.Program

/-!
# Ledgers for gates of unbounded fan-in

The frontier method charges each gate for its fan-in, so it cannot afford gates of unbounded
fan-in. A few of them can nevertheless be absorbed, when they *aggregate*: when their outputs are
determined by a product, in a commutative monoid, of contributions of the wires.

Mark a set of gates as *special*. A *ledger* for them in a commutative monoid `M`
(`Frontier.Ledger`) assigns to each wire and each of its values a *contribution* in `M`, and
reads off the value of every special gate from the product of the contributions of all wires.
The defining identity holds for *every* assignment of values to the wires, not only for runs of
the program. For example, `k` gates computing AND, OR, parity, or counts modulo `m` of their
arguments have a ledger in a product of `k` small monoids (`Frontier.exists_ledger_of_aggregates`).

**Guess and check.** Replace each special gate by a constant *placeholder* (`Frontier.erase`):
the result has fan-in bounded by that of the other gates. To run it, guess the final product
`m ∈ M` and let each placeholder read its value from `m` (`Frontier.Ledger.run`). The guess is
*consistent* when the run reproduces it: when the product of the contributions of the run is `m`.

* A consistent guess yields the true run (`Frontier.Ledger.run_eq_trace`): the placeholders
  hold the values that the special gates compute from the run.
* The product of the contributions of the true run is a consistent guess
  (`Frontier.Ledger.run_total_trace`).

So a program with special gates is an ordinary program, of bounded fan-in, together with one
global register in `M`: the guess, checked against an accumulated product. A sweep carries the
guess and the product accumulated so far in its messages, at a cost of `2 log |M|`.

## Main definitions

* `Cslib.Circuits.Frontier.guessSignature σ`: the signature `σ` with a placeholder constant for
  every natural number.
* `Cslib.Circuits.Frontier.erase special p`: the program `p` with its special gates replaced by
  placeholders.
* `Cslib.Circuits.Frontier.Ledger p I special M`: a ledger for the special gates of `p` in `M`.
* `Cslib.Circuits.Frontier.Ledger.run`: the run of the erased program on a guess.

## Main results

* `Cslib.Circuits.Frontier.innerGates_erase`: the inner gates of the erased program are the
  ordinary inner gates.
* `Cslib.Circuits.Frontier.fanInAtMost_erase`: erasing the special gates leaves the fan-in of
  the other gates.
* `Cslib.Circuits.Frontier.Ledger.run_eq_trace`, `Cslib.Circuits.Frontier.Ledger.run_total_trace`:
  guess and check.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

universe v

variable {σ : Signature.{v}} {n s : ℕ} {U : Type*}

/-- The signature `σ` with a *placeholder* constant for every natural number. -/
abbrev guessSignature (σ : Signature.{v}) : Signature.{v} where
  Op := σ.Op ⊕ ℕ
  Arity := Sum.elim σ.Arity fun _ => 0

/-- The interpretation `I`, with the placeholder `k` holding the value `γ k`. -/
def guessInterpretation (I : Interpretation σ U) (γ : ℕ → U) :
    Interpretation (guessSignature σ) U
  | .inl o, x => I o x
  | .inr k, _ => γ k

/-- The line of the placeholder for the gate numbered `g`. -/
def placeholderLine (g : ℕ) : Line (guessSignature σ) n s :=
  ⟨.inr g, Fin.elim0⟩

/-- An ordinary line, over the signature with placeholders. -/
def liftLine (line : Line σ n s) : Line (guessSignature σ) n s :=
  ⟨.inl line.op, line.wires⟩

theorem placeholderLine_mapWires {n' s' : ℕ} (g : ℕ) (f : Wire n s → Wire n' s') :
    (placeholderLine (σ := σ) g).mapWires f = placeholderLine g := by
  simp only [placeholderLine, Line.mapWires]
  congr 1
  funext a
  exact a.elim0

theorem liftLine_mapWires {n' s' : ℕ} (line : Line σ n s) (f : Wire n s → Wire n' s') :
    (liftLine line).mapWires f = liftLine (line.mapWires f) :=
  rfl

variable (special : ℕ → Prop)

section Erase

variable [DecidablePred special]

/-- **Erasing the special gates.** The gate numbered `g` becomes the placeholder `g` when
`special g`, and is unchanged otherwise. -/
def erase : {s : ℕ} → Program σ n s → Program (guessSignature σ) n s
  | _, .empty => .empty
  | _, @Program.gate _ _ s p line =>
    (erase p).gate (if special s then placeholderLine s else liftLine line)

variable {special}

/-- The lines of an erased program. -/
theorem lines_erase (p : Program σ n s) (g : Fin s) :
    (erase special p).lines g = if special g then placeholderLine g else liftLine (p.lines g) := by
  induction p with
  | empty => exact g.elim0
  | @gate s p line ih =>
    refine Fin.lastCases ?_ (fun g => ?_) g
    · rw [erase, Program.lines_gate_last, Program.lines_gate_last, Fin.val_last]
      split_ifs <;> simp [placeholderLine_mapWires, liftLine_mapWires]
    · rw [erase, Program.lines_gate_castSucc, Program.lines_gate_castSucc, ih, Fin.val_castSucc]
      split_ifs <;> simp [placeholderLine_mapWires, liftLine_mapWires]

theorem lines_erase_of_special (p : Program σ n s) {g : Fin s} (hg : special g) :
    (erase special p).lines g = placeholderLine g := by
  simp [lines_erase, hg]

theorem lines_erase_of_not_special (p : Program σ n s) {g : Fin s} (hg : ¬special g) :
    (erase special p).lines g = liftLine (p.lines g) := by
  simp [lines_erase, hg]

/-- The arity of a gate of the erased program: zero for a placeholder, and the arity of the gate
otherwise. -/
theorem arity_lines_erase (p : Program σ n s) (g : Fin s) :
    (guessSignature σ).Arity ((erase special p).lines g).op =
      if special g then 0 else σ.Arity (p.lines g).op := by
  rw [lines_erase]
  split_ifs <;> rfl

/-- The inner gates of the erased program are the inner gates that are not special. -/
theorem innerGates_erase (p : Program σ n s) :
    (erase special p).innerGates = p.innerGates.filter fun g : Fin s => ¬special g := by
  ext g
  rw [Finset.mem_filter, Program.mem_innerGates, Program.mem_innerGates, arity_lines_erase]
  split_ifs <;> tauto

/-- Erasing the special gates leaves the fan-in of the others. -/
theorem fanInAtMost_erase (p : Program σ n s) {r : ℕ}
    (h : ∀ g : Fin s, ¬special g → σ.Arity (p.lines g).op ≤ r) :
    (erase special p).FanInAtMost r := by
  refine Program.fanInAtMost_iff.2 fun g => ?_
  rw [arity_lines_erase]
  split_ifs with hg
  · exact Nat.zero_le r
  · exact h g hg

end Erase

/-- A *ledger* for the special gates of a program, in a commutative monoid `M`: a contribution
of each wire for each of its values, and a readout of the value of each special gate from the
product of all contributions. The identity holds for every assignment of values to the wires.

The readout is indexed by the numbers of the gates; its values at numbers of gates that are not
special, or at no gate at all, are never consulted. -/
structure Ledger (p : Program σ n s) (I : Interpretation σ U) (M : Type*) [CommMonoid M] where
  /-- The contribution of a wire carrying a value. -/
  contribution : Wire n s → U → M
  /-- The value of each special gate, read off the product of the contributions. -/
  readout : M → ℕ → U
  /-- The readout of a special gate is the gate applied to the values of its arguments. -/
  readout_prod : ∀ (v : Wire n s → U) (g : Fin s), special g →
    readout (∏ w, contribution w (v w)) g = I (p.lines g).op fun a => v ((p.lines g).wires a)

variable {special}

namespace Ledger

variable {p : Program σ n s} {I : Interpretation σ U} {M : Type*} [CommMonoid M]
  (L : Ledger special p I M)

/-- The product of the contributions of an assignment of values to the wires. -/
def total (v : Wire n s → U) : M :=
  ∏ w, L.contribution w (v w)

open Classical in
/-- The product of the contributions of the wires in `Q`. -/
noncomputable def ledgerOn (Q : Set (Wire n s)) (v : Wire n s → U) : M :=
  ∏ w ∈ Finset.univ.filter (· ∈ Q), L.contribution w (v w)

/-- The total is the ledger on `Q` times the ledger on its complement. -/
theorem total_eq_mul (Q : Set (Wire n s)) (v : Wire n s → U) :
    L.total v = L.ledgerOn Q v * L.ledgerOn Qᶜ v := by
  classical
  rw [total, ledgerOn, ledgerOn, ← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ Q)]
  simp only [Set.mem_compl_iff]

variable [DecidablePred special]

/-- The run of the erased program, with the placeholders reading their values from the guess
`m`. -/
def run (m : M) (x : Fin n → U) : Wire n s → U :=
  (erase special p).trace (guessInterpretation I (L.readout m)) x

@[simp] theorem run_input (m : M) (x : Fin n → U) (i : Fin n) : L.run m x (.input i) = x i :=
  rfl

/-- The value of a gate in the run with guess `m`: the readout for a special gate, and the gate
applied to the values of its arguments otherwise. -/
theorem run_gate (m : M) (x : Fin n → U) (g : Fin s) :
    L.run m x (.gate g) = if special g then L.readout m g
      else I (p.lines g).op fun a => L.run m x ((p.lines g).wires a) := by
  change (erase special p).eval _ x g = _
  rw [← Program.lines_eval, lines_erase]
  split_ifs <;> rfl

/-- The value of a special gate in the run with guess `m` is its readout. -/
theorem run_gate_of_special (m : M) (x : Fin n → U) {g : Fin s} (hg : special g) :
    L.run m x (.gate g) = L.readout m g := by
  simp only [run_gate, hg, ↓reduceIte]

/-- The value of an ordinary gate in the run with guess `m` is the gate applied to its
arguments. -/
theorem run_gate_of_not_special (m : M) (x : Fin n → U) {g : Fin s} (hg : ¬special g) :
    L.run m x (.gate g) = I (p.lines g).op fun a => L.run m x ((p.lines g).wires a) := by
  simp only [run_gate, hg, ↓reduceIte]

/-- **Guess and check, soundness.** If the run with guess `m` reproduces `m`, it is the true
run. -/
theorem run_eq_trace {m : M} {x : Fin n → U} (h : L.total (L.run m x) = m) :
    L.run m x = p.trace I x := by
  refine Program.eq_trace_of_forall_gate (fun _ => rfl) fun g => ?_
  rw [run_gate]
  split_ifs with hg
  · have hread := L.readout_prod (L.run m x) g hg
    rwa [← total, h] at hread
  · rfl

/-- **Guess and check, completeness.** The product of the contributions of the true run is a
guess whose run is the true run. -/
theorem run_total_trace (x : Fin n → U) : L.run (L.total (p.trace I x)) x = p.trace I x := by
  -- The true run satisfies the equations of the erased program with this guess.
  have htrace (g : Fin s) := p.trace_gate I x g
  have hgates : (fun g => p.trace I x (.gate g)) =
      (erase special p).eval (guessInterpretation I (L.readout (L.total (p.trace I x)))) x := by
    refine (erase special p).eq_eval_of_forall_lines_eval _ x _ fun g => ?_
    have helim : (Wire.elim x fun g => p.trace I x (.gate g)) = p.trace I x := by
      funext w
      cases w <;> rfl
    rw [lines_erase]
    split_ifs with hg
    · exact (L.readout_prod _ g hg).trans (htrace g).symm
    · simp only [Line.eval, liftLine, guessInterpretation, helim]
      exact (htrace g).symm
  change Wire.elim x ((erase special p).eval _ x) = _
  rw [← hgates]
  funext w
  cases w <;> rfl

/-- **The consistent guess is unique.** A guess reproduces itself exactly when it is the product
of the contributions of the true run. -/
theorem total_run_eq_iff (m : M) (x : Fin n → U) :
    L.total (L.run m x) = m ↔ m = L.total (p.trace I x) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [L.run_eq_trace h] at h
    exact h.symm
  · rw [h, L.run_total_trace]

end Ledger

end Cslib.Circuits.Frontier
