/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.EvaluationTime
public import Complexity.Crypto.Computational.Basic
public import Complexity.Crypto.Game.Statistical
public import Complexity.Foundations.Data.BitString.Parity
public import Complexity.Probability.BitString
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Data.Fintype.BigOperators

/-!
# Completeness of Oblivious Transfer for Multiparty Computation with Abort

In the ideal oblivious-transfer (`OT`) hybrid model, every polynomial-time multiparty functionality
admits a protocol secure against static malicious corruptions with abort, under standard
authenticated point-to-point and broadcast communication channels [Kilian1988, IPS2008,
Goldreich2004Vol2]. Because communication is not simultaneous, security with abort does not
guarantee fairness or delivery of outputs [Cleve1986].

## Overview of the formalization

1. **Ideal 1-out-of-2 Oblivious Transfer (`idealOT`, `idealStringOT`, `otAndShare`)**:
   The ideal 1-out-of-2 oblivious transfer functionality delivers `b_{choice}` to the receiver and
   no information about `choice` to the sender. When a sender with share `a` and uniform mask `r`
   inputs `(r, r ^^ a)` and a receiver inputs choice bit `b`, the receiver learns
   `otAndShare r a b = r ^^ (a && b)`, which XORs with the sender's kept mask `r` to `a && b`
   (`xor_otAndShare`) and is uniformly distributed on `Bool` (`otAndShare_uniform`).

2. **Multiparty Additive Secret Sharing and OT-Hybrid Circuit Evaluation
   (`shareConst`, `shareNot`, `shareAnd`, `shareOr`, `evalLineOT`, `evalProgramOT`,
   `evalCircuitOT`)**:
   Every wire of a `k`-party De Morgan Boolean circuit is shared additively across `Fin k` so that
   its reconstructed value is `parity k shares`. Constants and negations are evaluated locally on
   shares; conjunctions and disjunctions are evaluated via pairwise calls to `idealOT`. We prove
   (`parity_evalCircuitOT`) that for every `k ≥ 1`, every De Morgan circuit `c`, every input
   sharing, and every family of OT sender masks, reconstructing the output wire shares recovers the
   exact circuit evaluation `c.eval Boolean.interpretation` on the reconstructed inputs.

3. **Real/Ideal Simulation Security with Abort (`MaliciousOTAdversary`, `IdealSimulator`,
   `realOTHybridExecution`, `idealExecutionWithAbort`, `StatisticallySecureFamilyWithAbort`,
   `ComputationallySecureWithAbort`)**:
   A static malicious adversary controlling `C : Finset (Fin k)` may substitute effective inputs for
   `i ∈ C`, abort during the input-commitment or OT gate-evaluation phase (detected by the
   OT-hybrid consistency check before output reconstruction), or wait to receive the honest
   parties' output reconstruction shares for the corrupted parties' outputs (learning the
   corrupted parties' outputs) and then decide whether to deliver outputs to the honest parties
   (`some y`) or abort (`none`).
   We construct the canonical black-box simulator `kilianSimulator` and prove via the triangular
   self-inverse OT mask bijection `programMaskToCorruptedOT` that the real OT-hybrid execution and
   the ideal execution with abort have the **exact same probability distribution**
   (`realOTHybridExecution_eq_idealExecutionWithAbort`), yielding both statistical security with
   zero error (`ot_complete_statisticallySecureWithAbort`) and uniform computational security
   against strict PPT distinguishers (`ot_complete_computationallySecureWithAbort`) for every
   polynomial-time multiparty functionality family.

4. **Impossibility of Output Delivery and Fairness (`not_guaranteedOutputDelivery_of_abort`,
   `unfair_twoPartyXor_execution`, `cleve_unfair_fallback`)**:
   We prove explicitly that security with abort does not guarantee output delivery, that for the
   two-party XOR functionality a rushing adversary controlling party `0` learns the exact output
   (and hence the honest party's secret input bit) with probability `1` while forcing the honest
   party to output `none`, and that no fallback rule can achieve fair two-party output delivery
   against early abort [Cleve1986].

## Main definitions

* `Cslib.Crypto.Multiparty.idealOT`, `Cslib.Crypto.Multiparty.idealStringOT`: ideal 1-out-of-2
  oblivious transfer.
* `Cslib.Crypto.Multiparty.otAndShare`, `Cslib.Crypto.Multiparty.shareAnd`: OT-based pairwise and
  multiparty share multiplication.
* `Cslib.Crypto.Multiparty.evalCircuitOT`: gate-by-gate evaluation of a De Morgan circuit on
  `k`-party additive secret shares in the ideal OT-hybrid model.
* `Cslib.Crypto.Multiparty.realOTHybridExecution`,
  `Cslib.Crypto.Multiparty.idealExecutionWithAbort`: real OT-hybrid and ideal-with-abort execution
  distributions against static malicious corruptions.
* `Cslib.Crypto.Multiparty.kilianSimulator`: black-box ideal-world simulator extracting effective
  corrupted inputs and simulating all corrupted wire shares and OT transcripts.
* `Cslib.Crypto.Multiparty.StatisticallySecureFamilyWithAbort`,
  `Cslib.Crypto.Multiparty.ComputationallySecureWithAbort`: real/ideal simulation security with
  abort.
* `Cslib.Crypto.Multiparty.PolyTimeFunctionality`: polynomial-time multiparty functionality
  families with certified De Morgan circuit realizations.

## Main results

* `Cslib.Crypto.Multiparty.parity_evalCircuitOT`: OT-hybrid share evaluation of any De Morgan
  circuit reconstructs the exact circuit output.
* `Cslib.Crypto.Multiparty.realOTHybridExecution_eq_idealExecutionWithAbort`: exact distributional
  equality of the real OT-hybrid execution and the ideal execution with abort.
* `Cslib.Crypto.Multiparty.ot_complete_statisticallySecureWithAbort`,
  `Cslib.Crypto.Multiparty.ot_complete_computationallySecureWithAbort`: **Completeness of
  oblivious transfer** [Kilian1988, IPS2008, Goldreich2004Vol2].
* `Cslib.Crypto.Multiparty.not_guaranteedOutputDelivery_of_abort`,
  `Cslib.Crypto.Multiparty.unfair_twoPartyXor_execution`,
  `Cslib.Crypto.Multiparty.cleve_unfair_fallback`: **Non-fairness and lack of guaranteed output
  delivery** [Cleve1986].

## References

* [J. Kilian, *Founding Cryptography on Oblivious Transfer*][Kilian1988]
* [Y. Ishai, M. Prabhakaran, A. Sahai,
  *Founding Cryptography on Oblivious Transfer — Efficiently*][IPS2008]
* [O. Goldreich, *Foundations of Cryptography: Volume 2, Basic Applications*][Goldreich2004Vol2],
  Chapter 7.
* [R. Cleve, *Limits on the Security of Coin Flips when Half the Processors Are Faulty*][Cleve1986]
-/

@[expose] public section

namespace Cslib.Crypto.Multiparty

open Cslib Cslib.Circuits Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

/-! ### Ideal 1-out-of-2 Oblivious Transfer -/

/-- **Ideal 1-out-of-2 bit oblivious transfer**: the sender inputs `(b₀, b₁)` and receives `()`,
while the receiver inputs `choice` and receives `b_{choice}`. -/
def idealOT (b₀ b₁ choice : Bool) : Bool :=
  if choice then b₁ else b₀

/-- **Ideal 1-out-of-2 string/message oblivious transfer** over an arbitrary message type `α`. -/
def idealStringOT {α : Type*} (s₀ s₁ : α) (choice : Bool) : α :=
  if choice then s₁ else s₀

@[simp] theorem idealOT_false (b₀ b₁ : Bool) : idealOT b₀ b₁ false = b₀ := rfl

@[simp] theorem idealOT_true (b₀ b₁ : Bool) : idealOT b₀ b₁ true = b₁ := rfl

@[simp] theorem idealStringOT_false {α : Type*} (s₀ s₁ : α) :
    idealStringOT s₀ s₁ false = s₀ := rfl

@[simp] theorem idealStringOT_true {α : Type*} (s₀ s₁ : α) :
    idealStringOT s₀ s₁ true = s₁ := rfl

/-- Evaluating `idealOT` on a masked pair `(r, r ^^ a)` with choice bit `b` yields
`r ^^ (a && b)`. -/
theorem idealOT_xor_mask (r a b : Bool) : idealOT r (r ^^ a) b = (r ^^ (a && b)) := by
  cases b <;> simp [idealOT]

/-- **OT-based pairwise multiplication share**: the sender holding bit `a` and mask `r` offers
`(r, r ^^ a)` to `idealOT`, and the receiver holding bit `b` selects with `b`. -/
def otAndShare (r a b : Bool) : Bool :=
  idealOT r (r ^^ a) b

theorem otAndShare_eq (r a b : Bool) : otAndShare r a b = (r ^^ (a && b)) :=
  idealOT_xor_mask r a b

/-- The sender's kept mask `r` and the receiver's OT output `otAndShare r a b` form an additive
secret sharing of the product `a && b`. -/
@[simp] theorem xor_otAndShare (r a b : Bool) : (r ^^ otAndShare r a b) = (a && b) := by
  cases r <;> cases a <;> cases b <;> rfl

/-- Fixing `a` and `b`, `r ↦ otAndShare r a b` is a self-inverse bijection on `Bool`. -/
@[simp] theorem otAndShare_otAndShare (r a b : Bool) :
    otAndShare (otAndShare r a b) a b = r := by
  cases r <;> cases a <;> cases b <;> rfl

/-- The bijection `r ↦ otAndShare r a b` on `Bool`. -/
def otAndShareEquiv (a b : Bool) : Bool ≃ Bool where
  toFun r := otAndShare r a b
  invFun u := otAndShare u a b
  left_inv r := otAndShare_otAndShare r a b
  right_inv u := otAndShare_otAndShare u a b

/-- When the sender's mask `r` is uniform on `Bool`, the receiver's OT output `otAndShare r a b` is
uniform on `Bool`, completely independent of the sender's bit `a` and receiver's bit `b`. -/
theorem otAndShare_uniform (a b : Bool) :
    (PMF.uniformOfFintype Bool).map (fun r => otAndShare r a b) = PMF.uniformOfFintype Bool :=
  PMF.uniformOfFintype_map_equiv (otAndShareEquiv a b)

/-! ### Multiparty Additive Secret Sharing and OT-Hybrid Gate Evaluation -/

/-- Share a public constant bit `b` among `k` parties by assigning `b` to party `0` and `false`
to all other parties. -/
def shareConst (k : ℕ) (b : Bool) : Fin k → Bool :=
  fun i => if i.val = 0 then b else false

/-- Reconstructing `shareConst k b` via `parity k` recovers `b` whenever `k ≥ 1`. -/
@[simp] theorem parity_shareConst (k : ℕ) [NeZero k] (b : Bool) :
    parity k (shareConst k b) = b := by
  rw [parity, parityOn_eq_sum]
  rw [Finset.sum_eq_single (0 : Fin k)]
  · simp [shareConst]
  · intro j _ hj0
    have hjval : j.val ≠ 0 := Fin.val_ne_of_ne hj0
    simp only [shareConst, hjval, ↓reduceIte]
    rfl
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin k)) h

/-- Negate a shared bit by flipping party `0`'s share. -/
def shareNot {k : ℕ} (a : Fin k → Bool) : Fin k → Bool :=
  a + shareConst k true

/-- Reconstructing `shareNot a` negates the reconstructed secret `parity k a`. -/
@[simp] theorem parity_shareNot {k : ℕ} [NeZero k] (a : Fin k → Bool) :
    parity k (shareNot a) = !parity k a := by
  rw [shareNot, parity, parityOn_add, ← parity, parity_shareConst, Bool.xor_true]

/-- **Multiparty OT-based AND gate on additive shares**: given wire share vectors
`a, b : Fin k → Bool` and pairwise OT sender masks `r : Fin k → Fin k → Bool`, party `i` combines
its received OT shares `otAndShare (r j i) (a j) (b i)` and its kept sender masks `r i j`. -/
def shareAnd {k : ℕ} (r : Fin k → Fin k → Bool) (a b : Fin k → Bool) : Fin k → Bool :=
  fun i => ∑ j : Fin k, (otAndShare (r j i) (a j) (b i) + r i j)

/-- Party `i`'s share in `shareAnd` separates into its local product `a i && b i` and pairwise OT
terms with distinct parties `j ≠ i`. -/
theorem shareAnd_apply_eq_erase {k : ℕ} (r : Fin k → Fin k → Bool) (a b : Fin k → Bool)
    (i : Fin k) :
    shareAnd r a b i =
      ((a i && b i) + ∑ j ∈ Finset.univ.erase i, (otAndShare (r j i) (a j) (b i) + r i j)) := by
  rw [shareAnd, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  congr 1
  cases r i i <;> cases a i <;> cases b i <;> rfl

/-- **Correctness of multiparty OT-based share multiplication**: for any mask matrix `r`, the
reconstructed secret of `shareAnd r a b` is the conjunction `parity k a && parity k b`. -/
@[simp] theorem parity_shareAnd {k : ℕ} (r : Fin k → Fin k → Bool) (a b : Fin k → Bool) :
    parity k (shareAnd r a b) = (parity k a && parity k b) := by
  simp only [parity, parityOn_eq_sum, shareAnd]
  have hterm (i j : Fin k) :
      otAndShare (r j i) (a j) (b i) + r i j = (r j i + r i j) + a j * b i := by
    cases r j i <;> cases r i j <;> cases a j <;> cases b i <;> rfl
  simp_rw [hterm, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun x y => r y x), BooleanRing.add_self, zero_add,
    Finset.sum_comm (f := fun x y => a y * b x), ← Finset.sum_mul_sum, Bool.mul_eq_and]

/-- **Multiparty OT-based OR gate on additive shares**, via De Morgan's law on `shareAnd`. -/
def shareOr {k : ℕ} (r : Fin k → Fin k → Bool) (a b : Fin k → Bool) : Fin k → Bool :=
  shareNot (shareAnd r (shareNot a) (shareNot b))

/-- Reconstructing `shareOr r a b` yields the disjunction `parity k a || parity k b`. -/
@[simp] theorem parity_shareOr {k : ℕ} [NeZero k] (r : Fin k → Fin k → Bool)
    (a b : Fin k → Bool) :
    parity k (shareOr r a b) = (parity k a || parity k b) := by
  rw [shareOr, parity_shareNot, parity_shareAnd, parity_shareNot, parity_shareNot,
    Bool.not_and, Bool.not_not, Bool.not_not]

/-- Evaluate one De Morgan circuit line on `k`-party additive wire shares using OT mask matrix
`r`. -/
def evalLineOT {k n g : ℕ} (line : Line Boolean.signature n g)
    (r : Fin k → Fin k → Bool) (inputs : Fin n → Fin k → Bool)
    (gates : Fin g → Fin k → Bool) : Fin k → Bool :=
  match line.op, line.wires with
  | .const b, _ => shareConst k b
  | .not, w => shareNot (Wire.elim inputs gates (w 0))
  | .and, w => shareAnd r (Wire.elim inputs gates (w 0)) (Wire.elim inputs gates (w 1))
  | .or, w => shareOr r (Wire.elim inputs gates (w 0)) (Wire.elim inputs gates (w 1))

/-- Reconstructing the output shares of `evalLineOT` matches `Line.eval Boolean.interpretation` on
the reconstructed input and gate wires. -/
@[simp] theorem parity_evalLineOT {k n g : ℕ} [NeZero k] (line : Line Boolean.signature n g)
    (r : Fin k → Fin k → Bool) (inputs : Fin n → Fin k → Bool)
    (gates : Fin g → Fin k → Bool) :
    parity k (evalLineOT line r inputs gates) =
      line.eval Boolean.interpretation (fun i => parity k (inputs i))
        (fun j => parity k (gates j)) := by
  have hw (w : Wire n g) :
      parity k (Wire.elim inputs gates w) =
        Wire.elim (fun i => parity k (inputs i)) (fun j => parity k (gates j)) w := by
    cases w <;> rfl
  rcases line with ⟨op, w⟩
  cases op <;> simp [evalLineOT, Line.eval, Boolean.interpretation, hw]

/-- Evaluate a De Morgan circuit program gate-by-gate on `k`-party additive wire shares using a
sequence of OT mask matrices `masks`. -/
def evalProgramOT {k n : ℕ} : {g : ℕ} →
    Program Boolean.signature n g →
    (Fin g → Fin k → Fin k → Bool) →
    (Fin n → Fin k → Bool) → (Fin g → Fin k → Bool)
  | 0, .empty, _, _ => Fin.elim0
  | g + 1, .gate p line, masks, inputs =>
    let prev := evalProgramOT p (fun j => masks j.castSucc) inputs
    Fin.snoc prev (evalLineOT line (masks (Fin.last g)) inputs prev)

/-- Reconstructing each gate wire of `evalProgramOT` matches `Program.eval Boolean.interpretation`
on the reconstructed inputs. -/
theorem parity_evalProgramOT {k n g : ℕ} [NeZero k]
    (p : Program Boolean.signature n g)
    (masks : Fin g → Fin k → Fin k → Bool)
    (inputs : Fin n → Fin k → Bool) :
    (fun j => parity k (evalProgramOT p masks inputs j)) =
      p.eval Boolean.interpretation (fun i => parity k (inputs i)) := by
  induction p with
  | empty =>
    funext j
    exact j.elim0
  | @gate g p line ih =>
    funext j
    induction j using Fin.lastCases with
    | last =>
      simp [evalProgramOT, Program.eval_gate_last, ih]
    | cast j =>
      simp only [evalProgramOT, Fin.snoc_castSucc, Program.eval_gate_castSucc]
      exact congrFun (ih _) j

/-- Evaluate a De Morgan circuit `c` on `k`-party additive input wire shares in the ideal OT-hybrid
model, returning the `k`-party additive shares of each output wire. -/
def evalCircuitOT {k n m : ℕ} (c : Circuit Boolean.signature n m)
    (masks : Fin c.size → Fin k → Fin k → Bool)
    (inputs : Fin n → Fin k → Bool) : Fin m → Fin k → Bool :=
  fun j => Wire.elim inputs (evalProgramOT c.program masks inputs) (c.outputs j)

/-- **Gate-by-gate OT-hybrid evaluation correctness**: reconstructing the output shares of
`evalCircuitOT` recovers the exact evaluation of the De Morgan circuit `c` on the reconstructed
input bits. -/
@[simp] theorem parity_evalCircuitOT {k n m : ℕ} [NeZero k]
    (c : Circuit Boolean.signature n m)
    (masks : Fin c.size → Fin k → Fin k → Bool)
    (inputs : Fin n → Fin k → Bool) (j : Fin m) :
    parity k (evalCircuitOT c masks inputs j) =
      c.eval Boolean.interpretation (fun i => parity k (inputs i)) j := by
  rw [evalCircuitOT, Circuit.eval, Function.comp_apply, Program.trace]
  cases c.outputs j with
  | input i => rfl
  | gate g =>
    simp only [Wire.elim_gate]
    exact congrFun (parity_evalProgramOT c.program masks inputs) g

/-! ### Secret Sharing Privacy and Corrupted-View OT Bijection -/

/-- Share a secret bit `v` among `k` parties with pivot party `h`: all parties `i ≠ h` receive
their random share `r i`, and party `h` receives `v ^^ parityOn (Finset.univ.erase h) r`. -/
def shareBitWithPivot {k : ℕ} (h : Fin k) (v : Bool) (r : Fin k → Bool) : Fin k → Bool :=
  Function.update r h (v ^^ parityOn (Finset.univ.erase h) r)

/-- Reconstructing `shareBitWithPivot h v r` recovers `v` for every randomness vector `r`. -/
@[simp] theorem parity_shareBitWithPivot {k : ℕ} (h : Fin k) (v : Bool) (r : Fin k → Bool) :
    parity k (shareBitWithPivot h v r) = v := by
  rw [parity, parityOn_eq_xor_erase (Finset.mem_univ h), shareBitWithPivot, Function.update_self,
    parityOn_update_of_notMem (Finset.notMem_erase h Finset.univ),
    Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- Every party `i ≠ h` observes only its random share `r i` in `shareBitWithPivot h v r`. -/
theorem shareBitWithPivot_of_ne {k : ℕ} (h : Fin k) (v : Bool) (r : Fin k → Bool)
    {i : Fin k} (hi : i ≠ h) :
    shareBitWithPivot h v r i = r i :=
  Function.update_of_ne hi _ _

/-- The parity of the honest parties' shares `Finset.univ \ C` equals the full secret `parity k s`
XORed with the parity of the corrupted parties' shares `parityOn C s`. -/
theorem parityOn_univ_sdiff {k : ℕ} (C : Finset (Fin k)) (s : Fin k → Bool) :
    parityOn (Finset.univ \ C) s = (parity k s ^^ parityOn C s) := by
  have hunion : (Finset.univ \ C) ∪ C = (Finset.univ : Finset (Fin k)) :=
    Finset.sdiff_union_of_subset (Finset.subset_univ C)
  have hdisj : Disjoint (Finset.univ \ C) C := disjoint_sdiff_self_left
  have hpar : parity k s = (parityOn (Finset.univ \ C) s ^^ parityOn C s) := by
    rw [← parityOn_union hdisj s, hunion, parity]
  rw [hpar, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- Canonical choice of an honest pivot party outside `C` when `Finset.univ \ C` is nonempty,
defaulting to `0` when all parties are corrupted (`C = Finset.univ`). -/
def chooseHonestPivot {k : ℕ} [NeZero k] (C : Finset (Fin k)) : Fin k :=
  if h : (Finset.univ \ C).Nonempty then (Finset.univ \ C).min' h else 0

theorem chooseHonestPivot_notMem {k : ℕ} [NeZero k] {C : Finset (Fin k)}
    (h : (Finset.univ \ C).Nonempty) :
    chooseHonestPivot C ∉ C := by
  rw [chooseHonestPivot, dite_eq_left h]
  exact (Finset.mem_sdiff.mp ((Finset.univ \ C).min'_mem h)).2

/-- Self-inverse bijection transforming honest-to-corrupted OT sender masks `(j ∉ C ∧ i ∈ C)` into
the OT outputs `otAndShare (r j i) (a j) (b i)` delivered to corrupted receivers by `idealOT`. -/
def maskToCorruptedOT {k : ℕ} (C : Finset (Fin k)) (a b : Fin k → Bool) :
    (Fin k → Fin k → Bool) ≃ (Fin k → Fin k → Bool) where
  toFun r j i := if j ∉ C ∧ i ∈ C then otAndShare (r j i) (a j) (b i) else r j i
  invFun u j i := if j ∉ C ∧ i ∈ C then otAndShare (u j i) (a j) (b i) else u j i
  left_inv r := by
    ext j i
    by_cases h : j ∉ C ∧ i ∈ C <;> simp [h]
  right_inv u := by
    ext j i
    by_cases h : j ∉ C ∧ i ∈ C <;> simp [h]

/-- Simulated `AND`-gate share computation for corrupted parties: uses `otAndShare` when the sender
`j` is also in `C`, and uses the received OT bit `u j i` directly when the sender `j ∉ C` is
honest. -/
def simulatedShareAnd {k : ℕ} (C : Finset (Fin k)) (u : Fin k → Fin k → Bool)
    (a b : Fin k → Bool) : Fin k → Bool :=
  fun i => ∑ j : Fin k, ((if j ∈ C then otAndShare (u j i) (a j) (b i) else u j i) + u i j)

/-- For every corrupted party `i ∈ C`, `shareAnd r a b i` agrees with `simulatedShareAnd` on
`maskToCorruptedOT C a b r`. -/
theorem shareAnd_eq_simulatedShareAnd_of_mem {k : ℕ} (C : Finset (Fin k))
    (r : Fin k → Fin k → Bool) (a b : Fin k → Bool) {i : Fin k} (hi : i ∈ C) :
    shareAnd r a b i = simulatedShareAnd C (maskToCorruptedOT C a b r) a b i := by
  simp only [shareAnd, simulatedShareAnd]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j ∈ C <;> simp [maskToCorruptedOT, hi, hj]

/-- On corrupted parties `i ∈ C`, `simulatedShareAnd C u a b i` depends only on the corrupted shares
`(a j)_{j ∈ C}` and `(b j)_{j ∈ C}` and on the entries of `u` incident to `C`. -/
theorem simulatedShareAnd_congr_corrupted {k : ℕ} (C : Finset (Fin k))
    {u u' : Fin k → Fin k → Bool} {a a' b b' : Fin k → Bool}
    (hu : ∀ j i, (j ∈ C ∨ i ∈ C) → u j i = u' j i)
    (ha : ∀ j ∈ C, a j = a' j) (hb : ∀ j ∈ C, b j = b' j)
    {i : Fin k} (hi : i ∈ C) :
    simulatedShareAnd C u a b i = simulatedShareAnd C u' a' b' i := by
  simp only [simulatedShareAnd]
  apply Finset.sum_congr rfl
  intro j _
  have hu1 : u j i = u' j i := hu j i (Or.inr hi)
  have hu2 : u i j = u' i j := hu i j (Or.inl hi)
  by_cases hj : j ∈ C
  · simp [hj, hu1, hu2, ha j hj, hb i hi]
  · simp [hj, hu1, hu2]

/-- Per-line OT mask bijection transforming honest-to-corrupted OT masks into corrupted OT receiver
outputs. -/
def lineMaskToCorruptedOT {k n g : ℕ} (C : Finset (Fin k))
    (line : Line Boolean.signature n g)
    (inputs : Fin n → Fin k → Bool) (gates : Fin g → Fin k → Bool) :
    (Fin k → Fin k → Bool) ≃ (Fin k → Fin k → Bool) :=
  match line.op, line.wires with
  | .const _, _ => Equiv.refl _
  | .not, _ => Equiv.refl _
  | .and, w =>
    maskToCorruptedOT C (Wire.elim inputs gates (w 0)) (Wire.elim inputs gates (w 1))
  | .or, w =>
    maskToCorruptedOT C (shareNot (Wire.elim inputs gates (w 0)))
      (shareNot (Wire.elim inputs gates (w 1)))

/-- Simulated single-line gate share evaluation for corrupted parties. -/
def simulatedEvalLineOT {k n g : ℕ} (C : Finset (Fin k))
    (line : Line Boolean.signature n g)
    (u : Fin k → Fin k → Bool)
    (inputs : Fin n → Fin k → Bool) (gates : Fin g → Fin k → Bool) : Fin k → Bool :=
  match line.op, line.wires with
  | .const b, _ => shareConst k b
  | .not, w => shareNot (Wire.elim inputs gates (w 0))
  | .and, w =>
    simulatedShareAnd C u (Wire.elim inputs gates (w 0)) (Wire.elim inputs gates (w 1))
  | .or, w =>
    shareNot (simulatedShareAnd C u (shareNot (Wire.elim inputs gates (w 0)))
      (shareNot (Wire.elim inputs gates (w 1))))

/-- For every corrupted party `i ∈ C`, `evalLineOT` agrees with `simulatedEvalLineOT` under
`lineMaskToCorruptedOT`. -/
theorem evalLineOT_eq_simulatedEvalLineOT_of_mem {k n g : ℕ} (C : Finset (Fin k))
    (line : Line Boolean.signature n g) (r : Fin k → Fin k → Bool)
    (inputs : Fin n → Fin k → Bool) (gates : Fin g → Fin k → Bool)
    {i : Fin k} (hi : i ∈ C) :
    evalLineOT line r inputs gates i =
      simulatedEvalLineOT C line (lineMaskToCorruptedOT C line inputs gates r) inputs gates i := by
  rcases line with ⟨op, w⟩
  cases op with
  | const b => rfl
  | not => rfl
  | and =>
    exact shareAnd_eq_simulatedShareAnd_of_mem C r _ _ hi
  | or =>
    simp only [evalLineOT, shareOr, simulatedEvalLineOT, lineMaskToCorruptedOT, shareNot,
      Pi.add_apply]
    rw [shareAnd_eq_simulatedShareAnd_of_mem C r _ _ hi]

/-- On corrupted parties `i ∈ C`, `simulatedEvalLineOT` depends only on the corrupted wire shares
and the entries of `u` incident to `C`. -/
theorem simulatedEvalLineOT_congr_corrupted {k n g : ℕ} (C : Finset (Fin k))
    (line : Line Boolean.signature n g)
    {u u' : Fin k → Fin k → Bool}
    {inputs inputs' : Fin n → Fin k → Bool}
    {gates gates' : Fin g → Fin k → Bool}
    (hu : ∀ j i, (j ∈ C ∨ i ∈ C) → u j i = u' j i)
    (hin : ∀ w, ∀ j ∈ C, inputs w j = inputs' w j)
    (hgates : ∀ w, ∀ j ∈ C, gates w j = gates' w j)
    {i : Fin k} (hi : i ∈ C) :
    simulatedEvalLineOT C line u inputs gates i =
      simulatedEvalLineOT C line u' inputs' gates' i := by
  have hw (w : Wire n g) {j : Fin k} (hj : j ∈ C) :
      Wire.elim inputs gates w j = Wire.elim inputs' gates' w j := by
    cases w with
    | input w => exact hin w j hj
    | gate w => exact hgates w j hj
  rcases line with ⟨op, w⟩
  cases op with
  | const b => rfl
  | not =>
    simp only [simulatedEvalLineOT, shareNot, Pi.add_apply]
    rw [hw (w 0) hi]
  | and =>
    exact simulatedShareAnd_congr_corrupted C hu (fun j hj => hw (w 0) hj)
      (fun j hj => hw (w 1) hj) hi
  | or =>
    simp only [simulatedEvalLineOT, shareNot, Pi.add_apply]
    congr 1
    exact simulatedShareAnd_congr_corrupted C hu
      (fun j hj => by simp only [Pi.add_apply, hw (w 0) hj])
      (fun j hj => by simp only [Pi.add_apply, hw (w 1) hj]) hi

/-- Simulated gate-by-gate program evaluation on shares for corrupted parties. -/
def simulatedEvalProgramOT {k n : ℕ} (C : Finset (Fin k)) : {g : ℕ} →
    Program Boolean.signature n g →
    (Fin g → Fin k → Fin k → Bool) →
    (Fin n → Fin k → Bool) → (Fin g → Fin k → Bool)
  | 0, .empty, _, _ => Fin.elim0
  | g + 1, .gate p line, u, inputs =>
    let prev := simulatedEvalProgramOT C p (fun j => u j.castSucc) inputs
    Fin.snoc prev (simulatedEvalLineOT C line (u (Fin.last g)) inputs prev)

/-- Forward triangular transformation mapping sender OT masks `r` across all gates of `p` to the
OT values `u` observed by corrupted receivers. -/
def transformProgramMasks {k n : ℕ} (C : Finset (Fin k)) : {g : ℕ} →
    Program Boolean.signature n g →
    (Fin n → Fin k → Bool) →
    (Fin g → Fin k → Fin k → Bool) → (Fin g → Fin k → Fin k → Bool)
  | 0, .empty, _, _ => Fin.elim0
  | g + 1, .gate p line, inputs, r =>
    let prevMasks := fun j : Fin g => r j.castSucc
    let prevGates := evalProgramOT p prevMasks inputs
    Fin.snoc (transformProgramMasks C p inputs prevMasks)
      (lineMaskToCorruptedOT C line inputs prevGates (r (Fin.last g)))

/-- Inverse triangular transformation recovering sender OT masks `r` from `u`. -/
def untransformProgramMasks {k n : ℕ} (C : Finset (Fin k)) : {g : ℕ} →
    Program Boolean.signature n g →
    (Fin n → Fin k → Bool) →
    (Fin g → Fin k → Fin k → Bool) → (Fin g → Fin k → Fin k → Bool)
  | 0, .empty, _, _ => Fin.elim0
  | g + 1, .gate p line, inputs, u =>
    let prevMasks := untransformProgramMasks C p inputs (fun j : Fin g => u j.castSucc)
    let prevGates := evalProgramOT p prevMasks inputs
    Fin.snoc prevMasks
      ((lineMaskToCorruptedOT C line inputs prevGates).symm (u (Fin.last g)))

theorem untransformProgramMasks_transformProgramMasks {k n g : ℕ} (C : Finset (Fin k))
    (p : Program Boolean.signature n g) (inputs : Fin n → Fin k → Bool)
    (r : Fin g → Fin k → Fin k → Bool) :
    untransformProgramMasks C p inputs (transformProgramMasks C p inputs r) = r := by
  induction p with
  | empty =>
    funext j
    exact j.elim0
  | @gate g p line ih =>
    have hinit :
        (fun j : Fin g => transformProgramMasks C (p.gate line) inputs r j.castSucc) =
          transformProgramMasks C p inputs (fun j => r j.castSucc) := by
      funext j
      simp [transformProgramMasks]
    funext j
    induction j using Fin.lastCases with
    | last =>
      simp [untransformProgramMasks, transformProgramMasks, ih]
    | cast j =>
      simp only [untransformProgramMasks, Fin.snoc_castSucc, hinit]
      exact congrFun (ih (fun j => r j.castSucc)) j

theorem transformProgramMasks_untransformProgramMasks {k n g : ℕ} (C : Finset (Fin k))
    (p : Program Boolean.signature n g) (inputs : Fin n → Fin k → Bool)
    (u : Fin g → Fin k → Fin k → Bool) :
    transformProgramMasks C p inputs (untransformProgramMasks C p inputs u) = u := by
  induction p with
  | empty =>
    funext j
    exact j.elim0
  | @gate g p line ih =>
    have hinit :
        (fun j : Fin g => untransformProgramMasks C (p.gate line) inputs u j.castSucc) =
          untransformProgramMasks C p inputs (fun j => u j.castSucc) := by
      funext j
      simp [untransformProgramMasks]
    funext j
    induction j using Fin.lastCases with
    | last =>
      simp [transformProgramMasks, untransformProgramMasks]
    | cast j =>
      simp only [transformProgramMasks, Fin.snoc_castSucc, hinit]
      exact congrFun (ih (fun j => u j.castSucc)) j

/-- **Triangular OT mask bijection for a circuit program**: for any fixed input wire sharing
`inputs`, transforming the gate OT masks via `transformProgramMasks` is an equivalence on
`Fin g → Fin k → Fin k → Bool`. -/
def programMaskToCorruptedOT {k n g : ℕ} (C : Finset (Fin k))
    (p : Program Boolean.signature n g) (inputs : Fin n → Fin k → Bool) :
    (Fin g → Fin k → Fin k → Bool) ≃ (Fin g → Fin k → Fin k → Bool) where
  toFun := transformProgramMasks C p inputs
  invFun := untransformProgramMasks C p inputs
  left_inv := untransformProgramMasks_transformProgramMasks C p inputs
  right_inv := transformProgramMasks_untransformProgramMasks C p inputs

/-- For every gate `t : Fin g` and every corrupted party `i ∈ C`, `evalProgramOT` with masks `r`
equals `simulatedEvalProgramOT` with transformed masks `programMaskToCorruptedOT C p inputs r`. -/
theorem evalProgramOT_eq_simulatedEvalProgramOT_of_mem {k n g : ℕ} (C : Finset (Fin k))
    (p : Program Boolean.signature n g) (r : Fin g → Fin k → Fin k → Bool)
    (inputs : Fin n → Fin k → Bool) (t : Fin g) {i : Fin k} (hi : i ∈ C) :
    evalProgramOT p r inputs t i =
      simulatedEvalProgramOT C p (programMaskToCorruptedOT C p inputs r) inputs t i := by
  induction p generalizing i with
  | empty => exact t.elim0
  | @gate g p line ih =>
    have hinit :
        (fun j : Fin g => programMaskToCorruptedOT C (p.gate line) inputs r j.castSucc) =
          programMaskToCorruptedOT C p inputs (fun j => r j.castSucc) := by
      funext j
      simp [programMaskToCorruptedOT, transformProgramMasks]
    have hlast :
        programMaskToCorruptedOT C (p.gate line) inputs r (Fin.last g) =
          lineMaskToCorruptedOT C line inputs (evalProgramOT p (fun j => r j.castSucc) inputs)
            (r (Fin.last g)) := by
      simp [programMaskToCorruptedOT, transformProgramMasks]
    induction t using Fin.lastCases with
    | last =>
      simp only [evalProgramOT, simulatedEvalProgramOT, Fin.snoc_last, hinit, hlast]
      rw [evalLineOT_eq_simulatedEvalLineOT_of_mem C line (r (Fin.last g)) inputs _ hi]
      exact simulatedEvalLineOT_congr_corrupted C line (fun _ _ _ => rfl) (fun _ _ _ => rfl)
        (fun w j hj => ih (fun j => r j.castSucc) w hj) hi
    | cast t =>
      simp only [evalProgramOT, simulatedEvalProgramOT, Fin.snoc_castSucc, hinit]
      exact ih (fun j => r j.castSucc) t hi

/-- On corrupted parties `i ∈ C`, `simulatedEvalProgramOT` depends only on the corrupted input
shares and the entries of `u` incident to `C`. -/
theorem simulatedEvalProgramOT_congr_corrupted {k n g : ℕ} (C : Finset (Fin k))
    (p : Program Boolean.signature n g)
    {u u' : Fin g → Fin k → Fin k → Bool}
    {inputs inputs' : Fin n → Fin k → Bool}
    (hu : ∀ t j i, (j ∈ C ∨ i ∈ C) → u t j i = u' t j i)
    (hin : ∀ w, ∀ j ∈ C, inputs w j = inputs' w j)
    (t : Fin g) {i : Fin k} (hi : i ∈ C) :
    simulatedEvalProgramOT C p u inputs t i =
      simulatedEvalProgramOT C p u' inputs' t i := by
  induction p generalizing i with
  | empty => exact t.elim0
  | @gate g p line ih =>
    induction t using Fin.lastCases with
    | last =>
      simp only [simulatedEvalProgramOT, Fin.snoc_last]
      exact simulatedEvalLineOT_congr_corrupted C line (hu (Fin.last g)) hin
        (fun w j hj => ih (fun t => hu t.castSucc) w hj) hi
    | cast t =>
      simp only [simulatedEvalProgramOT, Fin.snoc_castSucc]
      exact ih (fun t => hu t.castSucc) t hi

/-- Simulated circuit output wire shares for corrupted parties. -/
def simulatedEvalCircuitOT {k n m : ℕ} (C : Finset (Fin k))
    (c : Circuit Boolean.signature n m)
    (u : Fin c.size → Fin k → Fin k → Bool)
    (inputs : Fin n → Fin k → Bool) : Fin m → Fin k → Bool :=
  fun j => Wire.elim inputs (simulatedEvalProgramOT C c.program u inputs) (c.outputs j)

theorem evalCircuitOT_eq_simulatedEvalCircuitOT_of_mem {k n m : ℕ} (C : Finset (Fin k))
    (c : Circuit Boolean.signature n m) (r : Fin c.size → Fin k → Fin k → Bool)
    (inputs : Fin n → Fin k → Bool) (j : Fin m) {i : Fin k} (hi : i ∈ C) :
    evalCircuitOT c r inputs j i =
      simulatedEvalCircuitOT C c (programMaskToCorruptedOT C c.program inputs r) inputs j i := by
  simp only [evalCircuitOT, simulatedEvalCircuitOT]
  cases c.outputs j with
  | input w => rfl
  | gate g =>
    simp only [Wire.elim_gate]
    exact evalProgramOT_eq_simulatedEvalProgramOT_of_mem C c.program r inputs g hi

theorem simulatedEvalCircuitOT_congr_corrupted {k n m : ℕ} (C : Finset (Fin k))
    (c : Circuit Boolean.signature n m)
    {u u' : Fin c.size → Fin k → Fin k → Bool}
    {inputs inputs' : Fin n → Fin k → Bool}
    (hu : ∀ t j i, (j ∈ C ∨ i ∈ C) → u t j i = u' t j i)
    (hin : ∀ w, ∀ j ∈ C, inputs w j = inputs' w j)
    (j : Fin m) {i : Fin k} (hi : i ∈ C) :
    simulatedEvalCircuitOT C c u inputs j i =
      simulatedEvalCircuitOT C c u' inputs' j i := by
  simp only [simulatedEvalCircuitOT]
  cases c.outputs j with
  | input w => exact hin w i hi
  | gate g =>
    simp only [Wire.elim_gate]
    exact simulatedEvalProgramOT_congr_corrupted C c.program hu hin g hi

/-! ### Multiparty Functionalities, Real OT-Hybrid Execution, and Ideal Execution with Abort -/

/-- A `k`-party functionality mapping `k` inputs of `inWidth` bits to `k` outputs of `outWidth`
bits. -/
abbrev MultipartyFunctionality (k inWidth outWidth : ℕ) : Type :=
  (Fin k → BitString inWidth) → (Fin k → BitString outWidth)

/-- Pack `k` party bit-strings of width `w` into a flat wire vector `Fin (k * w) → Bool`. -/
def packInputs {k w : ℕ} (inputs : Fin k → BitString w) (idx : Fin (k * w)) : Bool :=
  let p := finProdFinEquiv.symm idx
  inputs p.1 p.2

/-- Unpack a flat wire vector `Fin (k * w) → Bool` into `k` party bit-strings of width `w`. -/
def unpackOutputs {k w : ℕ} (flat : Fin (k * w) → Bool) (p : Fin k) (b : Fin w) : Bool :=
  flat (finProdFinEquiv (p, b))

@[simp] theorem unpackOutputs_packInputs {k w : ℕ} (inputs : Fin k → BitString w) :
    unpackOutputs (packInputs inputs) = inputs := by
  ext p b
  simp [unpackOutputs, packInputs]

@[simp] theorem packInputs_unpackOutputs {k w : ℕ} (flat : Fin (k * w) → Bool) :
    packInputs (unpackOutputs flat) = flat := by
  ext idx
  simp only [unpackOutputs, packInputs, Prod.mk.eta, Equiv.apply_symm_apply]

/-- The `k`-party functionality computed by a De Morgan Boolean circuit `c` with `k * inWidth`
input wires and `k * outWidth` output wires. -/
def circuitFunctionality {k inWidth outWidth : ℕ}
    (c : Circuit Boolean.signature (k * inWidth) (k * outWidth)) :
    MultipartyFunctionality k inWidth outWidth :=
  fun inputs => unpackOutputs (c.eval Boolean.interpretation (packInputs inputs))

/-- Effective inputs when corrupted parties `C` submit `adv` and honest parties outside `C` submit
`honest`. -/
def effectiveInputs {k inWidth : ℕ} (C : Finset (Fin k))
    (honest adv : Fin k → BitString inWidth) (p : Fin k) : BitString inWidth :=
  if p ∈ C then adv p else honest p

/-- Restrict party outputs so that only corrupted parties `p ∈ C` retain their output bits, while
honest parties' private outputs are zeroed to `false`. -/
def maskOutputsToCorrupted {k outWidth : ℕ} (C : Finset (Fin k))
    (outputs : Fin k → BitString outWidth) (p : Fin k) (b : Fin outWidth) : Bool :=
  if p ∈ C then outputs p b else false

/-- Share a flat vector of input wires across `k` parties using `chooseHonestPivot C`. -/
def shareInputWires {k N : ℕ} [NeZero k] (C : Finset (Fin k))
    (x : Fin N → Bool) (r_in : Fin N → Fin k → Bool) (w : Fin N) : Fin k → Bool :=
  shareBitWithPivot (chooseHonestPivot C) (x w) (r_in w)

@[simp] theorem parity_shareInputWires {k N : ℕ} [NeZero k] (C : Finset (Fin k))
    (x : Fin N → Bool) (r_in : Fin N → Fin k → Bool) (w : Fin N) :
    parity k (shareInputWires C x r_in w) = x w :=
  parity_shareBitWithPivot (chooseHonestPivot C) (x w) (r_in w)

/-- For every corrupted party `i ∈ C` and every wire `w`, the input share of
`effectiveInputs C honest adv` equals the input share of `adv` alone, without any dependence on the
honest parties' inputs `honest`. -/
theorem shareInputWires_effectiveInputs_eq_of_mem {k inWidth : ℕ} [NeZero k]
    (C : Finset (Fin k)) (honest adv : Fin k → BitString inWidth)
    (r_in : Fin (k * inWidth) → Fin k → Bool)
    (w : Fin (k * inWidth)) {i : Fin k} (hi : i ∈ C) :
    shareInputWires C (packInputs (effectiveInputs C honest adv)) r_in w i =
      shareInputWires C (packInputs adv) r_in w i := by
  by_cases hne : (Finset.univ \ C).Nonempty
  · have hpivot : chooseHonestPivot C ∉ C := chooseHonestPivot_notMem hne
    have hne_pivot : i ≠ chooseHonestPivot C := fun h => hpivot (h ▸ hi)
    simp [shareInputWires, shareBitWithPivot_of_ne _ _ _ hne_pivot]
  · have hall : ∀ p : Fin k, p ∈ C := by
      intro p
      by_contra hp
      exact hne ⟨p, Finset.mem_sdiff.mpr ⟨Finset.mem_univ p, hp⟩⟩
    have heff : effectiveInputs C honest adv = adv := by
      ext p b
      simp [effectiveInputs, hall p]
    rw [heff]

/-- Project wire shares onto the corrupted party set `C`, zeroing out honest parties' shares. -/
def maskSharesToCorrupted {k N : ℕ} (C : Finset (Fin k))
    (shares : Fin N → Fin k → Bool) (w : Fin N) (i : Fin k) : Bool :=
  if i ∈ C then shares w i else false

/-- Project gate OT values onto pairs incident to `C`, zeroing out honest-to-honest entries. -/
def maskOTToCorrupted {k g : ℕ} (C : Finset (Fin k))
    (u : Fin g → Fin k → Fin k → Bool) (t : Fin g) (j i : Fin k) : Bool :=
  if j ∈ C ∨ i ∈ C then u t j i else false

theorem maskOTToCorrupted_eq_of_mem {k g : ℕ} (C : Finset (Fin k))
    (u : Fin g → Fin k → Fin k → Bool) (t : Fin g) (j i : Fin k)
    (h : j ∈ C ∨ i ∈ C) :
    maskOTToCorrupted C u t j i = u t j i := by
  simp [maskOTToCorrupted, h]

theorem packInputs_maskOutputsToCorrupted_of_mem {k outWidth : ℕ} (C : Finset (Fin k))
    (outputs : Fin k → BitString outWidth) (o : Fin (k * outWidth))
    (ho : (finProdFinEquiv.symm o).1 ∈ C) :
    packInputs (maskOutputsToCorrupted C outputs) o = packInputs outputs o := by
  simp only [packInputs, maskOutputsToCorrupted, ho, ↓reduceIte]

/-- Combined honest output reconstruction shares sent to corrupted parties for output wires
belonging to corrupted parties `p ∈ C` (and `false` on output wires of honest parties `p ∉ C`). -/
def honestOutputReconstructionShares {k outWidth : ℕ} (C : Finset (Fin k))
    (outShares : Fin (k * outWidth) → Fin k → Bool)
    (o : Fin (k * outWidth)) : Bool :=
  if (finProdFinEquiv.symm o).1 ∈ C then parityOn (Finset.univ \ C) (outShares o) else false

/-- Simulated combined honest output reconstruction shares computed solely from the corrupted
parties' ideal outputs `corruptedOutputs` and simulated corrupted wire shares `simOutShares`. -/
def simulatedHonestOutputShares {k outWidth : ℕ} (C : Finset (Fin k))
    (corruptedOutputs : Fin k → BitString outWidth)
    (simOutShares : Fin (k * outWidth) → Fin k → Bool)
    (o : Fin (k * outWidth)) : Bool :=
  if (finProdFinEquiv.symm o).1 ∈ C then
    packInputs corruptedOutputs o ^^ parityOn C (simOutShares o)
  else
    false

/-- Each honest party `i ∉ C` receives `some (y i)` when `deliver = true` and `none` (`⊥`) on
abort (`deliver = false`); corrupted parties `i ∈ C` have their output recorded in the adversary's
view. -/
abbrev HonestOutputs (k outWidth : ℕ) : Type :=
  Fin k → Option (BitString outWidth)

/-- Format the honest parties' output vector given `deliver : Bool` and full outputs `y`. -/
def formatHonestOutputs {k outWidth : ℕ} (C : Finset (Fin k))
    (deliver : Bool) (y : Fin k → BitString outWidth) (i : Fin k) :
    Option (BitString outWidth) :=
  if i ∈ C then none else if deliver then some (y i) else none

/-- **Static malicious adversary in the OT-hybrid model**:
1. Submits effective corrupted inputs `chooseInputs` and an input-phase validity flag
   `corruptedInputValid` (modeling whether the adversary's input-commitment OTs are well-formed).
2. Observes the corrupted input shares and corrupted gate OT transcript, and decides whether to
   follow the authenticated gate checks (`gatePhaseConsistent = true`) or trigger an early abort
   (`gatePhaseConsistent = false`), in which case `finalizeEarlyAbort` produces the adversary's
   view without seeing any honest output reconstruction shares.
3. If the gate phase succeeds, receives the honest parties' output reconstruction shares for `C`'s
   outputs and runs `finalize` to produce its final `View` together with the rushing
   `deliver : Bool` decision for the honest parties' outputs. -/
structure MaliciousOTAdversary (k inWidth outWidth g : ℕ) (View : Type) where
  /-- Effective inputs chosen by the adversary for corrupted parties `i ∈ C`. -/
  chooseInputs : Fin k → BitString inWidth
  /-- Whether the adversary submits valid initial input-commitment OT shares. -/
  corruptedInputValid : Bool
  /-- Whether the adversary's gate-phase OT inputs pass the OT-hybrid consistency check. -/
  gatePhaseConsistent :
    (Fin (k * inWidth) → Fin k → Bool) → (Fin g → Fin k → Fin k → Bool) → Bool
  /-- Adversary output view when an early abort occurs before output reconstruction. -/
  finalizeEarlyAbort :
    (Fin (k * inWidth) → Fin k → Bool) → (Fin g → Fin k → Fin k → Bool) → View
  /-- Adversary output view and honest-output delivery flag after receiving output reconstruction
  shares for the corrupted parties' outputs. -/
  finalize :
    (Fin (k * inWidth) → Fin k → Bool) → (Fin g → Fin k → Fin k → Bool) →
    (Fin (k * outWidth) → Bool) → View × Bool

/-- **Ideal-world simulator with abort**:
Submits effective inputs `chooseInputs` for the corrupted parties `C`, receives from the trusted
party ONLY the corrupted parties' outputs `maskOutputsToCorrupted C (F x')`, and samples the
simulated adversary view and `deliver : Bool` flag deciding whether honest parties receive their
outputs (`some (F x' i)`) or abort (`none`). -/
structure IdealSimulator (k inWidth outWidth : ℕ) (View : Type) where
  /-- Effective inputs submitted to the ideal functionality for corrupted parties `i ∈ C`. -/
  chooseInputs : Fin k → BitString inWidth
  /-- Randomized simulation mapping the corrupted parties' outputs to `(view, deliver)`. -/
  run : (Fin k → BitString outWidth) → PMF (View × Bool)

/-- **Ideal execution with abort** of a `k`-party functionality `F` with static corruption set `C`
and simulator `S` on honest inputs `inputs`. -/
noncomputable def idealExecutionWithAbort {k inWidth outWidth : ℕ} {View : Type}
    (F : MultipartyFunctionality k inWidth outWidth)
    (C : Finset (Fin k))
    (S : IdealSimulator k inWidth outWidth View)
    (inputs : Fin k → BitString inWidth) :
    PMF (HonestOutputs k outWidth × View) :=
  let effInputs := effectiveInputs C inputs S.chooseInputs
  let fullOutputs := F effInputs
  let corruptedOutputs := maskOutputsToCorrupted C fullOutputs
  (S.run corruptedOutputs).map fun (view, deliver) =>
    (formatHonestOutputs C deliver fullOutputs, view)

/-- Deterministic step of the **real OT-hybrid execution** given input randomness `r_in` and gate
OT sender masks `r_masks`. Honest outputs are reconstructed directly from the OT-evaluated circuit
shares `evalCircuitOT c r_masks inputShares`. -/
def realOTHybridStep {k inWidth outWidth : ℕ} [NeZero k] {View : Type}
    (c : Circuit Boolean.signature (k * inWidth) (k * outWidth))
    (C : Finset (Fin k))
    (A : MaliciousOTAdversary k inWidth outWidth c.size View)
    (inputs : Fin k → BitString inWidth)
    (r_in : Fin (k * inWidth) → Fin k → Bool)
    (r_masks : Fin c.size → Fin k → Fin k → Bool) :
    HonestOutputs k outWidth × View :=
  let effInputs := effectiveInputs C inputs A.chooseInputs
  let inputShares := shareInputWires C (packInputs effInputs) r_in
  let outShares := evalCircuitOT c r_masks inputShares
  let reconstructedOutputs := unpackOutputs (fun o => parity k (outShares o))
  let corrInShares := maskSharesToCorrupted C inputShares
  let corrOT := maskOTToCorrupted C (programMaskToCorruptedOT C c.program inputShares r_masks)
  if A.corruptedInputValid && A.gatePhaseConsistent corrInShares corrOT then
    let honestOutShares := honestOutputReconstructionShares C outShares
    let (view, deliver) := A.finalize corrInShares corrOT honestOutShares
    (formatHonestOutputs C deliver reconstructedOutputs, view)
  else
    let view := A.finalizeEarlyAbort corrInShares corrOT
    (formatHonestOutputs C false reconstructedOutputs, view)

/-- **Real execution in the ideal OT-hybrid model**: samples uniform input-share randomness `r_in`
and uniform gate OT sender masks `r_masks`, and executes `realOTHybridStep`. -/
noncomputable def realOTHybridExecution {k inWidth outWidth : ℕ} [NeZero k] {View : Type}
    (c : Circuit Boolean.signature (k * inWidth) (k * outWidth))
    (C : Finset (Fin k))
    (A : MaliciousOTAdversary k inWidth outWidth c.size View)
    (inputs : Fin k → BitString inWidth) :
    PMF (HonestOutputs k outWidth × View) :=
  (PMF.uniformOfFintype (Fin (k * inWidth) → Fin k → Bool)).bind fun r_in =>
    (PMF.uniformOfFintype (Fin c.size → Fin k → Fin k → Bool)).map fun r_masks =>
      realOTHybridStep c C A inputs r_in r_masks

/-- Deterministic step of the **Kilian / IPS black-box simulator** given simulated input shares
`r_in`, simulated OT transcript `u`, and the corrupted parties' outputs `corruptedOutputs` from the
ideal functionality. Notice that `kilianSimulatorStep` does **not** take the honest parties' inputs
`inputs`. -/
def kilianSimulatorStep {k inWidth outWidth : ℕ} [NeZero k] {View : Type}
    (c : Circuit Boolean.signature (k * inWidth) (k * outWidth))
    (C : Finset (Fin k))
    (A : MaliciousOTAdversary k inWidth outWidth c.size View)
    (corruptedOutputs : Fin k → BitString outWidth)
    (r_in : Fin (k * inWidth) → Fin k → Bool)
    (u : Fin c.size → Fin k → Fin k → Bool) :
    View × Bool :=
  let simInShares := shareInputWires C (packInputs A.chooseInputs) r_in
  let corrInShares := maskSharesToCorrupted C simInShares
  let corrOT := maskOTToCorrupted C u
  if A.corruptedInputValid && A.gatePhaseConsistent corrInShares corrOT then
    let simOutShares := simulatedEvalCircuitOT C c corrOT simInShares
    let simHonestOut := simulatedHonestOutputShares C corruptedOutputs simOutShares
    A.finalize corrInShares corrOT simHonestOut
  else
    (A.finalizeEarlyAbort corrInShares corrOT, false)

/-- **Kilian / IPS ideal-world simulator** (`kilianSimulator`): runs the malicious OT-hybrid
adversary `A` black-box by extracting `A.chooseInputs` and simulating all corrupted input shares,
OT receiver outputs, and output reconstruction shares from uniform randomness and the corrupted
parties' ideal outputs. -/
noncomputable def kilianSimulator {k inWidth outWidth : ℕ} [NeZero k] {View : Type}
    (C : Finset (Fin k))
    (c : Circuit Boolean.signature (k * inWidth) (k * outWidth))
    (A : MaliciousOTAdversary k inWidth outWidth c.size View) :
    IdealSimulator k inWidth outWidth View where
  chooseInputs := A.chooseInputs
  run corruptedOutputs :=
    (PMF.uniformOfFintype (Fin (k * inWidth) → Fin k → Bool)).bind fun r_in =>
      (PMF.uniformOfFintype (Fin c.size → Fin k → Fin k → Bool)).map fun u =>
        kilianSimulatorStep c C A corruptedOutputs r_in u

/-- Key pointwise simulation identity: for every input assignment `inputs`, input-share randomness
`r_in`, and OT sender masks `r_masks`, setting
`u = programMaskToCorruptedOT C c.program inputShares r_masks` makes the real OT-hybrid step
identically equal to the ideal execution step with `kilianSimulatorStep`. -/
theorem realOTHybridStep_eq_kilianSimulatorStep {k inWidth outWidth : ℕ} [NeZero k] {View : Type}
    (c : Circuit Boolean.signature (k * inWidth) (k * outWidth))
    (C : Finset (Fin k))
    (A : MaliciousOTAdversary k inWidth outWidth c.size View)
    (inputs : Fin k → BitString inWidth)
    (r_in : Fin (k * inWidth) → Fin k → Bool)
    (r_masks : Fin c.size → Fin k → Fin k → Bool) :
    let effInputs := effectiveInputs C inputs A.chooseInputs
    let fullOutputs := circuitFunctionality c effInputs
    let inputShares := shareInputWires C (packInputs effInputs) r_in
    let u := programMaskToCorruptedOT C c.program inputShares r_masks
    let s := kilianSimulatorStep c C A (maskOutputsToCorrupted C fullOutputs) r_in u
    realOTHybridStep c C A inputs r_in r_masks =
      (formatHonestOutputs C s.2 fullOutputs, s.1) := by
  dsimp only [realOTHybridStep, kilianSimulatorStep]
  set effInputs := effectiveInputs C inputs A.chooseInputs
  set fullOutputs := circuitFunctionality c effInputs
  set inputShares := shareInputWires C (packInputs effInputs) r_in
  set simInShares := shareInputWires C (packInputs A.chooseInputs) r_in
  set u := programMaskToCorruptedOT C c.program inputShares r_masks
  have hin_corr (w : Fin (k * inWidth)) {i : Fin k} (hi : i ∈ C) :
      inputShares w i = simInShares w i :=
    shareInputWires_effectiveInputs_eq_of_mem C inputs A.chooseInputs r_in w hi
  have hmask_in : maskSharesToCorrupted C inputShares = maskSharesToCorrupted C simInShares := by
    ext w i
    by_cases hi : i ∈ C
    · simp [maskSharesToCorrupted, hi, hin_corr w hi]
    · simp [maskSharesToCorrupted, hi]
  have hreconstruct :
      unpackOutputs (fun o => parity k (evalCircuitOT c r_masks inputShares o)) = fullOutputs := by
    ext p b
    simp [inputShares, fullOutputs, unpackOutputs, circuitFunctionality]
  have hhonest_out :
      honestOutputReconstructionShares C (evalCircuitOT c r_masks inputShares) =
        simulatedHonestOutputShares C (maskOutputsToCorrupted C fullOutputs)
          (simulatedEvalCircuitOT C c (maskOTToCorrupted C u) simInShares) := by
    ext o
    simp only [honestOutputReconstructionShares, simulatedHonestOutputShares]
    split_ifs with ho
    · rw [parityOn_univ_sdiff C (evalCircuitOT c r_masks inputShares o),
        parity_evalCircuitOT]
      have hpar : (fun i => parity k (inputShares i)) = packInputs effInputs := by
        funext i
        exact parity_shareInputWires C (packInputs effInputs) r_in i
      have hpack :
          c.eval Boolean.interpretation (fun i => parity k (inputShares i)) o =
            packInputs (maskOutputsToCorrupted C fullOutputs) o := by
        rw [hpar, packInputs_maskOutputsToCorrupted_of_mem C fullOutputs o ho]
        simp [fullOutputs, circuitFunctionality]
      rw [hpack]
      congr 1
      apply parityOn_congr
      intro i hi
      rw [evalCircuitOT_eq_simulatedEvalCircuitOT_of_mem C c r_masks inputShares o hi]
      exact simulatedEvalCircuitOT_congr_corrupted C c
        (fun t j i' hmem => (maskOTToCorrupted_eq_of_mem C u t j i' hmem).symm)
        (fun w j hj => hin_corr w hj) o hi
    · rfl
  rw [hmask_in, hreconstruct, hhonest_out]
  split_ifs <;> rfl

/-- **Completeness of Oblivious Transfer (exact distributional simulation)**
[Kilian1988, IPS2008, Goldreich2004Vol2]:
For every `k ≥ 1`, every `k`-party De Morgan Boolean circuit `c`, every static corruption set
`C : Finset (Fin k)`, every malicious OT-hybrid adversary `A`, and every input vector `inputs`,
the real OT-hybrid execution distribution is **identically equal** to the ideal execution with
abort under `kilianSimulator C c A`. -/
theorem realOTHybridExecution_eq_idealExecutionWithAbort
    {k inWidth outWidth : ℕ} [NeZero k] {View : Type}
    (c : Circuit Boolean.signature (k * inWidth) (k * outWidth))
    (C : Finset (Fin k))
    (A : MaliciousOTAdversary k inWidth outWidth c.size View)
    (inputs : Fin k → BitString inWidth) :
    realOTHybridExecution c C A inputs =
      idealExecutionWithAbort (circuitFunctionality c) C (kilianSimulator C c A) inputs := by
  simp only [realOTHybridExecution, idealExecutionWithAbort, kilianSimulator, PMF.map_bind]
  apply PMF.bind_congr_on_support
  intro r_in _
  set effInputs := effectiveInputs C inputs A.chooseInputs
  set fullOutputs := circuitFunctionality c effInputs
  set inputShares := shareInputWires C (packInputs effInputs) r_in
  calc
    (PMF.uniformOfFintype (Fin c.size → Fin k → Fin k → Bool)).map
        (realOTHybridStep c C A inputs r_in)
      = ((PMF.uniformOfFintype (Fin c.size → Fin k → Fin k → Bool)).map
          (programMaskToCorruptedOT C c.program inputShares)).map
          ((fun x => (formatHonestOutputs C x.2 fullOutputs, x.1)) ∘
            kilianSimulatorStep c C A (maskOutputsToCorrupted C fullOutputs) r_in) := by
        rw [PMF.map_comp]
        congr 1
        funext r_masks
        exact realOTHybridStep_eq_kilianSimulatorStep c C A inputs r_in r_masks
    _ = ((PMF.uniformOfFintype (Fin c.size → Fin k → Fin k → Bool)).map
          (kilianSimulatorStep c C A (maskOutputsToCorrupted C fullOutputs) r_in)).map
          (fun x => (formatHonestOutputs C x.2 fullOutputs, x.1)) := by
        rw [PMF.uniformOfFintype_map_equiv, PMF.map_comp]

open scoped Cslib.Probability.PMF in
/-- Statistical distance between the real OT-hybrid execution and the ideal execution with abort is
zero. -/
@[simp] theorem dist_realOTHybridExecution_idealExecutionWithAbort
    {k inWidth outWidth : ℕ} [NeZero k] {View : Type} [Fintype View]
    (c : Circuit Boolean.signature (k * inWidth) (k * outWidth))
    (C : Finset (Fin k))
    (A : MaliciousOTAdversary k inWidth outWidth c.size View)
    (inputs : Fin k → BitString inWidth) :
    dist (realOTHybridExecution c C A inputs)
      (idealExecutionWithAbort (circuitFunctionality c) C (kilianSimulator C c A) inputs) = 0 := by
  rw [realOTHybridExecution_eq_idealExecutionWithAbort, dist_self]

/-! ### Statistical and Computational Indistinguishability for Multiparty Families -/

/-- A family of `k`-party functionalities indexed by security parameter `n : ℕ` is
**statistically secure with abort** in the OT-hybrid model if for every static corruption set `C`,
every family of malicious OT-hybrid adversaries `A`, and every input assignment family `inputs`,
there is a family of ideal-world simulators `S` such that the real OT-hybrid execution and ideal
execution with abort have zero distinguishing advantage against every Boolean distinguisher. -/
def StatisticallySecureFamilyWithAbort {k : ℕ} [NeZero k] {inWidth outWidth : ℕ → ℕ}
    {View : ℕ → Type}
    (c : (n : ℕ) → Circuit Boolean.signature (k * inWidth n) (k * outWidth n)) : Prop :=
  ∀ (C : Finset (Fin k))
    (A : (n : ℕ) → MaliciousOTAdversary k (inWidth n) (outWidth n) (c n).size (View n))
    (inputs : (n : ℕ) → Fin k → BitString (inWidth n)),
    ∃ S : (n : ℕ) → IdealSimulator k (inWidth n) (outWidth n) (View n),
      Game.IndistinguishableWithError
        (fun (distinguisher : (n : ℕ) → HonestOutputs k (outWidth n) × View n → PMF Bool) n =>
          (realOTHybridExecution (c n) C (A n) (inputs n)).bind (distinguisher n))
        (fun (distinguisher : (n : ℕ) → HonestOutputs k (outWidth n) × View n → PMF Bool) n =>
          (idealExecutionWithAbort (circuitFunctionality (c n)) C (S n) (inputs n)).bind
            (distinguisher n))
        (fun _ => True) (fun _ => 0)

/-- **Statistical OT-Hybrid Completeness**: every family of `k`-party De Morgan Boolean circuits is
statistically secure with abort in the ideal OT-hybrid model with zero error. -/
theorem ot_complete_statisticallySecureWithAbort {k : ℕ} [NeZero k] {inWidth outWidth : ℕ → ℕ}
    {View : ℕ → Type}
    (c : (n : ℕ) → Circuit Boolean.signature (k * inWidth n) (k * outWidth n)) :
    StatisticallySecureFamilyWithAbort (View := View) c := by
  intro C A inputs
  refine ⟨fun n => kilianSimulator C (c n) (A n), fun distinguisher _ n => ?_⟩
  dsimp only
  rw [realOTHybridExecution_eq_idealExecutionWithAbort, Game.advantage_self]

/-- **Polynomial-time multiparty functionality family**: a family of `k`-party functionalities
indexed by security parameter `n : ℕ`, realized by a family of De Morgan Boolean circuits whose gate
count `(c n).size`, per-party input width `inWidth n`, and per-party output width `outWidth n` are
polynomially bounded. -/
structure PolyTimeFunctionality (k : ℕ) where
  /-- Per-party input bit width at security parameter `n`. -/
  inWidth : ℕ → ℕ
  /-- Per-party output bit width at security parameter `n`. -/
  outWidth : ℕ → ℕ
  /-- De Morgan Boolean circuit computing the functionality at security parameter `n`. -/
  circuit : (n : ℕ) → Circuit Boolean.signature (k * inWidth n) (k * outWidth n)
  /-- Input width is polynomially bounded in `n`. -/
  poly_inWidth : PolynomiallyBounded inWidth
  /-- Output width is polynomially bounded in `n`. -/
  poly_outWidth : PolynomiallyBounded outWidth
  /-- Circuit size (number of gates) is polynomially bounded in `n`. -/
  poly_size : PolynomiallyBounded (fun n => (circuit n).size)

/-- Total number of pairwise `idealOT` calls made by `evalCircuitOT` on a `k`-party circuit `c`:
at most `k * k` calls per gate of `c`. -/
def otCallBudget (k : ℕ) {n m : ℕ} (c : Circuit Boolean.signature n m) : ℕ :=
  c.size * (k * k)

/-- For every `PolyTimeFunctionality`, the total number of `idealOT` calls is polynomially bounded
in the security parameter `n`. -/
theorem PolyTimeFunctionality.polynomiallyBounded_otCallBudget {k : ℕ}
    (F : PolyTimeFunctionality k) :
    PolynomiallyBounded (fun n => otCallBudget k (F.circuit n)) := by
  unfold otCallBudget
  have hconst : PolynomiallyBounded (fun _ : ℕ => k * k) := PolynomiallyBounded.const (k * k)
  exact F.poly_size.mul hconst

/-- Evaluating `circuitFunctionality (F.circuit n)` on party inputs `inputs` agrees with the
uniform polynomial-time circuit evaluator `Boolean.evalOutput` (certified by
`Cslib.Circuits.Boolean.computableTidilyInPolyTime_evalOutput`) on `(F.circuit n).code.1`. -/
theorem PolyTimeFunctionality.circuitFunctionality_apply_eq_evalOutput {k : ℕ}
    (F : PolyTimeFunctionality k) (n : ℕ)
    (inputs : Fin k → BitString (F.inWidth n)) (p : Fin k) (b : Fin (F.outWidth n)) :
    circuitFunctionality (F.circuit n) inputs p b =
      Boolean.evalOutput (List.ofFn (packInputs inputs)) (F.circuit n).code.1
        ((F.circuit n).outputs (finProdFinEquiv (p, b))).toNat :=
  (F.circuit n).eval_eq_evalOutput (packInputs inputs) (finProdFinEquiv (p, b))

/-- Encode a joint outcome `(HonestOutputs k (outWidth n) × List Bool)` as a bit string `List Bool`
for uniform PPT distinguishers: concatenates each party's delivery bit (`true` for `some`, `false`
for `none`) and output bits, followed by the adversary's output word. -/
def encodeJointOutcome {k outWidth : ℕ}
    (outcome : HonestOutputs k outWidth × List Bool) : List Bool :=
  (List.ofFn fun i : Fin k =>
    match outcome.1 i with
    | none => [false]
    | some bits => true :: List.ofFn bits).flatten ++ outcome.2

/-- A `PolyTimeFunctionality` is **computationally secure with abort** in the OT-hybrid model when
for every static corruption set `C`, every family of malicious OT-hybrid adversaries `A`, and every
input family `inputs`, there exists an ideal-world simulator family `S` such that the encoded real
OT-hybrid execution and ideal execution with abort are `ComputationallyIndistinguishable` against
every uniform strict PPT distinguisher (`IsPPT encBool`). -/
def ComputationallySecureWithAbort {k : ℕ} [NeZero k] (F : PolyTimeFunctionality k) : Prop :=
  ∀ (C : Finset (Fin k))
    (A : (n : ℕ) → MaliciousOTAdversary k (F.inWidth n) (F.outWidth n) (F.circuit n).size
      (List Bool))
    (inputs : (n : ℕ) → Fin k → BitString (F.inWidth n)),
    ∃ S : (n : ℕ) → IdealSimulator k (F.inWidth n) (F.outWidth n) (List Bool),
      ComputationallyIndistinguishable
        (fun n => (realOTHybridExecution (F.circuit n) C (A n) (inputs n)).map encodeJointOutcome)
        (fun n =>
          (idealExecutionWithAbort (circuitFunctionality (F.circuit n)) C (S n) (inputs n)).map
            encodeJointOutcome)

/-- **Completeness of Oblivious Transfer for Polynomial-Time Multiparty Functionalities**
[Kilian1988, IPS2008, Goldreich2004Vol2]:
Every polynomial-time multiparty functionality family `F : PolyTimeFunctionality k` is
computationally (and statistically) secure with abort in the ideal OT-hybrid model against any
static malicious corruption set `C : Finset (Fin k)`. -/
theorem ot_complete_computationallySecureWithAbort {k : ℕ} [NeZero k]
    (F : PolyTimeFunctionality k) :
    ComputationallySecureWithAbort F := by
  intro C A inputs
  refine ⟨fun n => kilianSimulator C (F.circuit n) (A n), ?_⟩
  have heq :
      (fun n => (realOTHybridExecution (F.circuit n) C (A n) (inputs n)).map encodeJointOutcome) =
        (fun n =>
          (idealExecutionWithAbort (circuitFunctionality (F.circuit n)) C
            (kilianSimulator C (F.circuit n) (A n)) (inputs n)).map encodeJointOutcome) := by
    funext n
    rw [realOTHybridExecution_eq_idealExecutionWithAbort]
  rw [heq]
  exact ComputationallyIndistinguishable.refl _

/-! ### Impossibility of Guaranteed Output Delivery and Fairness ([Cleve1986]) -/

/-- An execution distribution guarantees **output delivery** for honest parties outside `C` when
every supported outcome delivers `some y` (never `none`) to every honest party `i ∉ C`. -/
def GuaranteedOutputDelivery {k outWidth : ℕ} {View : Type}
    (C : Finset (Fin k)) (exec : PMF (HonestOutputs k outWidth × View)) : Prop :=
  ∀ outcome ∈ exec.support, ∀ i : Fin k, i ∉ C → (outcome.1 i).isSome = true

/-- A malicious adversary that aborts during output reconstruction (`deliver = false`), preventing
output delivery to honest parties. -/
def abortingAdversary (k inWidth outWidth g : ℕ) :
    MaliciousOTAdversary k inWidth outWidth g Unit where
  chooseInputs := fun _ _ => false
  corruptedInputValid := true
  gatePhaseConsistent := fun _ _ => true
  finalizeEarlyAbort := fun _ _ => ()
  finalize := fun _ _ _ => ((), false)

/-- In the OT-hybrid execution with `abortingAdversary`, every honest party `i ∉ C` outputs `none`
with certainty. -/
@[simp] theorem realOTHybridExecution_abortingAdversary
    {k inWidth outWidth : ℕ} [NeZero k]
    (c : Circuit Boolean.signature (k * inWidth) (k * outWidth))
    (C : Finset (Fin k))
    (inputs : Fin k → BitString inWidth) :
    realOTHybridExecution c C (abortingAdversary k inWidth outWidth c.size) inputs =
      PMF.pure (fun _ => none, ()) := by
  rw [realOTHybridExecution_eq_idealExecutionWithAbort]
  have hstep (corruptedOutputs : Fin k → BitString outWidth)
      (r_in : Fin (k * inWidth) → Fin k → Bool)
      (u : Fin c.size → Fin k → Fin k → Bool) :
      kilianSimulatorStep c C (abortingAdversary k inWidth outWidth c.size)
        corruptedOutputs r_in u = ((), false) := rfl
  have hfmt (y : Fin k → BitString outWidth) :
      formatHonestOutputs C false y = fun _ => none := by
    ext i
    simp [formatHonestOutputs]
  simp only [idealExecutionWithAbort, kilianSimulator, hstep, PMF.map_comp, Function.comp_def,
    hfmt, PMF.bind_const]
  exact PMF.map_const _ _

/-- **Security with abort does not guarantee output delivery**: whenever there is at least one
honest party `h ∉ C`, the aborting adversary forces all honest parties to output `none`, violating
`GuaranteedOutputDelivery`. -/
theorem not_guaranteedOutputDelivery_of_abort
    {k inWidth outWidth : ℕ} [NeZero k]
    (c : Circuit Boolean.signature (k * inWidth) (k * outWidth))
    (C : Finset (Fin k)) (hHonest : ∃ h : Fin k, h ∉ C)
    (inputs : Fin k → BitString inWidth) :
    ¬ GuaranteedOutputDelivery C
      (realOTHybridExecution c C (abortingAdversary k inWidth outWidth c.size) inputs) := by
  obtain ⟨h, hh⟩ := hHonest
  rw [realOTHybridExecution_abortingAdversary]
  intro hdeliv
  have hsome := hdeliv (fun _ => none, ()) (by simp) h hh
  simp at hsome

/-- Explicit 4-gate De Morgan circuit on 2 inputs and 2 outputs computing the 2-party XOR
functionality `(x₀, x₁) ↦ (x₀ ^^ x₁, x₀ ^^ x₁)` via `(x₀ || x₁) && !(x₀ && x₁)`:
- Gate 0: `x₀ || x₁`
- Gate 1: `x₀ && x₁`
- Gate 2: `!(x₀ && x₁)`
- Gate 3: `(x₀ || x₁) && !(x₀ && x₁)` -/
def twoPartyXorCircuit : Circuit Boolean.signature (2 * 1) (2 * 1) :=
  let p0 : Program Boolean.signature 2 0 := .empty
  let l0 : Line Boolean.signature 2 0 := ⟨.or, ![.input 0, .input 1]⟩
  let p1 : Program Boolean.signature 2 1 := p0.gate l0
  let l1 : Line Boolean.signature 2 1 := ⟨.and, ![.input 0, .input 1]⟩
  let p2 : Program Boolean.signature 2 2 := p1.gate l1
  let l2 : Line Boolean.signature 2 2 := ⟨.not, ![.gate 1]⟩
  let p3 : Program Boolean.signature 2 3 := p2.gate l2
  let l3 : Line Boolean.signature 2 3 := ⟨.and, ![.gate 0, .gate 2]⟩
  let p4 : Program Boolean.signature 2 4 := p3.gate l3
  ⟨p4, fun _ => .gate 3⟩

/-- `twoPartyXorCircuit` computes `x 0 ^^ x 1` on both output wires. -/
@[simp] theorem eval_twoPartyXorCircuit (x : Fin (2 * 1) → Bool) (j : Fin (2 * 1)) :
    twoPartyXorCircuit.eval Boolean.interpretation x j = (x 0 ^^ x 1) := by
  revert x j
  decide

/-- On 2-party 1-bit inputs `inputs : Fin 2 → BitString 1`,
`circuitFunctionality twoPartyXorCircuit` outputs `inputs 0 0 ^^ inputs 1 0` to both parties. -/
@[simp] theorem circuitFunctionality_twoPartyXorCircuit
    (inputs : Fin 2 → BitString 1) (p : Fin 2) (b : Fin 1) :
    circuitFunctionality twoPartyXorCircuit inputs p b = (inputs 0 0 ^^ inputs 1 0) := by
  revert inputs p b
  decide

/-- **Rushing unfair adversary for 2-party XOR** controlling corrupted party `0` (`C = {0}`):
submits effective input `false` for party `0`, runs the OT gate evaluation honestly, reconstructs
the XOR output bit `y₀ = false ^^ x₁ = x₁` from honest party `1`'s output share `honestOut 0` and
its own output share `simOutShares 0 0`, outputs `view = y₀` (learning honest party `1`'s exact
input bit `x₁`), and aborts (`deliver = false`) so honest party `1` receives `none`! -/
def unfairXorAdversary : MaliciousOTAdversary 2 1 1 twoPartyXorCircuit.size Bool where
  chooseInputs := fun _ _ => false
  corruptedInputValid := true
  gatePhaseConsistent := fun _ _ => true
  finalizeEarlyAbort := fun _ _ => false
  finalize := fun corrInShares corrOT honestOut =>
    let simOut := simulatedEvalCircuitOT {0} twoPartyXorCircuit corrOT corrInShares
    (honestOut 0 ^^ simOut 0 0, false)

/-- **Unfairness of Security with Abort for 2-Party XOR** [Cleve1986, Goldreich2004Vol2]:
When party `0` is corrupted (`C = {0}`) and runs `unfairXorAdversary`, the real OT-hybrid execution
(and ideal execution with abort) is a point mass at `((fun _ => none), inputs 1 0)`:
1. Honest party `1` receives `none` (abort, no output delivered), while
2. Corrupted party `0` learns the exact functionality output `inputs 1 0` (honest party `1`'s
   secret input bit) with probability `1`! -/
theorem unfair_twoPartyXor_execution (inputs : Fin 2 → BitString 1) :
    realOTHybridExecution twoPartyXorCircuit ({0} : Finset (Fin 2)) unfairXorAdversary inputs =
      PMF.pure (fun _ => none, inputs 1 0) := by
  rw [realOTHybridExecution_eq_idealExecutionWithAbort]
  have hstep (r_in : Fin (2 * 1) → Fin 2 → Bool)
      (u : Fin twoPartyXorCircuit.size → Fin 2 → Fin 2 → Bool) :
      kilianSimulatorStep twoPartyXorCircuit ({0} : Finset (Fin 2)) unfairXorAdversary
        (maskOutputsToCorrupted ({0} : Finset (Fin 2))
          (circuitFunctionality twoPartyXorCircuit
            (effectiveInputs ({0} : Finset (Fin 2)) inputs unfairXorAdversary.chooseInputs)))
        r_in u = (inputs 1 0, false) := by
    dsimp only [kilianSimulatorStep, unfairXorAdversary]
    simp only [Bool.and_self, ↓reduceIte, Prod.mk.injEq, and_true]
    set simIn := shareInputWires ({0} : Finset (Fin 2)) (packInputs fun _ _ => false) r_in
    set corrIn := maskSharesToCorrupted ({0} : Finset (Fin 2)) simIn
    set corrOT := maskOTToCorrupted ({0} : Finset (Fin 2)) u
    have hsim_eq :
        simulatedEvalCircuitOT ({0} : Finset (Fin 2)) twoPartyXorCircuit corrOT corrIn 0 0 =
          simulatedEvalCircuitOT ({0} : Finset (Fin 2)) twoPartyXorCircuit corrOT simIn 0 0 :=
      simulatedEvalCircuitOT_congr_corrupted ({0} : Finset (Fin 2)) twoPartyXorCircuit
        (fun _ _ _ _ => rfl)
        (fun w j hj => by simp [corrIn, maskSharesToCorrupted, hj])
        0 (Finset.mem_singleton_self 0)
    have hpar_singleton (s : Fin 2 → Bool) :
        parityOn ({0} : Finset (Fin 2)) s = s 0 := by
      rw [parityOn_eq_sum, Finset.sum_singleton]
    have hfst : (finProdFinEquiv.symm (0 : Fin (2 * 1))).1 ∈ ({0} : Finset (Fin 2)) := by
      decide
    have hout :
        packInputs
          (maskOutputsToCorrupted ({0} : Finset (Fin 2))
            (circuitFunctionality twoPartyXorCircuit
              (effectiveInputs ({0} : Finset (Fin 2)) inputs (fun _ _ => false)))) 0 =
          inputs 1 0 := by
      revert inputs
      decide
    simp only [simulatedHonestOutputShares, hfst, ↓reduceIte, hpar_singleton, hsim_eq,
      Bool.xor_assoc, Bool.xor_self, Bool.xor_false, hout]
  have hfmt (y : Fin 2 → BitString 1) :
      formatHonestOutputs ({0} : Finset (Fin 2)) false y = fun _ => none := by
    ext i
    simp [formatHonestOutputs]
  simp only [idealExecutionWithAbort, kilianSimulator, hstep, PMF.map_comp, Function.comp_def,
    hfmt, PMF.bind_const]
  exact PMF.map_const _ _

/-- **Cleve's Impossibility of Fair Fallback against Rushing Abort** [Cleve1986]:
If an honest party attempts to eliminate `none` on abort by substituting any fallback bit
`fallback : Bool` when the corrupted party aborts after learning the true balanced output bit
`y ← PMF.uniformOfFintype Bool`, the corrupted party can abort selectively whenever `y ≠ fallback`,
forcing the honest party's output to equal the constant `fallback` while the corrupted party still
learns `y`—so the two parties' outputs disagree with probability `1 / 2`. -/
theorem cleve_unfair_fallback (fallback : Bool) :
    ((PMF.uniformOfFintype Bool).toOuterMeasure
      {y : Bool | (if y != fallback then fallback else y) ≠ y}).toReal = 1 / 2 := by
  let event : Set Bool := {y : Bool | (if y != fallback then fallback else y) ≠ y}
  have hcard : (Finset.univ.filter (· ∈ event)).card = 1 := by
    cases fallback <;> decide
  change ((PMF.uniformOfFintype Bool).toOuterMeasure event).toReal = 1 / 2
  rw [PMF.toOuterMeasure_uniformOfFintype_toReal, hcard]
  norm_num

end Cslib.Crypto.Multiparty
