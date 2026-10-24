/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (design prototype for #643; not for merge)

public import Complexity.Computability.Interactive.Plain
public import Complexity.Crypto.Computational.ZeroKnowledge

/-!
# Zero knowledge against malicious verifiers (design prototype)

**Exact layer.** A malicious verifier is a strategy of the verifier's role
(`Interactive.VerifierStrategy`): it receives the prover's messages and chooses every challenge,
not necessarily at random, and ends with an arbitrary output, its view. `Reduction.ZK` is
zero knowledge with *arbitrary* auxiliary input, perfect or statistical: for every malicious
verifier and every auxiliary input, the named simulator reproduces the verifier's output from the
statement and the auxiliary input alone, within statistical distance `ε`.

**Computational contracts.** Two distinct notions, over any real-interaction semantics:

* `Crypto.ZeroKnowledgeAuxInput`, the standard auxiliary-input notion
  ([Goldreich2001], Definition 4.3.10): the families of instances, valid witnesses and auxiliary
  inputs are arbitrary, subject only to polynomially bounded encoded lengths;
* `Crypto.ZeroKnowledgeGenerable`, the library's restricted notion, in which these families are
  computable in polynomial time from `1ⁿ`. It is exactly `ZeroKnowledgeProof.zero_knowledge`
  (`Crypto.ZeroKnowledgeProof.zeroKnowledgeGenerable`).

In both, one uniform strict PPT simulator is chosen for each admissible malicious verifier
*before* the families, and it is charged on the whole encoded input `(1ⁿ, x, z)`. The general
notion implies the restricted one (`Crypto.ZeroKnowledgeAuxInput.generable`). The converse is
not claimed.

## Main definitions

* `Interactive.VerifierStrategy`, `Interactive.runAgainst`, `Interactive.Reduction.viewOf`.
* `Interactive.Reduction.ZK`: exact zero knowledge with auxiliary input.
* `Crypto.ZeroKnowledgeAuxInput`, `Crypto.ZeroKnowledgeGenerable`.

## Main results

* `Crypto.ZeroKnowledgeAuxInput.generable`: general auxiliary input implies the restricted notion.
* `Crypto.ZeroKnowledgeProof.zeroKnowledgeGenerable`: GMW's guarantee is the restricted notion.

## References

* [O. Goldreich, *Foundations of Cryptography: Volume 1, Basic Tools*][Goldreich2001],
  Section 4.3.
-/

@[expose] public section

namespace Cslib.Interactive

open scoped ENNReal
open Spec

/-! ### Exact zero knowledge with auxiliary input -/

/-- A strategy of the verifier's role over the rounds `s`, in the monad `m`, ending with an output
of type `α`. It receives each prover message and chooses each challenge. -/
@[reducible] def VerifierStrategy (m : Type → Type) : Spec → Type → Type
  | [], α => m α
  | .prover M _ :: s, α => M → m (VerifierStrategy m s α)
  | .verifier C :: s, α => m (C × VerifierStrategy m s α)

/-- Run a prover strategy against a verifier strategy: the transcript and both results. -/
def runAgainst {m : Type → Type} [Monad m] {α β : Type} :
    (s : Spec) → ProverStrategy m s α → VerifierStrategy m s β → m (Transcript s × α × β)
  | [], a, v => do
    let v : m β := v
    let b ← v
    return ((), a, b)
  | .prover M _ :: s, p, v => do
    let p : m (M × ProverStrategy m s α) := p
    let v : M → m (VerifierStrategy m s β) := v
    let (msg, p') ← p
    let v' ← v msg
    let r ← runAgainst s p' v'
    return ((msg, r.1), r.2)
  | .verifier C :: s, p, v => do
    let p : C → m (ProverStrategy m s α) := p
    let v : m (C × VerifierStrategy m s β) := v
    let (c, v') ← v
    let p' ← p c
    let r ← runAgainst s p' v'
    return ((c, r.1), r.2)

variable {s : Spec} {Stmt Wit StmtOut WitOut Aux View : Type}

/-- The law of a malicious verifier's output after interacting with the honest prover of `R` on
`(x, w)`, with auxiliary input `z`. -/
noncomputable def Reduction.viewOf (R : Reduction emptySpec emptySpec s Stmt Wit StmtOut WitOut)
    (Vstar : Stmt → Aux →
      ProbOracleComp emptySpec (VerifierStrategy (ProbOracleComp emptySpec) s View))
    (x : Stmt) (w : Wit) (z : Aux) : PMF View :=
  lawOf do
    let p ← R.prover x w
    let v ← Vstar x z
    let r ← runAgainst s p v
    return r.2.2

/-- **Zero knowledge with auxiliary input**, statistical with error `ε` (perfect for `ε = 0`), in
the plain model. For every malicious verifier `Vstar`, every valid `(x, w)` and every auxiliary
input `z`, the simulator `Sim Vstar`, which sees only `x` and `z`, reproduces the verifier's
output within statistical distance `ε`. The auxiliary input ranges over all of `Aux`. -/
def Reduction.ZK (R : Reduction emptySpec emptySpec s Stmt Wit StmtOut WitOut)
    (rel : Stmt → Wit → Prop)
    (Sim : (Stmt → Aux →
        ProbOracleComp emptySpec (VerifierStrategy (ProbOracleComp emptySpec) s View)) →
      Stmt → Aux → ProbOracleComp emptySpec View) (ε : ℝ≥0∞) : Prop :=
  ∀ Vstar x w z, rel x w → CloseTo (R.viewOf Vstar x w z) (lawOf (Sim Vstar x z)) ε

end Cslib.Interactive

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-! ### Computational zero knowledge: general and restricted auxiliary input -/

/-- **Computational zero knowledge with general auxiliary input** ([Goldreich2001],
Definition 4.3.10). For every admissible malicious verifier there is one uniform strict PPT
simulator on `(1ⁿ, x, z)`, chosen before the families, such that for all families of instances,
valid witnesses and auxiliary inputs with polynomially bounded encoded lengths, the real output
`real Vstar n (a n) (w n) (z n)` and the simulator's output are computationally
indistinguishable. The distinguisher sees the verifier's output, which may include `x` and `z`. -/
def ZeroKnowledgeAuxInput {α V : Type} (enc : α ↪ List Bool) (valid : α → List Bool → Prop)
    (Admissible : V → Prop) (real : V → ℕ → α → List Bool → List Bool → PMF (List Bool)) :
    Prop :=
  ∀ Vstar, Admissible Vstar →
    ∃ S : ℕ → α → List Bool → ProbComp (List Bool),
      IsPPTOn (encPair encUnary (encPair enc encBits)) encBits
          (fun p : ℕ × α × List Bool => S p.1 p.2.1 p.2.2) ∧
        ∀ (a : ℕ → α) (w z : ℕ → List Bool),
          PolynomiallyBounded (fun n => (enc (a n)).length) →
          PolynomiallyBounded (fun n => (w n).length) →
          PolynomiallyBounded (fun n => (z n).length) →
          (∀ n, valid (a n) (w n)) →
          ComputationallyIndistinguishable (fun n => real Vstar n (a n) (w n) (z n))
            (fun n => ProbComp.eval (S n (a n) (z n)))

/-- **Computational zero knowledge over polynomial-time-generable families**: the library's
restricted notion, as in `ZeroKnowledgeProof.zero_knowledge`. The quantifiers are those of
`ZeroKnowledgeAuxInput`, but the families of instances, witnesses and auxiliary inputs must be
computable in polynomial time from `1ⁿ`. -/
def ZeroKnowledgeGenerable {α V : Type} (enc : α ↪ List Bool) (valid : α → List Bool → Prop)
    (Admissible : V → Prop) (real : V → ℕ → α → List Bool → List Bool → PMF (List Bool)) :
    Prop :=
  ∀ Vstar, Admissible Vstar →
    ∃ S : ℕ → α → List Bool → ProbComp (List Bool),
      IsPPTOn (encPair encUnary (encPair enc encBits)) encBits
          (fun p : ℕ × α × List Bool => S p.1 p.2.1 p.2.2) ∧
        ∀ (a : ℕ → α) (w z : ℕ → List Bool),
          ComputableInPolyTime a encUnary enc →
          ComputableInPolyTime w encUnary encBits →
          ComputableInPolyTime z encUnary encBits →
          (∀ n, valid (a n) (w n)) →
          ComputationallyIndistinguishable (fun n => real Vstar n (a n) (w n) (z n))
            (fun n => ProbComp.eval (S n (a n) (z n)))

/-- A family computable in polynomial time from `1ⁿ` has polynomially bounded encoded length. -/
theorem polynomiallyBounded_length_of_computableInPolyTime {α : Type} {enc : α ↪ List Bool}
    {a : ℕ → α} (h : ComputableInPolyTime a encUnary enc) :
    PolynomiallyBounded (fun n => (enc (a n)).length) := by
  obtain ⟨c, d, hle⟩ := h.polyBounded_length.exists_le
  exact Cslib.polynomiallyBounded_iff_le.mpr ⟨c, d, fun n => by simpa using hle n⟩

/-- **General auxiliary input implies the restricted notion**: polynomial-time-generable families
have polynomially bounded lengths. -/
theorem ZeroKnowledgeAuxInput.generable {α V : Type} {enc : α ↪ List Bool}
    {valid : α → List Bool → Prop} {Admissible : V → Prop}
    {real : V → ℕ → α → List Bool → List Bool → PMF (List Bool)}
    (h : ZeroKnowledgeAuxInput enc valid Admissible real) :
    ZeroKnowledgeGenerable enc valid Admissible real := by
  intro Vstar hV
  obtain ⟨S, hS, hind⟩ := h Vstar hV
  exact ⟨S, hS, fun a w z ha hw hz hvalid =>
    hind a w z (polynomiallyBounded_length_of_computableInPolyTime ha)
      (polynomiallyBounded_length_of_computableInPolyTime hw)
      (polynomiallyBounded_length_of_computableInPolyTime hz) hvalid⟩

/-- The guarantee of a `ZeroKnowledgeProof` is the restricted notion, for its malicious verifiers
and real interactions. -/
theorem ZeroKnowledgeProof.zeroKnowledgeGenerable {α : Type} {enc : α ↪ List Bool} {A : Set α}
    (zk : ZeroKnowledgeProof enc A) :
    ZeroKnowledgeGenerable enc (fun a w => zk.isWitness a w = true)
      (fun Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool) =>
        IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
          (fun p : ℕ × α × List Bool => Vstar p.1 p.2.1 p.2.2))
      (fun Vstar n a w z =>
        ((zk.prover n a w).run (Vstar n a z) (zk.prover n a w).init).map Prod.fst) :=
  zk.zero_knowledge

end Cslib.Crypto
