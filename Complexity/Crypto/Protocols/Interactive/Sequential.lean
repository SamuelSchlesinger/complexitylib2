/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (design prototype for #643; not for merge)

public import Complexity.Crypto.Protocols.Interactive.Security

/-!
# Sequential composition of interactive reductions (design prototype)

`Reduction.append` runs a reduction from `rel₁` to `rel₂` and then one from `rel₂` to `rel₃`; its
rounds are the concatenation `s₁ ++ s₂`. Every construction is by structural recursion on `s₁`,
so for a concrete protocol the transcripts, challenges and message queries of the composition
compute to those of the components without casts.

The composition theorems are stated in the plain model, where every security notion holds from
every state of the (trivial) world; in oracle models one composes interactive protocols first and
compiles them once (Fiat–Shamir, BCS).
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.Interactive

open scoped ENNReal
open Spec

namespace Spec

variable {F : Type → Type}

/-- Concatenate transcripts. -/
def Transcript.append : (s₁ s₂ : Spec) → Transcript s₁ → Transcript s₂ → Transcript (s₁ ++ s₂)
  | [], _, _, τ₂ => τ₂
  | _ :: s₁, s₂, τ₁, τ₂ => (τ₁.1, Transcript.append s₁ s₂ τ₁.2 τ₂)

/-- Split a transcript of a composition. -/
def Transcript.split : (s₁ s₂ : Spec) → Transcript (s₁ ++ s₂) → Transcript s₁ × Transcript s₂
  | [], _, τ => ((), τ)
  | _ :: s₁, s₂, τ => ((τ.1, (Transcript.split s₁ s₂ τ.2).1), (Transcript.split s₁ s₂ τ.2).2)

/-- Concatenate per-challenge data. -/
def PerChallenge.append : (s₁ s₂ : Spec) → PerChallenge F s₁ → PerChallenge F s₂ →
    PerChallenge F (s₁ ++ s₂)
  | [], _, _, b => b
  | .prover _ _ :: s₁, s₂, a, b => PerChallenge.append s₁ s₂ a b
  | .verifier _ :: s₁, s₂, a, b => (a.1, PerChallenge.append s₁ s₂ a.2 b)

/-- Split per-challenge data of a composition. -/
def PerChallenge.split : (s₁ s₂ : Spec) → PerChallenge F (s₁ ++ s₂) →
    PerChallenge F s₁ × PerChallenge F s₂
  | [], _, b => ((), b)
  | .prover _ _ :: s₁, s₂, a => PerChallenge.split s₁ s₂ a
  | .verifier _ :: s₁, s₂, a =>
    ((a.1, (PerChallenge.split s₁ s₂ a.2).1), (PerChallenge.split s₁ s₂ a.2).2)

/-- Queries about the messages of `s₁` are queries about those of `s₁ ++ s₂`. -/
def liftMsgLeft : (s₁ s₂ : Spec) → (q : MsgQuery s₁) →
    OracleComp (msgSpec (s₁ ++ s₂)) (MsgResponse s₁ q)
  | [], _, q => q.elim
  | .prover M I :: s₁, s₂, .inl q =>
    OracleComp.query (spec := msgSpec (.prover M I :: (s₁ ++ s₂))) (.inl q)
  | .prover M I :: s₁, s₂, .inr q =>
    OracleComp.interpret
      (fun q' => OracleComp.query (spec := msgSpec (.prover M I :: (s₁ ++ s₂))) (.inr q'))
      (liftMsgLeft s₁ s₂ q)
  | .verifier C :: s₁, s₂, q =>
    OracleComp.interpret
      (fun q' => OracleComp.query (spec := msgSpec (.verifier C :: (s₁ ++ s₂))) q')
      (liftMsgLeft s₁ s₂ q)

/-- Queries about the messages of `s₂` are queries about those of `s₁ ++ s₂`. -/
def liftMsgRight : (s₁ s₂ : Spec) → (q : MsgQuery s₂) →
    OracleComp (msgSpec (s₁ ++ s₂)) (MsgResponse s₂ q)
  | [], s₂, q => OracleComp.query (spec := msgSpec s₂) q
  | .prover M I :: s₁, s₂, q =>
    OracleComp.interpret
      (fun q' => OracleComp.query (spec := msgSpec (.prover M I :: (s₁ ++ s₂))) (.inr q'))
      (liftMsgRight s₁ s₂ q)
  | .verifier C :: s₁, s₂, q =>
    OracleComp.interpret
      (fun q' => OracleComp.query (spec := msgSpec (.verifier C :: (s₁ ++ s₂))) q')
      (liftMsgRight s₁ s₂ q)

end Spec

/-- Continue a strategy with another one once it ends. -/
def ProverStrategy.append {m : Type → Type} [Monad m] {α β : Type} :
    (s₁ s₂ : Spec) → ProverStrategy m s₁ α → (α → m (ProverStrategy m s₂ β)) →
      m (ProverStrategy m (s₁ ++ s₂) β)
  | [], _, a, next => next a
  | .prover M _ :: s₁, s₂, st, next =>
    let st : m (M × ProverStrategy m s₁ α) := st
    pure (show m (M × ProverStrategy m (s₁ ++ s₂) β) from do
      let (msg, st') ← st
      let rest ← ProverStrategy.append s₁ s₂ st' next
      return (msg, rest))
  | .verifier C :: s₁, s₂, st, next =>
    let st : C → m (ProverStrategy m s₁ α) := st
    pure (show C → m (ProverStrategy m (s₁ ++ s₂) β) from fun c => do
      let st' ← st c
      ProverStrategy.append s₁ s₂ st' next)

variable {ιP ιV : Type} {oP : OracleSpec ιP} {oV : OracleSpec ιV} {s₁ s₂ : Spec}
  {S₁ W₁ S₂ W₂ S₃ W₃ : Type}

/-- Lift a decision on `s₁` to the composition. -/
def liftDecisionLeft {α : Type} (s₁ s₂ : Spec) :
    OracleComp (oV ⊕ₒ msgSpec s₁) α → OracleComp (oV ⊕ₒ msgSpec (s₁ ++ s₂)) α :=
  OracleComp.interpret fun q => match q with
    | .inl q => OracleComp.query (spec := oV ⊕ₒ msgSpec (s₁ ++ s₂)) (.inl q)
    | .inr q => OracleComp.interpret
        (fun q' => OracleComp.query (spec := oV ⊕ₒ msgSpec (s₁ ++ s₂)) (.inr q'))
        (liftMsgLeft s₁ s₂ q)

/-- Lift a decision on `s₂` to the composition. -/
def liftDecisionRight {α : Type} (s₁ s₂ : Spec) :
    OracleComp (oV ⊕ₒ msgSpec s₂) α → OracleComp (oV ⊕ₒ msgSpec (s₁ ++ s₂)) α :=
  OracleComp.interpret fun q => match q with
    | .inl q => OracleComp.query (spec := oV ⊕ₒ msgSpec (s₁ ++ s₂)) (.inl q)
    | .inr q => OracleComp.interpret
        (fun q' => OracleComp.query (spec := oV ⊕ₒ msgSpec (s₁ ++ s₂)) (.inr q'))
        (liftMsgRight s₁ s₂ q)

/-- Sequential composition of verifiers: the second decides on the first one's output. -/
def Verifier.append (V₁ : Verifier oV s₁ S₁ S₂) (V₂ : Verifier oV s₂ S₂ S₃) :
    Verifier oV (s₁ ++ s₂) S₁ S₃ where
  samplers := PerChallenge.append s₁ s₂ V₁.samplers V₂.samplers
  decide x c := do
    let cs := PerChallenge.split s₁ s₂ c
    match ← liftDecisionLeft s₁ s₂ (V₁.decide x cs.1) with
    | none => return none
    | some x' => liftDecisionRight s₁ s₂ (V₂.decide x' cs.2)

/-- Sequential composition of reductions. -/
def Reduction.append (R₁ : Reduction oP oV s₁ S₁ W₁ S₂ W₂)
    (R₂ : Reduction oP oV s₂ S₂ W₂ S₃ W₃) : Reduction oP oV (s₁ ++ s₂) S₁ W₁ S₃ W₃ where
  prover x w := do
    let st ← R₁.prover x w
    ProverStrategy.append s₁ s₂ st fun xw => R₂.prover xw.1 xw.2
  verifier := R₁.verifier.append R₂.verifier

/-! ### Composition theorems (statements) -/

section Plain

variable {R₁ : Reduction emptySpec emptySpec s₁ S₁ W₁ S₂ W₂}
  {R₂ : Reduction emptySpec emptySpec s₂ S₂ W₂ S₃ W₃}
  {V₁ : Verifier emptySpec s₁ S₁ S₂} {V₂ : Verifier emptySpec s₂ S₂ S₃}
  {rel₁ : S₁ → W₁ → Prop} {rel₂ : S₂ → W₂ → Prop} {rel₃ : S₃ → W₃ → Prop}
  {L₁ : Set S₁} {L₂ : Set S₂} {L₃ : Set S₃} {ε₁ ε₂ : ℝ≥0∞}

/-- Completeness errors add up under sequential composition. -/
theorem Reduction.Complete.append (h₁ : R₁.Complete World.plain rel₁ rel₂ ε₁)
    (h₂ : R₂.Complete World.plain rel₂ rel₃ ε₂) :
    (R₁.append R₂).Complete World.plain rel₁ rel₃ (ε₁ + ε₂) := by
  sorry

/-- Soundness errors add up under sequential composition, through the intermediate language. -/
theorem Verifier.Sound.append (h₁ : V₁.Sound (oP := emptySpec) World.plain L₁ L₂ ε₁)
    (h₂ : V₂.Sound (oP := emptySpec) World.plain L₂ L₃ ε₂) :
    (V₁.append V₂).Sound (oP := emptySpec) World.plain L₁ L₃ (ε₁ + ε₂) := by
  sorry

/-- Round-by-round soundness composes, with the concatenated per-round errors. -/
theorem Verifier.RbrSound.append {ε₁ : PerChallenge (fun _ => ℝ≥0∞) s₁}
    {ε₂ : PerChallenge (fun _ => ℝ≥0∞) s₂} (h₁ : V₁.RbrSound L₁ L₂ ε₁)
    (h₂ : V₂.RbrSound L₂ L₃ ε₂) :
    (V₁.append V₂).RbrSound L₁ L₃ (PerChallenge.append s₁ s₂ ε₁ ε₂) := by
  sorry

/-- Straight-line extractors compose: extract the intermediate witness from the second half of
the transcript, then the input witness from the first half. -/
theorem Verifier.KnowledgeSound.append {E₁ : S₁ → Transcript s₁ → W₂ → W₁}
    {E₂ : S₂ → Transcript s₂ → W₃ → W₂}
    (h₁ : V₁.KnowledgeSound (oP := emptySpec) World.plain rel₁ rel₂ E₁ ε₁)
    (h₂ : V₂.KnowledgeSound (oP := emptySpec) World.plain rel₂ rel₃ E₂ ε₂) :
    ∃ E : S₁ → Transcript (s₁ ++ s₂) → W₃ → W₁,
      (V₁.append V₂).KnowledgeSound (oP := emptySpec) World.plain rel₁ rel₃ E (ε₁ + ε₂) := by
  sorry

/-- The total error of concatenated per-round errors. -/
theorem PerChallenge.sum_append (ε₁ : PerChallenge (fun _ => ℝ≥0∞) s₁)
    (ε₂ : PerChallenge (fun _ => ℝ≥0∞) s₂) :
    PerChallenge.sum (s₁ ++ s₂) (PerChallenge.append s₁ s₂ ε₁ ε₂) =
      PerChallenge.sum s₁ ε₁ + PerChallenge.sum s₂ ε₂ := by
  induction s₁ with
  | nil => simp [PerChallenge.append, PerChallenge.sum]
  | cons r s₁ ih =>
    cases r with
    | prover M I => exact ih ε₁
    | verifier C =>
      change ε₁.1 + PerChallenge.sum (s₁ ++ s₂) (PerChallenge.append s₁ s₂ ε₁.2 ε₂) = _
      rw [ih, PerChallenge.sum, add_assoc]

end Plain

/-! ### Iteration -/

/-- `k` repetitions of the rounds `s`. -/
def iterSpec (s : Spec) : ℕ → Spec
  | 0 => []
  | k + 1 => iterSpec s k ++ s

/-- The reduction without rounds that keeps the statement and the witness. -/
def Reduction.id {S W : Type} : Reduction oP oV [] S W S W where
  prover x w := pure (x, w)
  verifier := { samplers := (), decide := fun x _ => pure (some x) }

/-- Run the reductions `R 0`, …, `R (k - 1)` in sequence. -/
def Reduction.iterate {s : Spec} {S W : Type} (R : ℕ → Reduction oP oV s S W S W) :
    (k : ℕ) → Reduction oP oV (iterSpec s k) S W S W
  | 0 => Reduction.id
  | k + 1 => (Reduction.iterate R k).append (R k)

/-- Repeat per-round errors. -/
def PerChallenge.iterate {s : Spec} (ε : ℕ → PerChallenge (fun _ => ℝ≥0∞) s) :
    (k : ℕ) → PerChallenge (fun _ => ℝ≥0∞) (iterSpec s k)
  | 0 => ()
  | k + 1 => PerChallenge.append (iterSpec s k) s (PerChallenge.iterate ε k) (ε k)

section Plain

variable {s : Spec} {S W : Type} {R : ℕ → Reduction emptySpec emptySpec s S W S W}

/-- The reduction without rounds is perfectly complete. -/
theorem Reduction.id_complete (rel : S → W → Prop) :
    (Reduction.id (oP := emptySpec) (oV := emptySpec)).Complete World.plain rel rel 0 := by
  sorry

/-- The reduction without rounds is round-by-round sound without error. -/
theorem Reduction.id_rbrSound (L : Set S) :
    (Reduction.id (oP := emptySpec) (oV := emptySpec) (W := W)).verifier.RbrSound L L () := by
  refine ⟨fun x _ => x ∈ L, fun x hx => hx, fun x hS ⟨x', hx', hout⟩ => hS ?_⟩
  have : x = x' := Option.some.inj hout
  exact this ▸ hx'

/-- **Iterated completeness**: if every step `R i` is complete from `rel i` to `rel (i + 1)` with
error `ε i`, the first `k` steps are complete from `rel 0` to `rel k` with the sum of the errors. -/
theorem Reduction.Complete.iterate {rel : ℕ → S → W → Prop} {ε : ℕ → ℝ≥0∞}
    (h : ∀ i, (R i).Complete World.plain (rel i) (rel (i + 1)) (ε i)) (k : ℕ) :
    (Reduction.iterate R k).Complete World.plain (rel 0) (rel k) (∑ i ∈ Finset.range k, ε i) := by
  induction k with
  | zero =>
    rw [Finset.sum_range_zero]
    exact Reduction.id_complete (rel 0)
  | succ k ih =>
    rw [Finset.sum_range_succ]
    exact ih.append (h k)

/-- **Iterated round-by-round soundness**, with the per-round errors of the steps in order. -/
theorem Verifier.RbrSound.iterate {L : ℕ → Set S} {ε : ℕ → PerChallenge (fun _ => ℝ≥0∞) s}
    (h : ∀ i, (R i).verifier.RbrSound (L i) (L (i + 1)) (ε i)) (k : ℕ) :
    (Reduction.iterate R k).verifier.RbrSound (L 0) (L k) (PerChallenge.iterate ε k) := by
  induction k with
  | zero => exact Reduction.id_rbrSound (L 0)
  | succ k ih => exact ih.append (h k)

/-- The total error of repeated per-round errors. -/
theorem PerChallenge.sum_iterate (ε : ℕ → PerChallenge (fun _ => ℝ≥0∞) s) (k : ℕ) :
    PerChallenge.sum (iterSpec s k) (PerChallenge.iterate ε k) =
      ∑ i ∈ Finset.range k, PerChallenge.sum s (ε i) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih]
    exact PerChallenge.sum_append _ _

end Plain

end Cslib.Crypto.Protocols.Interactive
