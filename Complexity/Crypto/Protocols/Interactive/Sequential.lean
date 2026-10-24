/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (design prototype for #643; not for merge)

public import Complexity.Crypto.Protocols.Interactive.Plain

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

/-! ### Round-by-round composition (proved) -/

section Rbr

/-- The challenges of a composed transcript split into those of its halves. -/
theorem challenges_split : ∀ (s₁ s₂ : Spec) (τ : Transcript (s₁ ++ s₂)),
    PerChallenge.split s₁ s₂ (Transcript.challenges (s₁ ++ s₂) τ) =
      (Transcript.challenges s₁ (Transcript.split s₁ s₂ τ).1,
        Transcript.challenges s₂ (Transcript.split s₁ s₂ τ).2)
  | [], _, _ => rfl
  | .prover _ _ :: s₁, s₂, τ => challenges_split s₁ s₂ τ.2
  | .verifier _ :: s₁, s₂, τ => by
    change ((τ.1, (PerChallenge.split s₁ s₂ (Transcript.challenges (s₁ ++ s₂) τ.2)).1),
      (PerChallenge.split s₁ s₂ (Transcript.challenges (s₁ ++ s₂) τ.2)).2) = _
    rw [challenges_split s₁ s₂ τ.2]
    rfl

/-- Lifted message queries of the first half are answered by the first half of the transcript. -/
theorem interpret_liftMsgLeft : ∀ (s₁ s₂ : Spec) (τ : Transcript (s₁ ++ s₂)) (q : MsgQuery s₁),
    OracleComp.interpret (m := Id) (Transcript.answer (s₁ ++ s₂) τ) (liftMsgLeft s₁ s₂ q) =
      Transcript.answer s₁ (Transcript.split s₁ s₂ τ).1 q
  | [], _, _, q => q.elim
  | .prover M I :: s₁, s₂, τ, .inl q => rfl
  | .prover M I :: s₁, s₂, τ, .inr q => by
    rw [liftMsgLeft, OracleComp.interpret_interpret]
    exact interpret_liftMsgLeft s₁ s₂ τ.2 q
  | .verifier C :: s₁, s₂, τ, q => by
    rw [liftMsgLeft, OracleComp.interpret_interpret]
    exact interpret_liftMsgLeft s₁ s₂ τ.2 q

/-- Lifted message queries of the second half are answered by the second half of the transcript. -/
theorem interpret_liftMsgRight : ∀ (s₁ s₂ : Spec) (τ : Transcript (s₁ ++ s₂)) (q : MsgQuery s₂),
    OracleComp.interpret (m := Id) (Transcript.answer (s₁ ++ s₂) τ) (liftMsgRight s₁ s₂ q) =
      Transcript.answer s₂ (Transcript.split s₁ s₂ τ).2 q
  | [], _, _, q => rfl
  | .prover M I :: s₁, s₂, τ, q => by
    rw [liftMsgRight, OracleComp.interpret_interpret]
    exact interpret_liftMsgRight s₁ s₂ τ.2 q
  | .verifier C :: s₁, s₂, τ, q => by
    rw [liftMsgRight, OracleComp.interpret_interpret]
    exact interpret_liftMsgRight s₁ s₂ τ.2 q



/-- The answers to the verifier's queries from a transcript, in the plain model. -/
def answerAll (s : Spec) (τ : Transcript s) : (q : Empty ⊕ MsgQuery s) → (emptySpec ⊕ₒ msgSpec s) q
  | .inl e => e.elim
  | .inr q => Transcript.answer s τ q

theorem outputOn_eq (V : Verifier emptySpec s₁ S₁ S₂) (x : S₁) (τ : Transcript s₁) :
    V.outputOn x τ = OracleComp.interpret (m := Id) (answerAll s₁ τ)
      (V.decide x (Transcript.challenges s₁ τ)) := by
  rw [Verifier.outputOn]
  congr 1

theorem interpret_liftDecisionLeft {α : Type} (τ : Transcript (s₁ ++ s₂))
    (p : OracleComp (emptySpec ⊕ₒ msgSpec s₁) α) :
    OracleComp.interpret (m := Id) (answerAll (s₁ ++ s₂) τ) (liftDecisionLeft s₁ s₂ p) =
      OracleComp.interpret (m := Id) (answerAll s₁ (Transcript.split s₁ s₂ τ).1) p := by
  rw [liftDecisionLeft]
  refine (OracleComp.interpret_interpret (m := Id) _ _ _).trans ?_
  congr 1
  funext q
  rcases q with e | q
  · exact e.elim
  · refine (OracleComp.interpret_interpret (m := Id) _ _ _).trans ?_
    exact interpret_liftMsgLeft s₁ s₂ τ q

theorem interpret_liftDecisionRight {α : Type} (τ : Transcript (s₁ ++ s₂))
    (p : OracleComp (emptySpec ⊕ₒ msgSpec s₂) α) :
    OracleComp.interpret (m := Id) (answerAll (s₁ ++ s₂) τ) (liftDecisionRight s₁ s₂ p) =
      OracleComp.interpret (m := Id) (answerAll s₂ (Transcript.split s₁ s₂ τ).2) p := by
  rw [liftDecisionRight]
  refine (OracleComp.interpret_interpret (m := Id) _ _ _).trans ?_
  congr 1
  funext q
  rcases q with e | q
  · exact e.elim
  · refine (OracleComp.interpret_interpret (m := Id) _ _ _).trans ?_
    exact interpret_liftMsgRight s₁ s₂ τ q

/-- The composed verifier's output is the second verifier's output on the first one's. -/
theorem outputOn_append (V₁ : Verifier emptySpec s₁ S₁ S₂) (V₂ : Verifier emptySpec s₂ S₂ S₃)
    (x : S₁) (τ : Transcript (s₁ ++ s₂)) :
    (V₁.append V₂).outputOn x τ =
      (V₁.outputOn x (Transcript.split s₁ s₂ τ).1).bind
        fun x' => V₂.outputOn x' (Transcript.split s₁ s₂ τ).2 := by
  rw [outputOn_eq, outputOn_eq]
  simp only [Verifier.append, challenges_split]
  refine (OracleComp.interpret_bind (m := Id) _ _ _).trans ?_
  erw [interpret_liftDecisionLeft]
  cases h : OracleComp.interpret (m := Id) (answerAll s₁ (Transcript.split s₁ s₂ τ).1)
      (V₁.decide x (Transcript.challenges s₁ (Transcript.split s₁ s₂ τ).1)) with
  | none => rfl
  | some x' =>
    refine (interpret_liftDecisionRight τ _).trans ?_
    exact (outputOn_eq V₂ x' _).symm


/-- The state function of a composition: that of the first half, then, once the first half is
complete, the second half's state function for that first half. -/
def compState : (s₁ s₂ : Spec) → (Prefix s₁ → Prop) → (Transcript s₁ → Prefix s₂ → Prop) →
    Prefix (s₁ ++ s₂) → Prop
  | [], _, _, next, p => next () p
  | _ :: _, _, S, _, none => S none
  | _ :: s₁, s₂, S, next, some (m, p) =>
    compState s₁ s₂ (fun q => S (some (m, q))) (fun τ => next (m, τ)) p

/-- A doomed start of the first half is a doomed start of the composition. -/
theorem not_compState_empty {s₁ s₂ : Spec} {smp : PerChallenge ProbComp s₁}
    {ε : PerChallenge (fun _ => ℝ≥0∞) s₁} {S : Prefix s₁ → Prop} {wins : Transcript s₁ → Prop}
    {next : Transcript s₁ → Prefix s₂ → Prop} (h : RbrFrom s₁ smp ε S wins)
    (hjunc : ∀ τ, ¬ wins τ → ¬ next τ (Prefix.empty s₂)) (hS : ¬ S (Prefix.empty s₁)) :
    ¬ compState s₁ s₂ S next (Prefix.empty (s₁ ++ s₂)) := by
  cases s₁ with
  | nil => exact hjunc () (h hS)
  | cons r s₁ => exact hS

/-- The round-by-round condition holds trivially when nothing is ever alive. -/
theorem rbrFrom_false : ∀ (s : Spec) (smp : PerChallenge ProbComp s)
    (ε : PerChallenge (fun _ => ℝ≥0∞) s), RbrFrom s smp ε (fun _ => False) (fun _ => False)
  | [], _, _ => fun _ h => h
  | .prover _ _ :: s, smp, ε => ⟨fun _ _ h => h, fun _ => rbrFrom_false s smp ε⟩
  | .verifier _ :: s, smp, ε => ⟨fun _ => by simp, fun _ => rbrFrom_false s smp.2 ε.2⟩

/-- The round-by-round condition is invariant under equivalent state functions and events. -/
theorem RbrFrom.congr : ∀ {s : Spec} {smp : PerChallenge ProbComp s}
    {ε : PerChallenge (fun _ => ℝ≥0∞) s} {S S' : Prefix s → Prop}
    {wins wins' : Transcript s → Prop},
    (∀ p, S p ↔ S' p) → (∀ τ, wins τ ↔ wins' τ) → RbrFrom s smp ε S wins →
      RbrFrom s smp ε S' wins'
  | [], _, _, _, _, _, _, hS, hw, h => fun h' hw' => h (mt (hS ()).1 h') ((hw ()).2 hw')
  | .prover _ _ :: s, _, _, _, _, _, _, hS, hw, h =>
    ⟨fun h0 m h1 => h.1 (mt (hS none).1 h0) m ((hS _).2 h1),
      fun m => RbrFrom.congr (fun p => hS _) (fun τ => hw _) (h.2 m)⟩
  | .verifier _ :: s, smp, _, S, S', _, _, hS, hw, h =>
    ⟨fun h0 => by
        have hset : {c | S' (some (c, Prefix.empty s))} = {c | S (some (c, Prefix.empty s))} :=
          Set.ext fun c => (hS _).symm
        rw [hset]
        exact h.1 (mt (hS none).1 h0),
      fun c => RbrFrom.congr (fun p => hS _) (fun τ => hw _) (h.2 c)⟩

/-- **Round-by-round composition, per prefix.** -/
theorem rbrFrom_append : ∀ (s₁ s₂ : Spec) (smp₁ : PerChallenge ProbComp s₁)
    (smp₂ : PerChallenge ProbComp s₂) (ε₁ : PerChallenge (fun _ => ℝ≥0∞) s₁)
    (ε₂ : PerChallenge (fun _ => ℝ≥0∞) s₂) (S : Prefix s₁ → Prop) (wins₁ : Transcript s₁ → Prop)
    (next : Transcript s₁ → Prefix s₂ → Prop) (wins₂ : Transcript s₁ → Transcript s₂ → Prop),
    RbrFrom s₁ smp₁ ε₁ S wins₁ → (∀ τ, ¬ wins₁ τ → ¬ next τ (Prefix.empty s₂)) →
    (∀ τ, RbrFrom s₂ smp₂ ε₂ (next τ) (wins₂ τ)) →
    RbrFrom (s₁ ++ s₂) (PerChallenge.append s₁ s₂ smp₁ smp₂) (PerChallenge.append s₁ s₂ ε₁ ε₂)
      (compState s₁ s₂ S next)
      (fun τ => wins₂ (Transcript.split s₁ s₂ τ).1 (Transcript.split s₁ s₂ τ).2)
  | [], _, _, _, _, _, _, _, _, _, _, _, h₂ => h₂ ()
  | .prover M I :: s₁, s₂, smp₁, smp₂, ε₁, ε₂, S, wins₁, next, wins₂, h₁, hjunc, h₂ =>
    ⟨fun h0 m => not_compState_empty (h₁.2 m) (fun τ => hjunc (m, τ)) (h₁.1 h0 m),
      fun m => rbrFrom_append s₁ s₂ smp₁ smp₂ ε₁ ε₂ _ _ (fun τ => next (m, τ))
        (fun τ => wins₂ (m, τ)) (h₁.2 m) (fun τ => hjunc (m, τ)) (fun τ => h₂ (m, τ))⟩
  | .verifier C :: s₁, s₂, smp₁, smp₂, ε₁, ε₂, S, wins₁, next, wins₂, h₁, hjunc, h₂ =>
    ⟨fun h0 => by
        refine le_trans (MeasureTheory.measure_mono fun c hc => ?_) (h₁.1 h0)
        by_contra hS
        exact not_compState_empty (h₁.2 c) (fun τ => hjunc (c, τ)) hS hc,
      fun c => rbrFrom_append s₁ s₂ smp₁.2 smp₂ ε₁.2 ε₂ _ _ (fun τ => next (c, τ))
        (fun τ => wins₂ (c, τ)) (h₁.2 c) (fun τ => hjunc (c, τ)) (fun τ => h₂ (c, τ))⟩


/-- **Round-by-round soundness composes**, with the concatenated per-round errors. -/
theorem Verifier.RbrSound.append {V₁ : Verifier emptySpec s₁ S₁ S₂}
    {V₂ : Verifier emptySpec s₂ S₂ S₃} {L₁ : Set S₁} {L₂ : Set S₂} {L₃ : Set S₃}
    {ε₁ : PerChallenge (fun _ => ℝ≥0∞) s₁} {ε₂ : PerChallenge (fun _ => ℝ≥0∞) s₂}
    (h₁ : V₁.RbrSound L₁ L₂ ε₁) (h₂ : V₂.RbrSound L₂ L₃ ε₂) :
    (V₁.append V₂).RbrSound L₁ L₃ (PerChallenge.append s₁ s₂ ε₁ ε₂) := by
  obtain ⟨T₁, hinit₁, hr₁⟩ := h₁
  obtain ⟨T₂, hinit₂, hr₂⟩ := h₂
  let next : S₁ → Transcript s₁ → Prefix s₂ → Prop :=
    fun x τ₁ p => ∃ x', V₁.outputOn x τ₁ = some x' ∧ T₂ x' p
  have hjunc : ∀ x τ₁, ¬ (∃ x' ∈ L₂, V₁.outputOn x τ₁ = some x') →
      ¬ next x τ₁ (Prefix.empty s₂) := by
    rintro x τ₁ hw ⟨x', hout, hT⟩
    by_cases hx' : x' ∈ L₂
    · exact hw ⟨x', hx', hout⟩
    · exact hinit₂ x' hx' hT
  have hsecond : ∀ x τ₁, RbrFrom s₂ V₂.samplers ε₂ (next x τ₁)
      (fun τ₂ => ∃ x'' ∈ L₃, (V₁.outputOn x τ₁).bind (fun x' => V₂.outputOn x' τ₂) = some x'') := by
    intro x τ₁
    cases hout : V₁.outputOn x τ₁ with
    | none =>
      refine RbrFrom.congr (fun p => ?_) (fun τ => ?_) (rbrFrom_false s₂ V₂.samplers ε₂)
      · simp [next, hout]
      · simp
    | some x' =>
      refine RbrFrom.congr (fun p => ?_) (fun τ => ?_) (hr₂ x')
      · simp [next, hout]
      · simp
  refine ⟨fun x => compState s₁ s₂ (T₁ x) (next x),
    fun x hx => not_compState_empty (hr₁ x) (hjunc x) (hinit₁ x hx), fun x => ?_⟩
  refine RbrFrom.congr (fun p => Iff.rfl) (fun τ => ?_)
    (rbrFrom_append s₁ s₂ V₁.samplers V₂.samplers ε₁ ε₂ (T₁ x) _ (next x) _ (hr₁ x) (hjunc x)
      (hsecond x))
  rw [outputOn_append]

end Rbr

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
  intro x w hxw
  rw [plain_eval]
  simp [Reduction.run, Verifier.execute, Reduction.id, lawOf₂_liftProver, runStrategy,
    lawOf₂_output, Verifier.outputOn, hxw]
  rfl

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
