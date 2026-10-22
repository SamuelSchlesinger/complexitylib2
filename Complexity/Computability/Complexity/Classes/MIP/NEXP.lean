/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.EXP
public import Complexity.Computability.Complexity.Classes.MIP.OptimalProver
public import Complexity.Computability.Complexity.Classes.NP.GuessVerify
public import Complexity.Computability.Complexity.Classes.NP.Witness
public import Complexity.Computability.Complexity.Classes.Padding
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Configuration
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Configuration
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Composition
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Probabilistic.PPT.Clock
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# The unconditional upper bound `MIP ⊆ NEXP`

Every problem with a multiprover interactive proof (`Cslib.Complexity.MIP` or
`Cslib.Complexity.MIP₂`) is decidable in nondeterministic exponential time
(`Cslib.Complexity.NEXP`) [Babai, Fortnow and Lund][BabaiFortnowLund1991],
[Arora and Barak, Section 8.10][AroraBarak09]:

$$\mathsf{MIP}_2 \subseteq \mathsf{MIP} \subseteq \mathsf{NEXP}.$$

## Proof overview

1. **Multi-channel live replay (`Cslib.Complexity.MIP.aliveRun`, `Cslib.Complexity.MIP.accepts`)**:
   A tagged history `th : TaggedHistory` is a list of `(channel, (query, reply))` entries with
   channel index in `ℕ` (encoded in unary). Given input `x` and coin string `r` of length `t`,
   `aliveRun M x r th` executes `M` for `t` steps, consuming `th` from the front whenever `M`
   issues an oracle query `(op, m)` and checking that the entry matches `(op.val, m)`. By
   `foldlWith_spec`, `accepts` is computable tidily in polynomial time.
2. **Correspondence with deterministic prover families (`queryAcceptProb_eq_one_of_accepts`,
   `queryAcceptProb_eq_ite_accepts_canonicalTrace`)**:
   Projecting a tagged history `th` onto prover `i`'s channel (`projHistory i th`) commutes with
   non-communicating state updates (`Function.update`). Hence `accepts M x r th = true` under
   projected histories valid for `D : Fin p → DetProver` implies
   `queryAcceptProb (Prover.independent fun i => (D i).toProver) ... (coinProgram M t x r) = 1`,
   and conversely every deterministic prover family `D` has a canonical tagged history
   `canonicalTrace M t D ... r` of length at most `t` with queries and replies of length at most
   `t`.
3. **Certificate verification in polynomial time on exponentially padded instances
   (`checkPaddedCert`, `paddedMIP_mem_NP`)**:
   A certificate `cert : Cert` lists accepting pairs `(r, th)` of coin strings and tagged
   histories. The polynomial-time checker verifies that every `(r, th) ∈ cert` has `r.length = t`
   and `accepts M x r th = true`, that the coin strings `r` are pairwise distinct, that for every
   prover `i < p` the projected histories `projHistory i th` are pairwise `consistentHist`, and
   that `2 ^ t < 2 * cert.length`. By `DetProver.ValidFrom.consistentHist` and
   `validFrom_candidateProver`, such a certificate exists if and only if some family of
   deterministic provers is accepted on more than half of the `2 ^ t` coin strings.
4. **Upward translation from `NP` to `NEXP` (`preimage_mem_NTIME_of_mem_NP`,
   `preimage_pad_mem_NEXP`, `MIP_subset_NEXP`)**:
   Composing the deterministic exponential-padding machine (`ComputableTidilyInO.unary_two_pow`)
   with the halting fair-coin certificate-verifier machine (`IsVerifier.exists_decidesInTime`) via
   `MultiTapePTM.comp` and converting to `MultiTapeNTM` via `MultiTapePTM.toNTM` places the
   unpadded language in `NEXP`.

The converse inclusion `NEXP ⊆ MIP₂` (which requires the Babai–Fortnow–Lund multilinearity test
and the arithmetization of `NEXP` verification tableaux) is not formalized here and remains open.

## Main definitions

* `Cslib.Complexity.MIP.TaggedHistory`: multi-channel `(prover, (query, reply))` transcripts.
* `Cslib.Complexity.MIP.projHistory`: projection of a tagged transcript onto one prover channel.
* `Cslib.Complexity.MIP.aliveRun`, `Cslib.Complexity.MIP.accepts`: polynomial-time multi-channel
  verifier replay.
* `Cslib.Complexity.MIP.checkCert`, `Cslib.Complexity.MIP.paddedMIP`: the certificate checker and
  exponentially padded `NP` language.

## Main results

* `Cslib.Complexity.preimage_mem_NTIME_of_mem_NP`, `Cslib.Complexity.preimage_pad_mem_NEXP`:
  pulling back an `NP` problem along an exponential-time padding function gives a problem in
  `NEXP`.
* `Cslib.Complexity.MIP_subset_NEXP`: `MIP ⊆ NEXP`.
* `Cslib.Complexity.MIP₂_subset_NEXP`: `MIP₂ ⊆ NEXP`.

## References

* [L. Babai, L. Fortnow, C. Lund, *Non-deterministic exponential time has two-prover interactive
  protocols*][BabaiFortnowLund1991]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Probability _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeMachine
open ComputableTidilyInPolyTime
open scoped ENNReal

namespace MIP

/-! ### Tagged histories and per-prover projections -/

/-- A single-prover history of `(query, reply)` word pairs. -/
abbrev History := List (List Bool × List Bool)

/-- A tagged query-reply entry `(channel, (query, reply))` with channel index in `ℕ`. -/
abbrev TaggedEntry := ℕ × (List Bool × List Bool)

/-- A multi-channel transcript of `(channel, (query, reply))` entries. -/
abbrev TaggedHistory := List TaggedEntry

/-- Encoding of single-prover histories. -/
abbrev encHistory : History ↪ List Bool := encList (encPair encBits encBits)

/-- Encoding of a tagged transcript entry, with the channel index in unary. -/
abbrev encTaggedEntry : TaggedEntry ↪ List Bool :=
  encPair encUnary (encPair encBits encBits)

/-- Encoding of multi-channel tagged transcripts. -/
abbrev encTaggedHistory : TaggedHistory ↪ List Bool := encList encTaggedEntry

/-- A suffix of a framed list has a shorter encoding. -/
theorem length_encList_le_of_suffix {α : Type} {enc : α ↪ List Bool} {l l' : List α}
    (h : l <:+ l') : (encList enc l).length ≤ (encList enc l').length := by
  obtain ⟨p, rfl⟩ := h
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [List.cons_append, encList_cons, List.length_append]
    lia

/-- Project a multi-channel `TaggedHistory` onto the single-prover `History` seen by channel `i`. -/
def projHistory (i : ℕ) (th : TaggedHistory) : History :=
  (th.filter fun e => e.1 == i).map Prod.snd

@[simp]
theorem projHistory_nil (i : ℕ) : projHistory i [] = [] := rfl

theorem projHistory_cons_self (i : ℕ) (my : List Bool × List Bool) (rest : TaggedHistory) :
    projHistory i ((i, my) :: rest) = my :: projHistory i rest := by
  simp [projHistory]

theorem projHistory_cons_of_ne {i j : ℕ} (hne : j ≠ i) (my : List Bool × List Bool)
    (rest : TaggedHistory) :
    projHistory i ((j, my) :: rest) = projHistory i rest := by
  have hbeq : (j == i) = false := beq_false_of_ne hne
  simp [projHistory, hbeq]

/-- Projecting a tagged history onto channel `i` is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_projHistory :
    ComputableTidilyInPolyTime (fun p : ℕ × TaggedHistory => projHistory p.1 p.2)
      (encPair encUnary encTaggedHistory) encHistory := by
  unfold projHistory
  fun_prop

/-! ### Pairwise history consistency in polynomial time -/

/-- One step of the left-fold implementation of `consistentHist`: `s = (rest₂, active, ok)`. -/
def consistentHistStep (s : History × Bool × Bool) (e₁ : List Bool × List Bool) :
    History × Bool × Bool :=
  if !s.2.1 || s.1.isEmpty then (s.1, false, s.2.2)
  else if e₁.1 == (s.1.headD ([], [])).1 then
    (s.1.tail, true, s.2.2 && (e₁.2 == (s.1.headD ([], [])).2))
  else
    (s.1.tail, false, s.2.2)

theorem foldl_consistentHistStep_false (h₁ h₂ : History) (ok : Bool) :
    (h₁.foldl consistentHistStep (h₂, false, ok)).2.2 = ok := by
  induction h₁ generalizing h₂ with
  | nil => rfl
  | cons e₁ rest₁ ih =>
    simp only [List.foldl_cons, consistentHistStep, Bool.not_false, Bool.true_or, ↓reduceIte]
    exact ih h₂

theorem foldl_consistentHistStep_true (h₁ h₂ : History) (ok : Bool) :
    (h₁.foldl consistentHistStep (h₂, true, ok)).2.2 = (ok && consistentHist h₁ h₂) := by
  induction h₁ generalizing h₂ ok with
  | nil =>
    simp [consistentHist]
  | cons e₁ rest₁ ih =>
    obtain ⟨q₁, r₁⟩ := e₁
    cases h₂ with
    | nil =>
      simp only [List.foldl_cons, consistentHistStep, Bool.not_true, List.isEmpty_nil,
        Bool.false_or, ↓reduceIte, foldl_consistentHistStep_false, consistentHist, Bool.and_true]
    | cons e₂ rest₂ =>
      obtain ⟨q₂, r₂⟩ := e₂
      simp only [List.foldl_cons, consistentHistStep, Bool.not_true, List.isEmpty_cons,
        Bool.false_or, Bool.false_eq_true, ↓reduceIte, List.headD_cons, List.tail_cons,
        consistentHist]
      by_cases hq : q₁ = q₂
      · subst hq
        simp only [beq_self_eq_true, ↓reduceIte, ih, Bool.and_assoc]
      · have hq' : (q₁ == q₂) = false := beq_false_of_ne hq
        simp only [hq', Bool.false_eq_true, ↓reduceIte, foldl_consistentHistStep_false,
          Bool.and_true]

theorem consistentHistStep_suffix {h₂ : History} {s : History × Bool × Bool}
    (hs : s.1 <:+ h₂) (e₁ : List Bool × List Bool) :
    (consistentHistStep s e₁).1 <:+ h₂ := by
  unfold consistentHistStep
  split_ifs
  · exact hs
  · exact (List.tail_suffix s.1).trans hs
  · exact (List.tail_suffix s.1).trans hs

/-- `consistentHist` is computable tidily in polynomial time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_consistentHist :
    ComputableTidilyInPolyTime (fun p : History × History => consistentHist p.1 p.2)
      (encPair encHistory encHistory) encBool := by
  have hstep : ComputableTidilyInPolyTime
      (fun q : (History × Bool × Bool) × (List Bool × List Bool) => consistentHistStep q.1 q.2)
      (encPair (encPair encHistory (encPair encBool encBool)) (encPair encBits encBits))
      (encPair encHistory (encPair encBool encBool)) := by
    unfold consistentHistStep
    fun_prop
  have hfold := (foldl_spec (encIn := encPair encHistory encHistory)
    (encA := encPair encBits encBits) (encL := encHistory)
    (encB := encPair encHistory (encPair encBool encBool))
    (list := Prod.fst) (init := fun p => (p.2, true, true)) (step := consistentHistStep)
    (by fun_prop) (by fun_prop) hstep
    (fun p _ s => s.1 <:+ p.2)
    (fun p => List.suffix_refl p.2)
    (fun _ _ s e₁ _ hs => consistentHistStep_suffix hs e₁)
    (size := fun p => 2 * (encPair encHistory encHistory p).length + 6)
    (PolyBounded.of_forall_le 8 1 fun p => by simp only [pow_one]; lia)
    (fun p _ s _ hs => by
      have hlen := length_encList_le_of_suffix (enc := encPair encBits encBits) hs
      have hp := length_le_encPair_right encHistory encHistory p
      simp only [length_encPair, encBool_apply, List.length_singleton]
      lia)).1
  have hres : ComputableTidilyInPolyTime
      (fun p : History × History => (p.1.foldl consistentHistStep (p.2, true, true)).2.2)
      (encPair encHistory encHistory) encBool := by fun_prop
  exact hres.of_enc_eq fun p => by
    rw [foldl_consistentHistStep_true, Bool.true_and]

/-! ### Multi-channel live replay in polynomial time -/

section Replay

variable {p k : ℕ} {Control : Type} (M : MultiTapePTM k Bool Control (Fin p))

variable (p k Control) in
/-- State of a multi-channel live replay: configuration, remaining tagged history, and liveness. -/
abbrev AliveState := MultiTapeMachine.FiniteConfig k Bool Control (Fin p) × TaggedHistory × Bool

/-- The instruction of `M` in configuration `cfg` with coin `b`, unless halted. -/
def instruction (cfg : MultiTapeMachine.FiniteConfig k Bool Control (Fin p)) (b : Bool) :
    Option (MultiTapeMachine.Action k Bool Control (Fin p)) :=
  cfg.tapes.state.map fun c =>
    M.tr c cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols b

/-- Answer a query on channel `op` from the remaining tagged history, checking both the channel
index `op.val` and the query word `(s.1.channels op).1`, and truncating the reply to `t` bits. -/
def answerFromHistory (t : ℕ) (op : Fin p) (next : Control) (s : AliveState p k Control) :
    AliveState p k Control :=
  if s.2.1.isEmpty then (s.1, s.2.1, false)
  else if (s.2.1.headD (0, ([], []))).1 == op.val &&
      (s.2.1.headD (0, ([], []))).2.1 == (s.1.channels op).1 then
    (s.1.receive op next ((s.2.1.headD (0, ([], []))).2.2.take t), s.2.1.tail, true)
  else (s.1, s.2.1, false)

/-- Dispatch a live replay step by liveness and finite instruction tag. -/
def taggedStep (t : ℕ) :
    Bool × Option (MultiTapeMachine.Action k Bool Control (Fin p)) → AliveState p k Control →
      AliveState p k Control
  | (false, _), s => s
  | (true, none), s => s
  | (true, some (.step action symbol move)), s => (s.1.step action symbol move, s.2.1, true)
  | (true, some (.query op next)), s => answerFromHistory t op next s

/-- One step of the multi-channel live replay of `M` with truncation bound `t` and coin `b`. -/
def aliveStep (t : ℕ) (s : AliveState p k Control) (b : Bool) : AliveState p k Control :=
  taggedStep t (s.2.2, instruction M s.1 b) s

/-- The multi-channel live replay of `M` on input `x` with coins `r` against tagged history `th`. -/
def aliveRun (x r : List Bool) (th : TaggedHistory) : AliveState p k Control :=
  r.foldl (aliveStep M r.length) (MultiTapeMachine.FiniteConfig.init M.initial x, th, true)

/-- Whether `M` on input `x` with coins `r` accepts along tagged history `th`: the replay stays
live, consumes the entire tagged history, and halts with output `[true]`. -/
def accepts (x r : List Bool) (th : TaggedHistory) : Bool :=
  (aliveRun M x r th).2.2 && (aliveRun M x r th).2.1.isEmpty &&
    decide ((aliveRun M x r th).1.tapes.output = [true])

variable [Finite Control]

/-- Encoding of `AliveState p k Control`. -/
noncomputable abbrev encAliveState : AliveState p k Control ↪ List Bool :=
  encPair encFiniteConfig (encPair encTaggedHistory encBool)

/-- Reading the current instruction of `M` is polynomial-time. -/
theorem computableTidilyInPolyTime_instruction :
    ComputableTidilyInPolyTime
      (fun q : MultiTapeMachine.FiniteConfig k Bool Control (Fin p) × Bool =>
        instruction M q.1 q.2)
      (encPair encFiniteConfig encBool)
      (encFinite (Option (MultiTapeMachine.Action k Bool Control (Fin p)))) := by
  have hobs : ComputableTidilyInPolyTime
      (fun q : MultiTapeMachine.FiniteConfig k Bool Control (Fin p) × Bool =>
        (q.1.tapes.state, q.1.tapes.inputSymbol, q.1.tapes.workTapeSymbols, q.1.answerSymbols, q.2))
      (encPair encFiniteConfig encBool)
      (encPair (encFinite (Option Control)) (encPair (encFinite (Option Bool))
        (encPair (encFinite (Fin k → Option Bool)) (encPair (encFinite (Fin p → Option Bool))
          encBool)))) := by
    fun_prop
  exact ((of_finite fun obs : Option Control × Option Bool × (Fin k → Option Bool) ×
      (Fin p → Option Bool) × Bool => obs.1.map fun c =>
        M.tr c obs.2.1 obs.2.2.1 obs.2.2.2.1 obs.2.2.2.2).comp hobs).of_enc_eq fun _ => rfl

/-- Answering a query on channel `op` from the tagged history is polynomial-time. -/
theorem computableTidilyInPolyTime_answerFromHistory (op : Fin p) (next : Control) :
    ComputableTidilyInPolyTime (fun q : (ℕ × AliveState p k Control) × Bool =>
      answerFromHistory q.1.1 op next q.1.2)
      (encPair (encPair encUnary encAliveState) encBool) encAliveState := by
  unfold answerFromHistory
  fun_prop

/-- One step of the multi-channel live replay is polynomial-time. -/
theorem computableTidilyInPolyTime_aliveStep :
    ComputableTidilyInPolyTime (fun q : (ℕ × AliveState p k Control) × Bool =>
      aliveStep M q.1.1 q.1.2 q.2)
      (encPair (encPair encUnary encAliveState) encBool) encAliveState := by
  unfold aliveStep
  refine finite_cases (tag := fun q : (ℕ × AliveState p k Control) × Bool =>
      (q.1.2.2.2, instruction M q.1.2.1 q.2))
    (branch := fun tag q => taggedStep q.1.1 tag q.1.2)
    (tagEncoding := encPair encBool (encFinite (Option (MultiTapeMachine.Action k Bool Control
      (Fin p))))) ?_ ?_
  · have h := computableTidilyInPolyTime_instruction M
    fun_prop
  · rintro ⟨_ | _, _ | (⟨action, symbol, move⟩ | ⟨op, next⟩)⟩
    · exact (fst _ _).snd'
    · exact (fst _ _).snd'
    · exact (fst _ _).snd'
    · exact (fst _ _).snd'
    · simp only [taggedStep]
      fun_prop
    · exact computableTidilyInPolyTime_answerFromHistory op next

omit [Finite Control] in
/-- A step of `aliveStep` preserves `SpaceBound` and consumes a suffix of the tagged history. -/
theorem aliveStep_spaceBound {n i t : ℕ} {th : TaggedHistory} {s : AliveState p k Control}
    (hs : MultiTapeMachine.FiniteConfig.SpaceBound n i t s.1 ∧ s.2.1 <:+ th) (b : Bool) :
    MultiTapeMachine.FiniteConfig.SpaceBound n (i + 1) t (aliveStep M t s b).1 ∧
      (aliveStep M t s b).2.1 <:+ th := by
  obtain ⟨cfg, rest, _ | _⟩ := s
  · exact ⟨hs.1.mono le_rfl (by lia) le_rfl, hs.2⟩
  · dsimp only at hs ⊢
    obtain ⟨hspace, hsuffix⟩ := hs
    rcases hst : cfg.tapes.state with _ | c
    · simp only [aliveStep, instruction, hst, Option.map_none, taggedStep]
      exact ⟨hspace.mono le_rfl (by lia) le_rfl, hsuffix⟩
    · rcases htr : M.tr c cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols b with
        ⟨action, symbol, move⟩ | ⟨op, next⟩
      · simp only [aliveStep, instruction, hst, Option.map_some, htr, taggedStep]
        exact ⟨hspace.step action symbol move, hsuffix⟩
      · simp only [aliveStep, instruction, hst, Option.map_some, htr, taggedStep,
          answerFromHistory]
        cases rest with
        | nil => exact ⟨hspace.mono le_rfl (by lia) le_rfl, hsuffix⟩
        | cons e rest =>
          simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.headD_cons,
            List.tail_cons]
          by_cases hcond : (e.1 == op.val && e.2.1 == (cfg.channels op).1) = true
          · simp only [hcond, ↓reduceIte]
            exact ⟨hspace.receive op next _ (List.length_take_le _ _),
              (List.suffix_cons _ _).trans hsuffix⟩
          · simp only [hcond]
            exact ⟨hspace.mono le_rfl (by lia) le_rfl, hsuffix⟩

/-- The multi-channel live replay `aliveRun` is polynomial-time. -/
theorem computableTidilyInPolyTime_aliveRun :
    ComputableTidilyInPolyTime (fun q : List Bool × List Bool × TaggedHistory =>
      aliveRun M q.1 q.2.1 q.2.2)
      (encPair encBits (encPair encBits encTaggedHistory)) encAliveState := by
  obtain ⟨cf, hcf⟩ := length_encFiniteConfig_le (k := k) (State := Control) (Oracle := Fin p)
  unfold aliveRun
  refine (foldlWith_spec (par := fun q : List Bool × List Bool × TaggedHistory => q.2.1.length)
    (list := fun q => q.2.1)
    (init := fun q => (MultiTapeMachine.FiniteConfig.init M.initial q.1, q.2.2, true))
    (step := aliveStep M) (encP := encUnary) (encA := encBool) (encL := encBits)
    (by fun_prop) (by fun_prop) (by fun_prop) (computableTidilyInPolyTime_aliveStep M)
    (fun q consumed s => MultiTapeMachine.FiniteConfig.SpaceBound q.1.length consumed.length
      q.2.1.length s.1 ∧ s.2.1 <:+ q.2.2)
    (fun q => ⟨MultiTapeMachine.FiniteConfig.spaceBound_init _ _ _, List.suffix_refl _⟩)
    (fun q consumed s b _ hs => by simpa using aliveStep_spaceBound M hs b)
    (size := fun q => 2 * cf * (3 * (encPair encBits (encPair encBits encTaggedHistory) q).length +
      1) + 2 * (encPair encBits (encPair encBits encTaggedHistory) q).length + 3)
    (PolyBounded.of_forall_le (2 * cf * 3 + 2 * cf + 2 + 3) 1 fun q => by
      simp only [pow_one]
      nlinarith)
    (fun q consumed s hprefix hs => ?_)).1
  have hcfg := hcf _ _ _ _ hs.1
  have hhist := length_encList_le_of_suffix (enc := encTaggedEntry) hs.2
  have hcons : consumed.length ≤ q.2.1.length := hprefix.length_le
  simp only [encAliveState, length_encPair, encBool_apply, List.length_singleton, encBits_apply]
    at hcfg hhist ⊢
  have hcfg' := hcfg.trans (Nat.mul_le_mul_left cf (show q.1.length + consumed.length +
    q.2.1.length + 1 ≤ 3 * (2 * q.1.length + 1 + (2 * q.2.1.length + 1 +
      (encList encTaggedEntry q.2.2).length)) + 1 by lia))
  nlinarith

/-- Multi-channel replay acceptance is polynomial-time in the input, coins, and tagged history. -/
@[fun_prop]
theorem computableTidilyInPolyTime_accepts :
    ComputableTidilyInPolyTime (fun q : List Bool × List Bool × TaggedHistory =>
      accepts M q.1 q.2.1 q.2.2)
      (encPair encBits (encPair encBits encTaggedHistory)) encBool := by
  have h := computableTidilyInPolyTime_aliveRun M
  unfold accepts
  fun_prop

/-! ### Correspondence between `accepts` and `coinProgram` against deterministic provers -/

omit [Finite Control] in
theorem aliveStep_of_false (t : ℕ) (cfg : MultiTapeMachine.FiniteConfig k Bool Control (Fin p))
    (th : TaggedHistory) (b : Bool) :
    aliveStep M t (cfg, th, false) b = (cfg, th, false) := rfl

omit [Finite Control] in
theorem foldl_aliveStep_false (t : ℕ) (l : List Bool)
    (cfg : MultiTapeMachine.FiniteConfig k Bool Control (Fin p)) (th : TaggedHistory) :
    l.foldl (aliveStep M t) (cfg, th, false) = (cfg, th, false) := by
  induction l with
  | nil => rfl
  | cons b l ih => exact ih

omit [Finite Control] in
/-- **Soundness of a single `aliveStep`**: if `aliveStep M t (cfg, th, true) b` remains live and
every prover channel's projection of `th` is valid for `D i` from `s i`, then `coinStep M t cfg b`
against `Prover.independent (fun i => (D i).toProver)` transitions deterministically to the same
configuration and an updated state vector `s'` for which the remaining tagged history is valid. -/
theorem aliveStep_sound (t : ℕ) (D : Fin p → DetProver)
    (cfg : MultiTapeMachine.FiniteConfig k Bool Control (Fin p)) (th : TaggedHistory)
    (s : ∀ i : Fin p, (D i).State) (b : Bool)
    (hvalid : ∀ i : Fin p, (D i).ValidFrom (s i) (projHistory i.val th))
    (hlive : (aliveStep M t (cfg, th, true) b).2.2 = true) :
    ∃ s' : ∀ i : Fin p, (D i).State,
      (∀ i : Fin p,
        (D i).ValidFrom (s' i) (projHistory i.val (aliveStep M t (cfg, th, true) b).2.1)) ∧
      ((OracleComp.interpret (Prover.independent fun i => (D i).toProver).respond
        (coinStep M t cfg b)).run s) =
        PMF.pure ((aliveStep M t (cfg, th, true) b).1, s') := by
  simp only [aliveStep, instruction, coinStep, MultiTapeMachine.finiteStep] at hlive ⊢
  rcases hs : cfg.tapes.state with _ | c
  · simp only [hs] at hlive ⊢
    refine ⟨s, hvalid, ?_⟩
    simp [taggedStep, OracleComp.interpret_pure, StateT.run_pure,
      Probability.PMF.monad_pure_eq_pure]
  · simp only [hs, Option.map_some, map_pure, pure_bind] at hlive ⊢
    rcases htr : M.tr c cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols b with
      ⟨action, symbol, move⟩ | ⟨op, next⟩
    · simp only [htr] at hlive ⊢
      refine ⟨s, hvalid, ?_⟩
      simp [taggedStep, OracleComp.interpret_pure, StateT.run_pure,
        Probability.PMF.monad_pure_eq_pure]
    · simp only [htr, taggedStep, answerFromHistory] at hlive ⊢
      cases th with
      | nil => simp at hlive
      | cons e rest =>
        obtain ⟨ch, m, y⟩ := e
        simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.headD_cons,
          List.tail_cons] at hlive ⊢
        by_cases hmatch : (ch == op.val && m == (cfg.channels op).1) = true
        · simp only [hmatch, ↓reduceIte]
          simp only [Bool.and_eq_true, beq_iff_eq] at hmatch
          obtain ⟨rfl, rfl⟩ := hmatch
          have hop := hvalid op
          rw [projHistory_cons_self] at hop
          obtain ⟨hy, hop_rest⟩ := hop
          let s' := Function.update s op ((D op).respond (cfg.channels op).1 (s op)).2
          refine ⟨s', ?_, ?_⟩
          · intro i
            by_cases hi : i = op
            · subst hi
              simpa only [s', Function.update_self] using hop_rest
            · have hne : op.val ≠ i.val := fun h => hi (Fin.ext h.symm)
              have hvi := hvalid i
              rw [projHistory_cons_of_ne hne] at hvi
              simpa only [s', Function.update_of_ne hi] using hvi
          · simp only [bind_map_left, OracleComp.interpret_bind, OracleComp.interpret_query,
              OracleComp.interpret_pure, StateT.run_bind, StateT.run_pure,
              Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
              StateT.run_mk, PMF.pure_map, PMF.pure_bind, ← hy]
            rfl
        · simp [hmatch] at hlive

omit [Finite Control] in
/-- **Soundness of `foldl (aliveStep M t)`**: if the multi-channel replay over `l` stays live and
`th` has valid projections for `D` from `s`, then `l.foldlM (coinStep M t) cfg` transitions
deterministically to the final configuration of the replay. -/
theorem foldl_aliveStep_sound (t : ℕ) (D : Fin p → DetProver) (l : List Bool)
    (cfg : MultiTapeMachine.FiniteConfig k Bool Control (Fin p)) (th : TaggedHistory)
    (s : ∀ i : Fin p, (D i).State)
    (hvalid : ∀ i : Fin p, (D i).ValidFrom (s i) (projHistory i.val th))
    (hlive : (l.foldl (aliveStep M t) (cfg, th, true)).2.2 = true) :
    ∃ s' : ∀ i : Fin p, (D i).State,
      (∀ i : Fin p, (D i).ValidFrom (s' i)
        (projHistory i.val (l.foldl (aliveStep M t) (cfg, th, true)).2.1)) ∧
      ((OracleComp.interpret (Prover.independent fun i => (D i).toProver).respond
        (l.foldlM (coinStep M t) cfg)).run s) =
        PMF.pure ((l.foldl (aliveStep M t) (cfg, th, true)).1, s') := by
  induction l generalizing cfg th s with
  | nil =>
    exact ⟨s, hvalid, by simp [OracleComp.interpret_pure, StateT.run_pure,
      Probability.PMF.monad_pure_eq_pure]⟩
  | cons b l ih =>
    simp only [List.foldl_cons] at hlive ⊢
    have hstep_live : (aliveStep M t (cfg, th, true) b).2.2 = true := by
      rcases hst : aliveStep M t (cfg, th, true) b with ⟨cfg₁, th₁, _ | _⟩
      · rw [hst, foldl_aliveStep_false] at hlive
        cases hlive
      · rfl
    obtain ⟨s₁, hvalid₁, hrun₁⟩ := aliveStep_sound M t D cfg th s b hvalid hstep_live
    have hst_eq : aliveStep M t (cfg, th, true) b =
        ((aliveStep M t (cfg, th, true) b).1, (aliveStep M t (cfg, th, true) b).2.1, true) := by
      rcases hst : aliveStep M t (cfg, th, true) b with ⟨cfg₁, th₁, live₁⟩
      simp only [hst] at hstep_live ⊢
      subst hstep_live
      rfl
    rw [hst_eq] at hlive ⊢
    obtain ⟨s₂, hvalid₂, hrun₂⟩ := ih (aliveStep M t (cfg, th, true) b).1
      (aliveStep M t (cfg, th, true) b).2.1 s₁ hvalid₁ hlive
    refine ⟨s₂, hvalid₂, ?_⟩
    simp only [List.foldlM_cons, OracleComp.interpret_bind, StateT.run_bind,
      Probability.PMF.monad_bind_eq_bind, hrun₁, PMF.pure_bind, hrun₂]

omit [Finite Control] in
/-- **Soundness of `accepts`**: if `r.length = t`, `accepts M x r th = true`, and every prover's
projection of `th` is valid for `D i` from `s i`, then `coinProgram M t x r` accepts with
probability `1` against `D`. -/
theorem queryAcceptProb_eq_one_of_accepts {x r : List Bool} {t : ℕ} (hr : r.length = t)
    (D : Fin p → DetProver) (s : ∀ i : Fin p, (D i).State) (th : TaggedHistory)
    (hvalid : ∀ i : Fin p, (D i).ValidFrom (s i) (projHistory i.val th))
    (hacc : accepts M x r th = true) :
    queryAcceptProb (Prover.independent fun i => (D i).toProver) s (coinProgram M t x r) = 1 := by
  subst hr
  simp only [accepts, aliveRun, Bool.and_eq_true] at hacc
  obtain ⟨⟨hlive, _⟩, hout⟩ := hacc
  have hout' := of_decide_eq_true hout
  obtain ⟨s', _, hrun⟩ := foldl_aliveStep_sound M r.length D r
    (MultiTapeMachine.FiniteConfig.init M.initial x) th s hvalid hlive
  simp only [queryAcceptProb, coinProgram, OracleComp.interpret_map, StateT.run_map,
    PMF.monad_map_eq_map, hrun, PMF.pure_map]
  simp [hout']

/-- The canonical tagged history generated by running `M` with truncation `t` against deterministic
provers `D : Fin p → DetProver` from configuration `cfg` and prover states `s` over coins `l`. -/
def canonicalTrace (t : ℕ) (D : Fin p → DetProver) :
    MultiTapeMachine.FiniteConfig k Bool Control (Fin p) → (∀ i : Fin p, (D i).State) →
      List Bool → TaggedHistory
  | _, _, [] => []
  | cfg, s, b :: l =>
    match cfg.tapes.state with
    | none => canonicalTrace t D cfg s l
    | some c =>
      match M.tr c cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols b with
      | .step action symbol move =>
        canonicalTrace t D (cfg.step action symbol move) s l
      | .query op next =>
        let m := (cfg.channels op).1
        let res := (D op).respond m (s op)
        let y := res.1.take t
        (op.val, (m, y)) ::
          canonicalTrace t D (cfg.receive op next y) (Function.update s op res.2) l

omit [Finite Control] in
/-- Every prover's projection of `canonicalTrace M t D cfg s l` is a valid history for the
`t`-truncated deterministic prover `(D i).truncate t` starting from `s i`. -/
theorem validFrom_canonicalTrace (t : ℕ) (D : Fin p → DetProver)
    (cfg : MultiTapeMachine.FiniteConfig k Bool Control (Fin p))
    (s : ∀ i : Fin p, (D i).State) (l : List Bool) (i : Fin p) :
    ((D i).truncate t).ValidFrom (s i) (projHistory i.val (canonicalTrace M t D cfg s l)) := by
  induction l generalizing cfg s with
  | nil => trivial
  | cons b l ih =>
    rcases hs : cfg.tapes.state with _ | c
    · simp only [canonicalTrace, hs]
      exact ih cfg s
    · rcases htr : M.tr c cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols b with
        ⟨action, symbol, move⟩ | ⟨op, next⟩
      · simp only [canonicalTrace, hs, htr]
        exact ih (cfg.step action symbol move) s
      · simp only [canonicalTrace, hs, htr]
        by_cases hi : i = op
        · subst hi
          rw [projHistory_cons_self]
          refine ⟨rfl, ?_⟩
          have := ih (cfg.receive i next (((D i).respond (cfg.channels i).1 (s i)).1.take t))
            (Function.update s i ((D i).respond (cfg.channels i).1 (s i)).2)
          simpa only [Function.update_self] using this
        · have hne : op.val ≠ i.val := fun h => hi (Fin.ext h.symm)
          rw [projHistory_cons_of_ne hne]
          have := ih (cfg.receive op next (((D op).respond (cfg.channels op).1 (s op)).1.take t))
            (Function.update s op ((D op).respond (cfg.channels op).1 (s op)).2)
          simpa only [Function.update_of_ne hi] using this

omit [Finite Control] in
/-- Running `foldl (aliveStep M t)` against `canonicalTrace M t D cfg s l` stays live, consumes the
entire trace, and reaches the exact configuration produced by `l.foldlM (coinStep M t) cfg` against
`D`. -/
theorem foldl_aliveStep_canonicalTrace (t : ℕ) (D : Fin p → DetProver)
    (cfg : MultiTapeMachine.FiniteConfig k Bool Control (Fin p))
    (s : ∀ i : Fin p, (D i).State) (l : List Bool) :
    ∃ (cfg' : MultiTapeMachine.FiniteConfig k Bool Control (Fin p))
      (s' : ∀ i : Fin p, (D i).State),
      l.foldl (aliveStep M t) (cfg, canonicalTrace M t D cfg s l, true) = (cfg', [], true) ∧
      ((OracleComp.interpret (Prover.independent fun i => (D i).toProver).respond
        (l.foldlM (coinStep M t) cfg)).run s) = PMF.pure (cfg', s') := by
  induction l generalizing cfg s with
  | nil =>
    exact ⟨cfg, s, rfl, by simp [OracleComp.interpret_pure, StateT.run_pure,
      Probability.PMF.monad_pure_eq_pure]⟩
  | cons b l ih =>
    rcases hs : cfg.tapes.state with _ | c
    · simp only [canonicalTrace, List.foldl_cons, List.foldlM_cons, aliveStep, instruction,
        coinStep, MultiTapeMachine.finiteStep, hs, Option.map_none, taggedStep]
      obtain ⟨cfg', s', hfold, hrun⟩ := ih cfg s
      refine ⟨cfg', s', hfold, ?_⟩
      simp only [OracleComp.interpret_bind, OracleComp.interpret_pure, StateT.run_bind,
        StateT.run_pure, Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
        PMF.pure_bind, hrun]
    · rcases htr : M.tr c cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols b with
        ⟨action, symbol, move⟩ | ⟨op, next⟩
      · simp only [canonicalTrace, List.foldl_cons, List.foldlM_cons, aliveStep, instruction,
          coinStep, MultiTapeMachine.finiteStep, hs, Option.map_some, htr, taggedStep, map_pure,
          pure_bind]
        obtain ⟨cfg', s', hfold, hrun⟩ := ih (cfg.step action symbol move) s
        exact ⟨cfg', s', hfold, hrun⟩
      · simp only [canonicalTrace, List.foldl_cons, List.foldlM_cons, aliveStep, instruction,
          coinStep, MultiTapeMachine.finiteStep, hs, Option.map_some, htr, map_pure, pure_bind]
        let m := (cfg.channels op).1
        let res := (D op).respond m (s op)
        let y := res.1.take t
        have hstep : taggedStep t (true, some (.query op next))
            (cfg, (op.val, (m, y)) :: canonicalTrace M t D (cfg.receive op next y)
              (Function.update s op res.2) l, true) =
            (cfg.receive op next y,
              canonicalTrace M t D (cfg.receive op next y) (Function.update s op res.2) l,
              true) := by
          simp [taggedStep, answerFromHistory, m, res, y, List.take_take]
        rw [hstep]
        obtain ⟨cfg', s', hfold, hrun⟩ :=
          ih (cfg.receive op next y) (Function.update s op res.2)
        refine ⟨cfg', s', hfold, ?_⟩
        rw [OracleComp.interpret_bind, StateT.run_bind, Probability.PMF.monad_bind_eq_bind]
        have hq : ((OracleComp.interpret (Prover.independent fun i => (D i).toProver).respond
            (do
              let answer ← List.take t <$> OracleComp.query (op, (cfg.channels op).1)
              pure (cfg.receive op next answer))).run s) =
            PMF.pure (cfg.receive op next y, Function.update s op res.2) := by
          simp only [bind_map_left, OracleComp.interpret_bind, OracleComp.interpret_query,
            OracleComp.interpret_pure, StateT.run_bind, StateT.run_pure,
            Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
            StateT.run_mk, PMF.pure_map, PMF.pure_bind]
          rfl
        rw [hq, PMF.pure_bind, hrun]

omit [Finite Control] in
/-- **Completeness of `accepts` via `canonicalTrace`**: for any `r` of length `t`, the acceptance
probability of `coinProgram M t x r` against deterministic provers `D` is `1` if `accepts` holds on
`canonicalTrace`, and `0` otherwise. -/
theorem queryAcceptProb_eq_ite_accepts_canonicalTrace {x r : List Bool} {t : ℕ}
    (hr : r.length = t) (D : Fin p → DetProver) :
    queryAcceptProb (Prover.independent fun i => (D i).toProver)
      (Prover.independent fun i => (D i).toProver).init (coinProgram M t x r) =
      if accepts M x r
        (canonicalTrace M t D (MultiTapeMachine.FiniteConfig.init M.initial x)
          (fun i => (D i).init) r) then 1 else 0 := by
  subst hr
  obtain ⟨cfg', s', hfold, hrun⟩ := foldl_aliveStep_canonicalTrace M r.length D
    (MultiTapeMachine.FiniteConfig.init M.initial x) (fun i => (D i).init) r
  simp only [queryAcceptProb, coinProgram, OracleComp.interpret_map, StateT.run_map,
    PMF.monad_map_eq_map, accepts, aliveRun, hfold, List.isEmpty_nil, Bool.true_and, hrun,
    PMF.pure_map]
  cases decide (cfg'.tapes.output = [true]) <;> simp

omit [Finite Control] in
/-- Size bounds on `canonicalTrace M t D cfg s l`: its length is at most `l.length`, every channel
index is at most `p`, every query has length at most `i + l.length`, and every reply has length at
most `t`. -/
theorem bounds_canonicalTrace {n i t : ℕ} (D : Fin p → DetProver)
    {cfg : MultiTapeMachine.FiniteConfig k Bool Control (Fin p)}
    (hspace : MultiTapeMachine.FiniteConfig.SpaceBound n i t cfg)
    (s : ∀ j : Fin p, (D j).State) (l : List Bool) :
    (canonicalTrace M t D cfg s l).length ≤ l.length ∧
      ∀ e ∈ canonicalTrace M t D cfg s l,
        e.1 ≤ p ∧ e.2.1.length ≤ i + l.length ∧ e.2.2.length ≤ t := by
  induction l generalizing i cfg s with
  | nil => simp [canonicalTrace]
  | cons b l ih =>
    rcases hs : cfg.tapes.state with _ | c
    · simp only [canonicalTrace, hs, List.length_cons]
      obtain ⟨hlen, hmem⟩ := ih (hspace.mono le_rfl (Nat.le_succ i) le_rfl) s
      refine ⟨Nat.le_succ_of_le hlen, fun e he => ?_⟩
      obtain ⟨h1, h2, h3⟩ := hmem e he
      exact ⟨h1, by lia, h3⟩
    · rcases htr : M.tr c cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols b with
        ⟨action, symbol, move⟩ | ⟨op, next⟩
      · simp only [canonicalTrace, hs, htr, List.length_cons]
        obtain ⟨hlen, hmem⟩ := ih (hspace.step action symbol move) s
        refine ⟨Nat.le_succ_of_le hlen, fun e he => ?_⟩
        obtain ⟨h1, h2, h3⟩ := hmem e he
        exact ⟨h1, by lia, h3⟩
      · simp only [canonicalTrace, hs, htr, List.length_cons]
        have hrec := hspace.receive op next
          (((D op).respond (cfg.channels op).1 (s op)).1.take t) (List.length_take_le _ _)
        obtain ⟨hlen, hmem⟩ := ih hrec
          (Function.update s op ((D op).respond (cfg.channels op).1 (s op)).2)
        refine ⟨Nat.succ_le_succ hlen, fun e he => ?_⟩
        rcases List.mem_cons.mp he with rfl | he
        · have hq := hspace.query op
          exact ⟨Nat.le_of_lt op.isLt, by lia, List.length_take_le _ _⟩
        · obtain ⟨h1, h2, h3⟩ := hmem e he
          exact ⟨h1, by lia, h3⟩

end Replay

/-! ### Polynomial-time certificate checking and the padded `NP` language -/

/-- A multiprover certificate is a list of `(coinString, taggedHistory)` pairs. -/
abbrev Cert := List (List Bool × TaggedHistory)

/-- Encoding of a single `(coinString, taggedHistory)` certificate entry. -/
abbrev encCertEntry : (List Bool × TaggedHistory) ↪ List Bool :=
  encPair encBits encTaggedHistory

/-- Encoding of multiprover certificates. -/
abbrev encCert : Cert ↪ List Bool := encList encCertEntry

/-- Total decoder for raw bit strings. -/
def bitsDecoder : Decoder encBits where
  decode := id
  decode_enc _ := rfl
  computable := (ComputableTidilyInPolyTime.id' (encIn := encBits)).exists_degree

/-- Total decoder for multiprover certificates. -/
def certDecoder : Decoder encCert :=
  Decoder.list (Decoder.pair bitsDecoder
    (Decoder.list (Decoder.pair Decoder.unary (Decoder.pair bitsDecoder bitsDecoder))))

section Checker

variable {p k : ℕ} {Control : Type} (M : MultiTapePTM k Bool Control (Fin p))

/-- Check whether `cert` is a valid accepting multiprover transcript table for `M` on input `x`
with clock `t = c * (x.length + 1) ^ d`:
1. every `(r, th) ∈ cert` has `r.length = t` and `accepts M x r th = true`,
2. every coin string `r` in `cert` appears once,
3. for every prover `i < p`, the projected histories `projHistory i th` are pairwise
   `consistentHist`,
4. `2 ^ t < 2 * cert.length`. -/
def checkCert (c d : ℕ) (x : List Bool) (cert : Cert) : Bool :=
  let t := c * (x.length + 1) ^ d
  (cert.all fun e => (e.1.length == t) && accepts M x e.1 e.2) &&
  (cert.all fun e₁ => cert.countP (fun e₂ => e₁.1 == e₂.1) == 1) &&
  (cert.all fun e₁ => cert.all fun e₂ =>
    (List.range p).all fun i => consistentHist (projHistory i e₁.2) (projHistory i e₂.2)) &&
  decide (2 ^ t < 2 * cert.length)

/-- Check a certificate on a padded instance `w`: require `(encCert cert).length ≤ w.length` and
run `checkCert` on the unframed prefix `unframe w`. -/
def checkPaddedCert (c d : ℕ) (q : List Bool × Cert) : Bool :=
  decide ((encCert q.2).length ≤ q.1.length) && checkCert M c d (unframe q.1) q.2

/-- The padded `NP` language associated to `M` and clock polynomial `c * (n + 1) ^ d`. -/
def paddedMIP (c d : ℕ) : Set (List Bool) :=
  {w : List Bool | ∃ cert : Cert, checkPaddedCert M c d (w, cert) = true}

variable [Finite Control]

/-- `checkCert` is computable tidily in polynomial time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_checkCert (c d : ℕ) :
    ComputableTidilyInPolyTime (fun q : List Bool × Cert => checkCert M c d q.1 q.2)
      (encPair encBits encCert) encBool := by
  have ht : ComputableTidilyInPolyTime
      (fun q : List Bool × Cert => c * (q.1.length + 1) ^ d)
      (encPair encBits encCert) encUnary := by
    have hlen : ComputableTidilyInPolyTime (fun q : List Bool × Cert => q.1.length)
        (encPair encBits encCert) encUnary := by fun_prop
    exact ((unary_eval (Polynomial.C c * (Polynomial.X + 1) ^ d)).comp hlen).of_enc_eq
      fun q => by simp
  have h1 : ComputableTidilyInPolyTime
      (fun q : List Bool × Cert =>
        q.2.all fun e => (e.1.length == c * (q.1.length + 1) ^ d) && accepts M q.1 e.1 e.2)
      (encPair encBits encCert) encBool := by
    apply allWithInput (by fun_prop)
    refine bool_and' ?_ (by fun_prop)
    exact unary_beq (by fun_prop) (ht.comp (fst _ _))
  have h2 : ComputableTidilyInPolyTime
      (fun q : List Bool × Cert =>
        q.2.all fun e₁ => q.2.countP (fun e₂ => e₁.1 == e₂.1) == 1)
      (encPair encBits encCert) encBool := by
    apply allWithInput (by fun_prop)
    refine unary_beq ?_ (const 1)
    apply countPWithInput (by fun_prop)
    fun_prop
  have h3 : ComputableTidilyInPolyTime
      (fun q : List Bool × Cert =>
        q.2.all fun e₁ => q.2.all fun e₂ =>
          (List.range p).all fun i => consistentHist (projHistory i e₁.2) (projHistory i e₂.2))
      (encPair encBits encCert) encBool := by
    apply allWithInput (by fun_prop)
    apply allWithInput (by fun_prop)
    apply allWithInput (range.comp (const p))
    fun_prop
  have h4 : ComputableTidilyInPolyTime
      (fun q : List Bool × Cert =>
        decide (2 ^ (c * (q.1.length + 1) ^ d) < 2 * q.2.length))
      (encPair encBits encCert) encBool := by
    have hpow : ComputableTidilyInPolyTime
        (fun q : List Bool × Cert => 2 ^ (c * (q.1.length + 1) ^ d))
        (encPair encBits encCert) encNat := binary_two_pow.comp ht
    have hlen : ComputableTidilyInPolyTime
        (fun q : List Bool × Cert => q.2.length)
        (encPair encBits encCert) encNat :=
      unary_to_binary.comp ((length_list encCertEntry).comp (snd encBits encCert))
    exact binary_lt' hpow (binary_mul' (const 2) hlen)
  exact bool_and' (bool_and' (bool_and' h1 h2) h3) h4

/-- `checkPaddedCert` is computable tidily in polynomial time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_checkPaddedCert (c d : ℕ) :
    ComputableTidilyInPolyTime (checkPaddedCert M c d) (encPair encBits encCert) encBool := by
  have hunframe : ComputableTidilyInPolyTime unframe encBits encBits :=
    .of_linear (.of_unframe fun _ => rfl)
  have hlen : ComputableTidilyInPolyTime
      (fun q : List Bool × Cert => decide ((encCert q.2).length ≤ q.1.length))
      (encPair encBits encCert) encBool :=
    unary_le' ((encoding_length encCert).comp (snd encBits encCert))
      (length_bits.comp (fst encBits encCert))
  exact bool_and' hlen ((computableTidilyInPolyTime_checkCert M c d).comp
    ((hunframe.comp (fst encBits encCert)).prod (snd encBits encCert)))

/-- The padded multiprover language `paddedMIP M c d` belongs to `NP encBits`. -/
theorem paddedMIP_mem_NP (c d : ℕ) : paddedMIP M c d ∈ NP encBits := by
  refine mem_NP_of_witness certDecoder (p := Polynomial.X)
    (computableTidilyInPolyTime_checkPaddedCert M c d) (fun _ _ => Iff.rfl) ?_
  intro w cert h
  refine ⟨cert, h, ?_⟩
  simp only [checkPaddedCert, Bool.and_eq_true, decide_eq_true_eq] at h
  simpa using h.1

/-! ### Soundness and completeness of `checkCert` -/

omit [Finite Control] in
/-- If every element `a ∈ l` has `l.countP (fun b => a == b) = 1`, then `l.Nodup`. -/
theorem nodup_of_forall_countP_eq_one {α : Type} [BEq α] [LawfulBEq α] {l : List α}
    (h : ∀ a ∈ l, l.countP (fun b => a == b) = 1) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a rest ih =>
    rw [List.nodup_cons]
    have ha := h a List.mem_cons_self
    simp only [List.countP_cons, beq_self_eq_true, ↓reduceIte] at ha
    have hcount0 : rest.countP (fun b => a == b) = 0 := by lia
    have hnotmem : a ∉ rest := by
      intro hmem
      have hpos : 0 < rest.countP (fun b => a == b) :=
        List.countP_pos_iff.mpr ⟨a, hmem, beq_self_eq_true a⟩
      lia
    refine ⟨hnotmem, ih fun x hx => ?_⟩
    have hx_all := h x (List.mem_cons_of_mem a hx)
    have hne : (x == a) = false := beq_false_of_ne (fun hxa => hnotmem (hxa ▸ hx))
    simpa [List.countP_cons, hne] using hx_all

omit [Finite Control] in
/-- **Soundness of `checkCert`**: if `checkCert M c d x cert = true`, then there exists an
independent family of deterministic provers `D : Fin p → DetProver` whose acceptance probability on
the `t = c * (x.length + 1) ^ d` coin family exceeds `1 / 2`. -/
theorem exists_detProver_of_checkCert {c d : ℕ} {x : List Bool} {cert : Cert}
    (hcheck : checkCert M c d x cert = true) :
    let t := c * (x.length + 1) ^ d
    ∃ D : Fin p → DetProver,
      (cert.length : ℝ≥0∞) ≤
        ∑ f : Fin t → Bool,
          queryAcceptProb (Prover.independent fun i => (D i).toProver)
            (Prover.independent fun i => (D i).toProver).init
            (coinProgram M t x (List.ofFn f)) ∧
      2 ^ t < 2 * cert.length := by
  set t := c * (x.length + 1) ^ d
  simp only [checkCert, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.mem_range] at hcheck
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hcheck
  let H (i : Fin p) : List History := cert.map fun e => projHistory i.val e.2
  let D (i : Fin p) : DetProver := candidateProver (H i)
  refine ⟨D, ?_, h4⟩
  have hvalid_cert : ∀ e ∈ cert, ∀ i : Fin p,
      (D i).ValidFrom (D i).init (projHistory i.val e.2) := by
    intro e he i
    refine validFrom_candidateProver (H i) (H i) ?_ (List.mem_map_of_mem he)
    intro h₁ hh₁ h₂ hh₂
    rw [List.mem_map] at hh₁ hh₂
    obtain ⟨e₁, he₁, rfl⟩ := hh₁
    obtain ⟨e₂, he₂, rfl⟩ := hh₂
    exact h3 e₁ he₁ e₂ he₂ i.val i.isLt
  have hprob_one : ∀ e ∈ cert,
      queryAcceptProb (Prover.independent fun i => (D i).toProver)
        (Prover.independent fun i => (D i).toProver).init
        (coinProgram M t x e.1) = 1 := by
    intro e he
    obtain ⟨hlen, hacc⟩ := h1 e he
    exact queryAcceptProb_eq_one_of_accepts M hlen D (fun i => (D i).init) e.2
      (hvalid_cert e he) hacc
  have hnodup_fst : (cert.map Prod.fst).Nodup := by
    refine nodup_of_forall_countP_eq_one ?_
    intro r hr
    rw [List.mem_map] at hr
    obtain ⟨e, he, rfl⟩ := hr
    have hcount := h2 e he
    rw [List.countP_map]
    exact hcount
  let toFin (r : List Bool) : Fin t → Bool := fun j => r.getD j false
  have hofFn_toFin : ∀ e ∈ cert, List.ofFn (toFin e.1) = e.1 := by
    intro e he
    have hlen : e.1.length = t := (h1 e he).1
    refine List.ext_getElem (by simp [hlen]) fun j h₁ h₂ => ?_
    simp [toFin, h₂]
  let S : Finset (Fin t → Bool) := (cert.map (fun e => toFin e.1)).toFinset
  have hnodup_toFin : (cert.map (fun e => toFin e.1)).Nodup := by
    rw [show cert.map (fun e => toFin e.1) = (cert.map Prod.fst).map toFin by
      rw [List.map_map]; rfl]
    refine hnodup_fst.map_on ?_
    intro r₁ hr₁ r₂ hr₂ heq
    rw [List.mem_map] at hr₁ hr₂
    obtain ⟨e₁, he₁, rfl⟩ := hr₁
    obtain ⟨e₂, he₂, rfl⟩ := hr₂
    rw [← hofFn_toFin e₁ he₁, ← hofFn_toFin e₂ he₂, heq]
  have hcard : S.card = cert.length := by
    rw [List.toFinset_card_of_nodup hnodup_toFin, List.length_map]
  calc (cert.length : ℝ≥0∞)
      = ∑ _f ∈ S, (1 : ℝ≥0∞) := by simp [hcard]
    _ ≤ ∑ f ∈ S,
          queryAcceptProb (Prover.independent fun i => (D i).toProver)
            (Prover.independent fun i => (D i).toProver).init
            (coinProgram M t x (List.ofFn f)) := by
        refine Finset.sum_le_sum fun f hf => ?_
        simp only [S, List.mem_toFinset, List.mem_map] at hf
        obtain ⟨e, he, rfl⟩ := hf
        rw [hofFn_toFin e he, hprob_one e he]
    _ ≤ ∑ f : Fin t → Bool,
          queryAcceptProb (Prover.independent fun i => (D i).toProver)
            (Prover.independent fun i => (D i).toProver).init
            (coinProgram M t x (List.ofFn f)) :=
        Finset.sum_le_univ_sum_of_nonneg fun _ => zero_le

omit [Finite Control] in
/-- Upper bound on the encoded length of the canonical certificate built from
`D : Fin p → DetProver` for `M` on `x` with `t` coins:
`(encCert cert).length ≤ 32 * (p + x.length + t + 1) ^ 2 * 2 ^ t`. -/
theorem exists_checkCert_of_detProver {c d : ℕ} (x : List Bool) (D : Fin p → DetProver)
    (hlt : 2 ^ (c * (x.length + 1) ^ d) <
      2 * ((Finset.univ : Finset (Fin (c * (x.length + 1) ^ d) → Bool)).filter fun f =>
        accepts M x (List.ofFn f)
          (canonicalTrace M (c * (x.length + 1) ^ d) D
            (MultiTapeMachine.FiniteConfig.init M.initial x) (fun i => (D i).init)
            (List.ofFn f))).card) :
    let t := c * (x.length + 1) ^ d
    ∃ cert : Cert,
      checkCert M c d x cert = true ∧
      (encCert cert).length ≤ 32 * (p + x.length + t + 1) ^ 2 * 2 ^ t := by
  set t := c * (x.length + 1) ^ d
  let traceOf (r : List Bool) : TaggedHistory :=
    canonicalTrace M t D (MultiTapeMachine.FiniteConfig.init M.initial x) (fun i => (D i).init) r
  let goodFinset : Finset (Fin t → Bool) :=
    (Finset.univ : Finset (Fin t → Bool)).filter fun f =>
      accepts M x (List.ofFn f) (traceOf (List.ofFn f))
  let goodFns : List (Fin t → Bool) := goodFinset.toList
  let cert : Cert := goodFns.map fun f => (List.ofFn f, traceOf (List.ofFn f))
  have hgood_length : goodFns.length = goodFinset.card := Finset.length_toList _
  have hcert_length : cert.length = goodFns.length := List.length_map _
  have hnodup_good : goodFns.Nodup := Finset.nodup_toList _
  have hnodup_fst : (cert.map Prod.fst).Nodup := by
    rw [show cert.map Prod.fst = goodFns.map List.ofFn by simp [cert, List.map_map]]
    refine hnodup_good.map_on ?_
    intro f₁ _ f₂ _ heq
    funext j
    have := congrArg (fun l : List Bool => l.getD j false) heq
    simpa using this
  refine ⟨cert, ?_, ?_⟩
  · simp only [checkCert, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq,
      List.mem_range]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · intro e he
      simp only [cert, goodFns, goodFinset, List.mem_map, Finset.mem_toList,
        Finset.mem_filter] at he
      obtain ⟨f, ⟨_, hacc⟩, rfl⟩ := he
      exact ⟨List.length_ofFn, hacc⟩
    · intro e₁ he₁
      have hcount : (cert.map Prod.fst).countP (fun r => e₁.1 == r) = 1 := by
        have hcomm : (fun r : List Bool => e₁.1 == r) = (fun r => r == e₁.1) := by
          funext r
          rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, eq_comm]
        rw [hcomm, ← List.count_eq_countP]
        exact List.count_eq_one_of_mem hnodup_fst (List.mem_map_of_mem he₁)
      rw [List.countP_map] at hcount
      exact hcount
    · intro e₁ he₁ e₂ he₂ i hi
      simp only [cert, List.mem_map] at he₁ he₂
      obtain ⟨f₁, _, rfl⟩ := he₁
      obtain ⟨f₂, _, rfl⟩ := he₂
      let iFin : Fin p := ⟨i, hi⟩
      have hv₁ := validFrom_canonicalTrace M t D
        (MultiTapeMachine.FiniteConfig.init M.initial x) (fun j => (D j).init) (List.ofFn f₁) iFin
      have hv₂ := validFrom_canonicalTrace M t D
        (MultiTapeMachine.FiniteConfig.init M.initial x) (fun j => (D j).init) (List.ofFn f₂) iFin
      exact DetProver.ValidFrom.consistentHist hv₁ hv₂
    · rw [hcert_length, hgood_length]
      exact hlt
  · -- Bound `(encCert cert).length`
    let B := p + x.length + t + 1
    have hentry : ∀ e ∈ cert, (encCertEntry e).length ≤ 9 * B ^ 2 := by
      intro e he
      simp only [cert, List.mem_map] at he
      obtain ⟨f, _, rfl⟩ := he
      have hlen_r : (List.ofFn f).length = t := List.length_ofFn
      have hbounds := bounds_canonicalTrace M D
        (MultiTapeMachine.FiniteConfig.spaceBound_init M.initial x t)
        (fun i => (D i).init) (List.ofFn f)
      rw [hlen_r, Nat.zero_add] at hbounds
      have htag : ∀ te ∈ traceOf (List.ofFn f), (encTaggedEntry te).length ≤ 3 * B := by
        intro te hte
        obtain ⟨h1, h2, h3⟩ := hbounds.2 te hte
        simp only [encTaggedEntry, length_encPair, encUnary_apply, List.length_replicate,
          encBits_apply]
        simp only [B]
        lia
      have hth_len : (encTaggedHistory (traceOf (List.ofFn f))).length ≤ B * (2 * (3 * B) + 1) := by
        refine (length_encList_le encTaggedEntry _ htag).trans ?_
        have hlen_th : (traceOf (List.ofFn f)).length ≤ B := hbounds.1.trans (by simp [B]; lia)
        exact Nat.mul_le_mul_right (2 * (3 * B) + 1) hlen_th
      simp only [encCertEntry, length_encPair, encBits_apply, hlen_r]
      have hB1 : 1 ≤ B := by simp [B]
      have htB : t + 1 ≤ B := by simp [B]
      have hsq : 2 * t + 1 + B * (2 * (3 * B) + 1) ≤ 9 * B ^ 2 := by nlinarith
      exact (Nat.add_le_add_left hth_len (2 * t + 1)).trans hsq
    have hcert_le : cert.length ≤ 2 ^ t := by
      rw [hcert_length, hgood_length]
      exact (Finset.card_le_univ _).trans (by simp)
    have htotal := length_encList_le encCertEntry cert hentry
    have hB1 : 1 ≤ B := by simp [B]
    have hmul : 2 * (9 * B ^ 2) + 1 ≤ 32 * B ^ 2 := by nlinarith
    calc (encCert cert).length
        ≤ cert.length * (2 * (9 * B ^ 2) + 1) := htotal
      _ ≤ 2 ^ t * (32 * B ^ 2) := Nat.mul_le_mul hcert_le hmul
      _ = 32 * B ^ 2 * 2 ^ t := by ring

end Checker

end MIP

/-! ### Upward translation from `NP` to `NTIME` and `NEXP` -/

section Translation

variable {α : Type} {enc : α ↪ List Bool}

/-- Pulling back a problem `B ∈ NP encBits` along a function `g : α → List Bool` computable tidily
within time `O(T₀ (enc a).length)` places `g ⁻¹' B` in `NTIME enc (fun n => (T₀ n + 1) ^ d)` for
some `d`: a deterministic machine writes `g a` to a buffer tape and hands off to the halting
fair-coin certificate verifier for `B`. -/
theorem preimage_mem_NTIME_of_mem_NP {B : Set (List Bool)} {g : α → List Bool} {T₀ : ℕ → ℕ}
    {S : α → ℕ} (hB : B ∈ NP encBits)
    (hg : ComputableTidilyInO g enc encBits (fun a => T₀ (enc a).length) S) :
    ∃ d, g ⁻¹' B ∈ NTIME enc fun n => (T₀ n + 1) ^ d := by
  obtain ⟨c₀, ⟨k₀, State₀, hfinite₀, tm, htm⟩, -⟩ := hg
  set t₁ : α → ℕ := fun a => c₀ * (T₀ (enc a).length + 1)
  have htm_run (a : α) :
      tm.runFrom (tm.initCfg (enc a)) (t₁ a) = wordsCfg (enc a) none (fun _ => []) (g a) := by
    obtain ⟨p, hh, hl, ht, -⟩ := computesTidily_iff.mp (htm a)
    have hhead : p.head = tm.initCfg (enc a) := hh.trans (Cfg.init_eq_wordsCfg tm.q₀ (enc a)).symm
    have hrun : tm.runFrom (tm.initCfg (enc a)) p.time =
        wordsCfg (enc a) none (fun _ => []) (g a) :=
      hhead ▸ (MultiTapeTM.runPath_apply_eq_runFrom p (.last _)).symm.trans hl
    have hhalt : (tm.runFrom (tm.initCfg (enc a)) p.time).state = none := by rw [hrun]; rfl
    exact (tm.runFrom_eq_of_halt (tm.initCfg (enc a)) ht hhalt).trans hrun
  have hg_len (a : α) : (g a).length ≤ t₁ a := (htm a).length_output_le
  let M_pad : MultiTapePTM k₀ Bool State₀ := MultiTapePTM.ofDeterministic tm
  have hfirst (a : α) :
      ∀ final ∈ (ProbComp.eval
        (M_pad.runClosedConfigFrom (t₁ a) (M_pad.initialConfig (enc a)))).support,
        final.tapes.state = none := by
    intro final hfinal
    rw [MultiTapePTM.eval_runClosedConfigFrom_ofDeterministic, PMF.mem_support_pure_iff] at hfinal
    subst hfinal
    change (tm.runFrom (tm.initCfg (enc a)) (t₁ a)).state = none
    rw [htm_run a]
    rfl
  have hout₁ (a : α) :
      ProbComp.eval (M_pad.runClosed (t₁ a) (enc a)) = PMF.pure (g a) := by
    rw [MultiTapePTM.eval_runClosed_ofDeterministic, htm_run a]
    rfl
  -- Unpack `B ∈ NP encBits` into a halting fair-coin machine `M_NP`
  obtain ⟨p, V, hV, hVer⟩ := hB
  let program (x : List Bool) : ProbComp Bool :=
    (fun w => V (x, w)) <$> BitString.sampleList (p.eval x.length)
  have hcount : ComputableTidilyInPolyTime (fun x : List Bool => p.eval x.length)
      encBits encUnary :=
    (unary_eval p).comp (encoding_length encBits)
  have hprogram : IsPPTOn encBits encBool program := hcount.sampleList.map_with hV
  obtain ⟨k₁, State₁, hfinite₁, M_NP, c₁, d₁, heval₂, hhalt₂⟩ := hprogram.exists_halting_machine
  set t₂ : α → ℕ := fun a => c₁ * (t₁ a + 1) ^ d₁
  have ht₂_le (a : α) : c₁ * ((g a).length + 1) ^ d₁ ≤ t₂ a :=
    Nat.mul_le_mul_left c₁ (Nat.pow_le_pow_left (Nat.add_le_add_right (hg_len a) 1) d₁)
  have hsecond (a : α) :
      ∀ word ∈ (ProbComp.eval (M_pad.runClosed (t₁ a) (enc a))).support,
        ∀ final ∈ (ProbComp.eval
          (M_NP.runClosedConfigFrom (t₂ a) (M_NP.initialConfig word))).support,
          final.tapes.state = none := by
    intro word hword final hfinal
    rw [hout₁ a, PMF.mem_support_pure_iff] at hword
    subst hword
    rw [M_NP.eval_runClosedConfigFrom_eq_of_halted _ (ht₂_le a) (hhalt₂ (g a))] at hfinal
    exact hhalt₂ (g a) final hfinal
  let M_comp := M_NP.comp M_pad false
  set totalTime : α → ℕ := fun a => t₁ a + (t₁ a + 4 + t₂ a)
  have hdecides : M_comp.toNTM.DecidesInTime enc (g ⁻¹' B) totalTime := by
    intro a
    have htime : M_comp.toNTM.RunsInTime (enc a) (totalTime a) :=
      M_comp.runsInTime_toNTM (M_pad.comp_halted M_NP false (enc a) (t₁ a) (t₂ a)
        (hfirst a) (hsecond a))
    refine ⟨htime, ?_⟩
    rw [Set.mem_preimage, hVer (g a), MultiTapeNTM.accepts_iff_exists_time_eq htime,
      M_comp.exists_computationPath_toNTM_iff (P := fun cfg => cfg.output = [true])]
    have hcomp_eval :
        ProbComp.eval (M_comp.runClosed (totalTime a) (enc a)) =
          ProbComp.eval (M_NP.runClosed (c₁ * ((g a).length + 1) ^ d₁) (g a)) := by
      rw [M_pad.eval_comp M_NP false (enc a) (t₁ a) (t₂ a) (hfirst a) (hsecond a),
        hout₁ a, PMF.pure_bind,
        M_NP.eval_runClosed_eq_of_halted (g a) (ht₂_le a) (hhalt₂ (g a))]
    have hsupport := congrArg (fun μ => [true] ∈ μ.support)
      ((heval₂ (g a)).trans hcomp_eval.symm)
    simp only [MultiTapePTM.runClosed_eq_map, ProbComp.eval_map, PMF.mem_support_map_iff,
      program, BitString.eval_sampleList, BitString.mem_support_uniformList_iff, encBool_apply,
      List.cons.injEq, and_true] at hsupport
    rw [← hsupport]
    exact ⟨fun ⟨w, hw, hV⟩ => ⟨true, ⟨w, hw, hV⟩, rfl⟩,
      fun ⟨_, ⟨w, hw, hV⟩, rfl⟩ => ⟨w, hw, hV⟩⟩
  refine ⟨d₁ + 1, (2 * c₀ + 4 + c₁ * (c₀ + 1) ^ d₁), 0, k₁ + k₀ + 2, _, inferInstance,
    M_comp.toNTM, hdecides.mono fun a => ?_⟩
  set X := T₀ (enc a).length + 1
  have hX : 1 ≤ X := Nat.succ_pos _
  have ht₁_bound : t₁ a + 1 ≤ (c₀ + 1) * X := by simp only [t₁, X]; nlinarith
  have ht₂_bound : t₂ a ≤ c₁ * (c₀ + 1) ^ d₁ * X ^ (d₁ + 1) := by
    calc t₂ a = c₁ * (t₁ a + 1) ^ d₁ := rfl
      _ ≤ c₁ * ((c₀ + 1) * X) ^ d₁ := Nat.mul_le_mul_left c₁ (Nat.pow_le_pow_left ht₁_bound d₁)
      _ = c₁ * (c₀ + 1) ^ d₁ * X ^ d₁ := by rw [Nat.mul_pow, Nat.mul_assoc]
      _ ≤ c₁ * (c₀ + 1) ^ d₁ * X ^ (d₁ + 1) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX (Nat.le_succ d₁))
  have hX_pow : X ≤ X ^ (d₁ + 1) := Nat.le_self_pow (by lia) X
  calc totalTime a
      = 2 * c₀ * X + 4 + t₂ a := by simp only [totalTime, t₁, X]; ring
    _ ≤ 2 * c₀ * X ^ (d₁ + 1) + 4 * X ^ (d₁ + 1) + c₁ * (c₀ + 1) ^ d₁ * X ^ (d₁ + 1) := by
        have : 4 ≤ 4 * X ^ (d₁ + 1) := Nat.le_mul_of_pos_right 4 (Nat.pow_pos hX)
        nlinarith
    _ = (2 * c₀ + 4 + c₁ * (c₀ + 1) ^ d₁) * X ^ (d₁ + 1) + 0 := by ring

/-- Pulling back `B ∈ NP encBits` along the exponential-padding map
`a ↦ frame (enc a) ++ List.replicate (2 ^ f (enc a).length) true`, where `f` is polynomial-time in
unary with `n ≤ f n`, gives a problem in `NEXP enc`. -/
theorem preimage_pad_mem_NEXP {B : Set (List Bool)} (hB : B ∈ NP encBits) {f : ℕ → ℕ}
    (hf : ComputableTidilyInPolyTime f encUnary encUnary) (hn : ∀ n, n ≤ f n) :
    (fun a : α => frame (enc a) ++ List.replicate (2 ^ f (enc a).length) true) ⁻¹' B ∈
      NEXP enc := by
  obtain ⟨d₀, e₀, hd₀⟩ := hf.exists_degree
  have hpad := ComputableTidilyInO.unary_two_pow.comp (hd₀.inO.comp ComputableTidilyInO.lengthUnary)
  have hpad' : ComputableTidilyInO (fun x : List Bool => 2 ^ f x.length) encBits encUnary
      (fun x => x.length + (x.length + 1) ^ d₀ + (f x.length + 1) * 2 ^ f x.length)
      (fun x => x.length + (x.length + 1) ^ d₀ + 2 ^ f x.length) :=
    hpad.mono_le (fun x => by simp [encUnary_apply]) fun x => by simp [encUnary_apply]
  let g (a : α) : List Bool := frame (enc a) ++ List.replicate (2 ^ f (enc a).length) true
  let T₀ (n : ℕ) : ℕ := n + (n + (n + 1) ^ d₀ + (f n + 1) * 2 ^ f n)
  have hg : ComputableTidilyInO g enc encBits (fun a => T₀ (enc a).length)
      (fun a => (enc a).length + ((enc a).length + ((enc a).length + 1) ^ d₀ +
        2 ^ f (enc a).length)) :=
    (ComputableTidilyInO.of_linear (.of_frame (f := id) (encOut := encFramed enc)
      fun _ => rfl)).append (hpad'.comp_enc enc) fun _ => rfl
  obtain ⟨D, hD⟩ := preimage_mem_NTIME_of_mem_NP hB hg
  obtain ⟨C₀, hC₀⟩ := (PolynomiallyBounded.of_forall_le 1 d₀ fun n => by
    simp only [one_mul]; exact le_rfl).exists_le_mul_two_pow (p := fun n => (n + 1) ^ d₀)
  obtain ⟨c_f, d_f, hf_le⟩ := hf.polyBounded_length.exists_le
  simp only [encUnary_apply, List.length_replicate] at hf_le
  have hNTIME : g ⁻¹' B ∈ NTIME enc fun n => 2 ^ (2 * D * f n) := by
    obtain ⟨c₁, c₂, k, State, hfinite, ntm, hdec⟩ := hD
    refine ⟨c₁ * (C₀ + 3) ^ D, c₂, k, State, hfinite, ntm, hdec.mono fun a => ?_⟩
    set n := (enc a).length
    have h₁ : 2 ^ n ≤ 2 ^ f n := Nat.pow_le_pow_right (by norm_num) (hn n)
    have h₂ : 2 * n + 1 ≤ 2 * 2 ^ n := by have := @Nat.lt_two_pow_self n; lia
    have h₃ : f n + 1 ≤ 2 ^ f n := Nat.lt_two_pow_self
    have h₄ : 2 ^ f n ≤ 2 ^ (2 * f n) := Nat.pow_le_pow_right (by norm_num) (by lia)
    have h₅ : (f n + 1) * 2 ^ f n ≤ 2 ^ (2 * f n) := by
      rw [two_mul, pow_add]
      exact Nat.mul_le_mul_right _ h₃
    have hle : T₀ n + 1 ≤ (C₀ + 3) * 2 ^ (2 * f n) := by
      have := hC₀ n
      have : C₀ * 2 ^ n ≤ C₀ * 2 ^ (2 * f n) := Nat.mul_le_mul_left _ (h₁.trans h₄)
      simp only [T₀]
      nlinarith
    have hpow : (T₀ n + 1) ^ D ≤ (C₀ + 3) ^ D * 2 ^ (2 * D * f n) := by
      calc (T₀ n + 1) ^ D
          ≤ ((C₀ + 3) * 2 ^ (2 * f n)) ^ D := Nat.pow_le_pow_left hle D
        _ = (C₀ + 3) ^ D * 2 ^ (2 * D * f n) := by rw [Nat.mul_pow, ← Nat.pow_mul]; ring_nf
    calc c₁ * (T₀ n + 1) ^ D + c₂
        ≤ c₁ * ((C₀ + 3) ^ D * 2 ^ (2 * D * f n)) + c₂ :=
          Nat.add_le_add_right (Nat.mul_le_mul_left c₁ hpow) c₂
      _ = c₁ * (C₀ + 3) ^ D * 2 ^ (2 * D * f n) + c₂ := by ring
  refine mem_NEXP_iff.mpr ⟨d_f + 1, NTIME_mono_of_eventually_le (Filter.eventually_atTop.mpr
    ⟨2 * D * c_f * 2 ^ d_f + 2, fun n hn' => Nat.pow_le_pow_right (by norm_num) ?_⟩) hNTIME⟩
  have hn1 : n + 1 ≤ 2 * n := by lia
  have hpow_n1 : (n + 1) ^ d_f ≤ 2 ^ d_f * n ^ d_f := by
    calc (n + 1) ^ d_f ≤ (2 * n) ^ d_f := Nat.pow_le_pow_left hn1 d_f
      _ = 2 ^ d_f * n ^ d_f := Nat.mul_pow 2 n d_f
  have hfn : f n ≤ c_f * (2 ^ d_f * n ^ d_f) :=
    (hf_le n).trans (Nat.mul_le_mul_left c_f hpow_n1)
  calc 2 * D * f n
      ≤ 2 * D * (c_f * (2 ^ d_f * n ^ d_f)) := Nat.mul_le_mul_left (2 * D) hfn
    _ = (2 * D * c_f * 2 ^ d_f) * n ^ d_f := by ring
    _ ≤ n * n ^ d_f := Nat.mul_le_mul_right (n ^ d_f) (by lia)
    _ = n ^ (d_f + 1) := (pow_succ' n d_f).symm

end Translation

/-! ### The unconditional upper bounds `MIP ⊆ NEXP` and `MIP₂ ⊆ NEXP` -/

private theorem natCast_div_le_natCast_div_iff {a b c d : ℕ} (hb : b ≠ 0) (hd : d ≠ 0) :
    (a : ℝ≥0∞) / b ≤ c / d ↔ a * d ≤ b * c := by
  rw [ENNReal.div_le_iff_le_mul (Or.inl (by exact_mod_cast hb)) (Or.inl (ENNReal.natCast_ne_top _)),
    ← ENNReal.mul_div_right_comm, ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hd))
      (Or.inl (ENNReal.natCast_ne_top _))]
  rw [mul_comm (c : ℝ≥0∞)]
  exact_mod_cast Iff.rfl

variable {α : Type} (enc : α ↪ List Bool)

/-- **`MIP ⊆ NEXP`** [Babai, Fortnow and Lund][BabaiFortnowLund1991],
[Arora and Barak, Section 8.10][AroraBarak09]: every problem with a multiprover interactive proof
is decidable in nondeterministic exponential time. -/
theorem MIP_subset_NEXP : MIP enc ⊆ NEXP enc := by
  rintro A ⟨p, verifier, hV, hproto⟩
  obtain ⟨_, k, Control, hfinControl, M, c, d, hreal⟩ := hV
  let f (n : ℕ) : ℕ := 32 * (p + n + c * (n + 1) ^ d + 1) ^ 2 + c * (n + 1) ^ d
  have hf : ComputableTidilyInPolyTime f encUnary encUnary := by
    have hpoly : ComputableTidilyInPolyTime (fun n : ℕ => c * (n + 1) ^ d) encUnary encUnary :=
      (unary_eval (Polynomial.C c * (Polynomial.X + 1) ^ d)).of_enc_eq fun n => by simp
    have hB : ComputableTidilyInPolyTime (fun n : ℕ => p + n + c * (n + 1) ^ d + 1)
        encUnary encUnary := by
      have hp_n := unary_add.comp ((const p).prod id')
      have hp_n_t := unary_add.comp (hp_n.prod hpoly)
      exact unary_add.comp (hp_n_t.prod (const 1))
    have hsq : ComputableTidilyInPolyTime
        (fun n : ℕ => 32 * (p + n + c * (n + 1) ^ d + 1) ^ 2) encUnary encUnary :=
      unary_mul.comp ((const 32).prod ((unary_pow 2).comp hB))
    exact unary_add.comp (hsq.prod hpoly)
  have hn : ∀ n, n ≤ f n := fun n => by
    have hB : n ≤ p + n + c * (n + 1) ^ d + 1 := by lia
    have hsq : p + n + c * (n + 1) ^ d + 1 ≤ (p + n + c * (n + 1) ^ d + 1) ^ 2 :=
      Nat.le_self_pow (by norm_num) _
    simp only [f]
    lia
  let g (a : α) : List Bool := frame (enc a) ++ List.replicate (2 ^ f (enc a).length) true
  have hNP : MIP.paddedMIP M c d ∈ NP encBits := MIP.paddedMIP_mem_NP M c d
  have hpre : A = g ⁻¹' MIP.paddedMIP M c d := by
    ext a
    simp only [Set.mem_preimage, MIP.paddedMIP, Set.mem_ofPred_eq, MIP.checkPaddedCert,
      Bool.and_eq_true, decide_eq_true_eq]
    have hunf : unframe (g a) = enc a := by simp [g, unframe_frame_append]
    rw [hunf]
    set x := enc a
    set t := c * (x.length + 1) ^ d
    have hpos : 2 ^ t ≠ 0 := by positivity
    have hcast : ((2 ^ t : ℕ) : ℝ≥0∞) = 2 ^ t := by push_cast; rfl
    constructor
    · intro ha
      obtain ⟨P, hP⟩ := hproto.complete a ha
      have haccP := MIP.acceptProb_eq_sum M (hreal a) (Prover.independent P)
      have hopt := MIP.exists_deterministic_prover_family
        (fun r : Fin t → Bool => MIP.coinProgram M t x (List.ofFn r))
        (fun r => by
          simpa only [MIP.coinFamily] using MIP.isBoundedComp_coinFamily M t x r)
        (fun _ => 1) P
      simp only [one_mul] at hopt
      obtain ⟨D, hD⟩ := hopt
      let traceOf (r : List Bool) : MIP.TaggedHistory :=
        MIP.canonicalTrace M t D (MultiTapeMachine.FiniteConfig.init M.initial x)
          (fun i => (D i).init) r
      let goodCard : ℕ :=
        ((Finset.univ : Finset (Fin t → Bool)).filter fun r =>
          MIP.accepts M x (List.ofFn r) (traceOf (List.ofFn r))).card
      have hsumD :
          (∑ r : Fin t → Bool,
            MIP.queryAcceptProb (Prover.independent fun i => (D i).toProver)
              (Prover.independent fun i => (D i).toProver).init
              (MIP.coinProgram M t x (List.ofFn r))) =
            (goodCard : ℝ≥0∞) := by
        have hterm (r : Fin t → Bool) :
            MIP.queryAcceptProb (Prover.independent fun i => (D i).toProver)
              (Prover.independent fun i => (D i).toProver).init
              (MIP.coinProgram M t x (List.ofFn r)) =
              if MIP.accepts M x (List.ofFn r) (traceOf (List.ofFn r)) then 1 else 0 :=
          MIP.queryAcceptProb_eq_ite_accepts_canonicalTrace M List.length_ofFn D
        simp only [hterm, goodCard, Finset.sum_boole]
      have hineq : (2 / 3 : ℝ≥0∞) ≤ (goodCard : ℝ≥0∞) / (2 ^ t : ℕ) := by
        calc (2 / 3 : ℝ≥0∞)
            ≤ acceptProb (verifier a) (Prover.independent P) := hP
          _ = (2 ^ t : ℝ≥0∞)⁻¹ * ∑ r : Fin t → Bool,
                MIP.queryAcceptProb (Prover.independent P) (Prover.independent P).init
                  (MIP.coinProgram M t x (List.ofFn r)) := by
                simpa only [MIP.coinFamily] using haccP
          _ ≤ (2 ^ t : ℝ≥0∞)⁻¹ * ∑ r : Fin t → Bool,
                MIP.queryAcceptProb (Prover.independent fun i => (D i).toProver)
                  (Prover.independent fun i => (D i).toProver).init
                  (MIP.coinProgram M t x (List.ofFn r)) :=
                mul_le_mul_right hD _
          _ = (goodCard : ℝ≥0∞) / (2 ^ t : ℕ) := by
                rw [hsumD, ENNReal.div_eq_inv_mul, hcast]
      rw [show (2 / 3 : ℝ≥0∞) = ((2 : ℕ) : ℝ≥0∞) / ((3 : ℕ) : ℝ≥0∞) by norm_num,
        natCast_div_le_natCast_div_iff (by norm_num) hpos] at hineq
      have hpow_pos := Nat.one_le_two_pow (n := t)
      have hlt_card : 2 ^ t < 2 * goodCard := by lia
      obtain ⟨cert, hcheck, hlen⟩ := MIP.exists_checkCert_of_detProver M x D hlt_card
      refine ⟨cert, ?_, hcheck⟩
      set m := 32 * (p + x.length + t + 1) ^ 2
      have hm_pow : m ≤ 2 ^ m := (Nat.lt_two_pow_self (n := m)).le
      have hcert_pow : (MIP.encCert cert).length ≤ 2 ^ f x.length := by
        calc (MIP.encCert cert).length
            ≤ m * 2 ^ t := hlen
          _ ≤ 2 ^ m * 2 ^ t := Nat.mul_le_mul_right (2 ^ t) hm_pow
          _ = 2 ^ (m + t) := (Nat.pow_add 2 m t).symm
          _ = 2 ^ f x.length := rfl
      have hg_len : 2 ^ f x.length ≤ (g a).length := by
        simp [g, x]
      exact hcert_pow.trans hg_len
    · rintro ⟨cert, -, hcheck⟩
      obtain ⟨D, hsum_le, hlt⟩ := MIP.exists_detProver_of_checkCert M hcheck
      by_contra ha
      have hsound := hproto.sound a ha (fun i => (D i).toProver)
      have haccD := MIP.acceptProb_eq_sum M (hreal a)
        (Prover.independent fun i => (D i).toProver)
      have hineq : (cert.length : ℝ≥0∞) / (2 ^ t : ℕ) ≤ (1 / 3 : ℝ≥0∞) := by
        calc (cert.length : ℝ≥0∞) / (2 ^ t : ℕ)
            = (2 ^ t : ℝ≥0∞)⁻¹ * (cert.length : ℝ≥0∞) := by
                rw [ENNReal.div_eq_inv_mul, hcast]
          _ ≤ (2 ^ t : ℝ≥0∞)⁻¹ * ∑ r : Fin t → Bool,
                MIP.queryAcceptProb (Prover.independent fun i => (D i).toProver)
                  (Prover.independent fun i => (D i).toProver).init
                  (MIP.coinProgram M t x (List.ofFn r)) :=
                mul_le_mul_right hsum_le _
          _ = acceptProb (verifier a) (Prover.independent fun i => (D i).toProver) := by
                simpa only [MIP.coinFamily] using haccD.symm
          _ ≤ 1 / 3 := hsound
      rw [show (1 / 3 : ℝ≥0∞) = ((1 : ℕ) : ℝ≥0∞) / ((3 : ℕ) : ℝ≥0∞) by norm_num,
        natCast_div_le_natCast_div_iff hpos (by norm_num)] at hineq
      lia
  rw [hpre]
  exact preimage_pad_mem_NEXP hNP hf hn

/-- **`MIP₂ ⊆ NEXP`**: every problem with a two-prover interactive proof is decidable in
nondeterministic exponential time. -/
theorem MIP₂_subset_NEXP : MIP₂ enc ⊆ NEXP enc :=
  (MIP₂_subset_MIP enc).trans (MIP_subset_NEXP enc)

end Cslib.Complexity
