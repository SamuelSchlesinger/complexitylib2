/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.IP.CoinFixing
public import Complexity.Computability.Complexity.Classes.Oracle.Deterministic
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Configuration
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Configuration
import Complexity.Computability.Complexity.Classes.SharpP.Space
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure
import Mathlib.Data.Nat.Size

/-!
# Counting the accepting coins in polynomial space

This file computes, for a verifier machine, the number of coin values whose programs accept after
a history (`Cslib.Complexity.Interaction.accepted`), within space polynomial in the input and the
history, and in exponential time.

* A replay keeping only whether it is still live
  (`Cslib.Complexity.Interaction.aliveStep`) decides whether the program of given coins accepts
  after a history (`Cslib.Complexity.Interaction.accepts_eq_true_iff`), in polynomial time
  (`Cslib.Complexity.Interaction.computableTidilyInPolyTime_accepts`): it folds one instruction per
  coin over the configuration of the machine, whose storage grows by a bounded amount per
  instruction.
* The coin values are enumerated by the binary counter `Cslib.BitString.increment`, and the
  accepting ones are counted with a binary accumulator (`Cslib.Complexity.Interaction.countAccepts`,
  `Cslib.Complexity.Interaction.countAccepts_eq_accepted`), within polynomial space
  (`Turing.MultiTapeTM.ComputableTidilyInPolySpace`,
  `Cslib.Complexity.Interaction.computableTidilyInPolySpace_countAccepts`).

## Main definitions

* `Cslib.Complexity.Interaction.accepts`: whether the program of given coins accepts.
* `Cslib.Complexity.Interaction.countAccepts`: the number of accepting coin values.

## Main results

* `Cslib.Complexity.Interaction.computableTidilyInPolyTime_accepts`: acceptance in polynomial time.
* `Cslib.Complexity.Interaction.countAccepts_eq_accepted`: the count of accepting coin values.
* `Cslib.Complexity.Interaction.computableTidilyInPolySpace_countAccepts`: the count in polynomial
  space.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

namespace Interaction

open Cslib.BitString (increment lsbValue)

/-! ### A live replay -/

/-- Histories, encoded as lists of pairs of words. -/
abbrev encHistory : History ↪ List Bool := encList (encPair encBits encBits)

/-- A suffix of a list has a shorter encoding. -/
theorem length_encList_le_of_suffix {α : Type} {enc : α ↪ List Bool} {l l' : List α}
    (h : l <:+ l') : (encList enc l).length ≤ (encList enc l').length := by
  obtain ⟨p, rfl⟩ := h
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [List.cons_append, encList_cons, List.length_append]
    lia

variable {k : ℕ} {Control : Type} (M : MultiTapePTM k Bool Control Unit)

variable (k Control) in
/-- The state of a replay that only records whether it is still live: the configuration, the rest
of the history and liveness. -/
abbrev AliveState := MultiTapeMachine.FiniteConfig k Bool Control Unit × History × Bool

/-- One instruction of a live replay: `replayStep`, where a failure only stops the replay. -/
def aliveStep (t : ℕ) (s : AliveState k Control) (b : Bool) : AliveState k Control :=
  if s.2.2 then
    match replayStep M t (s.1, s.2.1) b with
    | .ok p => (p.1, p.2, true)
    | .error _ => (s.1, s.2.1, false)
  else s

/-- The live replay of `M` on the input `x` with the coins `r` against the history `h`, its replies
truncated to the number of coins. -/
def aliveRun (x r : List Bool) (h : History) : AliveState k Control :=
  r.foldl (aliveStep M r.length) (MultiTapeMachine.FiniteConfig.init M.initial x, h, true)

/-- Whether the program of the coins `r` accepts after the history `h`: the replay is live, has
consumed the whole history and has output `[true]`. -/
def accepts (x r : List Bool) (h : History) : Bool :=
  (aliveRun M x r h).2.2 && (aliveRun M x r h).2.1.isEmpty &&
    decide ((aliveRun M x r h).1.tapes.output = [true])

/-- The live replay follows the replay while it succeeds, and dies when it fails. -/
private theorem foldl_aliveStep (t : ℕ) (l : List Bool)
    (acc : Except (Option (List Bool))
      (MultiTapeMachine.FiniteConfig k Bool Control Unit × History))
    (s : AliveState k Control)
    (hs : (∀ p, acc = .ok p → s = (p.1, p.2, true)) ∧
      (∀ e, acc = .error e → s.2.2 = false)) :
    (∀ p, l.foldl (fun acc b => acc.bind fun p => replayStep M t p b) acc = .ok p →
        l.foldl (aliveStep M t) s = (p.1, p.2, true)) ∧
      (∀ e, l.foldl (fun acc b => acc.bind fun p => replayStep M t p b) acc = .error e →
        (l.foldl (aliveStep M t) s).2.2 = false) := by
  induction l generalizing acc s with
  | nil => exact hs
  | cons b l ih =>
    refine ih _ _ ⟨fun p hp => ?_, fun e he => ?_⟩
    · rcases acc with e | q
      · cases hp
      · rw [hs.1 q rfl]
        change replayStep M t q b = .ok p at hp
        simp only [aliveStep, ite_true, hp]
    · rcases acc with e' | q
      · have := hs.2 e' rfl
        simp [aliveStep, this]
      · rw [hs.1 q rfl]
        change replayStep M t q b = .error e at he
        simp only [aliveStep, ite_true, he]

/-- **The live replay decides acceptance**: `accepts` holds exactly when the program of the coins
accepts after the history. -/
theorem accepts_eq_true_iff (x r : List Bool) (h : History) :
    accepts M x r h = true ↔ outcome (coinProgram M r.length x r) h = .done true := by
  have hrun := foldl_aliveStep M r.length r
    (.ok (MultiTapeMachine.FiniteConfig.init M.initial x, h))
    (MultiTapeMachine.FiniteConfig.init M.initial x, h, true)
    ⟨fun p hp => by simp only [Except.ok.injEq] at hp; subst hp; rfl, fun e he => by cases he⟩
  rw [outcome_coinProgram]
  unfold accepts aliveRun
  rcases hsim : simulate M r.length x r h with e | ⟨cfg, rest⟩
  · have hdead := hrun.2 e hsim
    simp only [hdead, Bool.false_and, Bool.false_eq_true, false_iff]
    rcases e with _ | m <;> simp [Except.map, replayOutcome]
  · rw [hrun.1 _ hsim]
    cases rest <;> simp [Except.map, replayOutcome]

/-- `accepts_eq_true_iff` for any number of coins equal to the length of the coins. -/
theorem accepts_eq_true_iff_of_length {x r : List Bool} {t : ℕ} (hr : r.length = t)
    (h : History) : accepts M x r h = true ↔ outcome (coinProgram M t x r) h = .done true := by
  subst hr
  exact accepts_eq_true_iff M x r h

/-! ### The live replay in polynomial time -/

section PolyTime

open ComputableTidilyInPolyTime

/-- The instruction of `M` in the configuration `cfg` with the coin `b`, unless it has halted. -/
def instruction (cfg : MultiTapeMachine.FiniteConfig k Bool Control Unit) (b : Bool) :
    Option (MultiTapeMachine.Action k Bool Control Unit) :=
  cfg.tapes.state.map fun c =>
    M.tr c cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols b

/-- Answer a request on the channel `op` from the history, moving to the control state `next`, or
stop when the history is exhausted or sends another message. -/
def answerFromHistory (t : ℕ) (op : Unit) (next : Control) (s : AliveState k Control) :
    AliveState k Control :=
  if s.2.1.isEmpty then (s.1, s.2.1, false)
  else if (s.2.1.headD ([], [])).1 = (s.1.channels op).1 then
    (s.1.receive op next ((s.2.1.headD ([], [])).2.take t), s.2.1.tail, true)
  else (s.1, s.2.1, false)

/-- The live replay step by its liveness and instruction. -/
def taggedStep (t : ℕ) :
    Bool × Option (MultiTapeMachine.Action k Bool Control Unit) → AliveState k Control →
      AliveState k Control
  | (false, _), s => s
  | (true, none), s => s
  | (true, some (.step action symbol move)), s => (s.1.step action symbol move, s.2.1, true)
  | (true, some (.query op next)), s => answerFromHistory t op next s

/-- The live replay step as a case distinction on a finite tag. -/
theorem aliveStep_eq (t : ℕ) (s : AliveState k Control) (b : Bool) :
    aliveStep M t s b = taggedStep t (s.2.2, instruction M s.1 b) s := by
  obtain ⟨cfg, rest, _ | _⟩ := s
  · rfl
  · simp only [aliveStep, ite_true, replayStep, instruction]
    cases cfg.tapes.state with
    | none => rfl
    | some c =>
      simp only [Option.map_some]
      cases M.tr c cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols b with
      | step => rfl
      | query op next =>
        simp only [taggedStep, answerFromHistory]
        cases rest with
        | nil => rfl
        | cons e rest =>
          obtain ⟨m, y⟩ := e
          simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false, List.headD_cons,
            List.tail_cons]
          split_ifs with hm <;> simp [hm]

variable [Finite Control]

/-- Live replay states, encoded by their fields. -/
noncomputable abbrev encAliveState : AliveState k Control ↪ List Bool :=
  encPair encFiniteConfig (encPair encHistory encBool)

/-- The instruction is polynomial-time: it reads finitely many observations. -/
theorem computableTidilyInPolyTime_instruction :
    ComputableTidilyInPolyTime (fun p : MultiTapeMachine.FiniteConfig k Bool Control Unit × Bool =>
      instruction M p.1 p.2) (encPair encFiniteConfig encBool)
      (encFinite (Option (MultiTapeMachine.Action k Bool Control Unit))) := by
  have hobs : ComputableTidilyInPolyTime
      (fun p : MultiTapeMachine.FiniteConfig k Bool Control Unit × Bool =>
        (p.1.tapes.state, p.1.tapes.inputSymbol, p.1.tapes.workTapeSymbols, p.1.answerSymbols, p.2))
      (encPair encFiniteConfig encBool)
      (encPair (encFinite (Option Control)) (encPair (encFinite (Option Bool))
        (encPair (encFinite (Fin k → Option Bool)) (encPair (encFinite (Unit → Option Bool))
          encBool)))) := by
    fun_prop
  exact ((of_finite fun obs : Option Control × Option Bool × (Fin k → Option Bool) ×
      (Unit → Option Bool) × Bool => obs.1.map fun c =>
        M.tr c obs.2.1 obs.2.2.1 obs.2.2.2.1 obs.2.2.2.2).comp hobs).of_enc_eq fun _ => rfl

/-- Answering from the history is polynomial-time. -/
theorem computableTidilyInPolyTime_answerFromHistory (op : Unit) (next : Control) :
    ComputableTidilyInPolyTime (fun p : (ℕ × AliveState k Control) × Bool =>
      answerFromHistory p.1.1 op next p.1.2) (encPair (encPair encUnary encAliveState) encBool)
      encAliveState := by
  unfold answerFromHistory
  fun_prop

/-- **A step of the live replay is polynomial-time.** -/
theorem computableTidilyInPolyTime_aliveStep :
    ComputableTidilyInPolyTime (fun p : (ℕ × AliveState k Control) × Bool =>
      aliveStep M p.1.1 p.1.2 p.2) (encPair (encPair encUnary encAliveState) encBool)
      encAliveState := by
  simp only [aliveStep_eq]
  refine finite_cases (tag := fun p : (ℕ × AliveState k Control) × Bool =>
      (p.1.2.2.2, instruction M p.1.2.1 p.2))
    (branch := fun tag p => taggedStep p.1.1 tag p.1.2)
    (tagEncoding := encPair encBool (encFinite (Option (MultiTapeMachine.Action k Bool Control
      Unit)))) ?_ ?_
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
/-- A step of the live replay grows the storage by a bounded amount and consumes the history. -/
theorem aliveStep_spaceBound {n i t : ℕ} {h : History} {s : AliveState k Control}
    (hs : MultiTapeMachine.FiniteConfig.SpaceBound n i t s.1 ∧ s.2.1 <:+ h) (b : Bool) :
    MultiTapeMachine.FiniteConfig.SpaceBound n (i + 1) t (aliveStep M t s b).1 ∧
      (aliveStep M t s b).2.1 <:+ h := by
  obtain ⟨cfg, rest, _ | _⟩ := s
  · exact ⟨hs.1.mono le_rfl (by lia) le_rfl, hs.2⟩
  · obtain ⟨hspace, hsuffix⟩ := hs
    simp only [aliveStep, ite_true, replayStep]
    cases cfg.tapes.state with
    | none => exact ⟨hspace.mono le_rfl (by lia) le_rfl, hsuffix⟩
    | some c =>
      simp only
      cases M.tr c cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols b with
      | step action symbol move => exact ⟨hspace.step action symbol move, hsuffix⟩
      | query op next =>
        simp only
        cases rest with
        | nil => exact ⟨hspace.mono le_rfl (by lia) le_rfl, hsuffix⟩
        | cons e rest =>
          obtain ⟨m, y⟩ := e
          simp only
          split_ifs
          · exact ⟨hspace.receive op next _ (List.length_take_le _ _),
              (List.suffix_cons _ _).trans hsuffix⟩
          · exact ⟨hspace.mono le_rfl (by lia) le_rfl, hsuffix⟩

/-- **The live replay is polynomial-time** in the input, the coins and the history. -/
theorem computableTidilyInPolyTime_aliveRun :
    ComputableTidilyInPolyTime (fun p : List Bool × List Bool × History =>
      aliveRun M p.1 p.2.1 p.2.2) (encPair encBits (encPair encBits encHistory))
      encAliveState := by
  obtain ⟨cf, hcf⟩ := length_encFiniteConfig_le (k := k) (State := Control) (Oracle := Unit)
  unfold aliveRun
  refine (foldlWith_spec (par := fun p : List Bool × List Bool × History => p.2.1.length)
    (list := fun p => p.2.1)
    (init := fun p => (MultiTapeMachine.FiniteConfig.init M.initial p.1, p.2.2, true))
    (step := aliveStep M) (encP := encUnary) (encA := encBool) (encL := encBits)
    (by fun_prop) (by fun_prop) (by fun_prop) (computableTidilyInPolyTime_aliveStep M)
    (fun p consumed s => MultiTapeMachine.FiniteConfig.SpaceBound p.1.length consumed.length
      p.2.1.length s.1 ∧ s.2.1 <:+ p.2.2)
    (fun p => ⟨MultiTapeMachine.FiniteConfig.spaceBound_init _ _ _, List.suffix_refl _⟩)
    (fun p consumed s b _ hs => by simpa using aliveStep_spaceBound M hs b)
    (size := fun p => 2 * cf * (3 * (encPair encBits (encPair encBits encHistory) p).length + 1) +
      2 * (encPair encBits (encPair encBits encHistory) p).length + 3)
    (PolyBounded.of_forall_le (2 * cf * 3 + 2 * cf + 2 + 3) 1 fun p => by
      simp only [pow_one]
      nlinarith)
    (fun p consumed s hprefix hs => ?_)).1
  have hcfg := hcf _ _ _ _ hs.1
  have hhist := length_encList_le_of_suffix (enc := encPair encBits encBits) hs.2
  have hcons : consumed.length ≤ p.2.1.length := hprefix.length_le
  simp only [encAliveState, length_encPair, encBool_apply, List.length_singleton, encBits_apply]
    at hcfg hhist ⊢
  have hcfg' := hcfg.trans (Nat.mul_le_mul_left cf (show p.1.length + consumed.length +
    p.2.1.length + 1 ≤ 3 * (2 * p.1.length + 1 + (2 * p.2.1.length + 1 +
      (encList (encPair encBits encBits) p.2.2).length)) + 1 by lia))
  nlinarith

/-- **Acceptance is polynomial-time** in the input, the coins and the history. -/
theorem computableTidilyInPolyTime_accepts :
    ComputableTidilyInPolyTime (fun p : List Bool × List Bool × History =>
      accepts M p.1 p.2.1 p.2.2) (encPair encBits (encPair encBits encHistory)) encBool := by
  have h := computableTidilyInPolyTime_aliveRun M
  unfold accepts
  fun_prop

end PolyTime

/-! ### Counting the accepting coins -/

section Count

variable {α : Type} (enc : α ↪ List Bool) (fuel : α → ℕ)

/-- One round of the count: test the coins, add the verdict, and move on to the next coins. -/
def countStep (s : (α × History) × List Bool × ℕ) : (α × History) × List Bool × ℕ :=
  (s.1, increment s.2.1, s.2.2 + if accepts M (enc s.1.1) s.2.1 s.1.2 then 1 else 0)

/-- The number of accepting values of `fuel a` coins after the history `h`, counted by trying the
coins one after another with a binary counter. -/
def countAccepts (q : α × History) : ℕ :=
  ((countStep M enc)^[2 ^ fuel q.1] (q, List.replicate (fuel q.1) false, 0)).2.2

open Classical in
/-- After `j` rounds the count has tried the first `j` values of the counter. -/
theorem iterate_countStep (q : α × History) (m j : ℕ) :
    (countStep M enc)^[j] (q, List.replicate m false, 0) =
      (q, increment^[j] (List.replicate m false),
        ((Finset.range j).filter fun i =>
          accepts M (enc q.1) (increment^[i] (List.replicate m false)) q.2).card) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [countStep, Function.iterate_succ_apply', Prod.mk.injEq, true_and]
    rw [Finset.range_add_one, Finset.filter_insert]
    split_ifs with hacc
    · rw [Finset.card_insert_of_notMem (by simp)]
    · rfl

open Classical in
/-- **The count of accepting coins**: `countAccepts` is the number of coin values of `fuel a` coins
whose programs accept after the history. -/
theorem countAccepts_eq_accepted (q : α × History) :
    countAccepts M enc fuel q = accepted (coinFamily M (fuel q.1) (enc q.1)) q.2 := by
  rw [countAccepts, iterate_countStep, accepted]
  simp only
  set t := fuel q.1
  refine Finset.card_bij'
    (fun i _ j => (increment^[i] (List.replicate t false)).getD j false)
    (fun f _ => lsbValue (List.ofFn f)) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at hi ⊢
    obtain ⟨_, hl⟩ := BitString.iterate_increment t i hi.1
    have hofFn : List.ofFn (fun j : Fin t =>
        (increment^[i] (List.replicate t false)).getD j false) =
        increment^[i] (List.replicate t false) := by
      refine List.ext_getElem (by simp [hl]) fun j h₁ h₂ => ?_
      simp
    rw [coinFamily, hofFn]
    exact (accepts_eq_true_iff_of_length M hl _).mp hi.2
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at hf ⊢
    have hlt := BitString.lsbValue_lt (List.ofFn f)
    rw [List.length_ofFn] at hlt
    refine ⟨hlt, ?_⟩
    have := BitString.iterate_increment_lsbValue (List.ofFn f)
    rw [List.length_ofFn] at this
    rw [this]
    exact (accepts_eq_true_iff_of_length M (List.length_ofFn (f := f)) _).mpr hf
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨hv, hl⟩ := BitString.iterate_increment t i hi.1
    have hofFn : List.ofFn (fun j : Fin t =>
        (increment^[i] (List.replicate t false)).getD j false) =
        increment^[i] (List.replicate t false) := by
      refine List.ext_getElem (by simp [hl]) fun j h₁ h₂ => ?_
      simp
    rw [hofFn, hv]
  · intro f _
    funext j
    have := BitString.iterate_increment_lsbValue (List.ofFn f)
    rw [List.length_ofFn] at this
    rw [this]
    simp

/-- **The count of accepting coins within polynomial space**, in the input and the history, for a
number of coins computed in polynomial time. -/
theorem computableTidilyInPolySpace_countAccepts [Finite Control] [Inhabited α]
    (hfuel : ComputableTidilyInPolyTime fuel enc encUnary) :
    ComputableTidilyInPolySpace (countAccepts M enc fuel) (encPair enc encHistory) encNat := by
  have hfuel' : ComputableTidilyInPolyTime (fun q : α × History => fuel q.1)
      (encPair enc encHistory) encUnary := hfuel.comp (ComputableTidilyInPolyTime.fst _ _)
  have hacc := computableTidilyInPolyTime_accepts M
  have hverify : ComputableTidilyInPolyTime
      (fun p : (α × History) × List Bool => accepts M (enc p.1.1) p.2 p.1.2)
      (encPair (encPair enc encHistory) encBits) encBool := by fun_prop
  refine (computableTidilyInPolySpace_acceptCount hverify hfuel').congr fun q => ?_
  rw [countAccepts_eq_accepted]
  unfold acceptCount accepted
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro r _
  exact accepts_eq_true_iff_of_length M (List.length_ofFn (f := r)) q.2

end Count

end Interaction

end Cslib.Complexity
