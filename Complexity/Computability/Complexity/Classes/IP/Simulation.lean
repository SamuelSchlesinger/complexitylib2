/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.IP.CoinFixing
public import Complexity.Computability.Complexity.Classes.Oracle.Deterministic
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Configuration
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Configuration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Transducer
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatPower
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
* The coin values are enumerated by a binary counter, and the accepting ones are counted with a
  binary accumulator (`Cslib.Complexity.Interaction.countAccepts`,
  `Cslib.Complexity.Interaction.countAccepts_eq_accepted`), in polynomial space
  (`Cslib.Complexity.Interaction.computableTidilyInPolySpace_countAccepts`).

`Cslib.Complexity.ComputableTidilyInPolySpace` packages tidy computability within polynomial space
and some time, with its closure under composition, pairing, case distinction and iteration
(`Cslib.Complexity.ComputableTidilyInPolySpace.iterate`).

## Main definitions

* `Cslib.Complexity.ComputableTidilyInPolySpace`: computability within polynomial space.
* `Cslib.Complexity.Interaction.accepts`: whether the program of given coins accepts.
* `Cslib.Complexity.Interaction.countAccepts`: the number of accepting coin values.

## Main results

* `Cslib.Complexity.ComputableTidilyInPolySpace.iterate`: iteration within polynomial space.
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

/-! ### Polynomial space -/

/-- `f` is tidily computable within some time and within space polynomially bounded in the length
of the encoded input. -/
def ComputableTidilyInPolySpace {α β : Type} (f : α → β) (encIn : α ↪ List Bool)
    (encOut : β ↪ List Bool) : Prop :=
  ∃ T S, PolyBounded (fun a => (encIn a).length) S ∧ ComputableTidilyInO f encIn encOut T S

namespace ComputableTidilyInPolySpace

variable {α β γ δ : Type} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool} {encD : δ ↪ List Bool}

/-- Polynomial time is within polynomial space. -/
theorem of_polyTime {f : α → β} (h : ComputableTidilyInPolyTime f encIn encMid) :
    ComputableTidilyInPolySpace f encIn encMid := by
  obtain ⟨d, _, h⟩ := h.exists_degree
  exact ⟨_, _, PolyBounded.of_forall_le (u := fun a => ((encIn a).length + 1) ^ d) 1 d
    fun a => by simp, h.inO⟩

/-- The encoded values have polynomial length. -/
theorem polyBounded_length {f : α → β} (h : ComputableTidilyInPolySpace f encIn encMid) :
    PolyBounded (fun a => (encIn a).length) fun a => (encMid (f a)).length := by
  obtain ⟨T, S, hS, h⟩ := h
  obtain ⟨c, hc⟩ := h.length_le
  exact ((PolyBounded.const c).mul (hS.add (.const 1))).mono hc

/-- Composition. -/
theorem comp {f : β → γ} {g : α → β} (hf : ComputableTidilyInPolySpace f encMid encOut)
    (hg : ComputableTidilyInPolySpace g encIn encMid) :
    ComputableTidilyInPolySpace (fun a => f (g a)) encIn encOut := by
  have hlen := hg.polyBounded_length
  obtain ⟨Tf, Sf, hSf, hf'⟩ := hf
  obtain ⟨Tg, Sg, hSg, hg'⟩ := hg
  exact ⟨_, _, hSg.add (hSf.comp hlen), hf'.comp hg'⟩

/-- Pairing. -/
theorem prod {f : α → β} {g : α → δ} (hf : ComputableTidilyInPolySpace f encIn encMid)
    (hg : ComputableTidilyInPolySpace g encIn encD) :
    ComputableTidilyInPolySpace (fun a => (f a, g a)) encIn (encPair encMid encD) := by
  obtain ⟨Tf, Sf, hSf, hf⟩ := hf
  obtain ⟨Tg, Sg, hSg, hg⟩ := hg
  exact ⟨_, _, hSf.add hSg, hf.prod hg⟩

/-- Case distinction. -/
theorem ite {c : α → Bool} {f g : α → β} (hc : ComputableTidilyInPolySpace c encIn encBool)
    (hf : ComputableTidilyInPolySpace f encIn encMid)
    (hg : ComputableTidilyInPolySpace g encIn encMid) :
    ComputableTidilyInPolySpace (fun a => if c a then f a else g a) encIn encMid := by
  obtain ⟨Tc, Sc, hSc, hc⟩ := hc
  obtain ⟨Tf, Sf, hSf, hf⟩ := hf
  obtain ⟨Tg, Sg, hSg, hg⟩ := hg
  refine ⟨_, _, (hSc.add (hSf.add hSg)).mono fun a => ?_, hc.ite hf hg⟩
  split_ifs <;> lia

/-- Agreement with a computable function. -/
theorem congr {f g : α → β} (h : ComputableTidilyInPolySpace f encIn encMid)
    (hfg : ∀ a, f a = g a) : ComputableTidilyInPolySpace g encIn encMid := by
  rwa [show g = f from funext fun a => (hfg a).symm]

/-- **Iteration within polynomial space**: iterating a step computable within polynomial space a
number of times computed in polynomial time in binary, from a start computable within polynomial
space, is within polynomial space when all the states along the way have polynomial length. -/
theorem iterate [Inhabited β] {n : α → ℕ} {init : α → β} {step : β → β}
    (hn : ComputableTidilyInPolyTime n encIn encNat)
    (hinit : ComputableTidilyInPolySpace init encIn encMid)
    (hstep : ComputableTidilyInPolySpace step encMid encMid) {B : α → ℕ}
    (hB : PolyBounded (fun a => (encIn a).length) B)
    (hstate : ∀ a, ∀ k ≤ n a, (encMid (step^[k] (init a))).length ≤ B a) :
    ComputableTidilyInPolySpace (fun a => step^[n a] (init a)) encIn encMid := by
  obtain ⟨dn, _, hn'⟩ := hn.exists_degree
  obtain ⟨Ti, Si, hSi, hinit⟩ := hinit
  obtain ⟨Ts, Ss, hSs, hstep⟩ := hstep
  obtain ⟨cs, ds, hSs⟩ := hSs.exists_le
  have hit := ComputableTidilyInO.iterate hn'.inO hinit hstep
    (R := fun a => (Finset.range (n a + 1)).sup fun k => Ts (step^[k] (init a)))
    (Q := fun a => cs * (B a + 1) ^ ds) (B := B)
    (fun a k hk => Finset.le_sup (f := fun k => Ts (step^[k] (init a)))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)))
    (fun a k hk => (hSs _).trans (Nat.mul_le_mul_left cs
      (Nat.pow_le_pow_left (Nat.add_le_add_right (hstate a k hk) 1) ds)))
    hstate
  refine ⟨_, _, ?_, hit⟩
  have hQ : PolyBounded (fun a => (encIn a).length) fun a => cs * (B a + 1) ^ ds :=
    PolyBounded.comp (size' := id) (v := fun m => cs * (m + 1) ^ ds)
      (PolyBounded.of_forall_le cs ds fun _ => le_rfl) hB
  exact ((((PolyBounded.of_forall_le (u := fun a => ((encIn a).length + 1) ^ dn) 1 dn
    fun a => by simp).add hSi).add hQ).add hB).add hn.polyBounded_length

end ComputableTidilyInPolySpace

namespace Interaction

/-! ### A binary counter -/

/-- Binary increment, least significant bit first, discarding the final carry. -/
def incrementBits : List Bool → List Bool
  | [] => []
  | false :: w => true :: w
  | true :: w => false :: incrementBits w

/-- The value of a word in binary, least significant bit first. -/
def lsbValue : List Bool → ℕ
  | [] => 0
  | b :: w => b.toNat + 2 * lsbValue w

@[simp] theorem length_incrementBits : ∀ w, (incrementBits w).length = w.length
  | [] => rfl
  | false :: _ => rfl
  | true :: w => by simp [incrementBits, length_incrementBits w]

theorem lsbValue_lt : ∀ w, lsbValue w < 2 ^ w.length
  | [] => by simp [lsbValue]
  | b :: w => by
    have := lsbValue_lt w
    cases b <;> simp [lsbValue, pow_succ] <;> lia

theorem lsbValue_incrementBits : ∀ w, lsbValue w + 1 < 2 ^ w.length →
    lsbValue (incrementBits w) = lsbValue w + 1
  | [] => by simp [lsbValue]
  | false :: w => fun _ => by simp [incrementBits, lsbValue]; lia
  | true :: w => fun h => by
    simp only [lsbValue, List.length_cons, pow_succ, Bool.toNat_true, incrementBits,
      Bool.toNat_false] at h ⊢
    rw [lsbValue_incrementBits w (by lia)]
    lia

theorem lsbValue_injective : ∀ {w w' : List Bool}, w.length = w'.length →
    lsbValue w = lsbValue w' → w = w'
  | [], [], _, _ => rfl
  | b :: w, b' :: w', hl, hv => by
    simp only [lsbValue] at hv
    have hb : b = b' := by
      cases b <;> cases b' <;> first | rfl | (simp at hv; lia)
    subst hb
    exact congrArg _ (lsbValue_injective (by simpa using hl) (by lia))

@[simp] theorem lsbValue_replicate_false : ∀ m, lsbValue (List.replicate m false) = 0
  | 0 => rfl
  | m + 1 => by simp [List.replicate_succ, lsbValue, lsbValue_replicate_false m]

theorem lsbValue_replicate_true : ∀ m, lsbValue (List.replicate m true) + 1 = 2 ^ m
  | 0 => rfl
  | m + 1 => by
    have := lsbValue_replicate_true m
    simp only [List.replicate_succ, lsbValue, Bool.toNat_true, pow_succ]
    lia

/-- The counter counts: the `j`-th iterate from zero has value `j`, below `2 ^ m`. -/
theorem iterate_incrementBits (m : ℕ) : ∀ j < 2 ^ m,
    lsbValue (incrementBits^[j] (List.replicate m false)) = j ∧
      (incrementBits^[j] (List.replicate m false)).length = m
  | 0, _ => ⟨lsbValue_replicate_false m, List.length_replicate⟩
  | j + 1, hj => by
    obtain ⟨hv, hl⟩ := iterate_incrementBits m j (by lia)
    rw [Function.iterate_succ_apply', length_incrementBits,
      lsbValue_incrementBits _ (by rw [hv, hl]; lia), hv]
    exact ⟨rfl, hl⟩

@[simp] theorem length_iterate_incrementBits (j : ℕ) (w : List Bool) :
    (incrementBits^[j] w).length = w.length := by
  induction j generalizing w with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply, ih, length_incrementBits]

/-- Every word is reached by counting up to its value. -/
theorem iterate_incrementBits_lsbValue (u : List Bool) :
    incrementBits^[lsbValue u] (List.replicate u.length false) = u :=
  let h := iterate_incrementBits u.length (lsbValue u) (lsbValue_lt u)
  lsbValue_injective h.2 h.1

/-- Increment by a two-state transducer, the state being the carry. -/
private def incrementT : Transducer Bool Bool where
  q₀ := true
  step c b := (c && b, [b ^^ c])
  final _ := []
  length_step_le _ _ := by simp
  length_final_le _ := by simp

private theorem incrementT_run_false (w : List Bool) : incrementT.run false w = w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [Transducer.run_cons]
    change [b ^^ false] ++ incrementT.run (false && b) w = b :: w
    rw [Bool.false_and, ih, Bool.xor_false]
    rfl

private theorem incrementT_run (w : List Bool) : incrementT.run true w = incrementBits w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [Transducer.run_cons]
    change [b ^^ true] ++ incrementT.run (true && b) w = incrementBits (b :: w)
    cases b
    · rw [Bool.true_and, incrementT_run_false]
      rfl
    · rw [Bool.true_and, ih]
      rfl

/-- Binary increment is polynomial-time. -/
theorem computableTidilyInPolyTime_incrementBits :
    ComputableTidilyInPolyTime incrementBits encBits encBits :=
  .of_linear (incrementT.computableTidilyInLinearTimeAndSpace fun w => by
    rw [show incrementT.q₀ = true from rfl, incrementT_run]; rfl)

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
    (acc : Except (Option (List Bool)) (MultiTapeMachine.FiniteConfig k Bool Control Unit × History))
    (s : AliveState k Control)
    (hs : (∀ p, acc = .ok p → s = (p.1, p.2, true)) ∧ (∀ e, acc = .error e → s.2.2 = false)) :
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
  have hrun := foldl_aliveStep M r.length r (.ok (MultiTapeMachine.FiniteConfig.init M.initial x, h))
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
  have hpost : ComputableTidilyInPolyTime (fun s : AliveState k Control =>
      s.2.2 && s.2.1.isEmpty && decide (s.1.tapes.output = [true])) encAliveState encBool := by
    fun_prop
  exact hpost.comp h

end PolyTime

/-! ### Counting the accepting coins -/

section Count

variable {α : Type} (enc : α ↪ List Bool) (fuel : α → ℕ)

/-- One round of the count: test the coins, add the verdict, and move on to the next coins. -/
def countStep (s : (α × History) × List Bool × ℕ) : (α × History) × List Bool × ℕ :=
  (s.1, incrementBits s.2.1, s.2.2 + if accepts M (enc s.1.1) s.2.1 s.1.2 then 1 else 0)

/-- The number of accepting values of `fuel a` coins after the history `h`, counted by trying the
coins one after another with a binary counter. -/
def countAccepts (q : α × History) : ℕ :=
  ((countStep M enc)^[2 ^ fuel q.1] (q, List.replicate (fuel q.1) false, 0)).2.2

open Classical in
theorem iterate_countStep (q : α × History) (m j : ℕ) :
    (countStep M enc)^[j] (q, List.replicate m false, 0) =
      (q, incrementBits^[j] (List.replicate m false),
        ((Finset.range j).filter fun i =>
          accepts M (enc q.1) (incrementBits^[i] (List.replicate m false)) q.2).card) := by
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
  refine Finset.card_bij' (fun i _ j => (incrementBits^[i] (List.replicate t false)).getD j false)
    (fun f _ => lsbValue (List.ofFn f)) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at hi ⊢
    obtain ⟨_, hl⟩ := iterate_incrementBits t i hi.1
    have hofFn : List.ofFn (fun j : Fin t =>
        (incrementBits^[i] (List.replicate t false)).getD j false) =
        incrementBits^[i] (List.replicate t false) := by
      refine List.ext_getElem (by simp [hl]) fun j h₁ h₂ => ?_
      simp
    rw [coinFamily, hofFn]
    exact (accepts_eq_true_iff_of_length M hl _).mp hi.2
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at hf ⊢
    have hlt := lsbValue_lt (List.ofFn f)
    rw [List.length_ofFn] at hlt
    refine ⟨hlt, ?_⟩
    have := iterate_incrementBits_lsbValue (List.ofFn f)
    rw [List.length_ofFn] at this
    rw [this]
    exact (accepts_eq_true_iff_of_length M (List.length_ofFn (f := f)) _).mpr hf
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨hv, hl⟩ := iterate_incrementBits t i hi.1
    have hofFn : List.ofFn (fun j : Fin t =>
        (incrementBits^[i] (List.replicate t false)).getD j false) =
        incrementBits^[i] (List.replicate t false) := by
      refine List.ext_getElem (by simp [hl]) fun j h₁ h₂ => ?_
      simp
    rw [hofFn, hv]
  · intro f _
    funext j
    have := iterate_incrementBits_lsbValue (List.ofFn f)
    rw [List.length_ofFn] at this
    rw [this]
    simp

/-- **The count of accepting coins within polynomial space**, in the input and the history, for a
number of coins computed in polynomial time. -/
theorem computableTidilyInPolySpace_countAccepts [Finite Control] [Inhabited α]
    (hfuel : ComputableTidilyInPolyTime fuel enc encUnary) :
    ComputableTidilyInPolySpace (countAccepts M enc fuel) (encPair enc encHistory) encNat := by
  open ComputableTidilyInPolyTime in
  have hn : ComputableTidilyInPolyTime (fun q : α × History => 2 ^ fuel q.1)
      (encPair enc encHistory) encNat :=
    ((ComputableTidilyInDegree.two_pow_length encUnary).computableTidilyInPolyTime.comp
      (hfuel.comp (fst _ _))).of_enc_eq fun q => by simp [encUnary_apply]
  have hfuel' : ComputableTidilyInPolyTime (fun q : α × History => fuel q.1)
      (encPair enc encHistory) encUnary := hfuel.comp (ComputableTidilyInPolyTime.fst _ _)
  have hinit : ComputableTidilyInPolyTime
      (fun q : α × History => (q, List.replicate (fuel q.1) false, 0))
      (encPair enc encHistory) (encPair (encPair enc encHistory) (encPair encBits encNat)) :=
    ComputableTidilyInPolyTime.id'.prod
      (((ComputableTidilyInPolyTime.bitsReplicate false).comp hfuel').prod
        (ComputableTidilyInPolyTime.const 0))
  have hacc := computableTidilyInPolyTime_accepts M
  have hinc := computableTidilyInPolyTime_incrementBits
  have hstep : ComputableTidilyInPolyTime (countStep M enc)
      (encPair (encPair enc encHistory) (encPair encBits encNat))
      (encPair (encPair enc encHistory) (encPair encBits encNat)) := by
    unfold countStep
    fun_prop
  have hlen := hfuel.polyBounded_length
  simp only [encUnary_apply, List.length_replicate] at hlen
  have hit := ComputableTidilyInPolySpace.iterate hn (.of_polyTime hinit) (.of_polyTime hstep)
    (B := fun q => 2 * (encPair enc encHistory q).length + 3 * fuel q.1 + 5)
    ((((PolyBounded.const 2).mul .self).add ((PolyBounded.const 3).mul
      (hlen.comp (g := Prod.fst) (size' := fun a => (enc a).length)
        (PolyBounded.of_forall_le 1 1 fun q => by simp; lia)))).add (.const 5))
    (fun q j hj => ?_)
  · exact (ComputableTidilyInPolySpace.of_polyTime
      ((ComputableTidilyInPolyTime.snd _ _).snd')).comp hit
  · rw [iterate_countStep]
    have hcard : ((Finset.range j).filter fun i =>
        accepts M (enc q.1) (incrementBits^[i] (List.replicate (fuel q.1) false)) q.2).card ≤
          2 ^ fuel q.1 :=
      (Finset.card_filter_le _ _).trans (by simpa using hj)
    have hsize : (encNat ((Finset.range j).filter fun i =>
        accepts M (enc q.1) (incrementBits^[i] (List.replicate (fuel q.1) false)) q.2).card).length
          ≤ fuel q.1 + 1 := by
      rw [encNat_apply, Nat.size_eq_bits_len]
      exact Nat.size_le.mpr (hcard.trans_lt (Nat.pow_lt_pow_right (by norm_num) (by lia)))
    simp only [length_encPair, encBits_apply, length_iterate_incrementBits,
      List.length_replicate] at hsize ⊢
    lia

end Count

end Interaction

end Cslib.Complexity
