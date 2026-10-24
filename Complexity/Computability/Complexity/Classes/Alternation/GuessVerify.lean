/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Alternation.Game
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.InputFromTape
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Frame

/-!
# Games of polynomially many moves are in `AP`

A polynomial-time game verifier (`Cslib.Complexity.IsGameVerifier`) decides a problem through a
game of `2 * p n` alternate single-bit moves, the existential player first. This file builds the
alternating machine that plays such a game, the guess-then-verify machine
(`Turing.MultiTapeATM.guessVerify`) [Chandra, Kozen and Stockmeyer][ChandraKozenStockmeyer1981]
[Arora and Barak, Section 5.3][AroraBarak09], and so proves that every problem with a
polynomial-time game verifier is in `AP` (`Cslib.Complexity.IsGameVerifier.mem_AP`).

The machine is assembled from one deterministic machine for each move
(`Turing.MultiTapeATM.ofTMs`). The machine of the move `b`
(`Turing.MultiTapeATM.GuessVerify.machine`) runs, in sequence (`Turing.MultiTapeTM.seq`):

1. a deterministic machine `prep`, which writes on work tape `B` the frame of `L` bits `true`
   (`Turing.MultiTapeTM.frame`) followed by the input;
2. the guessing machine (`Turing.MultiTapeATM.GuessVerify.guess`), which walks along the pairs
   `true, true` of the frame and writes the move `b` over the second cell of each pair; its states
   record which player is to move, and the states of the universal player's moves are the
   universal states;
3. a rewind of tape `B` (`Turing.MultiTapeTM.rewindWork`), and a deterministic machine `verify`,
   started on the frame of the moves followed by the input.

Outside the cells of the moves the two moves agree, so acceptance passes along these steps
(`Turing.MultiTapeATM.acceptsWithin_add_iff_of_next_eq`), and through the guessing phase it is the
game of `L` alternate moves (`Turing.MultiTapeATM.GuessVerify.acceptsWithin_lift_tag`). Halting
passes along in the same way (`Turing.MultiTapeATM.HaltsWithin`: every list of moves reaches a
halted configuration), which gives the time bound (`Turing.MultiTapeATM.guessVerify_spec`).

For a game verifier `V`, `prep` writes the frame of `2 * p (enc a).length` bits followed by
`enc a`, by a polynomial-time machine with its output redirected to tape `B`
(`Turing.MultiTapeTM.outputToWord`), and `verify` runs a polynomial-time machine computing
`V (a, z)` from the word on tape `B`, which is the encoded pair `encPair encBits enc (z, a)` of the
moves `z` and the instance (`Turing.MultiTapeTM.inputFromWord`). The machine therefore runs within
polynomial time, and it accepts `enc a` exactly when the existential player wins the game.

## Main definitions

* `Turing.MultiTapeATM.ofTMs`: the alternating machine of a deterministic machine for each move.
* `Turing.MultiTapeATM.HaltsWithin`: every list of moves reaches a halted configuration.
* `Turing.MultiTapeATM.GuessVerify.guess`: the guessing machine.
* `Turing.MultiTapeATM.guessVerify`: the guess-then-verify machine.

## Main results

* `Turing.MultiTapeATM.acceptsWithin_add_iff_of_next_eq`,
  `Turing.MultiTapeATM.haltsWithin_add_iff_of_next_eq`: moves that do not matter.
* `Turing.MultiTapeATM.GuessVerify.acceptsWithin_lift_tag`: the guessing phase is a game.
* `Turing.MultiTapeATM.guessVerify_spec`: the guess-then-verify machine plays the game within the
  time of `prep`, plus `4 * L + 3`, plus the time of `verify`.
* `Cslib.Complexity.IsGameVerifier.mem_AP`: every problem with a polynomial-time game verifier is
  in `AP`.

## References

* [A. K. Chandra, D. C. Kozen, L. J. Stockmeyer, *Alternation*][ChandraKozenStockmeyer1981]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Turing

/-- Setting a cell of a word sets the cell of its tape. -/
theorem tapeOfList_set {Symbol : Type*} (w : List Symbol) {i : ℕ} (hi : i < w.length)
    (s : Symbol) : tapeOfList (w.set i s) = Function.update (tapeOfList w) (i : ℤ) (some s) := by
  funext z
  cases z with
  | negSucc n => simp
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, tapeOfList_ofNat, Function.update_apply, Nat.cast_inj,
      List.getElem?_set]
    by_cases h : n = i
    · subst h
      simp [hi]
    · simp [h, Ne.symm h]

namespace MultiTapeATM

open MultiTapeMachine

/-! ### Alternating machines from deterministic machines -/

section OfTMs

variable {k : ℕ} {Symbol State : Type} {input : List Symbol}

/-- The alternating machine whose move `b` is a step of the deterministic machine `tm b`, with
universal states `universal`. -/
noncomputable def ofTMs (tm : Bool → MultiTapeTM k Symbol State) (universal : State → Bool) :
    MultiTapeATM k Symbol State where
  toPTM :=
    { initial := (tm false).q₀
      tr := fun q symbol work _ b => Action.emptyOracleEquiv.symm ((tm b).tr q symbol work) }
  universal := universal

/-- The move `b` of `ofTMs tm universal` is a step of `tm b`. -/
theorem next_ofTMs (tm : Bool → MultiTapeTM k Symbol State) (universal : State → Bool)
    (b : Bool) (c : Cfg k Symbol State input) : (ofTMs tm universal).next b c = (tm b).step c := by
  rcases hs : c.state with _ | q
  · rw [next_of_halted _ hs, MultiTapeTM.step_of_halt hs]
  · rw [next_of_state _ hs, MultiTapeTM.step_of_state hs]
    simp [action, ofTMs]

/-- The initial configuration of `ofTMs tm universal` is that of `tm false`. -/
theorem initCfg_ofTMs (tm : Bool → MultiTapeTM k Symbol State) (universal : State → Bool) :
    (ofTMs tm universal).toPTM.toNTM.initCfg input = Cfg.init (tm false).q₀ input :=
  rfl

end OfTMs

/-! ### Halting within a number of moves -/

section HaltsWithin

variable {k : ℕ} {Symbol State : Type} {input : List Symbol}

/-- Every list of `n` moves from `c` reaches a halted configuration. -/
def HaltsWithin (atm : MultiTapeATM k Symbol State) (n : ℕ) (c : Cfg k Symbol State input) :
    Prop :=
  ∀ coins : List Bool, coins.length = n → (atm.toPTM.stepCoins coins c).state = none

variable {atm : MultiTapeATM k Symbol State}

/-- Within no moves, only a halted configuration halts. -/
theorem haltsWithin_zero {c : Cfg k Symbol State input} :
    atm.HaltsWithin 0 c ↔ c.state = none :=
  ⟨fun h => h [] rfl, fun h coins hlen => by rw [List.length_eq_zero_iff.mp hlen]; exact h⟩

/-- Halting within `n + 1` moves is halting within `n` after either move. -/
theorem haltsWithin_succ {n : ℕ} {c : Cfg k Symbol State input} :
    atm.HaltsWithin (n + 1) c ↔ ∀ b, atm.HaltsWithin n (atm.next b c) := by
  constructor
  · intro h b coins hlen
    rw [← stepCoins_cons]
    exact h (b :: coins) (by simp [hlen])
  · intro h coins hlen
    obtain ⟨b, coins, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    rw [stepCoins_cons]
    exact h b coins (by simpa using hlen)

/-- A time bound is halting within as many moves from the initial configuration. -/
theorem runsInTime_iff_haltsWithin {t : ℕ} :
    atm.toPTM.toNTM.RunsInTime input t ↔ atm.HaltsWithin t (atm.toPTM.toNTM.initCfg input) :=
  runsInTime_iff_stepCoins

/-- Along steps of `f` whose two moves agree, halting moves forward. -/
theorem haltsWithin_add_iff_of_next_eq {f : Cfg k Symbol State input → Cfg k Symbol State input}
    {m n : ℕ} {c : Cfg k Symbol State input}
    (h : ∀ j < m, ∀ b, atm.next b (f^[j] c) = f^[j + 1] c) :
    atm.HaltsWithin (m + n) c ↔ atm.HaltsWithin n (f^[m] c) := by
  induction m generalizing c with
  | zero => simp
  | succ m ih =>
    have h0 : ∀ b, atm.next b c = f c := h 0 (by omega)
    rw [show m + 1 + n = m + n + 1 by omega, haltsWithin_succ]
    simp only [h0, forall_const]
    rw [ih fun j hj b => ?_, Function.iterate_succ_apply]
    simpa only [Function.iterate_succ_apply] using h (j + 1) (by omega) b

end HaltsWithin

/-! ### Moves that do not matter -/

section Deterministic

variable {k : ℕ} {State : Type} {atm : MultiTapeATM k Bool State} {input : List Bool}

/-- A configuration whose two moves agree accepts within `n + 1` moves exactly when the common
successor accepts within `n`. -/
theorem acceptsWithin_succ_of_next_eq {n : ℕ} {c c' : Cfg k Bool State input}
    (h : ∀ b, atm.next b c = c') : atm.AcceptsWithin (n + 1) c ↔ atm.AcceptsWithin n c' := by
  rcases hs : c.state with _ | q
  · have hc : c' = c := (h false).symm.trans (atm.next_of_halted hs false)
    subst hc
    rw [atm.acceptsWithin_of_halted hs, atm.acceptsWithin_of_halted hs]
  · cases hq : atm.universal q
    · rw [atm.acceptsWithin_succ_of_existential hs hq]
      simp only [h, exists_const]
    · rw [atm.acceptsWithin_succ_of_universal hs hq]
      simp only [h, forall_const]

/-- Along steps of `f` whose two moves agree, acceptance moves forward. -/
theorem acceptsWithin_add_iff_of_next_eq {f : Cfg k Bool State input → Cfg k Bool State input}
    {m n : ℕ} {c : Cfg k Bool State input}
    (h : ∀ j < m, ∀ b, atm.next b (f^[j] c) = f^[j + 1] c) :
    atm.AcceptsWithin (m + n) c ↔ atm.AcceptsWithin n (f^[m] c) := by
  induction m generalizing c with
  | zero => simp
  | succ m ih =>
    have h0 : ∀ b, atm.next b c = f c := h 0 (by omega)
    rw [show m + 1 + n = m + n + 1 by omega, acceptsWithin_succ_of_next_eq h0,
      Function.iterate_succ_apply, ih fun j hj b => ?_]
    simpa only [Function.iterate_succ_apply] using h (j + 1) (by omega) b

end Deterministic

/-! ### The guessing machine -/

/-- The states of the guessing machine: at a tag cell, or at a cell receiving a move, with the
label of the player of the next move (`true` for universal). -/
inductive GuessState
  | tag (universal : Bool)
  | move (universal : Bool)
  deriving DecidableEq

instance : Finite GuessState :=
  Finite.of_injective (fun s : GuessState => match s with
    | .tag u => (false, u)
    | .move u => (true, u)) (by
      rintro (_ | _) (_ | _) h <;> simp_all)

namespace GuessVerify

section Guess

variable {k : ℕ}

/-- The guessing machine with move `b` on work tape `B`: at a cell `true` it moves right to the
next cell, which receives the move `b`, and the player alternates; at any other cell it halts. -/
def guess (B : Fin k) (b : Bool) : MultiTapeTM k Bool GuessState :=
  MultiTapeTM.ofTr (.tag false) fun q _ work =>
    match q, work B with
    | .tag u, some true =>
      ⟨0, Function.update (fun _ => (none, 0)) B (none, 1), none, some (.move u)⟩
    | .tag _, _ => ⟨0, fun _ => (none, 0), none, none⟩
    | .move u, _ =>
      ⟨0, Function.update (fun _ => (none, 0)) B (some (some b), 1), none, some (.tag !u)⟩

variable {input : List Bool}

/-- A configuration with the word `w` on tape `B` and its head at `pos`, every other work tape
blank with its head at `0`, the input head at the start and no output. -/
def cfg {State : Type} (B : Fin k) (q : Option State) (w : List Bool) (pos : ℕ) :
    Cfg k Bool State input :=
  ⟨q, 1, Function.update (fun _ _ => none) B (tapeOfList w),
    Function.update (fun _ => 0) B (pos : ℤ), []⟩

/-- With its head at `0`, tape `B` is in the normal form of `Turing.wordsCfg`. -/
theorem cfg_zero {State : Type} (B : Fin k) (q : Option State) (w : List Bool) :
    cfg (input := input) B q w 0 =
      wordsCfg input q (Function.update (fun _ => []) B w) [] := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> by_cases hi : i = B <;>
    simp [cfg, wordsCfg, hi]

variable (B : Fin k) (b : Bool) {w : List Bool} {pos : ℕ} (u : Bool)

/-- At a tag `true`, the guessing machine moves right to the cell of the move. -/
theorem step_guess_tag (h : w[pos]? = some true) :
    (guess B b).step (cfg (input := input) B (some (.tag u)) w pos) =
      cfg B (some (.move u)) w (pos + 1) := by
  rw [MultiTapeTM.step_of_state rfl]
  simp only [guess, MultiTapeTM.tr_ofTr, Cfg.workTapeSymbols, cfg, Function.update_self,
    tapeOfList_ofNat, h]
  refine Cfg.ext rfl (by simp [moveInputPos_zero]) ?_ ?_ (by simp) <;> funext i <;>
    by_cases hi : i = B <;> simp [hi]

/-- At the cell of a move, the guessing machine writes its move, moves right, and the other player
is to move. -/
theorem step_guess_move (h : pos < w.length) :
    (guess B b).step (cfg (input := input) B (some (.move u)) w pos) =
      cfg B (some (.tag !u)) (w.set pos b) (pos + 1) := by
  rw [MultiTapeTM.step_of_state rfl]
  simp only [guess, MultiTapeTM.tr_ofTr, cfg]
  refine Cfg.ext rfl (by simp [moveInputPos_zero]) ?_ ?_ (by simp) <;> funext i <;>
    by_cases hi : i = B <;> simp [hi, tapeOfList_set w h]

/-- At any other cell, the guessing machine halts. -/
theorem step_guess_halt (h : w[pos]? ≠ some true) :
    (guess B b).step (cfg (input := input) B (some (.tag u)) w pos) =
      cfg B none w pos := by
  rw [MultiTapeTM.step_of_state rfl]
  have hread : (cfg (input := input) (State := GuessState) B (some (.tag u)) w
      pos).workTapeSymbols B = w[pos]? := by
    simp [Cfg.workTapeSymbols, cfg]
  simp only [guess, MultiTapeTM.tr_ofTr, hread]
  rcases hw : w[pos]? with _ | _ | _
  · refine Cfg.ext rfl (by simp [cfg, moveInputPos_zero]) ?_ ?_ (by simp [cfg]) <;>
      funext i <;> simp [cfg]
  · refine Cfg.ext rfl (by simp [cfg, moveInputPos_zero]) ?_ ?_ (by simp [cfg]) <;>
      funext i <;> simp [cfg]
  · exact absurd hw h

end Guess

/-! ### Guess, then verify -/

section Machine

open MultiTapeTM

variable {k : ℕ} {S₁ S₂ : Type} (B : Fin k) (prep : MultiTapeTM k Bool S₁)
  (verify : MultiTapeTM k Bool S₂)

/-- Rewind tape `B`, then run `verify`. -/
noncomputable def rewindVerify : MultiTapeTM k Bool (RewindWorkState ⊕ S₂) :=
  ((rewindWork Bool).extendTapes (tapeEmb B)).seq verify

/-- The deterministic machine of the move `b`: run `prep`, guess with the move `b`, rewind tape
`B` and run `verify`. -/
noncomputable def machine (b : Bool) :
    MultiTapeTM k Bool (S₁ ⊕ GuessState ⊕ RewindWorkState ⊕ S₂) :=
  prep.seq ((guess B b).seq (rewindVerify B verify))

/-- The universal states of the guess-then-verify machine: the cells of the moves of the universal
player. -/
def isUniversal : S₁ ⊕ GuessState ⊕ RewindWorkState ⊕ S₂ → Bool
  | .inr (.inl (.move u)) => u
  | _ => false

end Machine

end GuessVerify

section Machine

open MultiTapeTM

variable {k : ℕ} {S₁ S₂ : Type} (B : Fin k) (prep : MultiTapeTM k Bool S₁)
  (verify : MultiTapeTM k Bool S₂)

/-- **The guess-then-verify machine**: it prepares tape `B` by `prep`, writes the moves of the two
players, alternately, over the second cells of the pairs `true, true` that follow the tape's
initial pairs, rewinds tape `B` and runs `verify`. -/
noncomputable def guessVerify :
    MultiTapeATM k Bool (S₁ ⊕ GuessState ⊕ RewindWorkState ⊕ S₂) :=
  ofTMs (GuessVerify.machine B prep verify) GuessVerify.isUniversal

end Machine

namespace GuessVerify

section Phases

open MultiTapeTM MultiTapeTM.Sequential

variable {k : ℕ} {S₁ S₂ : Type} {B : Fin k} {prep : MultiTapeTM k Bool S₁}
  {verify : MultiTapeTM k Bool S₂} {input : List Bool}

/-- Outside the cells of the moves, the two moves agree. -/
theorem step_machine {c : Cfg k Bool (S₁ ⊕ GuessState ⊕ RewindWorkState ⊕ S₂) input}
    (h : ∀ u, c.state ≠ some (.inr (.inl (.move u)))) (b : Bool) :
    (machine B prep verify b).step c = (machine B prep verify false).step c := by
  rcases hs : c.state with _ | s
  · rw [MultiTapeTM.step_of_halt hs, MultiTapeTM.step_of_halt hs]
  · rw [MultiTapeTM.step_of_state hs, MultiTapeTM.step_of_state hs]
    congr 1
    rcases s with q | (g | r)
    · simp [machine, MultiTapeTM.seq, guess]
    · rcases g with u | u
      · simp only [machine, MultiTapeTM.seq, MultiTapeTM.tr_ofTr, guess]
        rcases c.workTapeSymbols B with _ | _ | _ <;> rfl
      · exact absurd hs (h u)
    · simp [machine, MultiTapeTM.seq]

variable (S₁ B verify) in
/-- A configuration of the guessing machine, as a configuration of the guess-then-verify
machine. -/
noncomputable def lift (c : Cfg k Bool GuessState input) :
    Cfg k Bool (S₁ ⊕ GuessState ⊕ RewindWorkState ⊕ S₂) input :=
  rightCfg (leftCfg (rewindVerify B verify) c)

/-- In the guessing phase, the move `b` is a step of the guessing machine with the move `b`. -/
theorem next_lift {c : Cfg k Bool GuessState input} (h : c.state ≠ none) (b : Bool) :
    (guessVerify B prep verify).next b (lift S₁ B verify c) =
      lift S₁ B verify ((guess B b).step c) := by
  rw [guessVerify, next_ofTMs, machine, lift, step_rightCfg, step_leftCfg _ h]
  rfl

/-- At the terminator of the frame, the guessing phase ends. -/
theorem next_lift_halt (zd : List Bool) (u b : Bool) :
    (guessVerify B prep verify).next b (lift S₁ B verify (cfg (input := input) B
      (some (.tag u)) (frame zd ++ input) (2 * zd.length))) =
      lift S₁ B verify (cfg (input := input) B none (frame zd ++ input)
        (2 * zd.length)) := by
  rw [next_lift (by simp [cfg]), step_guess_halt]
  simp [getElem?_frame_append_length]

/-- At the tag of a pair, the head moves to its second cell. -/
theorem next_lift_tag (zd v : List Bool) (c u b : Bool) :
    (guessVerify B prep verify).next b (lift S₁ B verify (cfg (input := input) B
      (some (.tag u)) (frame (zd ++ c :: v) ++ input) (2 * zd.length))) =
      lift S₁ B verify (cfg (input := input) B (some (.move u))
        (frame (zd ++ c :: v) ++ input) (2 * zd.length + 1)) := by
  rw [next_lift (by simp [cfg]),
    step_guess_tag _ _ _ (getElem?_frame_append_cons zd _ input c)]

/-- The second cell of a pair receives the move. -/
theorem next_lift_move (zd v : List Bool) (c u b : Bool) :
    (guessVerify B prep verify).next b (lift S₁ B verify (cfg (input := input) B
      (some (.move u)) (frame (zd ++ c :: v) ++ input) (2 * zd.length + 1))) =
      lift S₁ B verify (cfg (input := input) B (some (.tag !u))
        (frame (zd ++ b :: v) ++ input) (2 * (zd.length + 1))) := by
  rw [next_lift (by simp [cfg]), step_guess_move _ _ _
    (lt_length_frame_append_cons _ _ _ _), set_frame_append_cons]
  congr 2

/-- **The guessing phase.** From the tag of the first of `r` pairs `true, true` that follow the
pairs of the moves `zd`, with the player `u` to move (`true` for universal), acceptance within
`2 * r + 1 + n` moves is the game of `r` alternate moves, the first by the player `u`, after which
the configuration ending the guessing phase accepts within `n` moves. -/
theorem acceptsWithin_lift_tag (r : ℕ) : ∀ (zd : List Bool) (u : Bool) (n : ℕ),
    (guessVerify B prep verify).AcceptsWithin (2 * r + 1 + n)
      (lift S₁ B verify (cfg (input := input) B (some (.tag u))
        (frame (zd ++ List.replicate r true) ++ input) (2 * zd.length))) ↔
    Cslib.Complexity.Alternation (!u) (List.replicate r 1) fun zr =>
      (guessVerify B prep verify).AcceptsWithin n
        (lift S₁ B verify (cfg (input := input) B none (frame (zd ++ zr) ++ input)
          (2 * (zd.length + r)))) := by
  induction r with
  | zero =>
    intro zd u n
    rw [show 2 * 0 + 1 + n = n + 1 by omega, List.replicate_zero, List.replicate_zero,
      List.append_nil, acceptsWithin_succ_of_next_eq (next_lift_halt zd u),
      Cslib.Complexity.alternation_nil, List.append_nil, add_zero]
  | succ r ih =>
    intro zd u n
    simp only [List.replicate_succ]
    have hstate : (lift S₁ B verify (cfg (input := input) B (some (.move u))
        (frame (zd ++ true :: List.replicate r true) ++ input)
        (2 * zd.length + 1))).state = some (.inr (.inl (.move u))) := rfl
    have hgame (b : Bool) := ih (zd ++ [b]) (!u) n
    simp only [Bool.not_not, List.append_assoc, List.singleton_append, List.length_append,
      List.length_singleton, show zd.length + 1 + r = zd.length + (r + 1) by ring] at hgame
    rw [show 2 * (r + 1) + 1 + n = 2 * r + 1 + n + 1 + 1 by omega,
      acceptsWithin_succ_of_next_eq (next_lift_tag zd _ true u)]
    cases u
    · rw [(guessVerify B prep verify).acceptsWithin_succ_of_existential hstate rfl,
        Bool.not_false, Cslib.Complexity.alternation_true_one_cons]
      refine exists_congr fun b => ?_
      rw [next_lift_move]
      exact hgame b
    · rw [(guessVerify B prep verify).acceptsWithin_succ_of_universal hstate rfl,
        Bool.not_true, Cslib.Complexity.alternation_false_one_cons]
      refine forall_congr' fun b => ?_
      rw [next_lift_move]
      exact hgame b

/-- **The guessing phase halts** within `2 * r + 1 + n` moves from the tag of the first of `r` pairs
`true, true` exactly when every way of writing the `r` moves ends the guessing phase in a
configuration halting within `n` moves. -/
theorem haltsWithin_lift_tag (r : ℕ) : ∀ (zd : List Bool) (u : Bool) (n : ℕ),
    (guessVerify B prep verify).HaltsWithin (2 * r + 1 + n)
      (lift S₁ B verify (cfg (input := input) B (some (.tag u))
        (frame (zd ++ List.replicate r true) ++ input) (2 * zd.length))) ↔
    ∀ zr : List Bool, zr.length = r → (guessVerify B prep verify).HaltsWithin n
      (lift S₁ B verify (cfg (input := input) B none (frame (zd ++ zr) ++ input)
        (2 * (zd.length + r)))) := by
  induction r with
  | zero =>
    intro zd u n
    rw [show 2 * 0 + 1 + n = n + 1 by omega, haltsWithin_succ, List.replicate_zero,
      List.append_nil]
    simp only [next_lift_halt, forall_const, List.length_eq_zero_iff, forall_eq,
      List.append_nil, add_zero]
  | succ r ih =>
    intro zd u n
    simp only [List.replicate_succ]
    have hgame (b : Bool) := ih (zd ++ [b]) (!u) n
    simp only [List.append_assoc, List.singleton_append, List.length_append,
      List.length_singleton, show zd.length + 1 + r = zd.length + (r + 1) by ring] at hgame
    rw [show 2 * (r + 1) + 1 + n = 2 * r + 1 + n + 1 + 1 by omega, haltsWithin_succ]
    simp only [next_lift_tag, forall_const, haltsWithin_succ, next_lift_move, hgame]
    constructor
    · intro h zr hzr
      obtain ⟨b, zr, rfl⟩ := List.exists_cons_of_length_eq_add_one hzr
      exact h b zr (by simpa using hzr)
    · exact fun h b zr hzr => h (b :: zr) (by simp [hzr])

/-- The configurations after the guessing phase are never at the cell of a move. -/
theorem state_rightCfg_rightCfg_ne (c : Cfg k Bool (RewindWorkState ⊕ S₂) input)
    (u : Bool) : (rightCfg (State₀ := S₁) (rightCfg (State₀ := GuessState) c)).state ≠
      some (.inr (.inl (.move u))) := by
  rcases hc : c.state with _ | _ <;> simp [rightCfg, Cfg.mapState, hc]

/-- Rewinding tape `B` from `pos` takes `pos + 2` steps. -/
theorem runFrom_rewindWork_cfg {w : List Bool} {pos : ℕ} (hpos : pos ≤ w.length) :
    ((rewindWork Bool).extendTapes (tapeEmb B)).runFrom
      (cfg (input := input) B (some (rewindWork Bool).q₀) w pos) (pos + 2) =
      cfg B none w 0 := by
  rw [runFrom_tapeEmb, show oneTapeCfg B (cfg (input := input) B
      (some (rewindWork Bool).q₀) w pos) = ⟨some (rewindWork Bool).q₀, 1,
        fun _ => tapeOfList w, fun _ => (pos : ℤ), []⟩ by simp [oneTapeCfg, cfg],
    runFrom_rewindWork_none _ _ _ rfl hpos, embed_tapeEmb]
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> by_cases hi : i = B <;> simp [cfg, hi]

/-- After the guessing phase, the machine rewinds tape `B` and runs `verify`. -/
theorem runFrom_lift_none {w : List Bool} {pos t : ℕ} (hpos : pos ≤ w.length)
    (hfin : (verify.runFrom (wordsCfg input (some verify.q₀) (Function.update (fun _ => []) B w)
      []) t).state = none) (b : Bool) :
    (machine B prep verify b).runFrom
      (lift S₁ B verify (cfg (input := input) B none w pos)) (pos + 2 + t) =
      rightCfg (rightCfg (rightCfg (verify.runFrom (wordsCfg input (some verify.q₀)
        (Function.update (fun _ => []) B w) []) t))) := by
  rw [lift, leftCfg_of_halt rfl, machine, runFrom_rightCfg, runFrom_rightCfg]
  congr 2
  have hstart : (cfg (input := input) (State := GuessState) B none w pos).withState
      (some (rewindVerify B verify).q₀) =
        leftCfg verify (cfg B (some (rewindWork Bool).q₀) w pos) :=
    rfl
  rw [hstart, rewindVerify, runFrom_seq (runFrom_rewindWork_cfg hpos) rfl _ hfin]
  rw [← cfg_zero]
  rfl

/-- The configurations reached by the deterministic machine of the move `false` agree with those of
every move, outside the moves. -/
theorem next_iterate_rightCfg (c : Cfg k Bool (RewindWorkState ⊕ S₂) input) (j : ℕ)
    (b : Bool) : (guessVerify B prep verify).next b
      ((machine B prep verify false).step^[j] (rightCfg (rightCfg c))) =
      (machine B prep verify false).step^[j + 1] (rightCfg (rightCfg c)) := by
  rw [guessVerify, next_ofTMs, Function.iterate_succ_apply', step_machine]
  have : (machine B prep verify false).step^[j] (rightCfg (rightCfg c)) =
      rightCfg (rightCfg ((rewindVerify B verify).runFrom c j)) := by
    change (machine B prep verify false).runFrom _ j = _
    rw [machine, runFrom_rightCfg, runFrom_rightCfg]
  rw [this]
  exact state_rightCfg_rightCfg_ne _

/-- After the guessing phase, the moves do not matter, and the machine reaches the halted
configuration of `verify`. -/
private theorem iterate_lift_none {w : List Bool} {pos t : ℕ} (hpos : pos ≤ w.length)
    (hfin : (verify.runFrom (wordsCfg input (some verify.q₀) (Function.update (fun _ => []) B w)
      []) t).state = none) :
    (∀ j < pos + 2 + t, ∀ b, (guessVerify B prep verify).next b
      ((machine B prep verify false).step^[j] (lift S₁ B verify (cfg (input := input) B none w
        pos))) = (machine B prep verify false).step^[j + 1]
          (lift S₁ B verify (cfg (input := input) B none w pos))) ∧
    (machine B prep verify false).step^[pos + 2 + t]
      (lift S₁ B verify (cfg (input := input) B none w pos)) =
      rightCfg (rightCfg (rightCfg (verify.runFrom (wordsCfg input (some verify.q₀)
        (Function.update (fun _ => []) B w) []) t))) := by
  have hstart : lift S₁ B verify (cfg (input := input) B none w pos) =
      rightCfg (rightCfg ((cfg (input := input) (State := GuessState) B none w pos).withState
        (some (rewindVerify B verify).q₀))) := by
    rw [lift, leftCfg_of_halt rfl]
  have hend := runFrom_lift_none (S₁ := S₁) (prep := prep) hpos hfin false
  rw [hstart] at hend ⊢
  exact ⟨fun j _ b => next_iterate_rightCfg _ j b, hend⟩

/-- **The verifying phase.** After the guessing phase, with the word `w` on tape `B`, if `verify`
halts within `t` steps on `w`, the machine accepts within `pos + 2 + t` moves exactly when the
output of `verify` is `[true]`. -/
theorem acceptsWithin_lift_none {w : List Bool} {pos t : ℕ} (hpos : pos ≤ w.length)
    (hfin : (verify.runFrom (wordsCfg input (some verify.q₀) (Function.update (fun _ => []) B w)
      []) t).state = none) :
    (guessVerify B prep verify).AcceptsWithin (pos + 2 + t)
      (lift S₁ B verify (cfg (input := input) B none w pos)) ↔
      (verify.runFrom (wordsCfg input (some verify.q₀) (Function.update (fun _ => []) B w)
        []) t).output = [true] := by
  obtain ⟨hdet, hend⟩ := iterate_lift_none (prep := prep) hpos hfin
  rw [← add_zero (pos + 2 + t), acceptsWithin_add_iff_of_next_eq hdet, hend,
    acceptsWithin_of_halted _ (by simp [rightCfg, Cfg.mapState, hfin])]
  rfl

/-- **The verifying phase halts.** After the guessing phase, with the word `w` on tape `B`, if
`verify` halts within `t` steps on `w`, every list of `pos + 2 + t` moves reaches a halted
configuration. -/
theorem haltsWithin_lift_none {w : List Bool} {pos t : ℕ} (hpos : pos ≤ w.length)
    (hfin : (verify.runFrom (wordsCfg input (some verify.q₀) (Function.update (fun _ => []) B w)
      []) t).state = none) :
    (guessVerify B prep verify).HaltsWithin (pos + 2 + t)
      (lift S₁ B verify (cfg (input := input) B none w pos)) := by
  obtain ⟨hdet, hend⟩ := iterate_lift_none (prep := prep) hpos hfin
  rw [← add_zero (pos + 2 + t), haltsWithin_add_iff_of_next_eq hdet, hend, haltsWithin_zero]
  simp [rightCfg, Cfg.mapState, hfin]

/-- **The preparing phase.** If `prep` halts at step `u` with the word `w` on tape `B` and every
other work tape blank, then from the initial configuration the machine reaches the start of the
guessing phase in `u` moves that do not matter. -/
theorem prepare_spec {w : List Bool} {u : ℕ} (hu : prep.HaltsAt (Cfg.init prep.q₀ input) u)
    (hprep : prep.runFrom (Cfg.init prep.q₀ input) u =
      wordsCfg input none (Function.update (fun _ => []) B w) []) :
    (∀ j < u, ∀ b, (guessVerify B prep verify).next b
      ((machine B prep verify false).step^[j]
        ((guessVerify B prep verify).toPTM.toNTM.initCfg input)) =
      (machine B prep verify false).step^[j + 1]
        ((guessVerify B prep verify).toPTM.toNTM.initCfg input)) ∧
    (machine B prep verify false).step^[u]
      ((guessVerify B prep verify).toPTM.toNTM.initCfg input) =
      lift S₁ B verify (cfg (input := input) B (some (.tag false)) w 0) := by
  have hinit : (guessVerify B prep verify).toPTM.toNTM.initCfg input =
      leftCfg ((guess B false).seq (rewindVerify B verify)) (Cfg.init prep.q₀ input) :=
    rfl
  rw [hinit]
  refine ⟨fun j hj b => ?_, ?_⟩
  · rw [guessVerify, next_ofTMs, Function.iterate_succ_apply', step_machine]
    intro v
    have hrun : (machine B prep verify false).runFrom
        (leftCfg ((guess B false).seq (rewindVerify B verify)) (Cfg.init prep.q₀ input)) j =
        leftCfg ((guess B false).seq (rewindVerify B verify))
          (prep.runFrom (Cfg.init prep.q₀ input) j) :=
      runFrom_leftCfg _ j fun m hm => hu.not_halted (by omega)
    rw [show (machine B prep verify false).step^[j] _ =
      (machine B prep verify false).runFrom _ j from rfl, hrun]
    obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp (hu.not_halted hj)
    simp only [leftCfg, Cfg.mapState, hq]
    simp
  · change (machine B prep verify false).runFrom _ (u + 0) = _
    rw [machine, hu.runFrom_seq, hprep, MultiTapeTM.runFrom, Function.iterate_zero,
      id_eq, lift, cfg_zero]
    rfl

end Phases

end GuessVerify

section Spec

open MultiTapeTM

variable {k : ℕ} {S₁ S₂ : Type} {B : Fin k} {prep : MultiTapeTM k Bool S₁}
  {verify : MultiTapeTM k Bool S₂} {input : List Bool}

/-- **The guess-then-verify machine plays the game of `L` moves.** Suppose that `prep`, started on
the input with blank work tapes, has halted after `t₁` steps with the frame of `L` bits `true`
followed by the input on tape `B` and every other work tape blank, and that `verify`, started on
the frame of any `L` moves `z` followed by the input on tape `B` and every other work tape blank,
has halted after `t₂` steps with output `[V z]`. Then for some
`T ≤ t₁ + 4 * L + 3 + t₂`, every list of `T` moves reaches a halted configuration, and the
machine accepts within `T` moves exactly when the existential player wins the game of `L`
alternate moves, the existential first, with winning condition `V`. -/
theorem guessVerify_spec {L t₁ t₂ : ℕ} {V : List Bool → Bool}
    (hprep : prep.runFrom (Cfg.init prep.q₀ input) t₁ = wordsCfg input none
      (Function.update (fun _ => []) B (frame (List.replicate L true) ++ input)) [])
    (hverify : ∀ z : List Bool, z.length = L →
      (verify.runFrom (wordsCfg input (some verify.q₀)
        (Function.update (fun _ => []) B (frame z ++ input)) []) t₂).state = none ∧
      (verify.runFrom (wordsCfg input (some verify.q₀)
        (Function.update (fun _ => []) B (frame z ++ input)) []) t₂).output = [V z]) :
    ∃ T ≤ t₁ + (4 * L + 3 + t₂),
      (guessVerify B prep verify).HaltsWithin T
        ((guessVerify B prep verify).toPTM.toNTM.initCfg input) ∧
      ((guessVerify B prep verify).AcceptsWithin T
        ((guessVerify B prep verify).toPTM.toNTM.initCfg input) ↔
        Cslib.Complexity.Alternation true (List.replicate L 1) fun z => V z = true) := by
  obtain ⟨u, hut, hu⟩ := exists_haltsAt (tm := prep) (cfg := Cfg.init prep.q₀ input)
    (t := t₁) (by rw [hprep]; rfl)
  obtain ⟨hdet, hstart⟩ := GuessVerify.prepare_spec (S₁ := S₁) (verify := verify) hu
    ((hu.runFrom_eq hut).symm.trans hprep)
  have hguess (zd : List Bool) (hzd : zd = []) (pos : ℕ) (hpos : pos = 2 * zd.length) :
      GuessVerify.cfg (input := input) (State := GuessState) B (some (.tag false))
        (frame (List.replicate L true) ++ input) 0 =
      GuessVerify.cfg B (some (.tag false)) (frame (zd ++ List.replicate L true) ++ input) pos := by
    subst hzd hpos
    rfl
  have hpos (z : List Bool) : 2 * ([] ++ z).length ≤ (frame z ++ input).length := by
    simpa using two_mul_length_le_length_frame_append z input
  refine ⟨u + (2 * L + 1 + (2 * L + 2 + t₂)), by omega, ?_, ?_⟩
  · rw [haltsWithin_add_iff_of_next_eq hdet, hstart, hguess [] rfl _ rfl,
      GuessVerify.haltsWithin_lift_tag]
    intro z hz
    have := GuessVerify.haltsWithin_lift_none (S₁ := S₁) (prep := prep) (hpos z)
      (hverify z hz).1
    simp only [List.nil_append, List.length_nil, zero_add] at this ⊢
    rwa [hz] at this
  · rw [acceptsWithin_add_iff_of_next_eq hdet, hstart, hguess [] rfl _ rfl,
      GuessVerify.acceptsWithin_lift_tag, Bool.not_false]
    refine Cslib.Complexity.alternation_congr_of_length fun z hz => ?_
    rw [Cslib.Complexity.sum_replicate_one] at hz
    have := GuessVerify.acceptsWithin_lift_none (S₁ := S₁) (prep := prep) (hpos z)
      (hverify z hz).1
    simp only [List.nil_append, List.length_nil, zero_add, hz] at this ⊢
    rw [this, (hverify z hz).2]
    simp

end Spec

end MultiTapeATM

end Turing

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

/-- The embedding of `Fin m` into `Fin K` that places `j` at `B`. -/
private def placeAt {m K : ℕ} (h : m ≤ K) (j : Fin m) (B : Fin K) : Fin m ↪ Fin K :=
  (Fin.castLEEmb h).trans (Equiv.swap (Fin.castLE h j) B).toEmbedding

private theorem placeAt_self {m K : ℕ} (h : m ≤ K) (j : Fin m) (B : Fin K) :
    placeAt h j B j = B := by
  simp [placeAt]

variable {α : Type} {enc : α ↪ List Bool} {p : Polynomial ℕ} {V : α × List Bool → Bool}
  {A : Set α}

/-- **Games of polynomially many moves are in `AP`** [Chandra, Kozen and
Stockmeyer][ChandraKozenStockmeyer1981]: a problem with a polynomial-time game verifier is decided
in polynomial time by the guess-then-verify machine, which writes the moves of the two players,
alternately, and then runs the verifier. -/
theorem IsGameVerifier.mem_AP (hV : ComputableTidilyInPolyTime V (encPair enc encBits) encBool)
    (h : IsGameVerifier enc p V A) : A ∈ AP enc := by
  -- the number of moves, and the word prepared on tape `B`
  set L : α → ℕ := fun a => 2 * p.eval (enc a).length
  have hL : ComputableTidilyInPolyTime L enc encUnary :=
    ComputableTidilyInPolyTime.unary_mul.comp ((ComputableTidilyInPolyTime.const 2).prod
      ((ComputableTidilyInPolyTime.unary_eval p).comp
        (ComputableTidilyInPolyTime.encoding_length enc)))
  set g : α → List Bool := fun a => frame (List.replicate (L a) true) ++ enc a with hg_def
  have hg : ComputableTidilyInPolyTime g enc encBits :=
    (((ComputableTidilyInPolyTime.bitsReplicate true).comp hL).prod
      (ComputableTidilyInPolyTime.of_eq (encMid := enc) fun _ => rfl)).encoded
  have hLb : PolyBounded (fun a => (enc a).length) L := hL.polyBounded
  have hgl : PolyBounded (fun a => (enc a).length) fun a => (g a).length :=
    hg.polyBounded_length
  have hV' : ComputableTidilyInPolyTime (fun x : List Bool × α => V (x.2, x.1))
      (encPair encBits enc) encBool :=
    hV.comp ((ComputableTidilyInPolyTime.snd encBits enc).prod
      (ComputableTidilyInPolyTime.fst encBits enc))
  obtain ⟨tg, sg, htg, -, k₁, S₁, _, Tg, hTg⟩ := hg
  obtain ⟨tv, sv, htv, -, k₂, S₂, _, Tv, hTv⟩ := hV'
  obtain ⟨cv, dv, htv⟩ := htv.exists_le
  -- the machine
  have hk₁ : k₁ + 1 ≤ k₁ + 1 + (k₂ + 2) := by omega
  have hk₂ : k₂ + 2 ≤ k₁ + 1 + (k₂ + 2) := by omega
  let B : Fin (k₁ + 1 + (k₂ + 2)) := ⟨0, by omega⟩
  let prep := Tg.outputToWord.extendTapes (placeAt hk₁ (Fin.last k₁) B)
  let verify := (Tv.inputFromWord true).extendTapes (placeAt hk₂ (Fin.natAdd k₂ 0) B)
  -- the time bound
  let t₂ : α → ℕ := fun a => cv * ((g a).length + 1) ^ dv + 4
  let t : α → ℕ := fun a => tg a + (g a).length + 2 + (4 * L a + 3 + t₂ a)
  have hprep (a : α) : prep.runFrom (Cfg.init prep.q₀ (enc a)) (tg a + (g a).length + 2) =
      wordsCfg (enc a) none (Function.update (fun _ => []) B
        (frame (List.replicate (L a) true) ++ enc a)) [] := by
    obtain ⟨ws, em, hrun, ⟨rfl, rfl⟩, -⟩ := transformsTapes_iff_runFrom.mp
      ((hTg a).outputToWord_onTape (placeAt_self hk₁ (Fin.last k₁) B)) (enc a) (fun _ => [])
      [] ⟨rfl, rfl⟩
    rw [Cfg.init_eq_wordsCfg]
    exact hrun
  have hverify (a : α) (z : List Bool) (hz : z.length = L a) :
      (verify.runFrom (wordsCfg (enc a) (some verify.q₀)
        (Function.update (fun _ => []) B (frame z ++ enc a)) []) (t₂ a)).state = none ∧
      (verify.runFrom (wordsCfg (enc a) (some verify.q₀)
        (Function.update (fun _ => []) B (frame z ++ enc a)) []) (t₂ a)).output = [V (a, z)] := by
    have hlen : (encPair encBits enc (z, a)).length = (g a).length := by
      simp [hg_def, hz]
    obtain ⟨ws, em, hrun, ⟨rfl, rfl⟩, -⟩ := transformsTapes_iff_runFrom.mp
      (((hTv (z, a)).inputFromWord_extendTapes true
        (placeAt_self hk₂ (Fin.natAdd k₂ 0) B)).mono
        (Nat.add_le_add_right ((htv (z, a)).trans_eq (by rw [hlen])) 4) le_rfl)
      (enc a) _ [] rfl
    have hrun' : verify.runFrom (wordsCfg (enc a) (some verify.q₀)
        (Function.update (fun _ => []) B (frame z ++ enc a)) []) (t₂ a) = _ := hrun
    rw [hrun']
    exact ⟨rfl, rfl⟩
  have hspec (a : α) := MultiTapeATM.guessVerify_spec (hprep a) (hverify a)
  refine ⟨t, ?_, k₁ + 1 + (k₂ + 2), _, inferInstance, MultiTapeATM.guessVerify B prep verify,
    fun a => ?_⟩
  · have hpow : PolyBounded (fun a => (enc a).length) fun a => cv * ((g a).length + 1) ^ dv :=
      (PolyBounded.of_forall_le (size := id) cv dv fun _ => le_rfl).comp hgl
    exact ((htg.add hgl).add (.const 2)).add ((((PolyBounded.const 4).mul hLb).add
      (.const 3)).add (hpow.add (.const 4)))
  · obtain ⟨T, hT, hhalt, hacc⟩ := hspec a
    have hrun : (MultiTapeATM.guessVerify B prep verify).toPTM.toNTM.RunsInTime (enc a) T :=
      MultiTapeATM.runsInTime_iff_haltsWithin.mpr hhalt
    refine ⟨hrun.mono hT, ?_⟩
    rw [h a, MultiTapeATM.accepts_iff_acceptsWithin hrun, hacc]

end Cslib.Complexity
