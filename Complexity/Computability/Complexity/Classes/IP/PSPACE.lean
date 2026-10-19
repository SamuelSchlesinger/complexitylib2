/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.IP.GameTree
public import Complexity.Computability.Complexity.Classes.IP.Simulation
public import Complexity.Computability.Complexity.Classes.Space
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatPower

/-!
# `IP ⊆ PSPACE`

-/

@[expose] public section

namespace Cslib.Complexity.Interaction

open Finset

/-! ### Enumerating the short words -/

/-- The word coded by `u`: what follows its first `true`. -/
def decodeWord (u : List Bool) : List Bool := u.drop (u.idxOf true + 1)

/-- The code of a word `w` of length at most `L` among the words of length `L + 1`: `L - |w|`
zeros, a one, then `w`. -/
def encodeWord (L : ℕ) (w : List Bool) : List Bool :=
  List.replicate (L - w.length) false ++ true :: w

theorem idxOf_true_replicate_false_append (n : ℕ) (w : List Bool) :
    (List.replicate n false ++ true :: w).idxOf true = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, List.idxOf_cons_ne _ (by simp), ih]

theorem decodeWord_encodeWord (L : ℕ) (w : List Bool) : decodeWord (encodeWord L w) = w := by
  rw [decodeWord, encodeWord, idxOf_true_replicate_false_append, List.drop_append]
  simp

theorem length_encodeWord {L : ℕ} {w : List Bool} (hw : w.length ≤ L) :
    (encodeWord L w).length = L + 1 := by
  simp [encodeWord]
  lia

theorem true_mem_encodeWord (L : ℕ) (w : List Bool) : true ∈ encodeWord L w := by
  simp [encodeWord]

theorem length_decodeWord_le {L : ℕ} {u : List Bool} (hu : u.length = L + 1) :
    (decodeWord u).length ≤ L := by
  simp [decodeWord]
  lia

/-- A word with a `true` is its first `true` preceded by zeros and followed by its decoding. -/
theorem eq_replicate_append_decodeWord : ∀ {u : List Bool}, true ∈ u →
    u = List.replicate (u.idxOf true) false ++ true :: decodeWord u
  | b :: u, h => by
    cases b
    · have hu : true ∈ u := by simpa using h
      rw [decodeWord, List.idxOf_cons_ne _ (by simp)]
      have := eq_replicate_append_decodeWord hu
      rw [decodeWord] at this
      simp only [List.replicate_succ, List.cons_append, List.drop_succ_cons]
      exact congrArg _ this
    · simp [decodeWord]

theorem encodeWord_decodeWord {L : ℕ} {u : List Bool} (hu : u.length = L + 1) (ht : true ∈ u) :
    encodeWord L (decodeWord u) = u := by
  have h := eq_replicate_append_decodeWord ht
  have hlen := congrArg List.length h
  simp only [List.length_append, List.length_replicate, List.length_cons, hu] at hlen
  rw [encodeWord, show L - (decodeWord u).length = u.idxOf true by lia]
  exact h.symm

/-- A word with a `true` has a positive value. -/
theorem lsbValue_pos_of_true_mem : ∀ {u : List Bool}, true ∈ u → 0 < lsbValue u
  | b :: u, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp [lsbValue]
    · have := lsbValue_pos_of_true_mem h
      simp [lsbValue]
      lia

/-- A word without `true` has value `0`. -/
theorem lsbValue_eq_zero_of_true_not_mem : ∀ {u : List Bool}, true ∉ u → lsbValue u = 0
  | [], _ => rfl
  | b :: u, h => by
    simp only [List.mem_cons, not_or] at h
    have hb : b = false := by simpa using h.1
    subst hb
    simp [lsbValue, lsbValue_eq_zero_of_true_not_mem h.2]

variable (L : ℕ)

/-- The first code, `1` in binary. -/
def firstCode : List Bool := true :: List.replicate L false

/-- Whether a code is the last one, all ones. -/
def lastCode (u : List Bool) : Bool := decide (u = List.replicate (L + 1) true)

/-- The number of codes, and of the words of length at most `L`. -/
def codeCount : ℕ := 2 ^ (L + 1) - 1

theorem iterate_firstCode (i : ℕ) :
    incrementBits^[i] (firstCode L) = incrementBits^[i + 1] (List.replicate (L + 1) false) := by
  rw [Function.iterate_succ_apply]
  rfl

variable {L}

theorem lsbValue_iterate_firstCode {i : ℕ} (hi : i < codeCount L) :
    lsbValue (incrementBits^[i] (firstCode L)) = i + 1 ∧
      (incrementBits^[i] (firstCode L)).length = L + 1 := by
  rw [iterate_firstCode]
  exact iterate_incrementBits (L + 1) (i + 1) (by simp [codeCount] at hi; lia)

theorem lastCode_iterate_firstCode {i : ℕ} (hi : i < codeCount L) :
    lastCode L (incrementBits^[i] (firstCode L)) = decide (i + 1 = codeCount L) := by
  obtain ⟨hv, hl⟩ := lsbValue_iterate_firstCode hi
  have hall := lsbValue_replicate_true (L + 1)
  simp only [lastCode, decide_eq_decide]
  constructor
  · intro h
    rw [h] at hv
    simp only [codeCount]
    lia
  · intro h
    refine lsbValue_injective (by simp [hl]) ?_
    simp only [codeCount] at h
    lia

theorem true_mem_iterate_firstCode {i : ℕ} (hi : i < codeCount L) :
    true ∈ incrementBits^[i] (firstCode L) := by
  by_contra h
  have := lsbValue_eq_zero_of_true_not_mem h
  rw [(lsbValue_iterate_firstCode hi).1] at this
  lia

/-- **The codes enumerate the short words**: decoding the first `codeCount L` codes gives every word
of length at most `L` exactly once. -/
theorem image_decodeWord_iterate_firstCode :
    (range (codeCount L)).image (fun i => decodeWord (incrementBits^[i] (firstCode L))) =
      shortWords L := by
  ext w
  simp only [mem_image, mem_range, mem_shortWords]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact length_decodeWord_le (lsbValue_iterate_firstCode hi).2
  · intro hw
    have hlen := length_encodeWord hw
    have hpos := lsbValue_pos_of_true_mem (true_mem_encodeWord L w)
    have hlt := lsbValue_lt (encodeWord L w)
    rw [hlen] at hlt
    refine ⟨lsbValue (encodeWord L w) - 1, by simp [codeCount]; lia, ?_⟩
    rw [iterate_firstCode, Nat.sub_add_cancel hpos, ← hlen, iterate_incrementBits_lsbValue,
      decodeWord_encodeWord]

theorem injOn_decodeWord_iterate_firstCode :
    Set.InjOn (fun i => decodeWord (incrementBits^[i] (firstCode L))) (range (codeCount L)) := by
  intro i hi j hj h
  simp only [coe_range, Set.mem_Iio] at hi hj
  have hu := encodeWord_decodeWord (lsbValue_iterate_firstCode hi).2 (true_mem_iterate_firstCode hi)
  have hv := encodeWord_decodeWord (lsbValue_iterate_firstCode hj).2 (true_mem_iterate_firstCode hj)
  simp only at h
  have := congrArg lsbValue (hu.symm.trans ((congrArg (encodeWord L) h).trans hv))
  rw [(lsbValue_iterate_firstCode hi).1, (lsbValue_iterate_firstCode hj).1] at this
  lia

/-! ### The value as a game tree -/

section GameTree

variable {R : Type} [Fintype R] (F : R → WordQueryComp Unit Bool)

/-- The history coded by a game-tree history of codes, the most recent first. -/
def decodeHistory (hs : List (List Bool × List Bool)) : History :=
  (hs.map fun p => (decodeWord p.1, decodeWord p.2)).reverse

@[simp] theorem decodeHistory_nil : decodeHistory [] = [] := rfl

@[simp] theorem decodeHistory_cons (p : List Bool × List Bool) (hs : List (List Bool × List Bool)) :
    decodeHistory (p :: hs) = decodeHistory hs ++ [(decodeWord p.1, decodeWord p.2)] := by
  simp [decodeHistory]

/-- The leaf value of a game-tree history: the number of accepting programs. -/
noncomputable def leafValue (hs : List (List Bool × List Bool)) : ℕ :=
  accepted F (decodeHistory hs)

/-- **The value is the value of the game tree** of the codes of the short words, with sums capped
at a bound on the number of coin values. -/
theorem gameTree_value_eq {cap : ℕ} (hcap : Fintype.card R ≤ cap) (n : ℕ)
    (hs : List (List Bool × List Bool)) :
    GameTree.value (codeCount L) cap (firstCode L) incrementBits (leafValue F) n hs =
      value F L n (decodeHistory hs) := by
  have hle (n : ℕ) (h : History) : value F L n h ≤ cap :=
    (value_le_card n h).trans ((Finset.card_le_univ _).trans hcap)
  induction n generalizing hs with
  | zero => exact min_eq_right (hle 0 _)
  | succ n ih =>
    rw [GameTree.value, ← min_eq_right (hle (n + 1) (decodeHistory hs)), value]
    congr 2
    simp only [ih, decodeHistory_cons]
    have hsup (m : List Bool) : ((range (codeCount L)).sup fun j =>
        value F L n (decodeHistory hs ++ [(m, decodeWord (incrementBits^[j] (firstCode L)))])) =
        (shortWords L).sup fun y => value F L n (decodeHistory hs ++ [(m, y)]) := by
      rw [← image_decodeWord_iterate_firstCode, Finset.sup_image]
      rfl
    simp only [hsup]
    rw [← image_decodeWord_iterate_firstCode,
      Finset.sum_image injOn_decodeWord_iterate_firstCode]

end GameTree

/-! ### Polynomial-time parts -/

section PolyTime

open _root_.Turing _root_.Turing.MultiTapeTM ComputableTidilyInPolyTime

/-- Decoding a word is polynomial-time. -/
theorem computableTidilyInPolyTime_decodeWord :
    ComputableTidilyInPolyTime decodeWord encBits encBits := by
  have hidx : ComputableTidilyInPolyTime (fun u : List Bool => u.idxOf true + 1) encBits
      encUnary := by
    have h := (idxOf encBool).comp (bitsToList.prod (const (encMid := encBool) true))
    have hsucc : ComputableTidilyInPolyTime (· + 1) encUnary encUnary :=
      ComputableTidilyInDegree.unary_succ.computableTidilyInPolyTime
    exact hsucc.comp h
  exact bitsDropWithInput id' hidx

/-- Decoding a history is polynomial-time. -/
theorem computableTidilyInPolyTime_decodeHistory :
    ComputableTidilyInPolyTime decodeHistory (encList (encPair encBits encBits)) encHistory := by
  have hd := computableTidilyInPolyTime_decodeWord
  unfold decodeHistory
  fun_prop

end PolyTime

/-! ### The evaluation -/

section Evaluation

variable {α : Type} (enc : α ↪ List Bool) {k : ℕ} {Control : Type}
  (M : _root_.Turing.MultiTapePTM k Bool Control Unit) (fuel : α → ℕ)

/-- The states of the evaluation: the instance, the stack and the value being returned. -/
abbrev EvalState (α : Type) := α × List (GameTree.Frame (List Bool)) × Option ℕ

/-- One step of the evaluation of the game tree of the verifier `M` on `a`, with `fuel a` coins,
rounds and message lengths. -/
noncomputable def evalStep (s : EvalState α) : EvalState α :=
  (s.1, GameTree.step (fuel s.1) (2 ^ fuel s.1) (firstCode (fuel s.1)) incrementBits
    (lastCode (fuel s.1)) (leafValue (coinFamily M (fuel s.1) (enc s.1))) s.2)

/-- The number of steps of the evaluation, a bound on `GameTree.time`. -/
def evalTime (a : α) : ℕ := 2 ^ ((fuel a + 1) * (2 * fuel a + 1))

/-- The value computed by the evaluation. -/
noncomputable def evaluate (a : α) : ℕ :=
  ((evalStep enc M fuel)^[evalTime fuel a] (a, [], none)).2.2.getD 0

theorem iterate_evalStep (a : α) (st : List (GameTree.Frame (List Bool)) × Option ℕ) (j : ℕ) :
    (evalStep enc M fuel)^[j] (a, st) = (a, (GameTree.step (fuel a) (2 ^ fuel a)
      (firstCode (fuel a)) incrementBits (lastCode (fuel a))
        (leafValue (coinFamily M (fuel a) (enc a))))^[j] st) := by
  induction j generalizing st with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← ih]; rfl

/-- **The evaluation computes the value** of the verifier on `a`. -/
theorem evaluate_eq (a : α) :
    evaluate enc M fuel a = value (coinFamily M (fuel a) (enc a)) (fuel a) (fuel a) [] := by
  have hN : 0 < codeCount (fuel a) := by
    simp only [codeCount]
    have := Nat.one_lt_two_pow (n := fuel a + 1) (by lia)
    lia
  have htime : GameTree.time (codeCount (fuel a)) (fuel a) ≤ evalTime fuel a := by
    refine (GameTree.time_le _).trans (le_of_eq ?_)
    rw [evalTime, codeCount, Nat.sub_add_cancel (Nat.one_le_two_pow), ← pow_mul]
  rw [evaluate, iterate_evalStep, GameTree.iterate_step_eval hN
    (fun i hi => lastCode_iterate_firstCode hi) htime]
  simp only [Option.getD_some]
  rw [gameTree_value_eq _ (by simp), decodeHistory_nil]

end Evaluation

end Cslib.Complexity.Interaction
