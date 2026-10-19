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
import Complexity.Computability.Complexity.Classes.Oracle.Space
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

@[simp] theorem decodeHistory_cons (p : List Bool × List Bool)
    (hs : List (List Bool × List Bool)) :
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

/-- Returning a value into the stack, with its explicit cases. -/
def returnStep (L cap : ℕ) (st : List (GameTree.Frame (List Bool))) (v : ℕ) :
    List (GameTree.Frame (List Bool)) × Option ℕ :=
  if st.isEmpty then (st, some v)
  else
    let f := st.headD ([], [], 0, 0)
    if lastCode L f.2.1 then
      if lastCode L f.1 then (st.tail, some (min cap (f.2.2.1 + max f.2.2.2 v)))
      else ((incrementBits f.1, firstCode L, min cap (f.2.2.1 + max f.2.2.2 v), 0) :: st.tail, none)
    else ((f.1, incrementBits f.2.1, f.2.2.1, max f.2.2.2 v) :: st.tail, none)

theorem step_some_eq (L cap : ℕ) (leaf : List (List Bool × List Bool) → ℕ)
    (st : List (GameTree.Frame (List Bool))) (v : ℕ) :
    GameTree.step L cap (firstCode L) incrementBits (lastCode L) leaf (st, some v) =
      returnStep L cap st v := by
  rcases st with _ | ⟨⟨u, w, sm, ac⟩, st⟩
  · rfl
  · rfl

/-- Pushing a frame, or returning the leaf value at the maximal depth. -/
def pushStep (L : ℕ) (st : List (GameTree.Frame (List Bool))) (v : ℕ) :
    List (GameTree.Frame (List Bool)) × Option ℕ :=
  if st.length = L then (st, some v) else ((firstCode L, firstCode L, v, 0) :: st, none)

theorem step_none_eq (L cap : ℕ) (leaf : List (List Bool × List Bool) → ℕ)
    (st : List (GameTree.Frame (List Bool))) :
    GameTree.step L cap (firstCode L) incrementBits (lastCode L) leaf (st, none) =
      pushStep L st (min cap (leaf (GameTree.history st))) := rfl

/-- One step of the evaluation, as a case distinction calling the leaf value once. -/
theorem evalStep_eq (s : EvalState α) : evalStep enc M fuel s =
    if s.2.2.isSome then (s.1, returnStep (fuel s.1) (2 ^ fuel s.1) s.2.1 (s.2.2.getD 0))
    else (s.1, pushStep (fuel s.1) s.2.1 (min (2 ^ fuel s.1)
      (leafValue (coinFamily M (fuel s.1) (enc s.1)) (GameTree.history s.2.1)))) := by
  obtain ⟨a, st, _ | v⟩ := s
  · rfl
  · exact congrArg _ (step_some_eq _ _ _ st v)

end Evaluation

/-! ### The evaluation in polynomial space -/

section Space

open _root_.Turing _root_.Turing.MultiTapeTM ComputableTidilyInPolyTime

variable {γ : Type} {input : γ ↪ List Bool}

@[local fun_prop] private theorem max_pt {left right : γ → ℕ}
    (hl : ComputableTidilyInPolyTime left input encNat)
    (hr : ComputableTidilyInPolyTime right input encNat) :
    ComputableTidilyInPolyTime (fun x => max (left x) (right x)) input encNat := by
  simp only [max_def]
  exact ite_decide (binary_le' hl hr) hr hl

@[local fun_prop] private theorem min_pt {left right : γ → ℕ}
    (hl : ComputableTidilyInPolyTime left input encNat)
    (hr : ComputableTidilyInPolyTime right input encNat) :
    ComputableTidilyInPolyTime (fun x => min (left x) (right x)) input encNat := by
  simp only [min_def]
  exact ite_decide (binary_le' hl hr) hl hr

@[local fun_prop] private theorem twoPow_pt {count : γ → ℕ}
    (h : ComputableTidilyInPolyTime count input encUnary) :
    ComputableTidilyInPolyTime (fun x => 2 ^ count x) input encNat :=
  ((ComputableTidilyInDegree.two_pow_length encUnary).computableTidilyInPolyTime.comp h).of_enc_eq
    fun x => by simp [encUnary_apply]

@[local fun_prop] private theorem firstCode_pt {count : γ → ℕ}
    (h : ComputableTidilyInPolyTime count input encUnary) :
    ComputableTidilyInPolyTime (fun x => firstCode (count x)) input encBits :=
  bitsCons (const true) ((bitsReplicate false).comp h)

@[local fun_prop] private theorem lastCode_pt {count : γ → ℕ} {word : γ → List Bool}
    (h : ComputableTidilyInPolyTime count input encUnary)
    (hword : ComputableTidilyInPolyTime word input encBits) :
    ComputableTidilyInPolyTime (fun x => lastCode (count x) (word x)) input encBool := by
  have hsucc : ComputableTidilyInPolyTime (· + 1) encUnary encUnary :=
    ComputableTidilyInDegree.unary_succ.computableTidilyInPolyTime
  exact decide_eq' hword ((bitsReplicate true).comp (hsucc.comp h))

@[local fun_prop] private theorem incrementBits_pt {word : γ → List Bool}
    (hword : ComputableTidilyInPolyTime word input encBits) :
    ComputableTidilyInPolyTime (fun x => incrementBits (word x)) input encBits :=
  computableTidilyInPolyTime_incrementBits.comp hword

variable {α : Type} (enc : α ↪ List Bool) {k : ℕ} {Control : Type}
  (M : _root_.Turing.MultiTapePTM k Bool Control Unit) (fuel : α → ℕ)

/-- Frames, encoded by their fields. -/
noncomputable abbrev encFrame : GameTree.Frame (List Bool) ↪ List Bool :=
  encPair encBits (encPair encBits (encPair encNat encNat))

/-- States of the evaluation, encoded by their fields. -/
noncomputable abbrev encEvalState : EvalState α ↪ List Bool :=
  encPair enc (encPair (encList encFrame) (encOption encNat))

variable {enc fuel} (hfuel : ComputableTidilyInPolyTime fuel enc encUnary)
include hfuel

theorem computableTidilyInPolyTime_returnStep :
    ComputableTidilyInPolyTime (fun s : EvalState α =>
      (s.1, returnStep (fuel s.1) (2 ^ fuel s.1) s.2.1 (s.2.2.getD 0)))
      (encEvalState enc) (encEvalState enc) := by
  have hfuel' : ComputableTidilyInPolyTime (fun s : EvalState α => fuel s.1) (encEvalState enc)
      encUnary := hfuel.comp (fst _ _)
  unfold returnStep
  fun_prop

theorem computableTidilyInPolyTime_pushStep :
    ComputableTidilyInPolyTime (fun p : EvalState α × ℕ =>
      (p.1.1, pushStep (fuel p.1.1) p.1.2.1 p.2))
      (encPair (encEvalState enc) encNat) (encEvalState enc) := by
  have hfuel' : ComputableTidilyInPolyTime (fun p : EvalState α × ℕ => fuel p.1.1)
      (encPair (encEvalState enc) encNat) encUnary := hfuel.comp (by fun_prop)
  unfold pushStep
  fun_prop

/-- **The leaf value within polynomial space**: the count of accepting coins, capped. -/
theorem computableTidilyInPolySpace_leaf [Finite Control] [Inhabited α] :
    ComputableTidilyInPolySpace (fun s : EvalState α => min (2 ^ fuel s.1)
      (leafValue (coinFamily M (fuel s.1) (enc s.1)) (GameTree.history s.2.1)))
      (encEvalState enc) encNat := by
  have hcount := computableTidilyInPolySpace_countAccepts M enc fuel hfuel
  have hdec := computableTidilyInPolyTime_decodeHistory
  have harg : ComputableTidilyInPolyTime (fun s : EvalState α =>
      (s.1, decodeHistory (GameTree.history s.2.1))) (encEvalState enc)
      (encPair enc encHistory) := by
    unfold GameTree.history
    fun_prop
  have hcap : ComputableTidilyInPolyTime (fun s : EvalState α => 2 ^ fuel s.1)
      (encEvalState enc) encNat := twoPow_pt (hfuel.comp (fst _ _))
  have hmin : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => min p.1 p.2) (encPair encNat encNat)
      encNat := by fun_prop
  refine ((ComputableTidilyInPolySpace.of_polyTime hmin).comp
    ((ComputableTidilyInPolySpace.of_polyTime hcap).prod (hcount.comp
      (ComputableTidilyInPolySpace.of_polyTime harg)))).congr fun s => ?_
  simp only [leafValue, countAccepts_eq_accepted]

/-- **A step of the evaluation within polynomial space.** -/
theorem computableTidilyInPolySpace_evalStep [Finite Control] [Inhabited α] :
    ComputableTidilyInPolySpace (evalStep enc M fuel) (encEvalState enc) (encEvalState enc) := by
  have hcond : ComputableTidilyInPolyTime (fun s : EvalState α => s.2.2.isSome)
      (encEvalState enc) encBool := by fun_prop
  refine (ComputableTidilyInPolySpace.ite (.of_polyTime hcond)
    (.of_polyTime (computableTidilyInPolyTime_returnStep hfuel))
    ((ComputableTidilyInPolySpace.of_polyTime (computableTidilyInPolyTime_pushStep hfuel)).comp
      ((ComputableTidilyInPolySpace.of_polyTime id').prod
        (computableTidilyInPolySpace_leaf M hfuel)))).congr fun s => ?_
  rw [evalStep_eq]

omit hfuel in
/-- A number at most `2 ^ L` has a binary encoding of length at most `L + 1`. -/
private theorem length_encNat_le {m L : ℕ} (h : m ≤ 2 ^ L) : (encNat m).length ≤ L + 1 := by
  rw [encNat_apply, Nat.size_eq_bits_len]
  exact Nat.size_le.mpr (h.trans_lt (Nat.pow_lt_pow_right (by norm_num) (by lia)))

omit hfuel in
/-- **The states of the evaluation are of polynomial size.** -/
theorem length_encEvalState_iterate_le (a : α) (j : ℕ) :
    (encEvalState enc ((evalStep enc M fuel)^[j] (a, [], none))).length ≤
      2 * (enc a).length + 2 * fuel a * (14 * fuel a + 21) + fuel a + 4 := by
  rw [iterate_evalStep]
  have hgood := GameTree.good_iterate_step (D := fuel a) (cap := 2 ^ fuel a)
    (first := firstCode (fuel a)) (next := incrementBits) (last := lastCode (fuel a))
    (leaf := leafValue (coinFamily M (fuel a) (enc a)))
    (P := fun u => u.length = fuel a + 1) (by simp [firstCode])
    (fun u hu => by simpa using hu) j
  set st := (GameTree.step (fuel a) (2 ^ fuel a) (firstCode (fuel a)) incrementBits
    (lastCode (fuel a)) (leafValue (coinFamily M (fuel a) (enc a))))^[j] ([], none)
  have hframe : ∀ f ∈ st.1, (encFrame f).length ≤ 7 * fuel a + 10 := by
    intro f hf
    obtain ⟨hu, hw, hs, ha⟩ := hgood.frames f hf
    have hs' := length_encNat_le hs
    have ha' := length_encNat_le ha
    simp only [encFrame, length_encPair, encBits_apply, hu, hw] at hs' ha' ⊢
    lia
  have hlist := length_encList_le encFrame st.1 hframe
  have hdepth := Nat.mul_le_mul_right (2 * (7 * fuel a + 10) + 1) hgood.length
  have hret : (encOption encNat st.2).length ≤ fuel a + 2 := by
    rcases hst : st.2 with _ | v
    · simp
    · have := length_encNat_le (hgood.value v hst)
      simp only [encOption_some, List.length_cons]
      lia
  simp only [encEvalState, length_encPair]
  nlinarith

/-- **The evaluation within polynomial space.** -/
theorem computableTidilyInPolySpace_evaluate [Finite Control] [Inhabited α] :
    ComputableTidilyInPolySpace (evaluate enc M fuel) enc encNat := by
  have hn : ComputableTidilyInPolyTime (evalTime fuel) enc encNat := by
    have hexp : ComputableTidilyInPolyTime (fun a => (fuel a + 1) * (2 * fuel a + 1)) enc
        encUnary := by
      have h1 := unary_add.comp (hfuel.prod (const (encMid := encUnary) 1))
      have h2 := unary_add.comp ((unary_mul.comp ((const (encMid := encUnary) 2).prod hfuel)).prod
        (const (encMid := encUnary) 1))
      exact unary_mul.comp (h1.prod h2)
    exact twoPow_pt hexp
  have hinit : ComputableTidilyInPolyTime (fun a : α => ((a, [], none) : EvalState α)) enc
      (encEvalState enc) := by fun_prop
  have hlen := hfuel.polyBounded_length
  simp only [encUnary_apply, List.length_replicate] at hlen
  have hit := ComputableTidilyInPolySpace.iterate hn (.of_polyTime hinit)
    (computableTidilyInPolySpace_evalStep M hfuel)
    (B := fun a => 2 * (enc a).length + 2 * fuel a * (14 * fuel a + 21) + fuel a + 4)
    (((((PolyBounded.const 2).mul .self).add (((PolyBounded.const 2).mul hlen).mul
      (((PolyBounded.const 14).mul hlen).add (.const 21)))).add hlen).add (.const 4))
    (fun a j _ => length_encEvalState_iterate_le M a j)
  have hpost : ComputableTidilyInPolyTime (fun s : EvalState α => s.2.2.getD 0)
      (encEvalState enc) encNat := by fun_prop
  exact (ComputableTidilyInPolySpace.of_polyTime hpost).comp hit

end Space

end Cslib.Complexity.Interaction

namespace Cslib.Complexity

open Cslib.Probability Interaction _root_.Turing _root_.Turing.MultiTapeTM

private theorem natCast_div_le_natCast_div_iff {a b c d : ℕ} (hb : b ≠ 0) (hd : d ≠ 0) :
    (a : ENNReal) / b ≤ c / d ↔ a * d ≤ b * c := by
  rw [ENNReal.div_le_iff_le_mul (Or.inl (by exact_mod_cast hb)) (Or.inl (ENNReal.natCast_ne_top _)),
    ← ENNReal.mul_div_right_comm, ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hd))
      (Or.inl (ENNReal.natCast_ne_top _))]
  rw [mul_comm (c : ENNReal)]
  exact_mod_cast Iff.rfl

variable {α : Type} {enc : α ↪ List Bool} {k : ℕ} {Control : Type}

/-- **The value decides an interactive proof.** If the verifier `V` is realized, against every
stateful prover, by the run of the oracle machine `M` under the clock `fuel a`, then a member of the
problem is exactly an instance on which the value of the programs of `fuel a` coins exceeds half the
number of coin values: completeness `2 / 3` and the optimal prover give more than half, soundness
`1 / 3` and the bound on all provers give less. -/
theorem mem_iff_two_pow_lt_value {V : α → WordOracleComp Unit Bool} {A : Set α}
    {M : MultiTapePTM k Bool Control Unit} {fuel : α → ℕ}
    (hV : ∀ a (S : Type) (oracle : Unit × List Bool → StateT S PMF (List Bool)) s,
      (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (encBool <$> V a)).run s =
      (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (M.runOracle (fuel a) (enc a))).run s)
    (hA : IsInteractiveProof V A (2 / 3) (1 / 3)) (a : α) :
    a ∈ A ↔ 2 ^ fuel a < 2 * value (coinFamily M (fuel a) (enc a)) (fuel a) (fuel a) [] := by
  set t := fuel a
  set W := value (coinFamily M t (enc a)) t t []
  have hbounded := isBounded_coinProgram M t (enc a)
  have hacc (P : Prover Unit) : acceptProb (V a) P =
      (2 ^ t : ENNReal)⁻¹ * ∑ r, acceptFrom P P.init (some (coinFamily M t (enc a) r)) :=
    acceptProb_eq_sum M (hV a) P
  have hpos : 2 ^ t ≠ 0 := by positivity
  have hcast : ((2 ^ t : ℕ) : ENNReal) = 2 ^ t := by push_cast; rfl
  have hupper (P : Prover Unit) : acceptProb (V a) P ≤ (W : ENNReal) / (2 ^ t : ℕ) := by
    rw [hacc, ENNReal.div_eq_inv_mul, hcast]
    exact mul_le_mul_right (sum_acceptFrom_le_value hbounded P) _
  have hopt : acceptProb (V a) (optimalProver (coinFamily M t (enc a)) t t) =
      (W : ENNReal) / (2 ^ t : ℕ) := by
    rw [hacc, ENNReal.div_eq_inv_mul, hcast, sum_acceptFrom_optimalProver hbounded]
  constructor
  · intro ha
    obtain ⟨P, hP⟩ := hA.complete a ha
    have h := hP.trans (hupper P)
    rw [show (2 / 3 : ENNReal) = ((2 : ℕ) : ENNReal) / ((3 : ℕ) : ENNReal) by norm_num,
      natCast_div_le_natCast_div_iff (by norm_num) hpos] at h
    have := Nat.one_le_two_pow (n := t)
    lia
  · intro hlt
    by_contra ha
    have h := hopt ▸ hA.sound a ha (optimalProver _ t t)
    rw [show (1 / 3 : ENNReal) = ((1 : ℕ) : ENNReal) / ((3 : ℕ) : ENNReal) by norm_num,
      natCast_div_le_natCast_div_iff hpos (by norm_num)] at h
    lia

/-- **`IP ⊆ PSPACE`** [Arora and Barak, Theorem 8.19][AroraBarak09] [Sipser, Lemma
10.30][Sipser2013]. A problem with an interactive proof, whose verifier is strict oracle PPT, is
decided within polynomial space: by the evaluation of the optimal prover's game tree over the
messages and replies of length at most the clock, which counts the accepting coin values at every
history (`Cslib.Complexity.Interaction.evaluate`). -/
theorem IP_subset_PSPACE (enc : α ↪ List Bool) : IP enc ⊆ PSPACE enc := by
  rintro A ⟨V, hV, hA⟩
  rcases isEmpty_or_nonempty α with hα | hα
  · exact P_subset_PSPACE ⟨fun _ => false, ComputableTidilyInPolyTime.const false,
      fun a => isEmptyElim a⟩
  let _ : Inhabited α := Classical.inhabited_of_nonempty hα
  obtain ⟨_, k, Control, _, M, c, d, hreal⟩ := hV
  set fuel : α → ℕ := fun a => c * ((enc a).length + 1) ^ d
  have hfuel : ComputableTidilyInPolyTime fuel enc encUnary := by
    have hlen : ComputableTidilyInPolyTime (fun a => (enc a).length) enc encUnary := by fun_prop
    exact ((ComputableTidilyInPolyTime.unary_eval (Polynomial.C c * (Polynomial.X + 1) ^ d)).comp
      hlen).of_enc_eq fun a => by simp [fuel]
  have hdec : ComputableTidilyInPolySpace
      (fun a => decide (2 ^ fuel a < 2 * evaluate enc M fuel a)) enc encBool := by
    have hcap : ComputableTidilyInPolyTime (fun a => 2 ^ fuel a) enc encNat :=
      ((ComputableTidilyInDegree.two_pow_length encUnary).computableTidilyInPolyTime.comp
        hfuel).of_enc_eq fun a => by simp [encUnary_apply]
    have hpost : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => decide (p.1 < 2 * p.2))
        (encPair encNat encNat) encBool :=
      ComputableTidilyInPolyTime.binary_lt' (ComputableTidilyInPolyTime.fst _ _)
        (ComputableTidilyInPolyTime.binary_mul' (ComputableTidilyInPolyTime.const 2)
          (ComputableTidilyInPolyTime.snd _ _))
    exact (ComputableTidilyInPolySpace.of_polyTime hpost).comp
      ((ComputableTidilyInPolySpace.of_polyTime hcap).prod
        (computableTidilyInPolySpace_evaluate M hfuel))
  obtain ⟨T, S, hS, h⟩ := hdec
  refine mem_PSPACE_of_computableTidilyInO h hS fun a => ?_
  rw [mem_iff_two_pow_lt_value (fun a S oracle s => hreal a S oracle s) hA a, evaluate_eq,
    decide_eq_true_iff]

end Cslib.Complexity
