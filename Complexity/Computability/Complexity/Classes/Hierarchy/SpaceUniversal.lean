/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Universal.InPlace
import Complexity.Computability.Complexity.Classes.Hierarchy.Time

/-!
# The universal machine within a space budget

`Turing.MultiTapeTM.Universal.universalSpace (d, x, t, b)` runs the machine described by `d` on
`x` for `t` steps, as the universal function does, but within the *budget* `b`: a step whose
configuration of the simulation is encoded by more than `b` bits is not taken, and the simulation
stays at the last configuration within the budget (`Turing.MultiTapeTM.Universal.budgetStep`). It
returns the first two symbols of the output and whether the machine has halted: enough to tell
whether the output is a single given symbol, without storing an output that may be as long as the
run.

It is computed by the in-place run of the universal machine
(`Turing.MultiTapeTM.Universal.computableTidilyInTimeAndSpace_universal_inPlace`): the same
multi-pass fold over the input, one pass per step, reading the symbol under the simulated input
head by counting down the symbols of `x`, with the budget and the first two symbols of the output
added to its state, and a budget test at the end of each pass. So it is tidily computable within
space linear in `Turing.MultiTapeTM.Universal.budgetSpace`: the description, the budget, the
number of steps and the length of `x` in binary, and the largest symbol of `x`
(`Turing.MultiTapeTM.Universal.computableTidilyInO_universalSpace`), never the length of `x`
itself or the space the described machine would use beyond the budget.

Within the budget it agrees with the universal function
(`Turing.MultiTapeTM.Universal.universalSpace_eq_of_le`), and on the description of a machine it
returns the first two symbols of the output of the machine whenever the cells visited by the
machine fit, encoded, within the budget (`Turing.MultiTapeTM.Universal.universalSpace_desc`).

## Main definitions

* `Turing.MultiTapeTM.Universal.budgetStep`: a step of the simulation within a budget.
* `Turing.MultiTapeTM.Universal.universalSpace`: the universal function within a space budget.
* `Turing.MultiTapeTM.Universal.budgetSpace`: the bound on the states of its fold.

## Main results

* `Turing.MultiTapeTM.Universal.universalSpace_eq_of_le`,
  `Turing.MultiTapeTM.Universal.universalSpace_desc`: within the budget, the universal function.
* `Turing.MultiTapeTM.Universal.computableTidilyInO_universalSpace`: it is tidily computable in
  space linear in `budgetSpace`.
* `Turing.MultiTapeTM.Universal.budgetSpace_le`: `budgetSpace` is linear in the description, the
  budget and the lengths of the number of steps and of the length of the input in binary, plus
  the largest symbol of the input.
-/

namespace Turing.MultiTapeTM.Universal

/-! ### Simulating within a budget -/

/-- A step of the simulation within the budget `b`, keeping the first two symbols of the output:
the step of the machine described by `d` on `x`, unless the configuration it reaches is encoded by
more than `b` bits, in which case the configuration and the output stay. -/
@[expose] public def budgetStep (d : Desc) (x : List ℕ) (b : ℕ) (p : SCfg × List ℕ) :
    SCfg × List ℕ :=
  if (eCfg (step d x p.1).1).length ≤ b then
    ((step d x p.1).1, (p.2 ++ (step d x p.1).2.toList).take 2)
  else p

/-- **The universal function within a space budget.** The machine described by `i.1` runs on the
input `i.2.1` for `i.2.2.1` steps within the budget `i.2.2.2` (`budgetStep`); the result is the
first two symbols of its output and whether it has halted. -/
@[expose] public def universalSpace (i : Desc × List ℕ × ℕ × ℕ) : List ℕ × Bool :=
  (((budgetStep i.1 i.2.1 i.2.2.2)^[i.2.2.1] (init i.1, [])).2,
    ((budgetStep i.1 i.2.1 i.2.2.2)^[i.2.2.1] (init i.1, [])).1.state.isNone)

/-- The encoding of inputs of `universalSpace`: the number of steps in binary, the budget in
unary. -/
public abbrev eInS : Desc × List ℕ × ℕ × ℕ ↪ List Bool :=
  encPair eDesc (encPair (encList encUnary) (encPair encNat encUnary))

variable (d : Desc) (x : List ℕ) (b : ℕ)

lemma take_two_append_take_two (o e : List ℕ) : (o.take 2 ++ e).take 2 = (o ++ e).take 2 := by
  simp only [List.take_append, List.take_take, List.length_take]
  congr 2
  omega

lemma stepOut_iterate_succ (j : ℕ) :
    (stepOut d x)^[j + 1] (init d, []) =
      (run d x (j + 1), ((stepOut d x)^[j] (init d, [])).2 ++
        (step d x (run d x j)).2.toList) := by
  rw [Function.iterate_succ_apply', run_succ']
  rfl

/-- **The run within the budget** is the run of the simulation up to some step, with the first two
symbols of its output; past the start, that configuration is within the budget. -/
public theorem budgetStep_iterate (i : ℕ) : ∃ j ≤ i,
    (budgetStep d x b)^[i] (init d, []) = (run d x j, ((stepOut d x)^[j] (init d, [])).2.take 2) ∧
      (j = 0 ∨ (eCfg (run d x j)).length ≤ b) := by
  induction i with
  | zero => exact ⟨0, le_rfl, rfl, Or.inl rfl⟩
  | succ i ih =>
    obtain ⟨j, hj, heq, hb⟩ := ih
    rw [Function.iterate_succ_apply', heq, budgetStep]
    dsimp only
    split_ifs with h
    · refine ⟨j + 1, by omega, ?_, Or.inr (by rwa [run_succ'])⟩
      rw [stepOut_iterate_succ, take_two_append_take_two, run_succ']
    · exact ⟨j, by omega, rfl, hb⟩

/-- The run within the budget keeps at most two symbols of the output. -/
public lemma length_budgetStep_iterate_le (i : ℕ) :
    ((budgetStep d x b)^[i] (init d, [])).2.length ≤ 2 := by
  obtain ⟨j, -, heq, -⟩ := budgetStep_iterate d x b i
  rw [heq, List.length_take]
  exact min_le_left _ _

/-- The symbols of the output kept by the run within the budget are numbers of the description. -/
public lemma le_of_mem_budgetStep_iterate (i : ℕ) {o : ℕ}
    (ho : o ∈ ((budgetStep d x b)^[i] (init d, [])).2) : o ≤ descLen d := by
  obtain ⟨j, -, heq, -⟩ := budgetStep_iterate d x b i
  rw [heq] at ho
  exact (inv_iterate d x j).2.2 o (List.mem_of_mem_take ho)

/-- **Within the budget**, the run is the run of the simulation, with the first two symbols of its
output. -/
public theorem budgetStep_iterate_of_le {t : ℕ}
    (hb : ∀ j < t, (eCfg (run d x (j + 1))).length ≤ b) :
    (budgetStep d x b)^[t] (init d, []) = (run d x t, (simulate d x t).1.take 2) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih fun j hj => hb j (by omega), budgetStep]
    dsimp only
    split_ifs with h
    · simp only [simulate]
      rw [stepOut_iterate_succ, ← run_succ', take_two_append_take_two]
    · exact absurd (by rw [← run_succ']; exact hb t (by omega)) h

/-- **Within the budget, the universal function**: if every configuration of the simulation within
`t` steps is encoded within `b` bits, `universalSpace` returns the first two symbols of the output
of the universal function and whether the machine has halted. -/
public theorem universalSpace_eq_of_le {t : ℕ}
    (hb : ∀ j < t, (eCfg (run d x (j + 1))).length ≤ b) :
    universalSpace (d, x, t, b) = ((universal (d, x, t)).1.take 2, (universal (d, x, t)).2) := by
  simp only [universalSpace, budgetStep_iterate_of_le d x b hb, universal]
  rfl

/-- **On the description of a machine**, within a budget that holds the configurations of the
simulation (`Turing.MultiTapeTM.Universal.cfgSpace`, linear in the space of the machine), the
budgeted universal function returns the first two symbols of the numbered output of the machine
and whether it has halted. -/
public theorem universalSpace_desc {k : ℕ} {Symbol S : Type} [Fintype S] [Fintype Symbol]
    (eS : S ↪ ℕ) (eY : Symbol ↪ ℕ) (tm : MultiTapeTM k Symbol S) (x : List Symbol) (t b : ℕ)
    (hb : cfgSpace (desc eS eY tm) (x.map eY) t ≤ b) :
    universalSpace (desc eS eY tm, x.map eY, t, b) =
      (((tm.runFrom (tm.initCfg x) t).output.map eY).take 2,
        (tm.runFrom (tm.initCfg x) t).state.isNone) := by
  rw [universalSpace_eq_of_le _ _ _ fun j hj => ?_, universal_desc]
  refine (length_eCfg_le_space _ _ (j + 1)).trans (le_trans ?_ hb)
  have := simSpace_mono (desc eS eY tm) (x.map eY) (show j + 1 ≤ t by omega)
  unfold cfgSpace
  gcongr

/-! ### The fold within a budget -/

/-- The states of the fold within a budget: the state of the in-place fold
(`Turing.MultiTapeTM.Universal.St`), the budget and the first two symbols of the output so far. -/
public abbrev SSt := St × ℕ × List ℕ

/-- The encoding of the states of the fold within a budget, with the budget in unary. -/
public abbrev eSSt : SSt ↪ List Bool := encPair eSt (encPair encUnary (encList encUnary))

/-- The initial state: the initial state of the in-place fold, the budget and no output. -/
@[expose] public def foldInitS (i : Desc × List ℕ × ℕ × ℕ) : SSt :=
  (foldInit (i.1, i.2.1, i.2.2.1), i.2.2.2, [])

/-- A round: one event of the countdown, as in the in-place fold. -/
@[expose] public def foldNextS (p : SSt × Bool) : SSt := (foldNext (p.1.1, p.2), p.1.2)

/-- The end of a pass within the budget: the step of the in-place fold if the configuration it
reaches is encoded within the budget, keeping the first two symbols of the output; otherwise the
configuration stays, one step less is left and the countdown is reset to the input head. -/
@[expose] public def foldEndS (s : SSt) : SSt :=
  if (eCfg (stepAt s.1).1).length ≤ s.2.1 then
    (foldEnd s.1, s.2.1, (s.2.2 ++ (stepAt s.1).2.toList).take 2)
  else (((s.1.1.1, s.1.1.2), (s.1.2.1 - 1, s.1.1.2.inputPos, 0)), s.2)

/-- Whether another pass follows. -/
@[expose] public def foldContS (s : SSt) : Bool := foldCont s.1

/-- The result: the first two symbols of the output, and whether the machine has halted. -/
@[expose] public def foldFinishS (s : SSt) : List ℕ × Bool := (s.2.2, s.1.1.2.state.isNone)

lemma streamState_foldNextS (s : SSt) (l : List Bool) (j : ℕ) :
    streamState s foldNextS l j = ((s.1.1, (s.1.2.1, (l.take j).foldl scan s.1.2.2)), s.2) :=
  List.foldl_hom (fun a => ((s.1.1, (s.1.2.1, a)), s.2)) (fun _ _ => rfl)

-- restated from `Turing.MultiTapeTM.Universal.InPlace`, where it is private
lemma stepAt_scan' (c : SCfg) (r : ℕ) :
    stepAt ((d, c), (r, (events x).foldl scan (c.inputPos, 0))) =
      if r = 0 then (c, none) else step d x c := by
  rw [stepAt, step_eq_stepWith, inputSymbol_scan]
  rfl

/-- **The passes within the budget** follow the run within the budget, as long as steps are
left. -/
public theorem passState_foldS (t i : ℕ) :
    passState (foldInitS (d, x, t, b)) foldNextS foldEndS (events x) i =
      (((d, ((budgetStep d x b)^[min i t] (init d, [])).1),
        (t - i, ((budgetStep d x b)^[min i t] (init d, [])).1.inputPos, 0)), b,
        ((budgetStep d x b)^[min i t] (init d, [])).2) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [passState, ih, streamState_foldNextS, List.take_length]
    dsimp only
    have hP := length_budgetStep_iterate_le d x b (min i t)
    rcases Nat.lt_or_ge i t with h | h
    · rw [show min (i + 1) t = min i t + 1 by omega, Function.iterate_succ_apply']
      generalize (budgetStep d x b)^[min i t] (init d, []) = P at hP ⊢
      rw [foldEndS, stepAt_scan', budgetStep]
      simp only [show t - i ≠ 0 by omega, ↓reduceIte, foldEnd, stepAt_scan']
      split_ifs <;> simp only [Prod.mk.injEq, true_and, and_true] <;> omega
    · rw [show min (i + 1) t = min i t by omega]
      generalize (budgetStep d x b)^[min i t] (init d, []) = P at hP ⊢
      rw [foldEndS, stepAt_scan']
      simp only [show t - i = 0 by omega, ↓reduceIte, foldEnd, stepAt_scan', Option.toList_none,
        List.append_nil, List.take_of_length_le hP]
      split_ifs <;> simp only [Prod.mk.injEq, true_and, and_true] <;> omega

/-! ### The events of the input, and the parts of the input the initial state reads

The lemmas of this section restate private lemmas of `Turing.MultiTapeTM.Universal.InPlace` for
the encoding `Turing.MultiTapeTM.Universal.eInS`, whose input ends in a budget. -/

lemma inTr_run_frame (w v : List Bool) :
    inTr.run .descMarker (frame w ++ v) = inTr.run .marker v := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> exact ih

lemma inTr_run_steps (v : List Bool) : inTr.run .steps v = (.steps, []) := by
  induction v with
  | nil => rfl
  | cons b v ih => exact congrArg (fun p : InState × List Bool => (p.1, p.2)) ih

lemma inTr_run_symbol (n : ℕ) (v : List Bool) :
    inTr.run .marker (doubled (frame (List.replicate n true)) ++ v) =
      ((inTr.run .marker v).1, tok n ++ (inTr.run .marker v).2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, frame_cons, doubled_cons, doubled_cons]
    change ((inTr.run .marker (doubled (frame (List.replicate n true)) ++ v)).1,
      true :: (inTr.run .marker (doubled (frame (List.replicate n true)) ++ v)).2) = _
    rw [ih]
    simp [tok, List.replicate_succ]

/-- The events of the encoded input of `universalSpace` are the events of the symbols of `x`. -/
public theorem events_eInS (t : ℕ) : inTr.events (eInS (d, x, t, b)) = events x := by
  have hx : ∀ v, inTr.run .marker (doubled (encList encUnary x) ++ v) =
      ((inTr.run .marker v).1, events x ++ (inTr.run .marker v).2) := by
    intro v
    induction x with
    | nil => simp [events]
    | cons n x ih =>
      rw [encList_cons, doubled_append, List.append_assoc, encUnary_apply, inTr_run_symbol, ih]
      simp [events]
  rw [Translator.events, show eInS (d, x, t, b) = frame (eDesc d) ++ (frame (encList encUnary x) ++
    encPair encNat encUnary (t, b)) from rfl, show inTr.q₀ = .descMarker from rfl, inTr_run_frame,
    frame_eq_doubled, List.append_assoc, hx, List.singleton_append]
  change events x ++ (inTr.run .steps (encPair encNat encUnary (t, b))).2 = events x
  rw [inTr_run_steps, List.append_nil]

/-- Copies the framed description, drops the framed input and copies the rest: a copy of the
private transducer `extractT` of `Turing.MultiTapeTM.Universal.InPlace`. -/
@[simps q₀ step final]
def extractS : Transducer Bool ExState where
  q₀ := .descMarker
  step
    | .descMarker, true => (.descBit, [true])
    | .descMarker, false => (.marker, [false])
    | .descBit, b => (.descMarker, [b])
    | .marker, true => (.bit, [])
    | .marker, false => (.steps, [])
    | .bit, _ => (.marker, [])
    | .steps, b => (.steps, [b])
  final _ := []
  length_step_le q b := by cases q <;> cases b <;> simp
  length_final_le _ := by simp

lemma extractS_run (t : ℕ) :
    extractS.run extractS.q₀ (eInS (d, x, t, b)) =
      encPair eDesc (encPair encNat encUnary) (d, t, b) := by
  have h₁ (w v : List Bool) :
      extractS.run .descMarker (frame w ++ v) = frame w ++ extractS.run .marker v := by
    induction w with
    | nil => rfl
    | cons b w ih => cases b <;> simp [ih]
  have h₂ (w v : List Bool) : extractS.run .marker (frame w ++ v) = extractS.run .steps v := by
    induction w with
    | nil => rfl
    | cons b w ih => cases b <;> simp [ih]
  have h₃ (w : List Bool) : extractS.run .steps w = w := by
    induction w with
    | nil => rfl
    | cons b w ih => simp [ih]
  simp only [eInS, encPair_apply, extractS_q₀, h₁, h₂, h₃]

/-! ### The size of the states -/

-- restated from `Turing.MultiTapeTM.Universal.InPlace`, where it is private
lemma foldl_scan_replicate' (k cur j : ℕ) :
    (List.replicate j true).foldl scan (k, cur) = (k, if k = 1 then cur + j else cur) := by
  induction j generalizing cur with
  | zero => simp
  | succ j ih =>
    rw [List.replicate_succ, List.foldl_cons]
    simp only [scan, ↓reduceIte, ih]
    split_ifs <;> simp
    omega

-- restated from `Turing.MultiTapeTM.Universal.InPlace`, where it is private
lemma scan_zero' (l : List Bool) (cur : ℕ) : l.foldl scan (0, cur) = (0, cur) := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [scan, ih]

-- restated from `Turing.MultiTapeTM.Universal.InPlace`, where it is private
lemma scan_take_tok' (n k cur j : ℕ) :
    (((tok n).take j).foldl scan (k, cur)).1 ≤ k ∧
      (((tok n).take j).foldl scan (k, cur)).2 ≤ cur + n ∧
      ((((tok n).take j).foldl scan (k, cur)).2 = cur ∨ k = 1) := by
  rcases Nat.lt_or_ge n j with h | h
  · rw [List.take_of_length_le (by simp [tok]; omega), scan_tok]
    split_ifs <;> simp_all
  · rw [tok, List.take_append_of_le_length (by simpa using h), List.take_replicate,
      Nat.min_eq_left h, foldl_scan_replicate']
    split_ifs <;> simp_all

-- restated from `Turing.MultiTapeTM.Universal.InPlace`, where it is private
/-- Along the events of the input, the countdown does not go up and the symbol read stays within
the largest symbol. -/
lemma scan_take' (x : List ℕ) (k cur j : ℕ) :
    (((events x).take j).foldl scan (k, cur)).1 ≤ k ∧
      (((events x).take j).foldl scan (k, cur)).2 ≤ cur + x.foldr max 0 := by
  induction x generalizing k cur j with
  | nil => simp [events]
  | cons n x ih =>
    rw [events, List.map_cons, List.flatten_cons, ← events, List.take_append, List.foldl_append]
    obtain ⟨h₁, h₂, h₃⟩ := scan_take_tok' n k cur j
    set p := ((tok n).take j).foldl scan (k, cur)
    obtain ⟨h₄, h₅⟩ := ih p.1 p.2 (j - (tok n).length)
    simp only [Prod.mk.eta] at h₄ h₅
    refine ⟨h₄.trans h₁, ?_⟩
    rcases h₃ with h₃ | rfl
    · simp only [List.foldr_cons] at h₅ ⊢
      omega
    · rcases Nat.lt_or_ge j (tok n).length with hj | hj
      · rw [Nat.sub_eq_zero_of_le hj.le]
        simp only [List.take_zero, List.foldl_nil, List.foldr_cons]
        omega
      · have hp : p = (0, cur + n) := by
          simp only [p, List.take_of_length_le hj, scan_tok, ↓reduceIte]
        rw [hp, scan_zero']
        simp only [List.foldr_cons]
        omega

/-- A bound on the states of the fold within the budget `b`: the description, a configuration
within the budget or the initial one, the number of steps and the position of the input head in
binary, the largest symbol of the input, the budget in unary and two symbols of the output. -/
@[expose] public def budgetSpace (i : Desc × List ℕ × ℕ × ℕ) : ℕ :=
  2 * (2 * (2 * descLen i.1 + 1 + max i.2.2.2 (eCfg (init i.1)).length) + 1 +
    (2 * (encNat i.2.2.1).length + 1 + (2 * (encNat (i.2.1.length + 1)).length + 1 +
      i.2.1.foldr max 0))) + 1 + (2 * i.2.2.2 + 1 + 2 * (2 * descLen i.1 + 1))

/-- **The size of the states** of the fold within the budget. -/
public lemma length_eSSt_le (t i j : ℕ) :
    (eSSt (streamState (passState (foldInitS (d, x, t, b)) foldNextS foldEndS (events x) i)
      foldNextS (events x) j)).length ≤ budgetSpace (d, x, t, b) := by
  rw [passState_foldS, streamState_foldNextS]
  obtain ⟨j', -, heq, hb'⟩ := budgetStep_iterate d x b (min i t)
  rw [heq]
  dsimp only
  have hout := List.length_take_le 2 ((stepOut d x)^[j'] (init d, [])).2
  have hval (o : ℕ) (ho : o ∈ ((stepOut d x)^[j'] (init d, [])).2.take 2) : o ≤ descLen d :=
    (inv_iterate d x j').2.2 o (List.mem_of_mem_take ho)
  have hc : (eCfg (run d x j')).length ≤ max b (eCfg (init d)).length := by
    rcases hb' with rfl | hb'
    · exact le_max_right _ _
    · exact hb'.trans (le_max_left _ _)
  have hpos : (run d x j').inputPos ≤ x.length + 1 := (inv_iterate d x j').1.inputPos
  obtain ⟨hk, hcur⟩ := scan_take' x (run d x j').inputPos 0 j
  have hr := ComputableTidilyInO.length_encNat_mono (show t - i ≤ t by omega)
  have hk' := ComputableTidilyInO.length_encNat_mono (hk.trans hpos)
  have ho := length_encList_le encUnary (((stepOut d x)^[j'] (init d, [])).2.take 2)
    (b := descLen d) fun o ho => by rw [encUnary_apply, List.length_replicate]; exact hval o ho
  have ho' := Nat.mul_le_mul_right (2 * descLen d + 1) hout
  simp only [length_encPair, encUnary_apply, List.length_replicate, budgetSpace, descLen] at *
  omega

end Turing.MultiTapeTM.Universal
