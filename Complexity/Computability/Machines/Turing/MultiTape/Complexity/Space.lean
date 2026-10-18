/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Machine.Space
public import Complexity.Computability.Machines.Turing.MultiTape.Machine.ChoiceTable
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Configuration
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Encoding

/-!
# Testing the steps of views in polynomial time

The step relation of the views of a machine with finitely many states
(`Turing.MultiTapeNTM.ViewStep`) is decided by `Turing.MultiTapeNTM.viewStepB`: a halted view
steps only to itself, and a running view to the summarized result of one of the finitely many
actions its transition relation permits for its control and read symbols. The test is
polynomial-time in the encoded pair of views: it branches on the finite key of the first view,
and each branch compares the second view with the results of a fixed finite list of fixed actions.

## Main definitions

* `Turing.MultiTapeNTM.viewStepB`: the Boolean step test of views.

## Main results

* `Turing.MultiTapeNTM.viewStepB_iff`: the test decides `Turing.MultiTapeNTM.ViewStep`.
* `Turing.MultiTapeNTM.computableTidilyInPolyTime_viewStepB`: the test is polynomial-time.
-/

@[expose] public section

namespace Turing

open MultiTapeTM

namespace MultiTapeTM.ComputableTidilyInPolyTime

/-- The output summary is polynomial-time on raw words. -/
@[fun_prop]
theorem outputClass : ComputableTidilyInPolyTime Turing.outputClass encBits encBits := by
  have h : Turing.outputClass = fun word : List Bool =>
      if decide (word = []) then [] else if decide (word = [true]) then [true] else [false] := by
    funext word
    unfold Turing.outputClass
    split_ifs <;> simp_all
  rw [h]
  fun_prop

end MultiTapeTM.ComputableTidilyInPolyTime

namespace MultiTapeNTM

variable {k : ℕ} {State : Type} [Finite State] (ntm : MultiTapeNTM k Bool State)

open scoped Classical in
/-- **The step test of views.** -/
noncomputable def viewStepB (views : FiniteCfg k Bool State × FiniteCfg k Bool State) : Bool :=
  match views.1.state with
  | none => decide (views.2 = views.1)
  | some state => (ntm.actions state views.1.inputSymbol views.1.workTapeSymbols).any
      fun action => decide (views.2 = (views.1.step action).summary)

/-- The test decides the steps of views. -/
theorem viewStepB_iff {finite next : FiniteCfg k Bool State} :
    ntm.viewStepB (finite, next) = true ↔ ntm.ViewStep finite next := by
  unfold viewStepB ViewStep
  rcases finite.state with _ | state
  · simp
  · simp only [List.any_eq_true, decide_eq_true_eq, mem_actions]

/-- The summary of a view is polynomial-time. -/
theorem computableTidilyInPolyTime_summary :
    ComputableTidilyInPolyTime (FiniteCfg.summary (k := k) (State := State)) encFiniteCfg
      encFiniteCfg := by
  unfold FiniteCfg.summary
  fun_prop

/-- **The step test is polynomial-time** in the encoded pair of views. -/
theorem computableTidilyInPolyTime_viewStepB :
    ComputableTidilyInPolyTime ntm.viewStepB (encPair encFiniteCfg encFiniteCfg) encBool := by
  classical
  -- branch on the finite key of the first view
  let key (views : FiniteCfg k Bool State × FiniteCfg k Bool State) :
      Option State × Option Bool × (Fin k → Option Bool) :=
    (views.1.state, views.1.inputSymbol, views.1.workTapeSymbols)
  let branch (tag : Option State × Option Bool × (Fin k → Option Bool))
      (views : FiniteCfg k Bool State × FiniteCfg k Bool State) : Bool :=
    match tag.1 with
    | none => decide (views.2 = views.1)
    | some state => (ntm.actions state tag.2.1 tag.2.2).any
        fun action => decide (views.2 = (views.1.step action).summary)
  have heq : ntm.viewStepB = fun views => branch (key views) views := by
    funext views
    rfl
  have hfst := ComputableTidilyInPolyTime.fst (encFiniteCfg (k := k) (State := State))
    (encFiniteCfg (k := k) (State := State))
  have hsnd := ComputableTidilyInPolyTime.snd (encFiniteCfg (k := k) (State := State))
    (encFiniteCfg (k := k) (State := State))
  rw [heq]
  refine ComputableTidilyInPolyTime.finite_cases
    (tagEncoding := encPair (encFinite _) (encPair (encFinite _) (encFinite _))) ?_ fun tag => ?_
  · exact (ComputableTidilyInPolyTime.finiteCfg_state.comp hfst).prod
      ((ComputableTidilyInPolyTime.finiteCfg_inputSymbol.comp hfst).prod
        (ComputableTidilyInPolyTime.finiteCfg_workTapeSymbols.comp hfst))
  · rcases tag with ⟨_ | state, symbol, work⟩
    · exact ComputableTidilyInPolyTime.decide_eq' hsnd hfst
    · refine ComputableTidilyInPolyTime.anyConst _ fun action _ => ?_
      exact ComputableTidilyInPolyTime.decide_eq' hsnd
        ((computableTidilyInPolyTime_summary.comp
          (ComputableTidilyInPolyTime.finiteCfg_step action)).comp hfst)

/-! ### Codes of views -/

/-- Pad a word to width `width + 1`: zeros, a one, then the word. -/
def padWord (width : ℕ) (word : List Bool) : List Bool :=
  List.replicate (width - word.length) false ++ true :: word

/-- Remove the padding of `Turing.MultiTapeNTM.padWord`: the leading zeros and the one after
them. -/
def unpadWord (code : List Bool) : List Bool :=
  (code.dropWhile (!·)).tail

@[simp]
theorem unpadWord_padWord (width : ℕ) (word : List Bool) :
    unpadWord (padWord width word) = word := by
  unfold unpadWord padWord
  induction width - word.length with
  | zero => simp
  | succ n ih => simp [List.replicate_succ]

theorem length_padWord {width : ℕ} {word : List Bool} (h : word.length ≤ width) :
    (padWord width word).length = width + 1 := by
  simp only [padWord, List.length_append, List.length_replicate, List.length_cons]
  omega

variable (dec : List Bool → Option (FiniteCfg k Bool State))

/-- The code of a view at width `width`: a zero tag, then its padded encoding. -/
noncomputable def viewCode (width : ℕ) (finite : FiniteCfg k Bool State) : List Bool :=
  false :: padWord width (encFiniteCfg finite)

/-- The accepting code at width `width`: all ones. Its tag is one, so it is no view's code. -/
def acceptCode (width : ℕ) : List Bool := List.replicate (width + 2) true

/-- Read the view of a code with a zero tag, by the decoder `dec`. -/
def decodeView : List Bool → Option (FiniteCfg k Bool State)
  | false :: code => dec (unpadWord code)
  | _ => none

open scoped Classical in
/-- **The edge test of codes.** A code of a view `finite` has an edge to every code with tag one
if `finite` has halted with output `[true]`, and to the code of every view `finite` steps to. -/
noncomputable def codeEdge (code next : List Bool) : Bool :=
  match decodeView dec code, next with
  | none, _ => false
  | some finite, true :: _ => decide (finite.state = none) && decide (finite.output = [true])
  | some finite, next => match decodeView dec next with
    | none => false
    | some next => ntm.viewStepB (finite, next)

/-- The edges between codes of width `width + 2`. -/
def CodeStep (width : ℕ) (code next : List Bool) : Prop :=
  code.length = width + 2 ∧ next.length = width + 2 ∧ ntm.codeEdge dec code next = true

variable {ntm dec}

theorem decodeView_viewCode (hdec : ∀ finite, dec (encFiniteCfg finite) = some finite)
    (width : ℕ) (finite : FiniteCfg k Bool State) :
    decodeView dec (viewCode width finite) = some finite := by
  simp only [decodeView, viewCode, unpadWord_padWord, hdec]

theorem length_viewCode {width : ℕ} {finite : FiniteCfg k Bool State}
    (h : (encFiniteCfg finite).length ≤ width) : (viewCode width finite).length = width + 2 := by
  rw [viewCode, List.length_cons, length_padWord h]

theorem codeEdge_viewCode (hdec : ∀ finite, dec (encFiniteCfg finite) = some finite)
    {width : ℕ} {finite next : FiniteCfg k Bool State} :
    ntm.codeEdge dec (viewCode width finite) (viewCode width next) = true ↔
      ntm.ViewStep finite next := by
  simp only [codeEdge, viewCode, decodeView, unpadWord_padWord, hdec]
  exact ntm.viewStepB_iff

theorem codeEdge_acceptCode (hdec : ∀ finite, dec (encFiniteCfg finite) = some finite)
    {width : ℕ} {finite : FiniteCfg k Bool State} :
    ntm.codeEdge dec (viewCode width finite) (acceptCode width) = true ↔
      finite.state = none ∧ finite.output = [true] := by
  simp only [codeEdge, decodeView_viewCode hdec, acceptCode, List.replicate_succ, Bool.and_eq_true,
    decide_eq_true_eq]

/-- **Acceptance is reachability of the accepting code**, along the edges between codes of a
width at least the length of the encoding of every reachable view. -/
theorem accepts_iff_reflTransGen_codeStep (hdec : ∀ finite, dec (encFiniteCfg finite) = some finite)
    {input : List Bool} {width : ℕ}
    (hwidth : ∀ finite, Relation.ReflTransGen ntm.ViewStep (ntm.initView input) finite →
      (encFiniteCfg finite).length ≤ width) :
    ntm.Accepts input ↔ Relation.ReflTransGen (ntm.CodeStep dec width)
      (viewCode width (ntm.initView input)) (acceptCode width) := by
  rw [accepts_iff_reflTransGen_viewStep]
  constructor
  · rintro ⟨finite, hreach, hstate, houtput⟩
    have hcodes : ∀ next, Relation.ReflTransGen ntm.ViewStep (ntm.initView input) next →
        Relation.ReflTransGen (ntm.CodeStep dec width) (viewCode width (ntm.initView input))
          (viewCode width next) := by
      intro next hnext
      induction hnext with
      | refl => rfl
      | @tail view next hview hstep ih =>
        exact ih.tail ⟨length_viewCode (hwidth _ hview),
          length_viewCode (hwidth _ (hview.tail hstep)), (codeEdge_viewCode hdec).mpr hstep⟩
    exact (hcodes finite hreach).tail ⟨length_viewCode (hwidth _ hreach),
      List.length_replicate .., (codeEdge_acceptCode hdec).mpr ⟨hstate, houtput⟩⟩
  · intro hreach
    -- every reachable code is the code of a reachable view, or has tag one after an accepting view
    have hinv : ∀ code, Relation.ReflTransGen (ntm.CodeStep dec width)
        (viewCode width (ntm.initView input)) code →
        (∃ finite, decodeView dec code = some finite ∧
          Relation.ReflTransGen ntm.ViewStep (ntm.initView input) finite) ∨
        (code.head? = some true ∧ ∃ finite,
          Relation.ReflTransGen ntm.ViewStep (ntm.initView input) finite ∧
            finite.state = none ∧ finite.output = [true]) := by
      intro code hcode
      induction hcode with
      | refl => exact .inl ⟨_, decodeView_viewCode hdec _ _, .refl⟩
      | @tail code next _ hstep ih =>
        obtain ⟨-, -, hedge⟩ := hstep
        unfold codeEdge at hedge
        rcases ih with ⟨finite, hfinite, hreach⟩ | ⟨hhead, -⟩
        · rw [hfinite] at hedge
          rcases next with _ | ⟨_ | _, next⟩
          · simp [decodeView] at hedge
          · simp only at hedge
            rcases hview : decodeView dec (false :: next) with _ | view
            · simp [hview] at hedge
            · simp only [hview, viewStepB_iff] at hedge
              exact .inl ⟨view, rfl, hreach.tail hedge⟩
          · simp only [Bool.and_eq_true, decide_eq_true_eq] at hedge
            exact .inr ⟨rfl, finite, hreach, hedge⟩
        · rcases code with _ | ⟨_ | _, code⟩ <;> simp at hhead
          simp [decodeView] at hedge
    rcases hinv _ hreach with ⟨finite, hfinite, -⟩ | ⟨-, hacc⟩
    · simp [acceptCode, List.replicate_succ, decodeView] at hfinite
    · exact hacc

/-! ### The edge test in polynomial time -/

/-- The transducer of `Turing.MultiTapeNTM.unpadWord`: skip zeros up to the first one, then copy.
Its state records whether the first one has been read. -/
private def unpadT : MultiTapeTM.Transducer Bool Bool where
  q₀ := false
  step copying bit := if copying then (true, [bit]) else (bit, [])
  final _ := []
  length_step_le copying _ := by cases copying <;> simp
  length_final_le _ := by simp

private theorem unpadT_run (code : List Bool) :
    unpadT.run false code = unpadWord code ∧ unpadT.run true code = code := by
  induction code with
  | nil => exact ⟨rfl, rfl⟩
  | cons bit code ih =>
    cases bit <;> simp [unpadT, unpadWord, MultiTapeTM.Transducer.run_cons] at ih ⊢ <;> simp [ih]

theorem computableTidilyInPolyTime_unpadWord :
    ComputableTidilyInPolyTime unpadWord encBits encBits :=
  .of_linear (unpadT.computableTidilyInLinearTimeAndSpace fun code => (unpadT_run code).1.symm)

omit [Finite State] in
theorem decodeView_eq (code : List Bool) :
    decodeView dec code = if code.headD true then none else dec (unpadWord code.tail) := by
  rcases code with _ | ⟨_ | _, code⟩ <;> rfl

section Certificate

variable {α : Type} {encA : α ↪ List Bool}

/-- Reading the view of a computed code is polynomial-time, for a polynomial-time decoder. -/
theorem computableTidilyInPolyTime_decodeView
    (hdec : ComputableTidilyInPolyTime dec encBits (encOption encFiniteCfg)) {code : α → List Bool}
    (hcode : ComputableTidilyInPolyTime code encA encBits) :
    ComputableTidilyInPolyTime (fun a => decodeView dec (code a)) encA
      (encOption encFiniteCfg) := by
  simp only [decodeView_eq]
  exact (ComputableTidilyInPolyTime.headD true |>.comp hcode).cond (.const none)
    (hdec.comp (computableTidilyInPolyTime_unpadWord.comp
      (ComputableTidilyInPolyTime.tail (encA := encBool) |>.comp hcode)))

theorem codeEdge_eq (code next : List Bool) : ntm.codeEdge dec code next =
    (decodeView dec code).elim false fun finite =>
      if next.headD false then
        decide (finite.state = none) && decide (finite.output = [true])
      else (decodeView dec next).elim false fun view => ntm.viewStepB (finite, view) := by
  unfold codeEdge
  rcases decodeView dec code with _ | finite
  · rfl
  · rcases next with _ | ⟨_ | _, next⟩
    · rfl
    · simp only [List.headD_cons, Bool.false_eq_true, ite_false]
      cases decodeView dec (false :: next) <;> rfl
    · rfl

/-- **The edge test of codes is polynomial-time**, for a polynomial-time decoder. -/
theorem computableTidilyInPolyTime_codeEdge
    (hdec : ComputableTidilyInPolyTime dec encBits (encOption encFiniteCfg))
    {code next : α → List Bool} (hcode : ComputableTidilyInPolyTime code encA encBits)
    (hnext : ComputableTidilyInPolyTime next encA encBits) :
    ComputableTidilyInPolyTime (fun a => ntm.codeEdge dec (code a) (next a)) encA encBool := by
  classical
  simp only [codeEdge_eq]
  have hfst := ComputableTidilyInPolyTime.fst encA (encFiniteCfg (k := k) (State := State))
  have hsnd := ComputableTidilyInPolyTime.snd encA (encFiniteCfg (k := k) (State := State))
  refine (computableTidilyInPolyTime_decodeView hdec hcode).optionElimWithInput (.const false) ?_
  refine ((ComputableTidilyInPolyTime.headD false).comp (hnext.comp hfst)).cond ?_ ?_
  · exact ComputableTidilyInPolyTime.bool_and.comp
      (((ComputableTidilyInPolyTime.of_finite fun state : Option State =>
          decide (state = none)).comp (ComputableTidilyInPolyTime.finiteCfg_state.comp hsnd)).prod
      (ComputableTidilyInPolyTime.decide_eq'
        (ComputableTidilyInPolyTime.finiteCfg_output.comp hsnd) (.const [true])))
  · refine (computableTidilyInPolyTime_decodeView hdec (hnext.comp hfst)).optionElimWithInput
      (.const false) ?_
    exact ntm.computableTidilyInPolyTime_viewStepB.comp
      ((hsnd.comp (ComputableTidilyInPolyTime.fst _ _)).prod (ComputableTidilyInPolyTime.snd _ _))

end Certificate

end MultiTapeNTM

end Turing
