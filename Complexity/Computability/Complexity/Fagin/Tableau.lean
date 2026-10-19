/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.CookLevin.Correctness
public import Complexity.Computability.Complexity.Fagin.Layout

/-!
# Existential second-order tableau sentence on `Fin B`

Given a deterministic multi-tape Turing machine `tm : MultiTapeTM m Bool State` (`[Fintype State]
[DecidableEq State]`) and a language `L₀` equipped with a strict linear order `lt` on `Fin B` and
unary relations `uLenRel` and `uBitRel` describing an input prefix `u : List Bool`, this file
constructs an existential second-order sentence `FO.tableauESOSentence lt uLenRel uBitRel tm` over
`L₀`.

On `Fin B` with `u.length + 1 < B`, `FO.tableauESOSentence lt uLenRel uBitRel tm` is realized if
and only if there exists a certificate word `w : List Bool` with `u.length + w.length + 1 < B` such
that `tm`, started on `u ++ w`, halts within `B - 1` steps with output `[true]` — equivalently,
by `Cslib.Complexity.CookLevin.tableau_satisfiable_iff`, if and only if
`CookLevin.tableau tm u L (B - 1)` is satisfiable for some `L` with `u.length + L + 1 < B`.

## Main definitions

* `Cslib.Logic.FO.TableauRels`: bundle of the 12 relation-symbol families used by the first-order
  tableau formulas.
* `Cslib.Logic.FO.tableauESOSentence`: the existential second-order sentence encoding an accepting
  computation of `tm` on `u ++ w` within `B - 1` steps.
* `Cslib.Logic.Vocabulary.tableauESOSentence`: specialization to
  `v.powerLanguage.sum v.inputVarLanguage`.

## Main results

* `Cslib.Logic.FO.realize_tableauESOSentence`: on `Fin B`, `tableauESOSentence` holds iff some
  certificate `w` with `u.length + w.length + 1 < B` is accepted within `B - 1` steps.
* `Cslib.Logic.Vocabulary.realize_tableauESOSentence`: on `Fin B`, `v.tableauESOSentence tm`
  holds iff `CookLevin.tableau tm u L (B - 1)` is satisfiable for some `L` with
  `u.length + L + 1 < B`.

## References

* [R. Fagin, *Generalized first-order spectra and polynomial-time recognizable sets*][Fagin1974]
* [N. Immerman, *Descriptive Complexity*][Immerman1999]
* [C. H. Papadimitriou, *Computational Complexity*][Papadimitriou94], Theorem 8.3
-/

@[expose] public section

universe u v

namespace Cslib.Logic

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure
open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Feature
open Cslib.Complexity

namespace FO

/-! ### Relation variables of the ESO tableau sentence -/

/-- Indices of the unary relation variables of the ESO tableau sentence:
* `.inl ()`: `endPos` (holds of the unique element `e = u.length + w.length`),
* `.inr (.inl ())`: `certBit` (holds of input position `j` for `u.length < j ≤ e` when
  `w[j - 1 - u.length] = true`),
* `.inr (.inr (.inl q))`: `state q` at time `t`,
* `.inr (.inr (.inr o))`: `out o` at time `t`. -/
abbrev UnaryTableauVar (State : Type) : Type :=
  Unit ⊕ Unit ⊕ Option State ⊕ OutView

/-- Indices of the binary relation variables of the ESO tableau sentence:
* `.inl ()`: `inPos` at `(t, j)`,
* `.inr (.inl i)`: `head i (+a)` at `(t, a)`,
* `.inr (.inr (.inl i))`: `head i (-a)` at `(t, a)`,
* `.inr (.inr (.inr (.inl (i, s))))`: `cell i (+a) s` at `(t, a)`,
* `.inr (.inr (.inr (.inr (i, s))))`: `cell i (-a) s` at `(t, a)`. -/
abbrev BinaryTableauVar (m : ℕ) : Type :=
  Unit ⊕ Fin m ⊕ Fin m ⊕ (Fin m × Option Bool) ⊕ (Fin m × Option Bool)

/-- Indices of all existential relation variables of the ESO tableau sentence. -/
abbrev TableauVar (m : ℕ) (State : Type) : Type :=
  UnaryTableauVar State ⊕ BinaryTableauVar m

/-- Arity assignment for `TableauVar m State`. -/
def tableauArity (m : ℕ) (State : Type) : TableauVar m State → ℕ
  | .inl _ => 1
  | .inr _ => 2

/-- Bundle of the 12 relation-symbol families used by the first-order tableau formulas over `L'`. -/
structure TableauRels (L' : Language.{0, 0}) (m : ℕ) (State : Type) where
  /-- Strict linear order `<` on `Fin B`. -/
  lt : L'.Relations 2
  /-- Unary relation holding of the unique element `z = u.length`. -/
  uLen : L'.Relations 1
  /-- Unary relation holding of `p < u.length` when `u[p] = true`. -/
  uBit : L'.Relations 1
  /-- Unary relation holding of the unique certificate end position `e = u.length + w.length`. -/
  endPos : L'.Relations 1
  /-- Unary relation holding of `j ∈ (u.length, e]` when `w[j - 1 - u.length] = true`. -/
  certBit : L'.Relations 1
  /-- Unary relation family for `(Feature.state q).Holds (cfg t)`. -/
  state : Option State → L'.Relations 1
  /-- Unary relation family for `(Feature.out o).Holds (cfg t)`. -/
  out : OutView → L'.Relations 1
  /-- Binary relation for `(Feature.inPos j).Holds (cfg t)`. -/
  inPos : L'.Relations 2
  /-- Binary relation family for `(Feature.head i (+a)).Holds (cfg t)`. -/
  headPos : Fin m → L'.Relations 2
  /-- Binary relation family for `(Feature.head i (-a)).Holds (cfg t)`. -/
  headNeg : Fin m → L'.Relations 2
  /-- Binary relation family for `(Feature.cell i (+a) s).Holds (cfg t)`. -/
  cellPos : Fin m → Option Bool → L'.Relations 2
  /-- Binary relation family for `(Feature.cell i (-a) s).Holds (cfg t)`. -/
  cellNeg : Fin m → Option Bool → L'.Relations 2

section Formulas

variable {L' : Language.{0, 0}} {m : ℕ} {State : Type} (r : TableauRels L' m State)

/-- Sentence asserting that `r.endPos` holds of a unique element `e`, and that `r.uLen ≤ e` and `e`
is not the maximum element (`e + 1 < B`). -/
noncomputable def endPosSentence : L'.Sentence :=
  closeEx (Fin 1) (
    rel₁ r.endPos 0 ⊓
      Formula.iExs (Fin 1) (rel₁ r.uLen (.inr 0) ⊓ le r.lt (.inr 0) (.inl 0)) ⊓
      ∼(isMax r.lt 0)) ⊓
    closeAll (Fin 2) ((rel₁ r.endPos 0 ⊓ rel₁ r.endPos 1) ⟹ varEq 0 1)

/-- Formula expressing `inputAt (u ++ w) j = s` at variable `vJ : V`. -/
noncomputable def inputAtFormula (s : Option Bool) {V : Type*} (vJ : V) : L'.Formula V :=
  match s with
  | none =>
    isZero r.lt vJ ⊔
      Formula.iExs (Fin 1) (rel₁ r.endPos (.inr 0) ⊓ lt r.lt (.inr 0) (.inl vJ))
  | some true =>
    Formula.iExs (Fin 2) (
      succ r.lt (.inr 0) (.inl vJ) ⊓ rel₁ r.uLen (.inr 1) ⊓
        lt r.lt (.inr 0) (.inr 1) ⊓ rel₁ r.uBit (.inr 0)) ⊔
      Formula.iExs (Fin 2) (
        rel₁ r.uLen (.inr 0) ⊓ rel₁ r.endPos (.inr 1) ⊓
          lt r.lt (.inr 0) (.inl vJ) ⊓ le r.lt (.inl vJ) (.inr 1) ⊓ rel₁ r.certBit (.inl vJ))
  | some false =>
    Formula.iExs (Fin 2) (
      succ r.lt (.inr 0) (.inl vJ) ⊓ rel₁ r.uLen (.inr 1) ⊓
        lt r.lt (.inr 0) (.inr 1) ⊓ ∼(rel₁ r.uBit (.inr 0))) ⊔
      Formula.iExs (Fin 2) (
        rel₁ r.uLen (.inr 0) ⊓ rel₁ r.endPos (.inr 1) ⊓
          lt r.lt (.inr 0) (.inl vJ) ⊓ le r.lt (.inl vJ) (.inr 1) ⊓ ∼(rel₁ r.certBit (.inl vJ)))

/-- Formula expressing `(Feature.inRead s).Holds (cfg t)` at time variable `vT : V`. -/
noncomputable def inReadFormula (s : Option Bool) {V : Type*} (vT : V) : L'.Formula V :=
  Formula.iExs (Fin 1) (
    rel₂ r.inPos (.inl vT) (.inr 0) ⊓ inputAtFormula r s (.inr 0))

/-- Formula expressing `(Feature.read i s).Holds (cfg t)` at time variable `vT : V`. -/
noncomputable def readFormula (i : Fin m) (s : Option Bool) {V : Type*} (vT : V) : L'.Formula V :=
  Formula.iExs (Fin 1) (
    (rel₂ (r.headPos i) (.inl vT) (.inr 0) ⊓ rel₂ (r.cellPos i s) (.inl vT) (.inr 0)) ⊔
      (rel₂ (r.headNeg i) (.inl vT) (.inr 0) ⊓ rel₂ (r.cellNeg i s) (.inl vT) (.inr 0)))

/-- Formula expressing `(Feature.sit y).Holds (cfg t)` at time variable `vT : V`. -/
noncomputable def sitFormula (y : Situation m State) {V : Type*} (vT : V) : L'.Formula V :=
  rel₁ (r.state (some y.1)) vT ⊓
    inReadFormula r y.2.1 vT ⊓
    Formula.iInf fun i : Fin m => readFormula r i (y.2.2 i) vT

/-- Formula expressing that the input head moves to `vJ` from its position at time `vT` under
direction `d`. -/
noncomputable def inPosPrevFormula (d : SignType) {V : Type*} (vT vJ : V) : L'.Formula V :=
  match d with
  | .zero => rel₂ r.inPos vT vJ
  | .neg =>
    (isZero r.lt vJ ⊓ rel₂ r.inPos vT vJ) ⊔
      Formula.iExs (Fin 1) (succ r.lt (.inl vJ) (.inr 0) ⊓ rel₂ r.inPos (.inl vT) (.inr 0))
  | .pos =>
    Formula.iExs (Fin 1) (
      rel₁ r.endPos (.inr 0) ⊓ succ r.lt (.inr 0) (.inl vJ) ⊓
        rel₂ r.inPos (.inl vT) (.inl vJ)) ⊔
      Formula.iExs (Fin 2) (
        rel₁ r.endPos (.inr 1) ⊓ le r.lt (.inr 0) (.inr 1) ⊓
          succ r.lt (.inr 0) (.inl vJ) ⊓ rel₂ r.inPos (.inl vT) (.inr 0))

/-- Formula expressing that a work-tape head moves to signed offset `vA` from its position at time
`vT` under effective direction `d` (where `d = .pos` means moving away from `0` and `d = .neg`
means moving toward `0`, crossing into `headOpp` at `1` when `vA = 0` and `d = .pos`). -/
noncomputable def headPrevFormula (headSame headOpp : L'.Relations 2) (d : SignType)
    {V : Type*} (vT vA : V) : L'.Formula V :=
  match d with
  | .zero => rel₂ headSame vT vA
  | .pos =>
    (isZero r.lt vA ⊓ Formula.iExs (Fin 1) (
        succ r.lt (.inl vA) (.inr 0) ⊓ rel₂ headOpp (.inl vT) (.inr 0))) ⊔
      Formula.iExs (Fin 1) (
        succ r.lt (.inr 0) (.inl vA) ⊓ rel₂ headSame (.inl vT) (.inr 0))
  | .neg =>
    Formula.iExs (Fin 1) (
      succ r.lt (.inl vA) (.inr 0) ⊓ rel₂ headSame (.inl vT) (.inr 0))

variable [Fintype State] [DecidableEq State] (tm : MultiTapeTM m Bool State)

/-- Right-hand side of the step equation for `state q'` at time `vT`. -/
noncomputable def stateStepRHS (q' : Option State) {V : Type*} (vT : V) : L'.Formula V :=
  (rel₁ (r.state none) vT ⊓ if q' = none then ⊤ else ⊥) ⊔
    Formula.iSup fun y : Situation m State =>
      (if (tm.actionOf y).state = q' then ⊤ else ⊥) ⊓ sitFormula r y vT

/-- Right-hand side of the step equation for `out o` at time `vT`. -/
noncomputable def outStepRHS (o : OutView) {V : Type*} (vT : V) : L'.Formula V :=
  (rel₁ (r.state none) vT ⊓ rel₁ (r.out o) vT) ⊔
    Formula.iSup fun p : Situation m State × OutView =>
      (if p.2.push (tm.actionOf p.1).output = o then ⊤ else ⊥) ⊓
        sitFormula r p.1 vT ⊓ rel₁ (r.out p.2) vT

/-- Right-hand side of the step equation for `inPos` at time `vT` and position `vJ`. -/
noncomputable def inPosStepRHS {V : Type*} (vT vJ : V) : L'.Formula V :=
  (rel₁ (r.state none) vT ⊓ rel₂ r.inPos vT vJ) ⊔
    Formula.iSup fun y : Situation m State =>
      sitFormula r y vT ⊓ inPosPrevFormula r (tm.actionOf y).inputTape vT vJ

/-- Right-hand side of the step equation for a work-tape head at time `vT` and offset `vA`, with
orientation `sign` (`1` for `+a`, `-1` for `-a`). -/
noncomputable def headStepRHS (headSame headOpp : L'.Relations 2) (sign : SignType) (i : Fin m)
    {V : Type*} (vT vA : V) : L'.Formula V :=
  (rel₁ (r.state none) vT ⊓ rel₂ headSame vT vA) ⊔
    Formula.iSup fun y : Situation m State =>
      sitFormula r y vT ⊓
        headPrevFormula r headSame headOpp (sign * ((tm.actionOf y).workTapes i).2) vT vA

/-- Right-hand side of the step equation for a work-tape cell at time `vT` and offset `vA`. -/
noncomputable def cellStepRHS (headSame : L'.Relations 2) (cellSame : Option Bool → L'.Relations 2)
    (i : Fin m) (s : Option Bool) {V : Type*} (vT vA : V) : L'.Formula V :=
  (rel₂ (cellSame s) vT vA ⊓ (rel₁ (r.state none) vT ⊔ ∼(rel₂ headSame vT vA))) ⊔
    Formula.iSup fun p : Situation m State × Option Bool =>
      (if ((tm.actionOf p.1).workTapes i).1.getD p.2 = s then ⊤ else ⊥) ⊓
        sitFormula r p.1 vT ⊓ rel₂ headSame vT vA ⊓ rel₂ (cellSame p.2) vT vA

/-- Sentence fixing all basic features at `t = 0`. -/
noncomputable def initSentence : L'.Sentence :=
  closeAll (Fin 1) (
    isZero r.lt 0 ⟹
      ((Formula.iInf fun q : Option State =>
          rel₁ (r.state q) 0 ⇔ (if q = some tm.q₀ then ⊤ else ⊥)) ⊓
        (Formula.iInf fun o : OutView =>
          rel₁ (r.out o) 0 ⇔ (if o = .empty then ⊤ else ⊥)) ⊓
        Formula.iAlls (Fin 1) (
          rel₂ r.inPos (.inl 0) (.inr 0) ⇔
            Formula.iExs (Fin 1) (isZero r.lt (.inr 0) ⊓ succ r.lt (.inr 0) (.inl (.inr 0)))) ⊓
        Formula.iInf fun i : Fin m =>
          Formula.iAlls (Fin 1) (
            (rel₂ (r.headPos i) (.inl 0) (.inr 0) ⇔ isZero r.lt (.inr 0)) ⊓
              (rel₂ (r.headNeg i) (.inl 0) (.inr 0) ⇔ isZero r.lt (.inr 0)) ⊓
              Formula.iInf fun s : Option Bool =>
                (rel₂ (r.cellPos i s) (.inl 0) (.inr 0) ⇔ (if s = none then ⊤ else ⊥)) ⊓
                  (rel₂ (r.cellNeg i s) (.inl 0) (.inr 0) ⇔ (if s = none then ⊤ else ⊥)))))

/-- Sentence imposing the step equations from `t` to `t + 1` for all basic features. -/
noncomputable def stepSentence : L'.Sentence :=
  closeAll (Fin 2) (
    succ r.lt 0 1 ⟹
      ((Formula.iInf fun q' : Option State =>
          rel₁ (r.state q') 1 ⇔ stateStepRHS r tm q' 0) ⊓
        (Formula.iInf fun o : OutView =>
          rel₁ (r.out o) 1 ⇔ outStepRHS r tm o 0) ⊓
        Formula.iAlls (Fin 1) (
          rel₂ r.inPos (.inl 1) (.inr 0) ⇔ inPosStepRHS r tm (.inl 0) (.inr 0)) ⊓
        Formula.iInf fun i : Fin m =>
          Formula.iAlls (Fin 1) (
            (rel₂ (r.headPos i) (.inl 1) (.inr 0) ⇔
                headStepRHS r tm (r.headPos i) (r.headNeg i) .pos i (.inl 0) (.inr 0)) ⊓
              (rel₂ (r.headNeg i) (.inl 1) (.inr 0) ⇔
                headStepRHS r tm (r.headNeg i) (r.headPos i) .neg i (.inl 0) (.inr 0)) ⊓
              Formula.iInf fun s : Option Bool =>
                (rel₂ (r.cellPos i s) (.inl 1) (.inr 0) ⇔
                    cellStepRHS r tm (r.headPos i) (r.cellPos i) i s (.inl 0) (.inr 0)) ⊓
                  (rel₂ (r.cellNeg i s) (.inl 1) (.inr 0) ⇔
                    cellStepRHS r tm (r.headNeg i) (r.cellNeg i) i s (.inl 0) (.inr 0)))))

/-- Sentence asking that at the maximum time step `B - 1`, the machine is halted (`state none`)
with output `[true]` (`out (.one true)`). -/
noncomputable def acceptSentence : L'.Sentence :=
  closeAll (Fin 1) (
    isMax r.lt 0 ⟹ (rel₁ (r.state none) 0 ⊓ rel₁ (r.out (.one true)) 0))

end Formulas

/-! ### Semantic realization lemmas on `Fin B` -/

section Semantics

variable {L' : Language.{0, 0}} {B : ℕ} [L'.Structure (Fin B)]
  {m : ℕ} {State : Type} {r : TableauRels L' m State}
  (hlt : ∀ x : Fin 2 → Fin B, RelMap r.lt x ↔ x 0 < x 1)
  {tm : MultiTapeTM m Bool State}

include hlt in
/-- Soundness of `endPosSentence`: extracts the unique certificate end position `e : Fin B` with
`u.length ≤ e` and `e + 1 < B`. -/
theorem exists_of_realize_endPosSentence {u : List Bool}
    (huLen : ∀ z : Fin B, RelMap r.uLen ![z] ↔ (z : ℕ) = u.length)
    (h : (Fin B) ⊨ endPosSentence r) :
    ∃ e : Fin B, u.length ≤ (e : ℕ) ∧ (e : ℕ) + 1 < B ∧
      ∀ z : Fin B, RelMap r.endPos ![z] ↔ (z : ℕ) = (e : ℕ) := by
  simp only [endPosSentence, Sentence.realize_inf, realize_closeEx, realize_closeAll,
    Formula.realize_inf, Formula.realize_not, Formula.realize_imp, Formula.realize_iExs,
    realize_rel₁, realize_le hlt, realize_isMax hlt, realize_varEq,
    Sum.elim_inl, Sum.elim_inr] at h
  obtain ⟨⟨yE, ⟨hE, ⟨yU, hU, hle⟩⟩, hnotMax⟩, huniq⟩ := h
  have hU_eq : (yU 0 : ℕ) = u.length := (huLen (yU 0)).1 hU
  rw [Fin.le_def] at hle
  have he0 := (yE 0).2
  refine ⟨yE 0, by omega, by omega, fun z => ?_⟩
  constructor
  · intro hz
    have := huniq ![z, yE 0] ⟨hz, hE⟩
    exact congrArg Fin.val this
  · intro hz
    have heq : z = yE 0 := Fin.ext hz
    rwa [heq]

include hlt in
/-- Completeness of `endPosSentence`. -/
theorem realize_endPosSentence_of_canonical {u : List Bool} {e : ℕ}
    (hle : u.length ≤ e) (heB : e + 1 < B)
    (huLen : ∀ z : Fin B, RelMap r.uLen ![z] ↔ (z : ℕ) = u.length)
    (hend : ∀ z : Fin B, RelMap r.endPos ![z] ↔ (z : ℕ) = e) :
    (Fin B) ⊨ endPosSentence r := by
  simp only [endPosSentence, Sentence.realize_inf, realize_closeEx, realize_closeAll,
    Formula.realize_inf, Formula.realize_not, Formula.realize_imp, Formula.realize_iExs,
    realize_rel₁, realize_le hlt, realize_isMax hlt, realize_varEq,
    Sum.elim_inl, Sum.elim_inr]
  refine ⟨⟨![(⟨e, by omega⟩ : Fin B)], ⟨(hend _).2 rfl, ⟨![(⟨u.length, by omega⟩ : Fin B)],
    (huLen _).2 rfl, ?_⟩⟩, ?_⟩, fun y ⟨h0, h1⟩ => ?_⟩
  · simpa [Fin.le_def] using hle
  · dsimp; omega
  · exact Fin.ext (((hend (y 0)).1 h0).trans ((hend (y 1)).1 h1).symm)

include hlt in
/-- Semantic characterization of `inputAtFormula`. -/
theorem realize_inputAtFormula {u w : List Bool}
    (heB : u.length + w.length + 1 < B)
    (huLen : ∀ z : Fin B, RelMap r.uLen ![z] ↔ (z : ℕ) = u.length)
    (huBit : ∀ p : Fin B, (p : ℕ) < u.length → (RelMap r.uBit ![p] ↔ u[(p : ℕ)]? = some true))
    (hend : ∀ z : Fin B, RelMap r.endPos ![z] ↔ (z : ℕ) = u.length + w.length)
    (hcert : ∀ j : Fin B, u.length < (j : ℕ) → (j : ℕ) ≤ u.length + w.length →
      (RelMap r.certBit ![j] ↔ w[(j : ℕ) - 1 - u.length]? = some true))
    (s : Option Bool) {V : Type*} (vJ : V) (env : V → Fin B) :
    (inputAtFormula r s vJ).Realize env ↔
      inputAt (u ++ w) (env vJ : ℕ) = s := by
  rcases s with _ | (_ | _)
  · -- `s = none`
    simp only [inputAtFormula, Formula.realize_sup, realize_isZero hlt, Formula.realize_iExs,
      Formula.realize_inf, realize_rel₁, realize_lt hlt, Sum.elim_inl, Sum.elim_inr,
      Fin.lt_def]
    constructor
    · rintro (hj0 | ⟨yE, hE, hltE⟩)
      · simp [inputAt, hj0]
      · have hE' := (hend (yE 0)).1 hE
        simp only [inputAt, show (env vJ : ℕ) ≠ 0 by omega, ite_false]
        exact List.getElem?_eq_none (by simp; omega)
    · intro hnone
      by_cases hj0 : (env vJ : ℕ) = 0
      · exact Or.inl hj0
      · right
        simp only [inputAt, hj0, ite_false, List.getElem?_eq_none_iff, List.length_append] at hnone
        refine ⟨![(⟨u.length + w.length, by omega⟩ : Fin B)], (hend _).2 rfl, ?_⟩
        dsimp
        omega
  · -- `s = some false`
    simp only [inputAtFormula, Formula.realize_sup, Formula.realize_iExs, Formula.realize_inf,
      Formula.realize_not, realize_succ hlt, realize_rel₁, realize_lt hlt,
      realize_le hlt, Sum.elim_inl, Sum.elim_inr, Fin.lt_def, Fin.le_def]
    constructor
    · rintro (⟨y, ⟨⟨hp, hU⟩, hltU⟩, hnotBit⟩ | ⟨y, ⟨⟨⟨hU, hE⟩, hgtU⟩, hleE⟩, hnotCert⟩)
      · have hU' := (huLen (y 1)).1 hU
        have hp_lt : (y 0 : ℕ) < u.length := by omega
        have hnotTrue : u[(y 0 : ℕ)]? ≠ some true := mt (huBit (y 0) hp_lt).2 hnotBit
        have hj_sub : (env vJ : ℕ) - 1 = (y 0 : ℕ) := by omega
        simp only [inputAt, show (env vJ : ℕ) ≠ 0 by omega, ite_false, hj_sub,
          List.getElem?_append_left hp_lt, List.getElem?_eq_getElem hp_lt,
          Option.some.injEq, Bool.eq_false_iff]
        simpa [List.getElem?_eq_getElem hp_lt] using hnotTrue
      · have hU' := (huLen (y 0)).1 hU
        have hE' := (hend (y 1)).1 hE
        have hnotTrue : w[(env vJ : ℕ) - 1 - u.length]? ≠ some true :=
          mt (hcert (env vJ) (by omega) (by omega)).2 hnotCert
        have hidx : (env vJ : ℕ) - 1 - u.length < w.length := by omega
        have hge : u.length ≤ (env vJ : ℕ) - 1 := by omega
        simp only [inputAt, show (env vJ : ℕ) ≠ 0 by omega, ite_false,
          List.getElem?_append_right hge, List.getElem?_eq_getElem hidx,
          Option.some.injEq, Bool.eq_false_iff]
        simpa [List.getElem?_eq_getElem hidx] using hnotTrue
    · intro hfalse
      have hj0 : (env vJ : ℕ) ≠ 0 := by rintro h0; simp [inputAt, h0] at hfalse
      simp only [inputAt, hj0, ite_false] at hfalse
      by_cases hju : (env vJ : ℕ) ≤ u.length
      · left
        have hp_lt : (env vJ : ℕ) - 1 < u.length := by omega
        rw [List.getElem?_append_left hp_lt] at hfalse
        let p : Fin B := ⟨(env vJ : ℕ) - 1, by omega⟩
        let uFin : Fin B := ⟨u.length, by omega⟩
        refine ⟨![p, uFin], ⟨⟨by dsimp [p]; omega, (huLen uFin).2 rfl⟩, hp_lt⟩, ?_⟩
        rw [Matrix.cons_val_zero, huBit p hp_lt, hfalse]
        decide
      · right
        have hge : u.length ≤ (env vJ : ℕ) - 1 := by omega
        rw [List.getElem?_append_right hge] at hfalse
        have hidx : (env vJ : ℕ) - 1 - u.length < w.length := by
          by_contra hle
          rw [List.getElem?_eq_none (by omega)] at hfalse
          cases hfalse
        let uFin : Fin B := ⟨u.length, by omega⟩
        let eFin : Fin B := ⟨u.length + w.length, by omega⟩
        refine ⟨![uFin, eFin], ⟨⟨⟨(huLen uFin).2 rfl, (hend eFin).2 rfl⟩,
          by dsimp [uFin]; omega⟩, by dsimp [eFin]; omega⟩, ?_⟩
        rw [hcert (env vJ) (by omega) (by omega), hfalse]
        decide
  · -- `s = some true`
    simp only [inputAtFormula, Formula.realize_sup, Formula.realize_iExs, Formula.realize_inf,
      realize_succ hlt, realize_rel₁, realize_lt hlt,
      realize_le hlt, Sum.elim_inl, Sum.elim_inr, Fin.lt_def, Fin.le_def]
    constructor
    · rintro (⟨y, ⟨⟨hp, hU⟩, hltU⟩, hBit⟩ | ⟨y, ⟨⟨⟨hU, hE⟩, hgtU⟩, hleE⟩, hCert⟩)
      · have hU' := (huLen (y 1)).1 hU
        have hp_lt : (y 0 : ℕ) < u.length := by omega
        have hTrue := (huBit (y 0) hp_lt).1 hBit
        have hj_sub : (env vJ : ℕ) - 1 = (y 0 : ℕ) := by omega
        simp only [inputAt, show (env vJ : ℕ) ≠ 0 by omega, ite_false, hj_sub,
          List.getElem?_append_left hp_lt]
        exact hTrue
      · have hU' := (huLen (y 0)).1 hU
        have hE' := (hend (y 1)).1 hE
        have hTrue := (hcert (env vJ) (by omega) (by omega)).1 hCert
        have hge : u.length ≤ (env vJ : ℕ) - 1 := by omega
        simp only [inputAt, show (env vJ : ℕ) ≠ 0 by omega, ite_false,
          List.getElem?_append_right hge]
        exact hTrue
    · intro htrue
      have hj0 : (env vJ : ℕ) ≠ 0 := by rintro h0; simp [inputAt, h0] at htrue
      simp only [inputAt, hj0, ite_false] at htrue
      by_cases hju : (env vJ : ℕ) ≤ u.length
      · left
        have hp_lt : (env vJ : ℕ) - 1 < u.length := by omega
        rw [List.getElem?_append_left hp_lt] at htrue
        let p : Fin B := ⟨(env vJ : ℕ) - 1, by omega⟩
        let uFin : Fin B := ⟨u.length, by omega⟩
        refine ⟨![p, uFin], ⟨⟨by dsimp [p]; omega, (huLen uFin).2 rfl⟩, hp_lt⟩, ?_⟩
        rw [Matrix.cons_val_zero, huBit p hp_lt]
        exact htrue
      · right
        have hge : u.length ≤ (env vJ : ℕ) - 1 := by omega
        rw [List.getElem?_append_right hge] at htrue
        have hidx : (env vJ : ℕ) - 1 - u.length < w.length := by
          by_contra hle
          rw [List.getElem?_eq_none (by omega)] at htrue
          cases htrue
        let uFin : Fin B := ⟨u.length, by omega⟩
        let eFin : Fin B := ⟨u.length + w.length, by omega⟩
        refine ⟨![uFin, eFin], ⟨⟨⟨(huLen uFin).2 rfl, (hend eFin).2 rfl⟩,
          by dsimp [uFin]; omega⟩, by dsimp [eFin]; omega⟩, ?_⟩
        rw [hcert (env vJ) (by omega) (by omega)]
        exact htrue

/-- Predicate stating that the relation symbols of `r` at time `t : Fin B` agree with a
configuration `cfg : Cfg m Bool State input`. -/
structure TableauRels.AgreesAt (r : TableauRels L' m State)
    {input : List Bool} (cfg : Cfg m Bool State input) (t : Fin B) : Prop where
  state : ∀ q : Option State, RelMap (r.state q) ![t] ↔ (Feature.state q).Holds cfg
  out : ∀ o : OutView, RelMap (r.out o) ![t] ↔ (Feature.out o).Holds cfg
  inPos : ∀ j : Fin B, RelMap r.inPos ![t, j] ↔ (Feature.inPos (j : ℕ)).Holds cfg
  headPos : ∀ (i : Fin m) (a : Fin B),
    RelMap (r.headPos i) ![t, a] ↔ (Feature.head i (a : ℤ)).Holds cfg
  headNeg : ∀ (i : Fin m) (a : Fin B),
    RelMap (r.headNeg i) ![t, a] ↔ (Feature.head i (-(a : ℤ))).Holds cfg
  cellPos : ∀ (i : Fin m) (s : Option Bool) (a : Fin B),
    RelMap (r.cellPos i s) ![t, a] ↔ (Feature.cell i (a : ℤ) s).Holds cfg
  cellNeg : ∀ (i : Fin m) (s : Option Bool) (a : Fin B),
    RelMap (r.cellNeg i s) ![t, a] ↔ (Feature.cell i (-(a : ℤ)) s).Holds cfg

include hlt in
/-- Semantic characterization of `inReadFormula` under `AgreesAt`. -/
theorem realize_inReadFormula {u w : List Bool} {cfg : Cfg m Bool State (u ++ w)} {t : Fin B}
    (heB : u.length + w.length + 1 < B)
    (huLen : ∀ z : Fin B, RelMap r.uLen ![z] ↔ (z : ℕ) = u.length)
    (huBit : ∀ p : Fin B, (p : ℕ) < u.length → (RelMap r.uBit ![p] ↔ u[(p : ℕ)]? = some true))
    (hend : ∀ z : Fin B, RelMap r.endPos ![z] ↔ (z : ℕ) = u.length + w.length)
    (hcert : ∀ j : Fin B, u.length < (j : ℕ) → (j : ℕ) ≤ u.length + w.length →
      (RelMap r.certBit ![j] ↔ w[(j : ℕ) - 1 - u.length]? = some true))
    (hA : r.AgreesAt cfg t)
    (s : Option Bool) {V : Type*} (vT : V) (env : V → Fin B) (ht : env vT = t) :
    (inReadFormula r s vT).Realize env ↔ (Feature.inRead s).Holds cfg := by
  simp only [inReadFormula, Formula.realize_iExs, Formula.realize_inf, realize_rel₂,
    realize_inputAtFormula hlt heB huLen huBit hend hcert, Sum.elim_inl, Sum.elim_inr, ht,
    hA.inPos, holds_inPos, holds_inRead, Cfg.inputSymbol_eq_inputAt]
  constructor
  · rintro ⟨y, hpos, hs⟩
    rwa [hpos]
  · intro hs
    have hp : cfg.inputPos.val < u.length + w.length + 2 := by simpa using cfg.inputPos.isLt
    exact ⟨![(⟨cfg.inputPos.val, by omega⟩ : Fin B)], rfl, hs⟩

/-- Semantic characterization of `readFormula` under `AgreesAt`. -/
theorem realize_readFormula {input : List Bool} {cfg : Cfg m Bool State input} {t : Fin B}
    (hb : ∀ i : Fin m, |cfg.workTapePos i| < B) (hA : r.AgreesAt cfg t)
    (i : Fin m) (s : Option Bool) {V : Type*} (vT : V) (env : V → Fin B) (ht : env vT = t) :
    (readFormula r i s vT).Realize env ↔ (Feature.read i s).Holds cfg := by
  simp only [readFormula, Formula.realize_iExs, Formula.realize_sup, Formula.realize_inf,
    realize_rel₂, Sum.elim_inl, Sum.elim_inr, ht,
    hA.headPos, hA.headNeg, hA.cellPos, hA.cellNeg,
    holds_head, holds_cell, holds_read, Cfg.workTapeSymbols]
  constructor
  · rintro ⟨y, (⟨hh, hc⟩ | ⟨hh, hc⟩)⟩ <;> rwa [hh]
  · intro hs
    have hbi := hb i
    rw [abs_lt] at hbi
    by_cases hnonneg : 0 ≤ cfg.workTapePos i
    · let a : Fin B := ⟨(cfg.workTapePos i).toNat, by omega⟩
      refine ⟨![a], Or.inl ⟨by dsimp [a]; omega, ?_⟩⟩
      have heq : ((a : ℕ) : ℤ) = cfg.workTapePos i := by dsimp [a]; omega
      rwa [Matrix.cons_val_zero, heq]
    · let a : Fin B := ⟨(-cfg.workTapePos i).toNat, by omega⟩
      refine ⟨![a], Or.inr ⟨by dsimp [a]; omega, ?_⟩⟩
      have heq : -((a : ℕ) : ℤ) = cfg.workTapePos i := by dsimp [a]; omega
      rwa [Matrix.cons_val_zero, heq]

include hlt in
/-- Semantic characterization of `sitFormula` under `AgreesAt`. -/
theorem realize_sitFormula {u w : List Bool} {cfg : Cfg m Bool State (u ++ w)} {t : Fin B}
    (heB : u.length + w.length + 1 < B) (hb : ∀ i : Fin m, |cfg.workTapePos i| < B)
    (huLen : ∀ z : Fin B, RelMap r.uLen ![z] ↔ (z : ℕ) = u.length)
    (huBit : ∀ p : Fin B, (p : ℕ) < u.length → (RelMap r.uBit ![p] ↔ u[(p : ℕ)]? = some true))
    (hend : ∀ z : Fin B, RelMap r.endPos ![z] ↔ (z : ℕ) = u.length + w.length)
    (hcert : ∀ j : Fin B, u.length < (j : ℕ) → (j : ℕ) ≤ u.length + w.length →
      (RelMap r.certBit ![j] ↔ w[(j : ℕ) - 1 - u.length]? = some true))
    (hA : r.AgreesAt cfg t)
    (y : Situation m State) {V : Type*} (vT : V) (env : V → Fin B) (ht : env vT = t) :
    (sitFormula r y vT).Realize env ↔ (Feature.sit y).Holds cfg := by
  simp only [sitFormula, Formula.realize_inf, Formula.realize_iInf, realize_rel₁, ht,
    hA.state, realize_inReadFormula hlt heB huLen huBit hend hcert hA _ vT env ht,
    realize_readFormula hb hA _ _ vT env ht, holds_sit_iff, and_assoc]

include hlt in
/-- Semantic characterization of `inPosPrevFormula` under `AgreesAt`. -/
theorem realize_inPosPrevFormula {u w : List Bool} {cfg : Cfg m Bool State (u ++ w)} {t : Fin B}
    (heB : u.length + w.length + 1 < B)
    (hend : ∀ z : Fin B, RelMap r.endPos ![z] ↔ (z : ℕ) = u.length + w.length)
    (hA : r.AgreesAt cfg t)
    (d : SignType) {V : Type*} (vT vJ : V) (env : V → Fin B) (ht : env vT = t) :
    (inPosPrevFormula r d vT vJ).Realize env ↔
      moveInputPosNat (u ++ w).length cfg.inputPos.val d = (env vJ : ℕ) := by
  have hp : cfg.inputPos.val < u.length + w.length + 2 := by simpa using cfg.inputPos.isLt
  have hlen : (u ++ w).length = u.length + w.length := List.length_append
  rcases d with _ | _ | _
  · -- `d = .zero`
    simp only [inPosPrevFormula, realize_rel₂, ht, hA.inPos, holds_inPos,
      moveInputPosNat, SignType.zero_eq_zero, SignType.coe_zero]
    omega
  · -- `d = .neg`
    simp only [inPosPrevFormula, Formula.realize_sup, Formula.realize_inf,
      realize_isZero hlt, Formula.realize_iExs, realize_succ hlt, realize_rel₂,
      Sum.elim_inl, Sum.elim_inr, ht, hA.inPos, holds_inPos,
      moveInputPosNat, SignType.neg_eq_neg_one, SignType.coe_neg_one]
    constructor
    · rintro (⟨hj0, hp0⟩ | ⟨y, hy, hpy⟩) <;> omega
    · intro hmove
      by_cases hp0 : cfg.inputPos.val = 0
      · exact Or.inl ⟨by omega, by omega⟩
      · right
        refine ⟨![(⟨cfg.inputPos.val, by omega⟩ : Fin B)], by dsimp; omega, rfl⟩
  · -- `d = .pos`
    simp only [inPosPrevFormula, Formula.realize_sup, Formula.realize_inf,
      Formula.realize_iExs, realize_rel₁, realize_succ hlt, realize_le hlt,
      realize_rel₂, Sum.elim_inl, Sum.elim_inr, Fin.le_def, ht, hA.inPos, holds_inPos,
      moveInputPosNat, SignType.pos_eq_one, SignType.coe_one]
    constructor
    · rintro (⟨y, ⟨hE, hsucc⟩, hpj⟩ | ⟨y, ⟨⟨⟨hE, hle⟩, hsucc⟩, hp0⟩⟩)
      · have hE' := (hend (y 0)).1 hE
        omega
      · have hE' := (hend (y 1)).1 hE
        omega
    · intro hmove
      by_cases hpe : cfg.inputPos.val = u.length + w.length + 1
      · left
        refine ⟨![(⟨u.length + w.length, by omega⟩ : Fin B)],
          ⟨(hend _).2 rfl, by dsimp; omega⟩, by omega⟩
      · right
        let j' : Fin B := ⟨cfg.inputPos.val, by omega⟩
        let eFin : Fin B := ⟨u.length + w.length, by omega⟩
        refine ⟨![j', eFin], ⟨⟨⟨(hend eFin).2 rfl, by dsimp [j', eFin]; omega⟩,
          by dsimp [j']; omega⟩, rfl⟩⟩

include hlt in
/-- Semantic characterization of `headPrevFormula`. -/
theorem realize_headPrevFormula {headSame headOpp : L'.Relations 2} {t : Fin B}
    {pos : ℤ} (hb : |pos| + 1 < B) {sign : ℤ} (hsign : sign = 1 ∨ sign = -1)
    (hSame : ∀ a : Fin B, RelMap headSame ![t, a] ↔ pos = sign * (a : ℤ))
    (hOpp : ∀ a : Fin B, RelMap headOpp ![t, a] ↔ pos = -sign * (a : ℤ))
    (d : SignType) {V : Type*} (vT vA : V) (env : V → Fin B) (ht : env vT = t) :
    (headPrevFormula r headSame headOpp d vT vA).Realize env ↔
      pos + sign * (d : ℤ) = sign * (env vA : ℤ) := by
  have hb' : |pos| < (B : ℤ) - 1 := by omega
  rw [abs_lt] at hb'
  rcases d with _ | _ | _
  · -- `d = .zero`
    simp only [headPrevFormula, realize_rel₂, ht, hSame,
      SignType.zero_eq_zero, SignType.coe_zero, mul_zero, add_zero]
  · -- `d = .neg`
    simp only [headPrevFormula, Formula.realize_iExs, Formula.realize_inf,
      realize_succ hlt, realize_rel₂, Sum.elim_inl, Sum.elim_inr, ht, hSame,
      SignType.neg_eq_neg_one, SignType.coe_neg_one]
    constructor
    · rintro ⟨y, hsucc, hpos⟩
      rcases hsign with rfl | rfl <;> omega
    · intro hmove
      have haB : (env vA : ℕ) + 1 < B := by rcases hsign with rfl | rfl <;> omega
      refine ⟨![(⟨(env vA : ℕ) + 1, haB⟩ : Fin B)], rfl, ?_⟩
      dsimp
      rcases hsign with rfl | rfl <;> omega
  · -- `d = .pos`
    simp only [headPrevFormula, Formula.realize_sup, Formula.realize_inf,
      realize_isZero hlt, Formula.realize_iExs, realize_succ hlt, realize_rel₂,
      Sum.elim_inl, Sum.elim_inr, ht, hSame, hOpp,
      SignType.pos_eq_one, SignType.coe_one, mul_one]
    constructor
    · rintro (⟨ha0, y, hsucc, hpos⟩ | ⟨y, hsucc, hpos⟩)
      · rcases hsign with rfl | rfl <;> omega
      · rcases hsign with rfl | rfl <;> omega
    · intro hmove
      by_cases ha0 : (env vA : ℕ) = 0
      · left
        refine ⟨ha0, ![(⟨1, by omega⟩ : Fin B)], by dsimp; omega, ?_⟩
        dsimp
        rcases hsign with rfl | rfl <;> omega
      · right
        refine ⟨![(⟨(env vA : ℕ) - 1, by omega⟩ : Fin B)], by dsimp; omega, ?_⟩
        dsimp
        rcases hsign with rfl | rfl <;> omega

variable [Fintype State]

include hlt in
/-- Semantic characterization of `stateStepRHS` under `AgreesAt`. -/
theorem realize_stateStepRHS [DecidableEq State]
    {u w : List Bool} {cfg : Cfg m Bool State (u ++ w)} {t : Fin B}
    (heB : u.length + w.length + 1 < B) (hb : ∀ i : Fin m, |cfg.workTapePos i| < B)
    (huLen : ∀ z : Fin B, RelMap r.uLen ![z] ↔ (z : ℕ) = u.length)
    (huBit : ∀ p : Fin B, (p : ℕ) < u.length → (RelMap r.uBit ![p] ↔ u[(p : ℕ)]? = some true))
    (hend : ∀ z : Fin B, RelMap r.endPos ![z] ↔ (z : ℕ) = u.length + w.length)
    (hcert : ∀ j : Fin B, u.length < (j : ℕ) → (j : ℕ) ≤ u.length + w.length →
      (RelMap r.certBit ![j] ↔ w[(j : ℕ) - 1 - u.length]? = some true))
    (hA : r.AgreesAt cfg t)
    (q' : Option State) {V : Type*} (vT : V) (env : V → Fin B) (ht : env vT = t) :
    (stateStepRHS r tm q' vT).Realize env ↔ (Feature.state q').Holds (tm.step cfg) := by
  simp only [stateStepRHS, Formula.realize_sup, Formula.realize_inf, Formula.realize_iSup,
    realize_rel₁, ht, hA.state,
    realize_sitFormula hlt heB hb huLen huBit hend hcert hA _ vT env ht]
  rw [holds_step_state_iff tm q']
  refine or_congr ⟨fun ⟨h, hq⟩ => ⟨h, by split_ifs at hq with h' <;> simp_all⟩,
    fun ⟨h, hq⟩ => ⟨h, by simp [hq]⟩⟩ ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact exists_congr fun y => ⟨fun ⟨hq, hy⟩ => ⟨by split_ifs at hq with h' <;> simp_all, hy⟩,
    fun ⟨hq, hy⟩ => ⟨by simp [hq], hy⟩⟩

include hlt in
/-- Semantic characterization of `outStepRHS` under `AgreesAt`. -/
theorem realize_outStepRHS {u w : List Bool} {cfg : Cfg m Bool State (u ++ w)} {t : Fin B}
    (heB : u.length + w.length + 1 < B) (hb : ∀ i : Fin m, |cfg.workTapePos i| < B)
    (huLen : ∀ z : Fin B, RelMap r.uLen ![z] ↔ (z : ℕ) = u.length)
    (huBit : ∀ p : Fin B, (p : ℕ) < u.length → (RelMap r.uBit ![p] ↔ u[(p : ℕ)]? = some true))
    (hend : ∀ z : Fin B, RelMap r.endPos ![z] ↔ (z : ℕ) = u.length + w.length)
    (hcert : ∀ j : Fin B, u.length < (j : ℕ) → (j : ℕ) ≤ u.length + w.length →
      (RelMap r.certBit ![j] ↔ w[(j : ℕ) - 1 - u.length]? = some true))
    (hA : r.AgreesAt cfg t)
    (o : OutView) {V : Type*} (vT : V) (env : V → Fin B) (ht : env vT = t) :
    (outStepRHS r tm o vT).Realize env ↔ (Feature.out o).Holds (tm.step cfg) := by
  classical
  simp only [outStepRHS, Formula.realize_sup, Formula.realize_inf, Formula.realize_iSup,
    realize_rel₁, ht, hA.state, hA.out,
    realize_sitFormula hlt heB hb huLen huBit hend hcert hA _ vT env ht]
  rw [holds_step_out_iff tm o]
  refine or_congr Iff.rfl ?_
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
  exact exists_congr fun p =>
    ⟨fun ⟨⟨ho, hs⟩, hp⟩ => ⟨by split_ifs at ho with h' <;> simp_all, hs, hp⟩,
     fun ⟨ho, hs, hp⟩ => ⟨⟨by simp [ho], hs⟩, hp⟩⟩

include hlt in
/-- Semantic characterization of `inPosStepRHS` under `AgreesAt`. -/
theorem realize_inPosStepRHS {u w : List Bool} {cfg : Cfg m Bool State (u ++ w)} {t : Fin B}
    (heB : u.length + w.length + 1 < B) (hb : ∀ i : Fin m, |cfg.workTapePos i| < B)
    (huLen : ∀ z : Fin B, RelMap r.uLen ![z] ↔ (z : ℕ) = u.length)
    (huBit : ∀ p : Fin B, (p : ℕ) < u.length → (RelMap r.uBit ![p] ↔ u[(p : ℕ)]? = some true))
    (hend : ∀ z : Fin B, RelMap r.endPos ![z] ↔ (z : ℕ) = u.length + w.length)
    (hcert : ∀ j : Fin B, u.length < (j : ℕ) → (j : ℕ) ≤ u.length + w.length →
      (RelMap r.certBit ![j] ↔ w[(j : ℕ) - 1 - u.length]? = some true))
    (hA : r.AgreesAt cfg t)
    {V : Type*} (vT vJ : V) (env : V → Fin B) (ht : env vT = t) :
    (inPosStepRHS r tm vT vJ).Realize env ↔ (Feature.inPos (env vJ : ℕ)).Holds (tm.step cfg) := by
  classical
  simp only [inPosStepRHS, Formula.realize_sup, Formula.realize_inf, Formula.realize_iSup,
    realize_rel₁, realize_rel₂, ht, hA.state, hA.inPos,
    realize_sitFormula hlt heB hb huLen huBit hend hcert hA _ vT env ht,
    realize_inPosPrevFormula hlt heB hend hA _ vT vJ env ht]
  rcases hq : cfg.state with _ | q
  · simp [hq, not_holds_sit hq]
  · simp [holds_state, hq, holds_sit_iff_eq hq, holds_inPos, step_eq_apply tm hq,
      Action.apply_inputPos, val_moveInputPos_eq_moveInputPosNat]

include hlt in
/-- Semantic characterization of `headStepRHS` (positive orientation) under `AgreesAt`. -/
theorem realize_headPosStepRHS {u w : List Bool} {cfg : Cfg m Bool State (u ++ w)} {t : Fin B}
    (heB : u.length + w.length + 1 < B) (hb : ∀ i : Fin m, |cfg.workTapePos i| + 1 < B)
    (huLen : ∀ z : Fin B, RelMap r.uLen ![z] ↔ (z : ℕ) = u.length)
    (huBit : ∀ p : Fin B, (p : ℕ) < u.length → (RelMap r.uBit ![p] ↔ u[(p : ℕ)]? = some true))
    (hend : ∀ z : Fin B, RelMap r.endPos ![z] ↔ (z : ℕ) = u.length + w.length)
    (hcert : ∀ j : Fin B, u.length < (j : ℕ) → (j : ℕ) ≤ u.length + w.length →
      (RelMap r.certBit ![j] ↔ w[(j : ℕ) - 1 - u.length]? = some true))
    (hA : r.AgreesAt cfg t)
    (i : Fin m) {V : Type*} (vT vA : V) (env : V → Fin B) (ht : env vT = t) :
    (headStepRHS r tm (r.headPos i) (r.headNeg i) .pos i vT vA).Realize env ↔
      (Feature.head i (env vA : ℤ)).Holds (tm.step cfg) := by
  classical
  have hb' : ∀ i : Fin m, |cfg.workTapePos i| < B := fun i => by have := hb i; omega
  have hSame : ∀ a' : Fin B,
      RelMap (r.headPos i) ![t, a'] ↔ cfg.workTapePos i = 1 * (a' : ℤ) := by
    intro a'; simpa using hA.headPos i a'
  have hOpp : ∀ a' : Fin B,
      RelMap (r.headNeg i) ![t, a'] ↔ cfg.workTapePos i = -1 * (a' : ℤ) := by
    intro a'; simpa using hA.headNeg i a'
  simp only [headStepRHS, Formula.realize_sup, Formula.realize_inf, Formula.realize_iSup,
    realize_rel₁, realize_rel₂, ht, hA.state, hA.headPos,
    realize_sitFormula hlt heB hb' huLen huBit hend hcert hA _ vT env ht,
    realize_headPrevFormula hlt (hb i) (Or.inl rfl) hSame hOpp _ vT vA env ht,
    SignType.pos_eq_one, one_mul]
  rcases hq : cfg.state with _ | q
  · simp [hq, not_holds_sit hq]
  · simp [holds_state, hq, holds_sit_iff_eq hq, holds_head, step_eq_apply tm hq,
      Action.apply_workTapePos]

include hlt in
/-- Semantic characterization of `headStepRHS` (negative orientation) under `AgreesAt`. -/
theorem realize_headNegStepRHS {u w : List Bool} {cfg : Cfg m Bool State (u ++ w)} {t : Fin B}
    (heB : u.length + w.length + 1 < B) (hb : ∀ i : Fin m, |cfg.workTapePos i| + 1 < B)
    (huLen : ∀ z : Fin B, RelMap r.uLen ![z] ↔ (z : ℕ) = u.length)
    (huBit : ∀ p : Fin B, (p : ℕ) < u.length → (RelMap r.uBit ![p] ↔ u[(p : ℕ)]? = some true))
    (hend : ∀ z : Fin B, RelMap r.endPos ![z] ↔ (z : ℕ) = u.length + w.length)
    (hcert : ∀ j : Fin B, u.length < (j : ℕ) → (j : ℕ) ≤ u.length + w.length →
      (RelMap r.certBit ![j] ↔ w[(j : ℕ) - 1 - u.length]? = some true))
    (hA : r.AgreesAt cfg t)
    (i : Fin m) {V : Type*} (vT vA : V) (env : V → Fin B) (ht : env vT = t) :
    (headStepRHS r tm (r.headNeg i) (r.headPos i) .neg i vT vA).Realize env ↔
      (Feature.head i (-(env vA : ℤ))).Holds (tm.step cfg) := by
  classical
  have hb' : ∀ i : Fin m, |cfg.workTapePos i| < B := fun i => by have := hb i; omega
  have hSame : ∀ a' : Fin B,
      RelMap (r.headNeg i) ![t, a'] ↔ cfg.workTapePos i = -1 * (a' : ℤ) := by
    intro a'; simpa using hA.headNeg i a'
  have hOpp : ∀ a' : Fin B,
      RelMap (r.headPos i) ![t, a'] ↔ cfg.workTapePos i = -(-1) * (a' : ℤ) := by
    intro a'; simpa using hA.headPos i a'
  have hneg_coe : ∀ d : SignType, ((-1 : ℤ) * ((SignType.neg * d : SignType) : ℤ)) = (d : ℤ) := by
    rintro (_ | _ | _) <;> rfl
  simp only [headStepRHS, Formula.realize_sup, Formula.realize_inf, Formula.realize_iSup,
    realize_rel₁, realize_rel₂, ht, hA.state, hA.headNeg,
    realize_sitFormula hlt heB hb' huLen huBit hend hcert hA _ vT env ht,
    realize_headPrevFormula hlt (hb i) (Or.inr rfl) hSame hOpp _ vT vA env ht,
    hneg_coe, neg_one_mul]
  rcases hq : cfg.state with _ | q
  · simp [hq, not_holds_sit hq]
  · simp [holds_state, hq, holds_sit_iff_eq hq, holds_head, step_eq_apply tm hq,
      Action.apply_workTapePos]

include hlt in
/-- Semantic characterization of `cellStepRHS` under `AgreesAt`. -/
theorem realize_cellStepRHS {u w : List Bool} {cfg : Cfg m Bool State (u ++ w)} {t : Fin B}
    (heB : u.length + w.length + 1 < B) (hb : ∀ i : Fin m, |cfg.workTapePos i| < B)
    (huLen : ∀ z : Fin B, RelMap r.uLen ![z] ↔ (z : ℕ) = u.length)
    (huBit : ∀ p : Fin B, (p : ℕ) < u.length → (RelMap r.uBit ![p] ↔ u[(p : ℕ)]? = some true))
    (hend : ∀ z : Fin B, RelMap r.endPos ![z] ↔ (z : ℕ) = u.length + w.length)
    (hcert : ∀ j : Fin B, u.length < (j : ℕ) → (j : ℕ) ≤ u.length + w.length →
      (RelMap r.certBit ![j] ↔ w[(j : ℕ) - 1 - u.length]? = some true))
    (hA : r.AgreesAt cfg t)
    (i : Fin m) (s : Option Bool) (z : ℤ)
    (headSame : L'.Relations 2) (cellSame : Option Bool → L'.Relations 2)
    {V : Type*} (vT vA : V) (env : V → Fin B) (ht : env vT = t)
    (hhead : RelMap headSame ![t, env vA] ↔ (Feature.head i z).Holds cfg)
    (hcell : ∀ s', RelMap (cellSame s') ![t, env vA] ↔ (Feature.cell i z s').Holds cfg) :
    (cellStepRHS r tm headSame cellSame i s vT vA).Realize env ↔
      (Feature.cell i z s).Holds (tm.step cfg) := by
  classical
  simp only [cellStepRHS, Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
    Formula.realize_iSup, realize_rel₁, realize_rel₂, ht, hA.state, hhead, hcell,
    realize_sitFormula hlt heB hb huLen huBit hend hcert hA _ vT env ht]
  rw [holds_step_cell_iff tm z s]
  refine or_congr Iff.rfl ?_
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
  exact exists_congr fun p =>
    ⟨fun ⟨⟨⟨hs, hsit⟩, hh⟩, hc⟩ => ⟨by split_ifs at hs with h' <;> simp_all, hsit, hh, hc⟩,
     fun ⟨hs, hsit, hh, hc⟩ => ⟨⟨⟨by simp [hs], hsit⟩, hh⟩, hc⟩⟩

include hlt in
/-- Semantic characterization of `initSentence`: it holds iff `AgreesAt` holds at `t = 0`. -/
theorem realize_initSentence [DecidableEq State] {input : List Bool} (hB1 : 1 < B) :
    (Fin B) ⊨ initSentence r tm ↔ r.AgreesAt (tm.initCfg input) (⟨0, by omega⟩ : Fin B) := by
  simp only [initSentence, realize_closeAll, Formula.realize_imp, Formula.realize_inf,
    Formula.realize_iInf, Formula.realize_iff, Formula.realize_iAlls, Formula.realize_iExs,
    realize_isZero hlt, realize_rel₁, realize_rel₂, realize_succ hlt,
    Sum.elim_inl, Sum.elim_inr]
  have h1_iff : ∀ j : Fin B,
      (∃ y : Fin 1 → Fin B, (y 0 : ℕ) = 0 ∧ (j : ℕ) = (y 0 : ℕ) + 1) ↔ (j : ℕ) = 1 := by
    intro j
    constructor
    · rintro ⟨y, h0, hj⟩; omega
    · intro hj
      exact ⟨![(⟨0, by omega⟩ : Fin B)], rfl, hj⟩
  constructor
  · intro h
    obtain ⟨⟨⟨hstate, hout⟩, hinPos⟩, hwork⟩ := h ![(⟨0, by omega⟩ : Fin B)] rfl
    refine ⟨fun q => ?_, fun o => ?_, fun j => ?_, fun i a => ?_, fun i a => ?_,
      fun i s a => ?_, fun i s a => ?_⟩
    · by_cases hq0 : q = some tm.q₀ <;>
        simpa [hq0, Feature.Holds, eq_comm] using hstate q
    · by_cases ho0 : o = .empty <;>
        simpa [ho0, Feature.Holds, OutView.ofList, eq_comm] using hout o
    · have hj := (hinPos ![j]).trans (h1_iff j)
      simpa [Feature.Holds, eq_comm] using hj
    · have ha := (hwork i ![a]).1.1
      simpa [Feature.Holds, eq_comm] using ha
    · have ha := (hwork i ![a]).1.2
      simpa [Feature.Holds, eq_comm] using ha
    · by_cases hs0 : s = none <;>
        simpa [hs0, Feature.Holds, eq_comm] using ((hwork i ![a]).2 s).1
    · by_cases hs0 : s = none <;>
        simpa [hs0, Feature.Holds, eq_comm] using ((hwork i ![a]).2 s).2
  · intro hA y hy0
    have hy : y 0 = ⟨0, by omega⟩ := Fin.ext hy0
    rw [hy]
    refine ⟨⟨⟨fun q => ?_, fun o => ?_⟩, fun yJ => ?_⟩, fun i yA => ⟨⟨?_, ?_⟩, fun s => ⟨?_, ?_⟩⟩⟩
    · rw [hA.state q]
      by_cases hq0 : q = some tm.q₀ <;>
        simp [hq0, Feature.Holds, eq_comm]
    · rw [hA.out o]
      by_cases ho0 : o = .empty <;>
        simp [ho0, Feature.Holds, OutView.ofList, eq_comm]
    · rw [hA.inPos (yJ 0), h1_iff (yJ 0)]
      simp [Feature.Holds, eq_comm]
    · rw [hA.headPos i (yA 0)]
      simp only [MultiTapeNTM.initCfg, Cfg.init, holds_head]
      omega
    · rw [hA.headNeg i (yA 0)]
      simp [Feature.Holds]
    · rw [hA.cellPos i s (yA 0)]
      by_cases hs0 : s = none <;>
        simp [hs0, Feature.Holds, eq_comm]
    · rw [hA.cellNeg i s (yA 0)]
      by_cases hs0 : s = none <;>
        simp [hs0, Feature.Holds, eq_comm]

end Semantics

/-! ### Full ESO tableau sentence -/

section TableauESO

variable {L₀ : Language.{0, 0}} (lt : L₀.Relations 2) (uLenRel uBitRel : L₀.Relations 1)
  {m : ℕ} {State : Type} [Fintype State] [DecidableEq State]
  (tm : MultiTapeTM m Bool State)

/-- The language of the first-order matrix of `tableauESOSentence`. -/
abbrev tableauMatrixLanguage (m : ℕ) (State : Type) : Language.{0, 0} :=
  L₀.sum (ESO.varLanguage (arity := tableauArity m State))

/-- The canonical `TableauRels` bundle in `tableauMatrixLanguage`. -/
def tableauRels : TableauRels (tableauMatrixLanguage (L₀ := L₀) m State) m State where
  lt := Sum.inl lt
  uLen := Sum.inl uLenRel
  uBit := Sum.inl uBitRel
  endPos := Sum.inr ⟨.inl (.inl ()), rfl⟩
  certBit := Sum.inr ⟨.inl (.inr (.inl ())), rfl⟩
  state q := Sum.inr ⟨.inl (.inr (.inr (.inl q))), rfl⟩
  out o := Sum.inr ⟨.inl (.inr (.inr (.inr o))), rfl⟩
  inPos := Sum.inr ⟨.inr (.inl ()), rfl⟩
  headPos i := Sum.inr ⟨.inr (.inr (.inl i)), rfl⟩
  headNeg i := Sum.inr ⟨.inr (.inr (.inr (.inl i))), rfl⟩
  cellPos i s := Sum.inr ⟨.inr (.inr (.inr (.inr (.inl (i, s))))), rfl⟩
  cellNeg i s := Sum.inr ⟨.inr (.inr (.inr (.inr (.inr (i, s))))), rfl⟩

/-- The first-order matrix of `tableauESOSentence`. -/
noncomputable def tableauMatrix : (tableauMatrixLanguage (L₀ := L₀) m State).Sentence :=
  let r := tableauRels (m := m) (State := State) lt uLenRel uBitRel
  endPosSentence r ⊓ initSentence r tm ⊓ stepSentence r tm ⊓ acceptSentence r

/-- The existential second-order sentence asserting that `tm`, started on `u ++ w` for some
certificate `w` with `u.length + w.length + 1 < B`, halts within `B - 1` steps with output
`[true]`. -/
noncomputable def tableauESOSentence : ESO.Sentence L₀ where
  Var := TableauVar m State
  arity := tableauArity m State
  matrix := tableauMatrix lt uLenRel uBitRel tm

/-- **Correctness of `tableauESOSentence` on `Fin B`.** -/
theorem realize_tableauESOSentence {B : ℕ} [L₀.Structure (Fin B)]
    (hlt0 : ∀ x : Fin 2 → Fin B, RelMap lt x ↔ x 0 < x 1)
    {u : List Bool} (huB : u.length + 1 < B)
    (huLen0 : ∀ z : Fin B, RelMap uLenRel ![z] ↔ (z : ℕ) = u.length)
    (huBit0 : ∀ p : Fin B, (p : ℕ) < u.length → (RelMap uBitRel ![p] ↔ u[(p : ℕ)]? = some true)) :
    (tableauESOSentence lt uLenRel uBitRel tm).Realize (Fin B) ↔
      ∃ w : List Bool, u.length + w.length + 1 < B ∧
        (tm.runFrom (tm.initCfg (u ++ w)) (B - 1)).state = none ∧
        (tm.runFrom (tm.initCfg (u ++ w)) (B - 1)).output = [true] := by
  classical
  have hB1 : 1 < B := by omega
  let r := tableauRels (m := m) (State := State) lt uLenRel uBitRel
  rw [tableauESOSentence, ESO.Sentence.Realize]
  constructor
  · -- Soundness
    rintro ⟨R, hmat⟩
    let _ := ESO.varLanguage.structure (arity := tableauArity m State) R
    have hlt : ∀ x : Fin 2 → Fin B, RelMap r.lt x ↔ x 0 < x 1 := hlt0
    have huLen : ∀ z : Fin B, RelMap r.uLen ![z] ↔ (z : ℕ) = u.length := huLen0
    have huBit : ∀ p : Fin B, (p : ℕ) < u.length →
        (RelMap r.uBit ![p] ↔ u[(p : ℕ)]? = some true) := huBit0
    change (endPosSentence r ⊓ initSentence r tm ⊓ stepSentence r tm ⊓ acceptSentence r).Realize
      (Fin B) at hmat
    simp only [Sentence.realize_inf] at hmat
    obtain ⟨⟨⟨hendSent, hinitSent⟩, hstepSent⟩, haccSent⟩ := hmat
    obtain ⟨e, hle_e, heB, hend⟩ := exists_of_realize_endPosSentence hlt huLen hendSent
    let L := (e : ℕ) - u.length
    have he_eq : u.length + L = (e : ℕ) := by omega
    let w : List Bool :=
      (List.range L).map fun k =>
        if hk : u.length + 1 + k < B then
          decide (RelMap r.certBit ![(⟨u.length + 1 + k, hk⟩ : Fin B)])
        else false
    have hw_len : w.length = L := by simp [w]
    have hwB : u.length + w.length + 1 < B := by omega
    have hend' : ∀ z : Fin B, RelMap r.endPos ![z] ↔ (z : ℕ) = u.length + w.length := by
      intro z; rw [hend z, hw_len, he_eq]
    have hcert : ∀ j : Fin B, u.length < (j : ℕ) → (j : ℕ) ≤ u.length + w.length →
        (RelMap r.certBit ![j] ↔ w[(j : ℕ) - 1 - u.length]? = some true) := by
      intro j hgt hle
      have hk_lt : (j : ℕ) - 1 - u.length < L := by omega
      have hj_eq : u.length + 1 + ((j : ℕ) - 1 - u.length) = (j : ℕ) := by omega
      have hjB : u.length + 1 + ((j : ℕ) - 1 - u.length) < B := by omega
      simp only [w, List.getElem?_map, List.getElem?_range hk_lt, Option.map_some,
        Option.some.injEq, hjB, ↓reduceDIte, decide_eq_true_eq]
      have hfin_eq : (⟨u.length + 1 + ((j : ℕ) - 1 - u.length), hjB⟩ : Fin B) = j :=
        Fin.ext hj_eq
      rw [hfin_eq]
    -- Unpack `stepSentence` at any `(t, t')` with `t' = t + 1`.
    simp only [stepSentence, realize_closeAll, Formula.realize_imp, Formula.realize_inf,
      Formula.realize_iInf, Formula.realize_iff, Formula.realize_iAlls, realize_succ hlt,
      realize_rel₁, realize_rel₂, Sum.elim_inl, Sum.elim_inr] at hstepSent
    -- Prove `AgreesAt` by induction on `n < B`.
    have hAgrees : ∀ (n : ℕ) (hn : n < B),
        r.AgreesAt (tm.runFrom (tm.initCfg (u ++ w)) n) ⟨n, hn⟩ := by
      intro n hn
      induction n with
      | zero =>
        simpa [runFrom] using (realize_initSentence hlt hB1).1 hinitSent
      | succ n ih =>
        let t : Fin B := ⟨n, by omega⟩
        let t' : Fin B := ⟨n + 1, hn⟩
        have hA_t := ih (by omega)
        have hb : ∀ i : Fin m,
            |(tm.runFrom (tm.initCfg (u ++ w)) n).workTapePos i| + 1 < B := by
          intro i
          have := abs_workTapePos_runFrom_le (tm := tm) (u ++ w) n i
          omega
        have hb' : ∀ i : Fin m,
            |(tm.runFrom (tm.initCfg (u ++ w)) n).workTapePos i| < B :=
          fun i => by have := hb i; omega
        obtain ⟨⟨⟨hs_state, hs_out⟩, hs_inPos⟩, hs_work⟩ := hstepSent ![t, t'] rfl
        rw [runFrom_succ]
        refine ⟨fun q' => ?_, fun o => ?_, fun j => ?_, fun i a => ?_, fun i a => ?_,
          fun i s a => ?_, fun i s a => ?_⟩
        · exact (hs_state q').trans
            (realize_stateStepRHS hlt hwB hb' huLen huBit hend' hcert hA_t q' 0 ![t, t'] rfl)
        · exact (hs_out o).trans
            (realize_outStepRHS hlt hwB hb' huLen huBit hend' hcert hA_t o 0 ![t, t'] rfl)
        · exact (hs_inPos ![j]).trans
            (realize_inPosStepRHS hlt hwB hb' huLen huBit hend' hcert hA_t
              (.inl 0) (.inr 0) (Sum.elim ![t, t'] ![j]) rfl)
        · exact (hs_work i ![a]).1.1.trans
            (realize_headPosStepRHS hlt hwB hb huLen huBit hend' hcert hA_t i
              (.inl 0) (.inr 0) (Sum.elim ![t, t'] ![a]) rfl)
        · exact (hs_work i ![a]).1.2.trans
            (realize_headNegStepRHS hlt hwB hb huLen huBit hend' hcert hA_t i
              (.inl 0) (.inr 0) (Sum.elim ![t, t'] ![a]) rfl)
        · exact ((hs_work i ![a]).2 s).1.trans
            (realize_cellStepRHS hlt hwB hb' huLen huBit hend' hcert hA_t i s (a : ℤ)
              (r.headPos i) (r.cellPos i)
              (.inl 0 : Fin 2 ⊕ Fin 1) (.inr 0) (Sum.elim ![t, t'] ![a]) rfl
              (hA_t.headPos i a) (fun s' => hA_t.cellPos i s' a))
        · exact ((hs_work i ![a]).2 s).2.trans
            (realize_cellStepRHS hlt hwB hb' huLen huBit hend' hcert hA_t i s (-(a : ℤ))
              (r.headNeg i) (r.cellNeg i)
              (.inl 0 : Fin 2 ⊕ Fin 1) (.inr 0) (Sum.elim ![t, t'] ![a]) rfl
              (hA_t.headNeg i a) (fun s' => hA_t.cellNeg i s' a))
    -- Specialize `hAgrees` at `B - 1`.
    have hA_last := hAgrees (B - 1) (by omega)
    simp only [acceptSentence, realize_closeAll, Formula.realize_imp, Formula.realize_inf,
      realize_isMax hlt, realize_rel₁] at haccSent
    obtain ⟨hstate_last, hout_last⟩ := haccSent ![(⟨B - 1, by omega⟩ : Fin B)] (by dsimp)
    refine ⟨w, hwB, (hA_last.state none).1 hstate_last, ?_⟩
    exact OutView.ofList_eq_one_iff.1 ((hA_last.out (.one true)).1 hout_last)
  · -- Completeness
    rintro ⟨w, hwB, hhalt, hout⟩
    let cfgAt (t : Fin B) : Cfg m Bool State (u ++ w) :=
      tm.runFrom (tm.initCfg (u ++ w)) (t : ℕ)
    let R : ∀ idx : TableauVar m State, Set (Fin (tableauArity m State idx) → Fin B)
      | .inl (.inl ()) => {x : Fin 1 → Fin B | (x 0 : ℕ) = u.length + w.length}
      | .inl (.inr (.inl ())) =>
        {x : Fin 1 → Fin B | w[(x 0 : ℕ) - 1 - u.length]? = some true}
      | .inl (.inr (.inr (.inl q))) =>
        {x : Fin 1 → Fin B | (Feature.state q).Holds (cfgAt (x 0))}
      | .inl (.inr (.inr (.inr o))) =>
        {x : Fin 1 → Fin B | (Feature.out o).Holds (cfgAt (x 0))}
      | .inr (.inl ()) =>
        {x : Fin 2 → Fin B | (Feature.inPos (x 1 : ℕ)).Holds (cfgAt (x 0))}
      | .inr (.inr (.inl i)) =>
        {x : Fin 2 → Fin B | (Feature.head i (x 1 : ℤ)).Holds (cfgAt (x 0))}
      | .inr (.inr (.inr (.inl i))) =>
        {x : Fin 2 → Fin B | (Feature.head i (-(x 1 : ℤ))).Holds (cfgAt (x 0))}
      | .inr (.inr (.inr (.inr (.inl (i, s))))) =>
        {x : Fin 2 → Fin B | (Feature.cell i (x 1 : ℤ) s).Holds (cfgAt (x 0))}
      | .inr (.inr (.inr (.inr (.inr (i, s))))) =>
        {x : Fin 2 → Fin B | (Feature.cell i (-(x 1 : ℤ)) s).Holds (cfgAt (x 0))}
    refine ⟨R, ?_⟩
    let _ := ESO.varLanguage.structure (arity := tableauArity m State) R
    have hlt : ∀ x : Fin 2 → Fin B, RelMap r.lt x ↔ x 0 < x 1 := hlt0
    have huLen : ∀ z : Fin B, RelMap r.uLen ![z] ↔ (z : ℕ) = u.length := huLen0
    have huBit : ∀ p : Fin B, (p : ℕ) < u.length →
        (RelMap r.uBit ![p] ↔ u[(p : ℕ)]? = some true) := huBit0
    have hend : ∀ z : Fin B, RelMap r.endPos ![z] ↔ (z : ℕ) = u.length + w.length :=
      fun _ => Iff.rfl
    have hcert : ∀ j : Fin B, u.length < (j : ℕ) → (j : ℕ) ≤ u.length + w.length →
        (RelMap r.certBit ![j] ↔ w[(j : ℕ) - 1 - u.length]? = some true) :=
      fun _ _ _ => Iff.rfl
    have hAgrees : ∀ t : Fin B, r.AgreesAt (cfgAt t) t := fun _ =>
      ⟨fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ _ => Iff.rfl,
        fun _ _ => Iff.rfl, fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl⟩
    change (endPosSentence r ⊓ initSentence r tm ⊓ stepSentence r tm ⊓ acceptSentence r).Realize
      (Fin B)
    simp only [Sentence.realize_inf]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · exact realize_endPosSentence_of_canonical hlt (Nat.le_add_right _ _) hwB huLen hend
    · exact (realize_initSentence hlt hB1).2 (hAgrees ⟨0, by omega⟩)
    · simp only [stepSentence, realize_closeAll, Formula.realize_imp, Formula.realize_inf,
        Formula.realize_iInf, Formula.realize_iff, Formula.realize_iAlls, realize_succ hlt,
        realize_rel₁, realize_rel₂, Sum.elim_inl, Sum.elim_inr]
      intro y hsucc
      let t := y 0
      let t' := y 1
      have hA_t := hAgrees t
      have hb : ∀ i : Fin m, |(cfgAt t).workTapePos i| + 1 < B := by
        intro i
        have := abs_workTapePos_runFrom_le (tm := tm) (u ++ w) (t : ℕ) i
        change |(tm.runFrom (tm.initCfg (u ++ w)) (t : ℕ)).workTapePos i| + 1 < B
        omega
      have hb' : ∀ i : Fin m, |(cfgAt t).workTapePos i| < B :=
        fun i => by have := hb i; omega
      have hstep_eq : cfgAt t' = tm.step (cfgAt t) := by
        dsimp [cfgAt]
        rw [hsucc, runFrom_succ]
      have hA_t' : r.AgreesAt (tm.step (cfgAt t)) t' := by
        rw [← hstep_eq]
        exact hAgrees t'
      refine ⟨⟨⟨fun q' => ?_, fun o => ?_⟩, fun yJ => ?_⟩,
        fun i yA => ⟨⟨?_, ?_⟩, fun s => ⟨?_, ?_⟩⟩⟩
      · exact (hA_t'.state q').trans
          (realize_stateStepRHS hlt hwB hb' huLen huBit hend hcert hA_t q' 0 y rfl).symm
      · exact (hA_t'.out o).trans
          (realize_outStepRHS hlt hwB hb' huLen huBit hend hcert hA_t o 0 y rfl).symm
      · exact (hA_t'.inPos (yJ 0)).trans
          (realize_inPosStepRHS hlt hwB hb' huLen huBit hend hcert hA_t
            (.inl 0) (.inr 0) (Sum.elim y yJ) rfl).symm
      · exact (hA_t'.headPos i (yA 0)).trans
          (realize_headPosStepRHS hlt hwB hb huLen huBit hend hcert hA_t i
            (.inl 0) (.inr 0) (Sum.elim y yA) rfl).symm
      · exact (hA_t'.headNeg i (yA 0)).trans
          (realize_headNegStepRHS hlt hwB hb huLen huBit hend hcert hA_t i
            (.inl 0) (.inr 0) (Sum.elim y yA) rfl).symm
      · exact (hA_t'.cellPos i s (yA 0)).trans
          (realize_cellStepRHS hlt hwB hb' huLen huBit hend hcert hA_t i s (yA 0 : ℤ)
            (r.headPos i) (r.cellPos i)
            (.inl 0 : Fin 2 ⊕ Fin 1) (.inr 0) (Sum.elim y yA) rfl
            (hA_t.headPos i (yA 0)) (fun s' => hA_t.cellPos i s' (yA 0))).symm
      · exact (hA_t'.cellNeg i s (yA 0)).trans
          (realize_cellStepRHS hlt hwB hb' huLen huBit hend hcert hA_t i s (-(yA 0 : ℤ))
            (r.headNeg i) (r.cellNeg i)
            (.inl 0 : Fin 2 ⊕ Fin 1) (.inr 0) (Sum.elim y yA) rfl
            (hA_t.headNeg i (yA 0)) (fun s' => hA_t.cellNeg i s' (yA 0))).symm
    · simp only [acceptSentence, realize_closeAll, Formula.realize_imp, Formula.realize_inf,
        realize_isMax hlt, realize_rel₁]
      intro y hmax
      change (Feature.state none).Holds (tm.runFrom (tm.initCfg (u ++ w)) (y 0 : ℕ)) ∧
        (Feature.out (.one true)).Holds (tm.runFrom (tm.initCfg (u ++ w)) (y 0 : ℕ))
      rw [hmax]
      exact ⟨hhalt, OutView.ofList_eq_one_iff.2 hout⟩

end TableauESO

end FO

namespace Vocabulary

variable {L : Language.{u, v}} (v : Vocabulary L)
  {m : ℕ} {State : Type} [Fintype State] [DecidableEq State]
  (tm : MultiTapeTM m Bool State)

/-- Specialization of `FO.tableauESOSentence` to `v.powerLanguage.sum inputVarLanguage`. -/
noncomputable def tableauESOSentence :
    ESO.Sentence (v.powerLanguage.sum inputVarLanguage) :=
  FO.tableauESOSentence (L₀ := v.powerLanguage.sum inputVarLanguage)
    (Sum.inl v.powerLt) (Sum.inr uLenSym) (Sum.inr uBitSym) tm

/-- **Correctness of `v.tableauESOSentence` on `Fin B`.** When `I_in` satisfies the layout
specification for `u`, `(v.tableauESOSentence tm).Realize (Fin B)` holds if and only if
`CookLevin.tableau tm u L (B - 1)` is satisfiable for some certificate length `L` with
`u.length + L + 1 < B`. -/
theorem realize_tableauESOSentence (a : EncodedStructure) (B : ℕ)
    (I_in : ∀ b : Bool, Set (Fin ((fun _ : Bool => 1) b) → Fin B))
    {u : List Bool} (huB : u.length + 1 < B)
    (huLen : ∀ z : Fin B, ![z] ∈ I_in true ↔ (z : ℕ) = u.length)
    (huBit : ∀ p : Fin B, (p : ℕ) < u.length →
      (![p] ∈ I_in false ↔ u[(p : ℕ)]? = some true)) :
    (letI := v.powerStructure a B;
      letI := ESO.varLanguage.structure (arity := fun _ : Bool => 1) I_in;
      (v.tableauESOSentence tm).Realize (Fin B)) ↔
      ∃ L : ℕ, u.length + L + 1 < B ∧
        (CookLevin.tableau tm u L (B - 1)).Satisfiable := by
  let _ := v.powerStructure a B
  let _ := ESO.varLanguage.structure (arity := fun _ : Bool => 1) I_in
  have h := FO.realize_tableauESOSentence (L₀ := v.powerLanguage.sum inputVarLanguage)
    (Sum.inl v.powerLt) (Sum.inr uLenSym) (Sum.inr uBitSym) tm
    (fun _ => Iff.rfl) huB huLen huBit
  rw [tableauESOSentence, h]
  simp only [CookLevin.tableau_satisfiable_iff]
  constructor
  · rintro ⟨w, hwB, hhalt, hout⟩
    exact ⟨w.length, hwB, w, rfl, hhalt, hout⟩
  · rintro ⟨L, hLB, w, rfl, hhalt, hout⟩
    exact ⟨w, hLB, hhalt, hout⟩

end Vocabulary

end Cslib.Logic
