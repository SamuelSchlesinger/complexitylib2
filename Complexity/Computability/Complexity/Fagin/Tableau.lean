/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Fagin.Tableau.Defs
public import Complexity.Computability.Complexity.Fagin.Tableau.Semantics

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

The relation-symbol bundle `FO.TableauRels` and component first-order formulas are defined in
`Complexity.Computability.Complexity.Fagin.Tableau.Defs`, and the configuration-agreement predicate
(`FO.TableauRels.AgreesAt`) and realization equivalences are proved in
`Complexity.Computability.Complexity.Fagin.Tableau.Semantics`; both are re-exported here.

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
