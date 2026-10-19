/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Reduction
import Complexity.Computability.Machines.Turing.MultiTape.Halting
import Complexity.Computability.Machines.Turing.MultiTape.Halting.Rice

/-! Concrete machines that halt and loop, their descriptions inside and outside the halting and
acceptance problems, the machines diverging on a verdict, the diagonal machine against candidate
deciders, a nontrivial property of self-applied behaviour for Rice's theorem, decidable sets and
reductions, input prefixes built into descriptions, the recursion theorem, Rice's theorem for a
nontrivial property of behaviour, and axiom guards. -/

namespace ComplexityTests.Halting

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal

/-! ### A machine that halts and a machine that loops -/

/-- Halt at once with output `[b]`. -/
def answer (b : Bool) : MultiTapeTM 0 Bool Unit :=
  MultiTapeTM.ofTr () fun _ _ _ =>
    { inputTape := 0, workTapes := Fin.elim0, output := some b, state := none }

/-- Stay in place forever. -/
def spin : MultiTapeTM 0 Bool Unit :=
  MultiTapeTM.ofTr () fun _ _ _ =>
    { inputTape := 0, workTapes := Fin.elim0, output := none, state := some () }

theorem answer_computes (b : Bool) (x : List Bool) : (answer b).Computes x [b] := by
  refine ⟨1, ?_, ?_⟩ <;>
  · rw [runFrom_one, MultiTapeTM.step_of_state (q := ()) rfl]
    simp [answer, Action.apply]

theorem not_halts_spin (x : List Bool) : ¬spin.Halts x := by
  rintro ⟨t, ht⟩
  refine MultiTapeTM.not_halts_of_repeat_nonhalt (tm := spin) (spin.initCfg x) (by simp) 0 ?_ t ht
  rw [zero_add, runFrom_one, MultiTapeTM.step_of_state (q := ()) rfl]
  exact Cfg.ext_zero_tapes (by simp [spin, Action.apply]) (by simp [spin, Action.apply])
    (by simp [spin, Action.apply])

example (b : Bool) (x : List Bool) : (answer b).Halts x := (answer_computes b x).halts

/-- A machine halts with one output only. -/
example (x : List Bool) : ¬(answer false).Computes x [true] :=
  fun h => by simpa using (answer_computes false x).unique h

/-- A halted computation is a computation within bounds. -/
example (b : Bool) (x : List Bool) :
    ∃ t s, (answer b).ComputesInTimeAndSpace x [b] t s :=
  (answer_computes b x).exists_computesInTimeAndSpace

/-! ### Descriptions in and out of the problems -/

/-- The numbering of the single state. -/
def unitNum : Unit ↪ ℕ := ⟨fun _ => 0, fun _ _ _ => rfl⟩

/-- The halting problem is about runs of the universal function. -/
example (p : List Bool × List Bool) :
    p ∈ haltingProblem ↔ ∃ t, (universal (decodeDesc p.1, p.2.map eBit, t)).2 = true :=
  Iff.rfl

example (b : Bool) (x : List Bool) : (eDesc (desc unitNum eBit (answer b)), x) ∈ haltingProblem :=
  (desc_mem_haltingProblem_iff unitNum (answer b) x).mpr (answer_computes b x).halts

example (x : List Bool) : (eDesc (desc unitNum eBit spin), x) ∉ haltingProblem :=
  fun h => not_halts_spin x ((desc_mem_haltingProblem_iff unitNum spin x).mp h)

example (b : Bool) : eDesc (desc unitNum eBit (answer b)) ∈ selfHaltingProblem :=
  (desc_mem_selfHaltingProblem_iff unitNum (answer b)).mpr (answer_computes b _).halts

example : eDesc (desc unitNum eBit spin) ∉ selfHaltingProblem :=
  fun h => not_halts_spin _ ((desc_mem_selfHaltingProblem_iff unitNum spin).mp h)

example (x : List Bool) : (eDesc (desc unitNum eBit (answer true)), x) ∈ acceptanceProblem :=
  (desc_mem_acceptanceProblem_iff unitNum (answer true) x).mpr (answer_computes true x)

example (x : List Bool) : (eDesc (desc unitNum eBit (answer false)), x) ∉ acceptanceProblem :=
  fun h => by
    simpa using (answer_computes false x).unique
      ((desc_mem_acceptanceProblem_iff unitNum (answer false) x).mp h)

example : eDesc (desc unitNum eBit (answer true)) ∈ selfAcceptanceProblem :=
  (desc_mem_selfAcceptanceProblem_iff unitNum (answer true)).mpr (answer_computes true _)

example : eDesc (desc unitNum eBit spin) ∉ selfAcceptanceProblem :=
  fun h => not_halts_spin _ ((desc_mem_selfAcceptanceProblem_iff unitNum spin).mp h).halts

/-! ### Diverging on a verdict -/

/-- After the verdict `true`, the machine loops: a concrete machine that never halts. -/
example (x : List Bool) : ¬(answer true).partialize.Halts x := by
  rw [Computes.halts_partialize (r := none) (answer_computes true x)]
  simp

/-- After the verdict `false`, the machine halts with the rest of the output, here empty. -/
example (x : List Bool) : (answer false).partialize.Computes x [] :=
  (Computes.partialize (r := some []) (answer_computes false x) []).mpr rfl

/-- The numbering of the states of a machine diverging on a verdict. -/
noncomputable def pNum : Option Unit × Option Bool ↪ ℕ :=
  (Fintype.equivFin _).toEmbedding.trans Fin.valEmbedding

/-- **The diagonal machine against the candidate decider "everything halts"**: the candidate's
verdict `true`, followed by divergence, is computed by `answer true`, and the diagonal machine
`(answer true).partialize` does not halt on its own description, which the candidate claims. -/
example : ¬(answer true).partialize.Halts (eDesc (desc pNum eBit (answer true).partialize)) := by
  rw [Computes.halts_partialize (r := none) (answer_computes true _)]
  simp

/-- **The diagonal machine against the candidate decider "nothing halts"**: it halts on its own
description. -/
example : (answer false).partialize.Halts (eDesc (desc pNum eBit (answer false).partialize)) := by
  rw [Computes.halts_partialize (r := some []) (answer_computes false _)]
  rfl

/-! ### Rice's theorem for the behaviour on self-descriptions -/

/-- The words whose machine halts on them with the empty output. -/
def haltsEmpty : Set (List Bool) := {w | (decodeDesc w).Computes (w.map eBit) []}

theorem desc_mem_haltsEmpty_iff {k : ℕ} {State : Type} [Fintype State] (eS : State ↪ ℕ)
    (tm : MultiTapeTM k Bool State) :
    eDesc (desc eS eBit tm) ∈ haltsEmpty ↔ tm.Computes (eDesc (desc eS eBit tm)) [] := by
  change (decodeDesc (eDesc (desc eS eBit tm))).Computes ((eDesc (desc eS eBit tm)).map eBit)
    (([] : List Bool).map eBit) ↔ _
  rw [decodeDesc_eDesc, Desc.computes_desc]

/-- The property is nontrivial: it holds for the description of a machine halting with the empty
output... -/
example : eDesc (desc pNum eBit (answer false).partialize) ∈ haltsEmpty :=
  (desc_mem_haltsEmpty_iff pNum _).mpr
    ((Computes.partialize (r := some []) (answer_computes false _) []).mpr rfl)

/-- ... and fails for the description of a machine that loops. -/
example : eDesc (desc unitNum eBit spin) ∉ haltsEmpty :=
  fun h => not_halts_spin _ ((desc_mem_haltsEmpty_iff unitNum spin).mp h).halts

/-- It separates divergence from halting with the empty output, so it is undecidable. -/
example : ¬IsDecidable haltsEmpty encBits :=
  not_isDecidable_of_separates_self_desc none (some [])
    (fun _ _ _ eS tm h hmem => nomatch (h []).mp ((desc_mem_haltsEmpty_iff eS tm).mp hmem))
    fun _ _ _ eS tm h => (desc_mem_haltsEmpty_iff eS tm).mpr ((h []).mpr rfl)

/-! ### Decidable sets and reductions -/

/-- A decidable set: the empty word. -/
example : IsDecidable {w : List Bool | w.isEmpty = true} encBits :=
  isDecidable_iff.mpr ⟨List.isEmpty,
    (ComputableTidilyInDegree.isEmpty (enc₁ := encBool) (enc := encBits)).isComputable,
    fun _ => Iff.rfl⟩

example : IsDecidable (∅ : Set (List Bool)) encBits :=
  isDecidable_iff.mpr ⟨fun _ => false, (ComputableTidilyInDegree.const false).isComputable,
    fun _ => by simp⟩

/-- Undecidability transfers to complements and along reductions. -/
example : ¬IsDecidable haltingProblemᶜ (encPair encBits encBits) := by
  rw [isDecidable_compl_iff]
  exact not_isDecidable_haltingProblem

example : MappingReducible encBits (encPair encBits encBits) selfHaltingProblemᶜ haltingProblemᶜ :=
  selfHaltingProblem_mappingReducible.compl

example : MappingReducible encBits (encPair encBits encBits) selfHaltingProblem haltingProblem :=
  (MappingReducible.refl encBits _).trans selfHaltingProblem_mappingReducible

/-- Polynomial-time reductions are mapping reductions. -/
example {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {A : Set α} {B : Set β}
    (h : Cslib.Complexity.PolyTimeReducible encA encB A B) : MappingReducible encA encB A B :=
  let ⟨f, hf, hAB⟩ := h
  ⟨f, hf.isComputable, hAB⟩

/-- No computable function decides, from the pair of a description and an input, whether the
described machine halts with output `[true]`. -/
example : ¬IsDecidable acceptanceProblem (encPair encBits encBits) :=
  not_isDecidable_acceptanceProblem

/-! ### Input prefixes built into descriptions -/

/-- Halt at once if the input starts with `true`, and stay in place forever otherwise. -/
def firstBit : MultiTapeTM 0 Bool Unit :=
  MultiTapeTM.ofTr () fun _ i _ =>
    { inputTape := 0, workTapes := Fin.elim0, output := none,
      state := if i = some true then none else some () }

theorem halts_firstBit (x : List Bool) : firstBit.Halts (true :: x) :=
  ⟨1, by
    rw [runFrom_one, MultiTapeTM.step_of_state (q := ()) rfl]
    simp [firstBit, Action.apply, Cfg.Halted, MultiTapeNTM.initCfg, Cfg.inputSymbol]⟩

theorem not_halts_firstBit (x : List Bool) : ¬firstBit.Halts (false :: x) := by
  rintro ⟨t, ht⟩
  refine MultiTapeTM.not_halts_of_repeat_nonhalt (tm := firstBit) (firstBit.initCfg _) (by simp) 0
    ?_ t ht
  rw [zero_add, runFrom_one, MultiTapeTM.step_of_state (q := ()) rfl]
  exact Cfg.ext_zero_tapes
    (by simp [firstBit, Action.apply, MultiTapeNTM.initCfg, Cfg.inputSymbol])
    (by simp [firstBit, Action.apply]) (by simp [firstBit, Action.apply])

/-- With the prefix `[true]` built in, `firstBit` halts on every input... -/
example (x : List Bool) : (hardwire (desc unitNum eBit firstBit) [true]).Halts (x.map eBit) :=
  (Desc.halts_hardwire _ _ x).mpr ((Desc.halts_desc unitNum eBit firstBit (true :: x)).mpr
    (halts_firstBit x))

/-- ... and with the prefix `[false]`, on none. -/
example (x : List Bool) : ¬(hardwire (desc unitNum eBit firstBit) [false]).Halts (x.map eBit) := by
  intro h
  rw [Desc.halts_hardwire, List.singleton_append, Desc.halts_desc] at h
  exact not_halts_firstBit x h

/-- Building in a prefix keeps the output. -/
example (b : Bool) (p x : List Bool) :
    (hardwire (desc unitNum eBit (answer b)) p).Computes (x.map eBit) [eBit b] :=
  (Desc.computes_hardwire _ p x _).mpr
    ((Desc.computes_desc unitNum eBit (answer b) (p ++ x) [b]).mpr (answer_computes b _))

/-- Building in a prefix is computable in polynomial time. -/
example : ComputableTidilyInPolyTime (fun dp : Desc × List Bool => hardwire dp.1 dp.2)
    (encPair eDesc encBits) eDesc :=
  computableTidilyInPolyTime_hardwire

/-! ### The recursion theorem and Rice's theorem -/

theorem behaviour_answer (b : Bool) (x : List Bool) :
    behaviour (eDesc (desc unitNum eBit (answer b))) x [eBit b] := by
  rw [behaviour, decodeDesc_eDesc, ← List.map_singleton, Desc.computes_desc]
  exact answer_computes b x

theorem not_behaviour_spin (x : List Bool) (o : List ℕ) :
    ¬behaviour (eDesc (desc unitNum eBit spin)) x o := fun h => by
  rw [behaviour, decodeDesc_eDesc] at h
  exact not_halts_spin x ((Desc.halts_desc unitNum eBit spin x).mp
    (Desc.halts_iff_exists_computes.mpr ⟨o, h⟩))

/-- A machine behaving as the description chosen by a constant verdict. -/
example : ∃ e : List Bool, ∀ (x : List Bool) (o : List ℕ),
    (decodeDesc e).Computes (x.map eBit) o ↔
      (desc unitNum eBit (answer true)).Computes (x.map eBit) o :=
  exists_behaviour_eq (f := fun _ => true) (ComputableTidilyInDegree.const true).isComputable
    fun _ => desc unitNum eBit (answer true)

/-- **Rice's theorem** for the nontrivial property of halting on the empty input: the description
of `answer false` has it and that of `spin` does not, so it is undecidable. -/
example : ¬IsDecidable {w | behaviour w ∈ {B : List Bool → List ℕ → Prop | ∃ o, B [] o}}
    encBits :=
  rice (w₀ := eDesc (desc unitNum eBit spin)) (w₁ := eDesc (desc unitNum eBit (answer false)))
    (fun ⟨o, h⟩ => not_behaviour_spin [] o h) ⟨_, behaviour_answer false []⟩

/-- The descriptions of machines accepting every input are undecidable. -/
example : ¬IsDecidable {w | ∀ x, behaviour w x [eBit true]} encBits :=
  not_isDecidable_of_behaviour (fun _ _ h hw x => h ▸ hw x)
    (w₀ := eDesc (desc unitNum eBit spin)) (w₁ := eDesc (desc unitNum eBit (answer true)))
    (fun h => not_behaviour_spin [] _ (h [])) (behaviour_answer true)

/-! ### Axioms -/

/--
info: 'Turing.MultiTapeTM.halting_problem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.halting_problem

/--
info: 'Turing.MultiTapeTM.halting_problem_self' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.halting_problem_self

/--
info: 'Turing.MultiTapeTM.acceptance_problem' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.acceptance_problem

/--
info: 'Turing.MultiTapeTM.acceptance_problem_self' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.acceptance_problem_self

/--
info: 'Turing.MultiTapeTM.not_isDecidable_haltingProblem' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.not_isDecidable_haltingProblem

/--
info: 'Turing.MultiTapeTM.not_isDecidable_selfHaltingProblem' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.not_isDecidable_selfHaltingProblem

/--
info: 'Turing.MultiTapeTM.not_isDecidable_acceptanceProblem' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.not_isDecidable_acceptanceProblem

/--
info: 'Turing.MultiTapeTM.not_isDecidable_selfAcceptanceProblem' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.not_isDecidable_selfAcceptanceProblem

/--
info: 'Turing.MultiTapeTM.not_isDecidable_of_separates_self_desc' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.not_isDecidable_of_separates_self_desc

/--
info: 'Turing.MultiTapeTM.exists_self_desc' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.exists_self_desc

/--
info: 'Turing.MultiTapeTM.Computes.partialize' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.Computes.partialize

/--
info: 'Turing.MultiTapeTM.IsComputable.comp' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.IsComputable.comp

/--
info: 'Turing.MultiTapeTM.isComputable_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.isComputable_iff

/--
info: 'Turing.MultiTapeTM.IsDecidable.of_mappingReducible' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.IsDecidable.of_mappingReducible

/--
info: 'Turing.MultiTapeTM.Universal.Desc.computes_hardwire' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.Universal.Desc.computes_hardwire

/--
info: 'Turing.MultiTapeTM.Universal.Desc.halts_hardwire' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.Universal.Desc.halts_hardwire

/--
info: 'Turing.MultiTapeTM.Universal.computableTidilyInPolyTime_hardwire' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.Universal.computableTidilyInPolyTime_hardwire

/--
info: 'Turing.MultiTapeTM.Universal.Desc.computes_dispatch' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.Universal.Desc.computes_dispatch

/--
info: 'Turing.MultiTapeTM.exists_behaviour_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.exists_behaviour_eq

/--
info: 'Turing.MultiTapeTM.rice' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.rice

/--
info: 'Turing.MultiTapeTM.not_isDecidable_of_behaviour' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.not_isDecidable_of_behaviour

end ComplexityTests.Halting
