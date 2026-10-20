/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.TaggedInterpretation
public import Complexity.Logics.SecondOrder.Existential
public import Mathlib.Data.Set.Card
import Mathlib.Tactic.FinCases

/-!
# Satisfiability of CNF structures

A formula in conjunctive normal form is given as a finite structure for the language
`CNF.language` of two binary relation symbols `pos` and `neg`. Every element `c` names a clause
and a variable: the clause named by `c` has the positive literal `x` when `pos(c, x)` holds and the
negative literal `¬x` when `neg(c, x)` holds. An element related to nothing names the empty clause.
A structure is **satisfiable** (`CNF.Satisfiable`) when some assignment of truth values to the
elements satisfies every clause, that is, when it satisfies the existential second-order sentence
`∃ S, ∀ c, ∃ x, (pos(c, x) ∧ S x) ∨ (neg(c, x) ∧ ¬ S x)`. It is a **3-CNF** structure
(`CNF.IsThreeCNF`) when every clause has at most three literals.

Descriptive complexity presents satisfiability as a class of finite structures in this way
[Immerman, Chapter 7][Immerman1999]; the conventions above are fixed here. A formula with `m`
clauses over `n` variables is presented by a structure with `max m n` elements: the clauses and the
variables are numbered from the same elements, and the elements naming no clause of the formula
name the tautology `x ∨ ¬x` of their own variable. The empty structure presents the empty
formula, which is satisfiable.

The classes `CNF.sat` and `CNF.threeSat` of satisfiable structures and of satisfiable 3-CNF
structures are existential second-order definable, hence closed under isomorphism, and they are
invariant under disjoint copies, so that tagged interpretations reduce to them.

## Main definitions

* `Cslib.Logic.FO.CNF.language`: the language of CNF structures, with `CNF.pos` and `CNF.neg`.
* `Cslib.Logic.FO.CNF.literals`: the literals of the clause named by an element.
* `Cslib.Logic.FO.CNF.Satisfies`, `Cslib.Logic.FO.CNF.Satisfiable`: satisfying assignments and
  satisfiability.
* `Cslib.Logic.FO.CNF.IsThreeCNF`: every clause has at most three literals.
* `Cslib.Logic.FO.CNF.sat`, `Cslib.Logic.FO.CNF.threeSat`: the classes SAT and 3SAT.
* `Cslib.Logic.FO.CNF.satSentence`, `Cslib.Logic.FO.CNF.threeCNFSentence`: their defining
  existential second-order and first-order sentences.

## Main results

* `Cslib.Logic.FO.CNF.realize_satSentence`, `Cslib.Logic.FO.CNF.realize_threeCNFSentence`: the
  semantics of the defining sentences.
* `Cslib.Logic.FO.CNF.definable_sat`, `Cslib.Logic.FO.CNF.definable_threeSat`: SAT and 3SAT are
  existential second-order definable.
* `Cslib.Logic.FO.CNF.isoClosed_sat`, `Cslib.Logic.FO.CNF.copyInvariant_sat` and their 3SAT
  versions.
* `Cslib.Logic.FO.CNF.satisfies_clause_iff_of_templates`: the clauses of a CNF structure
  interpreted by templates.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999]
-/

@[expose] public section

universe u v w

namespace Cslib.Logic.FO.CNF

open FirstOrder Language Structure CategoryTheory

/-! ### The language -/

/-- The relation symbols of CNF structures: the positive and the negative occurrence of a
variable in a clause. -/
inductive Rel : ℕ → Type
  | pos : Rel 2
  | neg : Rel 2
  deriving DecidableEq

/-- The **language of CNF structures**, with two binary relation symbols. -/
protected def language : Language :=
  ⟨fun _ => Empty, Rel⟩
  deriving IsRelational

/-- `pos(c, x)`: the variable `x` occurs positively in the clause `c`. -/
abbrev pos : CNF.language.Relations 2 :=
  .pos

/-- `neg(c, x)`: the variable `x` occurs negatively in the clause `c`. -/
abbrev neg : CNF.language.Relations 2 :=
  .neg

/-- The relation symbol of the literals of a polarity: `pos` for `true`, `neg` for `false`. -/
def lit : Bool → CNF.language.Relations 2
  | true => pos
  | false => neg

@[simp]
theorem lit_true : lit true = pos :=
  rfl

@[simp]
theorem lit_false : lit false = neg :=
  rfl

variable {M : Type*} [CNF.language.Structure M] {N : Type*} [CNF.language.Structure N]

theorem comp_pair {α β : Type*} (f : α → β) (a b : α) : f ∘ ![a, b] = ![f a, f b] := by
  funext i
  fin_cases i <;> rfl

/-- An isomorphism preserves the relations of pairs. -/
theorem relMap_pair_equiv (e : M ≃[CNF.language] N) (R : CNF.language.Relations 2) (a b : M) :
    RelMap R ![e a, e b] ↔ RelMap R ![a, b] := by
  rw [← e.map_rel R ![a, b], comp_pair]

/-! ### Satisfiability -/

/-- The literals of the clause named by `c`: a polarity and a variable. -/
def literals (c : M) : Set (Bool × M) :=
  {l | RelMap (lit l.1) ![c, l.2]}

theorem mem_literals {c : M} {l : Bool × M} : l ∈ literals c ↔ RelMap (lit l.1) ![c, l.2] :=
  Iff.rfl

/-- An assignment **satisfies** a CNF structure when every clause has a positive literal whose
variable is true or a negative literal whose variable is false. -/
def Satisfies (A : M → Prop) : Prop :=
  ∀ c, ∃ x, (RelMap pos ![c, x] ∧ A x) ∨ (RelMap neg ![c, x] ∧ ¬A x)

/-- A CNF structure is **satisfiable** when some assignment satisfies it. -/
def Satisfiable (M : Type*) [CNF.language.Structure M] : Prop :=
  ∃ A : M → Prop, Satisfies A

theorem satisfies_iff (A : M → Prop) :
    Satisfies A ↔ ∀ c, ∃ l ∈ literals c, (A l.2 ↔ l.1 = true) := by
  refine forall_congr' fun c => ⟨fun ⟨x, h⟩ => ?_, fun ⟨⟨b, x⟩, hl, h⟩ => ⟨x, ?_⟩⟩
  · rcases h with h | h
    · exact ⟨(true, x), h.1, by simp [h.2]⟩
    · exact ⟨(false, x), h.1, by simp [h.2]⟩
  · cases b
    · exact .inr ⟨hl, by simpa using h⟩
    · exact .inl ⟨hl, by simpa using h⟩

/-- Satisfiability is invariant under isomorphism. -/
theorem Satisfiable.of_equiv (e : M ≃[CNF.language] N) (h : Satisfiable M) : Satisfiable N := by
  obtain ⟨A, hA⟩ := h
  refine ⟨fun y => A (e.symm y), fun c => ?_⟩
  obtain ⟨x, hx⟩ := hA (e.symm c)
  have hrel (R : CNF.language.Relations 2) : RelMap R ![c, e x] ↔ RelMap R ![e.symm c, x] := by
    rw [← relMap_pair_equiv e, e.apply_symm_apply]
  refine ⟨e x, ?_⟩
  simpa only [hrel, e.symm_apply_apply] using hx

theorem satisfiable_iff_of_equiv (e : M ≃[CNF.language] N) : Satisfiable M ↔ Satisfiable N :=
  ⟨Satisfiable.of_equiv e, Satisfiable.of_equiv e.symm⟩

/-! ### 3-CNF structures -/

/-- A CNF structure is a **3-CNF** structure when every clause has at most three literals. -/
def IsThreeCNF (M : Type*) [CNF.language.Structure M] : Prop :=
  ∀ c : M, (literals c).encard ≤ 3

/-- A clause has at most three literals exactly when it has no four distinct ones. -/
theorem encard_literals_le_three_iff (c : M) :
    (literals c).encard ≤ 3 ↔ ¬∃ l : Fin 4 → Bool × M, (∀ i, l i ∈ literals c) ∧
      Function.Injective l := by
  rw [← Set.le_encard_iff_exists_fin_injective, not_le,
    show ((4 : ℕ) : ℕ∞) = ((3 : ℕ) : ℕ∞) + 1 by norm_cast, ENat.lt_natCast_add_one_iff]
  rfl

theorem isThreeCNF_iff_of_equiv (e : M ≃[CNF.language] N) : IsThreeCNF M ↔ IsThreeCNF N := by
  have hlit (c : M) : literals (e c) = Prod.map id e '' literals c := by
    ext ⟨b, y⟩
    simp only [mem_literals, Set.mem_image, Prod.exists, Prod.map, id, Prod.mk.injEq]
    refine ⟨fun h => ⟨b, e.symm y, ?_, rfl, e.apply_symm_apply y⟩, ?_⟩
    · rwa [← relMap_pair_equiv e, e.apply_symm_apply]
    · rintro ⟨b', x, hx, rfl, rfl⟩
      rwa [← relMap_pair_equiv e] at hx
  have hinj : Function.Injective (Prod.map (id : Bool → Bool) e) :=
    Function.Injective.prodMap (fun _ _ h => h) e.injective
  refine ⟨fun h c => ?_, fun h c => ?_⟩
  · rw [← e.apply_symm_apply c, hlit, hinj.encard_image]
    exact h _
  · rw [← hinj.encard_image, ← hlit]
    exact h _

/-! ### The classes SAT and 3SAT -/

/-- **SAT**: the class of satisfiable CNF structures. -/
def sat : Set (Bundled.{w} CNF.language.Structure) :=
  {M | Satisfiable M}

/-- **3SAT**: the class of satisfiable 3-CNF structures. -/
def threeSat : Set (Bundled.{w} CNF.language.Structure) :=
  {M | IsThreeCNF M ∧ Satisfiable M}

theorem isoClosed_sat : IsoClosed sat.{w} :=
  fun _ _ _ e => satisfiable_iff_of_equiv e

theorem isoClosed_threeSat : IsoClosed threeSat.{w} :=
  fun _ _ _ e => and_congr (isThreeCNF_iff_of_equiv e) (satisfiable_iff_of_equiv e)

/-- The empty structure is satisfiable. -/
theorem satisfiable_of_isEmpty [IsEmpty M] : Satisfiable M :=
  ⟨fun _ => True, fun c => isEmptyElim c⟩

theorem isThreeCNF_of_isEmpty [IsEmpty M] : IsThreeCNF M :=
  fun c => isEmptyElim c

/-! ### Copies -/

section Copies

variable {J : Type*}

theorem literals_copies (j : J) (c : M) :
    literals (M := Copies J M) ⟨j, c⟩ =
      (fun l : Bool × M => (l.1, (⟨j, l.2⟩ : Copies J M))) '' literals c := by
  ext ⟨b, ⟨j', x⟩⟩
  simp only [mem_literals, Copies.relMap_copies_two, Set.mem_image, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨rfl, hx⟩
    exact ⟨b, x, hx, rfl, rfl⟩
  · rintro ⟨b', x', hx, rfl, h⟩
    cases h
    exact ⟨rfl, hx⟩

/-- A positive number of disjoint copies of a CNF structure is satisfiable exactly when the
structure is. -/
theorem satisfiable_copies_iff [Nonempty J] : Satisfiable (Copies J M) ↔ Satisfiable M := by
  constructor
  · rintro ⟨A, hA⟩
    obtain ⟨j₀⟩ := ‹Nonempty J›
    refine ⟨fun x => A ⟨j₀, x⟩, fun c => ?_⟩
    obtain ⟨⟨j, x⟩, hx⟩ := hA ⟨j₀, c⟩
    simp only [Copies.relMap_copies_two] at hx
    rcases hx with ⟨⟨rfl, h⟩, hA⟩ | ⟨⟨rfl, h⟩, hA⟩
    · exact ⟨x, .inl ⟨h, hA⟩⟩
    · exact ⟨x, .inr ⟨h, hA⟩⟩
  · rintro ⟨A, hA⟩
    refine ⟨fun x => A x.val, fun ⟨j, c⟩ => ?_⟩
    obtain ⟨x, hx⟩ := hA c
    refine ⟨⟨j, x⟩, ?_⟩
    simpa only [Copies.relMap_copies_two, true_and] using hx

theorem isThreeCNF_copies_iff [Nonempty J] : IsThreeCNF (Copies J M) ↔ IsThreeCNF M := by
  have hinj (j : J) : Function.Injective fun l : Bool × M => (l.1, (⟨j, l.2⟩ : Copies J M)) := by
    intro l l' h
    simp only [Prod.mk.injEq, Copies.mk.injEq, true_and] at h
    exact Prod.ext h.1 h.2
  refine ⟨fun h c => ?_, fun h ⟨j, c⟩ => ?_⟩
  · obtain ⟨j₀⟩ := ‹Nonempty J›
    rw [← (hinj j₀).encard_image, ← literals_copies]
    exact h _
  · rw [literals_copies, (hinj j).encard_image]
    exact h c

theorem copyInvariant_sat : CopyInvariant sat.{w} :=
  fun _ _ _ _ _ _ => satisfiable_copies_iff

theorem copyInvariant_threeSat : CopyInvariant threeSat.{w} :=
  fun _ _ _ _ _ _ => and_congr isThreeCNF_copies_iff satisfiable_copies_iff

end Copies

/-! ### CNF structures interpreted by templates -/

section Templates

open TaggedInterpretation

variable {L : Language.{u, v}} {T : Type*} {ι : T → Type*} [∀ t, Finite (ι t)]
  {I : TaggedInterpretation L CNF.language T ι} {temps : ∀ t, Bool → List (Template L ι t)}
  {M : Type w} [L.Structure M]

/-- In a CNF structure interpreted by templates, the literals of a polarity of a clause are the
elements related to it by the templates of that polarity. -/
theorem relMap_lit_of_templates
    (hI : ∀ b ts, I.rel (lit b) ts = binaryRel (fun t w => Template.listFormula (temps t b) w) ts)
    (b : Bool) (c y : I.Model M) :
    RelMap (lit b) ![c, y] ↔ ∃ τ ∈ temps c.1 b, τ.Holds c.2.1 y.toSigma := by
  rw [relMap_binaryRel (hI b), Template.realize_listFormula]
  rfl

/-- In a CNF structure interpreted by templates, an assignment satisfies a clause when a template
of a polarity applies to its coordinates and relates it to a variable with that truth value. -/
theorem satisfies_clause_iff_of_templates
    (hI : ∀ b ts, I.rel (lit b) ts = binaryRel (fun t w => Template.listFormula (temps t b) w) ts)
    (A : I.Model M → Prop) (c : I.Model M) :
    (∃ y, (RelMap pos ![c, y] ∧ A y) ∨ (RelMap neg ![c, y] ∧ ¬A y)) ↔
      (∃ τ ∈ temps c.1 true, τ.guard.Realize c.2.1 ∧
        ∃ y hy, τ.Compat c.2.1 y ∧ A ⟨τ.target, y, hy⟩) ∨
      (∃ τ ∈ temps c.1 false, τ.guard.Realize c.2.1 ∧
        ∃ y hy, τ.Compat c.2.1 y ∧ ¬A ⟨τ.target, y, hy⟩) := by
  have hp := relMap_lit_of_templates hI true c
  have hn := relMap_lit_of_templates hI false c
  simp only [lit_true, lit_false] at hp hn
  constructor
  · rintro ⟨⟨w, z, hz⟩, ⟨hr, ha⟩ | ⟨hr, ha⟩⟩
    · obtain ⟨τ, hτ, hg, y, he, hc⟩ := (hp _).1 hr
      obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 he
      cases eq_of_heq h
      exact .inl ⟨τ, hτ, hg, _, hz, hc, ha⟩
    · obtain ⟨τ, hτ, hg, y, he, hc⟩ := (hn _).1 hr
      obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 he
      cases eq_of_heq h
      exact .inr ⟨τ, hτ, hg, _, hz, hc, ha⟩
  · rintro (⟨τ, hτ, hg, y, hy, hc, ha⟩ | ⟨τ, hτ, hg, y, hy, hc, ha⟩)
    · exact ⟨⟨τ.target, y, hy⟩, .inl ⟨(hp _).2 ⟨τ, hτ, hg, y, rfl, hc⟩, ha⟩⟩
    · exact ⟨⟨τ.target, y, hy⟩, .inr ⟨(hn _).2 ⟨τ, hτ, hg, y, rfl, hc⟩, ha⟩⟩

end Templates

/-! ### Defining sentences -/

/-- The symbol `pos` among those of the satisfiability sentence. -/
abbrev posSym : (CNF.language.sum (ESO.varLanguage fun _ : Unit => 1)).Relations 2 :=
  Sum.inl pos

/-- The symbol `neg` among those of the satisfiability sentence. -/
abbrev negSym : (CNF.language.sum (ESO.varLanguage fun _ : Unit => 1)).Relations 2 :=
  Sum.inl neg

/-- The relation variable `S` of the satisfiability sentence, the set of true variables. -/
abbrev trueSym : (CNF.language.sum (ESO.varLanguage fun _ : Unit => 1)).Relations 1 :=
  Sum.inr ⟨(), rfl⟩

/-- The first-order part of the satisfiability sentence:
`∀ c, ∃ x, (pos(c, x) ∧ S x) ∨ (neg(c, x) ∧ ¬ S x)`. -/
def satMatrix : (CNF.language.sum (ESO.varLanguage fun _ : Unit => 1)).Sentence :=
  ∀' ∃' ((posSym.boundedFormula₂ &0 &1 ⊓ trueSym.boundedFormula₁ &1) ⊔
    (negSym.boundedFormula₂ &0 &1 ⊓ ∼(trueSym.boundedFormula₁ &1)))

/-- The **satisfiability sentence** `∃ S, ∀ c, ∃ x, (pos(c, x) ∧ S x) ∨ (neg(c, x) ∧ ¬ S x)`. -/
def satSentence : ESO.Sentence CNF.language :=
  ⟨Unit, fun _ => 1, satMatrix⟩

theorem relMap_posSym (R : Unit → Set (Fin 1 → M)) (x : Fin 2 → M) :
    @RelMap _ M (@sumStructure _ _ M _ (ESO.varLanguage.structure R)) 2 posSym x ↔
      RelMap pos x :=
  Iff.rfl

theorem relMap_negSym (R : Unit → Set (Fin 1 → M)) (x : Fin 2 → M) :
    @RelMap _ M (@sumStructure _ _ M _ (ESO.varLanguage.structure R)) 2 negSym x ↔
      RelMap neg x :=
  Iff.rfl

theorem relMap_trueSym (R : Unit → Set (Fin 1 → M)) (x : Fin 1 → M) :
    @RelMap _ M (@sumStructure _ _ M _ (ESO.varLanguage.structure R)) 1 trueSym x ↔ x ∈ R () :=
  Iff.rfl

theorem realize_satMatrix (R : Unit → Set (Fin 1 → M)) :
    (letI := ESO.varLanguage.structure (arity := fun _ : Unit => 1) R; M ⊨ satMatrix) ↔
      Satisfies fun x => ![x] ∈ R () := by
  simp [satMatrix, Sentence.Realize, Formula.Realize, Fin.snoc, relMap_posSym, relMap_negSym,
    relMap_trueSym, Satisfies]

theorem realize_satSentence : satSentence.Realize M ↔ Satisfiable M := by
  change (∃ R : Unit → Set (Fin 1 → M),
    letI := ESO.varLanguage.structure (arity := fun _ : Unit => 1) R; M ⊨ satMatrix) ↔ _
  simp only [realize_satMatrix]
  refine ⟨fun ⟨R, h⟩ => ⟨_, h⟩, fun ⟨A, hA⟩ => ⟨fun _ => {v | A (v 0)}, ?_⟩⟩
  simpa using hA

/-- **SAT is existential second-order definable.** -/
theorem definable_sat : ESO.Definable sat.{w} :=
  ⟨satSentence, fun _ _ => realize_satSentence.symm⟩

/-- The formula in the variables `c` (`Sum.inl ()`) and `x₀, …, x₃` (`Sum.inr i`) saying that the
literals `(bs i, x i)` of the clause `c` are distinct. -/
noncomputable def fourLiteralsFormula (bs : Fin 4 → Bool) : CNF.language.Formula (Unit ⊕ Fin 4) :=
  Formula.iInf (fun i => (lit (bs i)).formula₂ (.var (.inl ())) (.var (.inr i))) ⊓
    Formula.iInf fun ij : Fin 4 × Fin 4 =>
      if ij.1 ≠ ij.2 ∧ bs ij.1 = bs ij.2 then ∼(varEq (.inr ij.1) (.inr ij.2)) else ⊤

/-- The **3-CNF sentence**: no clause has four distinct literals. -/
noncomputable def threeCNFSentence : CNF.language.Sentence :=
  closeAll Unit ∼(Formula.iSup fun bs : Fin 4 → Bool => Formula.iExs (Fin 4)
    (fourLiteralsFormula bs))

theorem realize_iExs_fourLiteralsFormula (c : M) :
    (Formula.iSup fun bs : Fin 4 → Bool => Formula.iExs (Fin 4) (fourLiteralsFormula bs)).Realize
        (fun _ : Unit => c) ↔
      ∃ l : Fin 4 → Bool × M, (∀ i, l i ∈ literals c) ∧ Function.Injective l := by
  classical
  simp only [Formula.realize_iSup, Formula.realize_iExs, fourLiteralsFormula,
    Formula.realize_inf, Formula.realize_iInf, Formula.realize_rel₂, Term.realize_var,
    Sum.elim_inl, Sum.elim_inr, Prod.forall]
  constructor
  · rintro ⟨bs, xs, hlit, hne⟩
    refine ⟨fun i => (bs i, xs i), hlit, fun i j h => ?_⟩
    by_contra hij
    have hb : bs i = bs j := congrArg Prod.fst h
    have hx : xs i = xs j := congrArg Prod.snd h
    have := hne i j
    split_ifs at this with hc
    · exact this ((realize_varEq (L := CNF.language) _ _ _).2 hx)
    · exact hc ⟨hij, hb⟩
  · rintro ⟨l, hlit, hinj⟩
    refine ⟨fun i => (l i).1, fun i => (l i).2, hlit, fun i j => ?_⟩
    split_ifs with h
    · simp only [Formula.realize_not, realize_varEq, Sum.elim_inr]
      exact fun hx => h.1 (hinj (Prod.ext h.2 hx))
    · simp

theorem realize_threeCNFSentence : M ⊨ threeCNFSentence ↔ IsThreeCNF M := by
  simp only [threeCNFSentence, realize_closeAll, Formula.realize_not]
  refine ⟨fun h c => ?_, fun h v => ?_⟩
  · rw [encard_literals_le_three_iff, ← realize_iExs_fourLiteralsFormula]
    exact h fun _ => c
  · rw [show v = fun _ => v () from funext fun _ => rfl, realize_iExs_fourLiteralsFormula,
      ← encard_literals_le_three_iff]
    exact h _

/-- The sentence saying that no clause is empty: `∀ c, ∃ x, pos(c, x) ∨ neg(c, x)`. -/
def nonemptyClausesSentence : CNF.language.Sentence :=
  ∀' ∃' (pos.boundedFormula₂ &0 &1 ⊔ neg.boundedFormula₂ &0 &1)

theorem realize_nonemptyClausesSentence :
    M ⊨ nonemptyClausesSentence ↔ ∀ c : M, (literals c).Nonempty := by
  simp only [nonemptyClausesSentence, Sentence.Realize, Formula.Realize,
    BoundedFormula.realize_all, BoundedFormula.realize_ex, BoundedFormula.realize_sup,
    BoundedFormula.realize_rel₂]
  refine forall_congr' fun c => ⟨fun ⟨x, hx⟩ => ?_, fun ⟨⟨b, x⟩, hx⟩ => ⟨x, ?_⟩⟩
  · rcases hx with hx | hx
    · exact ⟨(true, x), by simpa [mem_literals, Fin.snoc] using hx⟩
    · exact ⟨(false, x), by simpa [mem_literals, Fin.snoc] using hx⟩
  · cases b
    · exact .inr (by simpa [mem_literals, Fin.snoc] using hx)
    · exact .inl (by simpa [mem_literals, Fin.snoc] using hx)

/-- Every clause of a satisfiable CNF structure is nonempty. -/
theorem Satisfiable.literals_nonempty (h : Satisfiable M) (c : M) : (literals c).Nonempty := by
  obtain ⟨A, hA⟩ := h
  obtain ⟨x, ⟨hx, -⟩ | ⟨hx, -⟩⟩ := hA c
  · exact ⟨(true, x), hx⟩
  · exact ⟨(false, x), hx⟩

/-- **3-CNF structures form a first-order definable class.** -/
theorem definable_isThreeCNF :
    FO.Definable {M : Bundled.{w} CNF.language.Structure | IsThreeCNF M} :=
  ⟨threeCNFSentence, fun _ _ => realize_threeCNFSentence.symm⟩

/-- **3SAT is existential second-order definable.** -/
theorem definable_threeSat : ESO.Definable threeSat.{w} :=
  (ESO.Definable.of_fo definable_isThreeCNF).inter definable_sat

end Cslib.Logic.FO.CNF
