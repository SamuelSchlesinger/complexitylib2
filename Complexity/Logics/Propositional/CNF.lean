/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Std.Sat.CNF.Literal

/-!
# Conjunctive normal form

Propositional formulas in conjunctive normal form over an arbitrary type of variables `V`, with
their Boolean semantics. A literal (`Std.Sat.Literal`) is a variable together with the polarity
under which it is read, a clause is a list of literals read disjunctively, and a formula is a list
of clauses read conjunctively.

Formulas are plain lists so that reductions can build them with list operations and their sizes
can be read off directly. This is why `Std.Sat.CNF`, an array-based structure built for efficient
SAT solving in `bv_decide`, is not reused; neither is `Cslib.Logic.PL.Proposition`, whose
connectives are binary and whose formulas are not in normal form. The names follow `Std.Sat.CNF`
where they overlap (`relabel`, `eval`).

Reductions to satisfiability usually build formulas over structured variables (indexed by time
steps, tape cells, and so on) and relabel them injectively at the end; `CNF.satisfiable_relabel`
says that this preserves satisfiability.

## Main definitions

* `Cslib.Logic.PL.Literal`, `Clause`, `CNF`.
* `Cslib.Logic.PL.CNF.eval`, `Cslib.Logic.PL.CNF.Satisfiable`.
* `Cslib.Logic.PL.CNF.vars`: the variables of a formula, in order of occurrence.
* `Cslib.Logic.PL.CNF.relabel`: rename the variables of a formula.
* `Cslib.Logic.PL.CNF.countUnsat`: the number of clauses an assignment falsifies.
* `Cslib.Logic.PL.Clause.imp`, `Cslib.Logic.PL.Clause.impLits`: the clause `h₁ ∧ ⋯ ∧ hₙ → c`, for
  variables or literals `hᵢ`.

## Main results

* `Cslib.Logic.PL.CNF.eval_eq_true_iff`, `Cslib.Logic.PL.Clause.eval_eq_true_iff`: the semantics
  as quantifiers over clauses and literals.
* `Cslib.Logic.PL.CNF.eval_congr`: a formula only depends on its variables.
* `Cslib.Logic.PL.CNF.satisfiable_relabel`: injective relabelling preserves satisfiability.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 2.3][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Logic.PL

/-- A literal: a variable and the polarity under which it is read. -/
abbrev Literal (V : Type*) : Type _ := Std.Sat.Literal V

/-- A clause is a disjunction of literals. -/
abbrev Clause (V : Type*) : Type _ := List (Literal V)

/-- A formula in conjunctive normal form is a conjunction of clauses. -/
abbrev CNF (V : Type*) : Type _ := List (Clause V)

variable {V W : Type*}

/-- A literal `(v, b)` holds under `σ` when `σ v = b`. -/
def Literal.eval (σ : V → Bool) (l : Literal V) : Bool := σ l.1 == l.2

/-- A clause holds when one of its literals does. -/
def Clause.eval (σ : V → Bool) (c : Clause V) : Bool := c.any (Literal.eval σ)

/-- A formula holds when all of its clauses do. -/
def CNF.eval (σ : V → Bool) (φ : CNF V) : Bool := φ.all (Clause.eval σ)

/-- A formula is satisfiable when some assignment makes it true. -/
def CNF.Satisfiable (φ : CNF V) : Prop := ∃ σ : V → Bool, φ.eval σ = true

/-! ### Semantics -/

@[simp] theorem Literal.eval_eq_true_iff (σ : V → Bool) (v : V) (b : Bool) :
    Literal.eval σ (v, b) = true ↔ σ v = b := by
  simp [Literal.eval]

/-- A clause holds when some literal does. -/
theorem Clause.eval_eq_true_iff (σ : V → Bool) (c : Clause V) :
    c.eval σ = true ↔ ∃ l ∈ c, σ l.1 = l.2 := by
  simp [Clause.eval, Literal.eval]

@[simp] theorem Clause.eval_nil (σ : V → Bool) : Clause.eval σ [] = false := rfl

@[simp] theorem Clause.eval_cons (σ : V → Bool) (l : Literal V) (c : Clause V) :
    Clause.eval σ (l :: c) = (Literal.eval σ l || Clause.eval σ c) := rfl

/-- A formula holds when every clause does. -/
theorem CNF.eval_eq_true_iff (σ : V → Bool) (φ : CNF V) :
    φ.eval σ = true ↔ ∀ c ∈ φ, c.eval σ = true := by
  simp [CNF.eval]

@[simp] theorem CNF.eval_nil (σ : V → Bool) : CNF.eval σ [] = true := rfl

@[simp] theorem CNF.eval_append (σ : V → Bool) (φ ψ : CNF V) :
    CNF.eval σ (φ ++ ψ) = (CNF.eval σ φ && CNF.eval σ ψ) := by
  simp [CNF.eval, List.all_append]

@[simp] theorem CNF.eval_cons (σ : V → Bool) (c : Clause V) (φ : CNF V) :
    CNF.eval σ (c :: φ) = (Clause.eval σ c && CNF.eval σ φ) := rfl

/-- A formula made of one clause per element of a list holds when each of those clauses does. -/
theorem CNF.eval_map_eq_true_iff {ι : Type*} (σ : V → Bool) (l : List ι) (f : ι → Clause V) :
    CNF.eval σ (l.map f) = true ↔ ∀ i ∈ l, (f i).eval σ = true := by
  simp [CNF.eval_eq_true_iff]

/-- A formula made of one block of clauses per element of a list holds when each block does. -/
theorem CNF.eval_flatMap_eq_true_iff {ι : Type*} (σ : V → Bool) (l : List ι) (f : ι → CNF V) :
    CNF.eval σ (l.flatMap f) = true ↔ ∀ i ∈ l, CNF.eval σ (f i) = true := by
  simp only [CNF.eval_eq_true_iff, List.mem_flatMap, forall_exists_index, and_imp]
  exact ⟨fun h i hi c hc => h c i hi hc, fun h c i hi hc => h i hi c hc⟩

/-! ### Variables -/

/-- The variables of a formula, in order of occurrence and with repetitions. -/
def CNF.vars (φ : CNF V) : List V := φ.flatten.map Prod.fst

theorem CNF.length_vars (φ : CNF V) : φ.vars.length = (φ.map List.length).sum := by
  simp [CNF.vars, List.length_flatten, Function.comp_def]

/-- A formula only depends on the values of its variables. -/
theorem CNF.eval_congr {σ τ : V → Bool} {φ : CNF V} (h : ∀ v ∈ φ.vars, σ v = τ v) :
    φ.eval σ = φ.eval τ := by
  have key : ∀ c ∈ φ, ∀ l ∈ c, σ l.1 = τ l.1 := fun c hc l hl =>
    h l.1 (List.mem_map.2 ⟨l, List.mem_flatten.2 ⟨c, hc, hl⟩, rfl⟩)
  rw [Bool.eq_iff_iff, CNF.eval_eq_true_iff, CNF.eval_eq_true_iff]
  refine forall₂_congr fun c hc => ?_
  rw [Clause.eval_eq_true_iff, Clause.eval_eq_true_iff]
  exact exists_congr fun l => and_congr_right fun hl => by rw [key c hc l hl]

/-- The number of clauses of a formula, counted with repetition, mentioning the variable `v`. -/
def CNF.occurrences [DecidableEq V] (φ : CNF V) (v : V) : ℕ :=
  φ.countP fun c => decide (∃ l ∈ c, l.1 = v)

/-! ### Implications -/

/-- The clause `l₁ ∧ ⋯ ∧ lₙ → c` for literals `lᵢ`, that is `¬l₁ ∨ ⋯ ∨ ¬lₙ ∨ c`. -/
def Clause.impLits (hyps : List (Literal V)) (concl : V) : Clause V :=
  hyps.map Std.Sat.Literal.negate ++ [(concl, true)]

@[simp] theorem Clause.eval_impLits (σ : V → Bool) (hyps : List (Literal V)) (concl : V) :
    (Clause.impLits hyps concl).eval σ = true ↔
      ((∀ l ∈ hyps, σ l.1 = l.2) → σ concl = true) := by
  simp only [Clause.impLits, Clause.eval_eq_true_iff, List.mem_append, List.mem_map,
    List.mem_singleton]
  constructor
  · rintro ⟨l, hl | rfl, hσ⟩ hh
    · obtain ⟨h, hmem, rfl⟩ := hl
      simp [Std.Sat.Literal.negate, hh h hmem] at hσ
    · exact hσ
  · intro himp
    by_cases hall : ∀ l ∈ hyps, σ l.1 = l.2
    · exact ⟨_, Or.inr rfl, himp hall⟩
    · push Not at hall
      obtain ⟨⟨v, b⟩, hmem, hf⟩ := hall
      refine ⟨(v, !b), Or.inl ⟨(v, b), hmem, rfl⟩, ?_⟩
      cases b <;> simpa using hf

/-- The clause `h₁ ∧ ⋯ ∧ hₙ → c`, that is `¬h₁ ∨ ⋯ ∨ ¬hₙ ∨ c`. -/
def Clause.imp (hyps : List V) (concl : V) : Clause V :=
  Clause.impLits (hyps.map (·, true)) concl

@[simp] theorem Clause.eval_imp (σ : V → Bool) (hyps : List V) (concl : V) :
    (Clause.imp hyps concl).eval σ = true ↔ ((∀ h ∈ hyps, σ h = true) → σ concl = true) := by
  simp [Clause.imp]

/-! ### Relabelling -/

/-- Rename the variables of a clause along `f`. -/
def Clause.relabel (f : V → W) (c : Clause V) : Clause W := c.map (Prod.map f id)

/-- Rename the variables of a formula along `f`. -/
def CNF.relabel (f : V → W) (φ : CNF V) : CNF W := φ.map (Clause.relabel f)

@[simp] theorem Clause.eval_relabel (f : V → W) (σ : W → Bool) (c : Clause V) :
    (c.relabel f).eval σ = c.eval (σ ∘ f) := by
  induction c with
  | nil => rfl
  | cons l c ih => simp_all [Clause.relabel, Literal.eval]

@[simp] theorem CNF.eval_relabel (f : V → W) (σ : W → Bool) (φ : CNF V) :
    (φ.relabel f).eval σ = φ.eval (σ ∘ f) := by
  induction φ with
  | nil => rfl
  | cons c φ ih => simp_all [CNF.relabel]

@[simp] theorem Clause.length_relabel (f : V → W) (c : Clause V) :
    (c.relabel f).length = c.length := List.length_map _

/-- Relabelling along an injective map preserves satisfiability. An assignment of the new
variables restricts to the old ones, and an assignment of the old variables extends along `f`. -/
theorem CNF.satisfiable_relabel {f : V → W} (hf : Function.Injective f) (φ : CNF V) :
    (φ.relabel f).Satisfiable ↔ φ.Satisfiable := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ ∘ f, by simpa using hσ⟩
  · rintro ⟨σ, hσ⟩
    classical
    refine ⟨Function.extend f σ (fun _ => false), ?_⟩
    rwa [CNF.eval_relabel, Function.extend_comp hf]

/-- The number of clauses of `φ`, counted with multiplicity, that the assignment `σ` falsifies. -/
def CNF.countUnsat (σ : V → Bool) (φ : CNF V) : ℕ :=
  φ.countP fun c ↦ !c.eval σ

/-- An assignment falsifies no clause exactly when it satisfies the formula. -/
theorem CNF.countUnsat_eq_zero_iff {σ : V → Bool} {φ : CNF V} :
    φ.countUnsat σ = 0 ↔ φ.eval σ = true := by
  simp [countUnsat, List.countP_eq_zero, CNF.eval_eq_true_iff]

/-- An assignment falsifies at most all the clauses. -/
theorem CNF.countUnsat_le_length (σ : V → Bool) (φ : CNF V) : φ.countUnsat σ ≤ φ.length :=
  List.countP_le_length

end Cslib.Logic.PL
