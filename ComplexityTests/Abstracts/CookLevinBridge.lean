/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import ComplexityTests.Abstracts.Check
import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Complexity.Problems.ExactThreeSAT
import Complexity.Computability.Complexity.Classes.NP
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Bridge for the Cook–Levin formal abstract

Connects the self-contained definitions in `CookLevinAbstract.lean` (plain CNF formulas as nested
lists of `(ℕ × Bool)`, framed binary encodings, and plain upstream `Cslib` polynomial-time Turing
machine computability) to `Cslib.Complexity.CookLevin.SAT_npComplete`, `UNSAT_coNPComplete`, and
`ExactThreeSAT_npComplete`. Also hosts the `#guard_msgs` regression test suite (`AuditTests`) for
`#check_abstract`.
-/

namespace ComplexityTests.Abstracts.CookLevinBridge

open Turing Turing.MultiTapeTM Cslib.Logic.PL Cslib.Complexity

/-- Framing a bitstring by doubling each bit `b` as `[true, b]` and terminating with `[false]`. -/
def frame (w : List Bool) : List Bool := w.flatMap (fun b => [true, b]) ++ [false]

/-- Encoding a pair by framing the first component followed by the second. -/
def encodePair {α β : Type} (encA : α → List Bool) (encB : β → List Bool) (p : α × β) :
    List Bool :=
  frame (encA p.1) ++ encB p.2

/-- Encoding a list by concatenating the framed encodings of its elements. -/
def encodeList {α : Type} (enc : α → List Bool) (l : List α) : List Bool :=
  l.flatMap (frame ∘ enc)

/-- Encoding a CNF formula over `ℕ` as a list of clauses of `(ℕ × Bool)` literals. -/
def encodeCNF : List (List (ℕ × Bool)) → List Bool :=
  encodeList (encodeList (encodePair Nat.bits (fun b => [b])))

theorem encodePair_injective {α β : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool) :
    Function.Injective (encodePair encA encB) :=
  (Turing.MultiTapeTM.encPair encA encB).injective

theorem encodeCNF_injective : Function.Injective encodeCNF :=
  Cslib.Complexity.encCNF.injective

/-- Embedding of pairs using `encodePair`. Definitionally equal to `Turing.MultiTapeTM.encPair`. -/
def encPair {α β : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool) : α × β ↪ List Bool :=
  ⟨encodePair encA encB, encodePair_injective encA encB⟩

/-- Embedding of CNF formulas using `encodeCNF`, matching `Cslib.Complexity.encCNF`. -/
def encCNF : List (List (ℕ × Bool)) ↪ List Bool :=
  ⟨encodeCNF, encodeCNF_injective⟩

/-- Plain polynomial-time computability in terms of upstream `Cslib` multi-tape Turing machines. -/
def ComputableInPolyTime {α β : Type} (f : α → β)
    (encA : α ↪ List Bool) (encB : β ↪ List Bool) : Prop :=
  ∃ t s : ℕ → ℕ, Cslib.PolynomiallyBounded t ∧ Cslib.PolynomiallyBounded s ∧
    Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength f encA encB t s

theorem computableInPolyTime_iff_tidy {α β : Type} {f : α → β}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} :
    ComputableInPolyTime f encA encB ↔ ComputableTidilyInPolyTime f encA encB :=
  computableTidilyInPolyTime_iff_exists_computableInTimeAndSpaceOfLength.symm

/-- Plain polynomial-time verifier condition. -/
def IsVerifier {α : Type} (enc : α ↪ List Bool) (p : Polynomial ℕ)
    (V : α × List Bool → Bool) (A : Set α) : Prop :=
  ∀ a, a ∈ A ↔ ∃ w : List Bool, w.length = p.eval (enc a).length ∧ V (a, w) = true

/-- The class `NP` defined directly from plain polynomial-time verifiers. -/
def NP {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc (Function.Embedding.refl _))
      ⟨fun b => [b], by intro a b h; injection h⟩ ∧
    IsVerifier enc p V A}

/-- The class `coNP` of complements of `NP` problems. -/
def coNP {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | Aᶜ ∈ NP enc}

theorem mem_NP_iff {α : Type} {enc : α ↪ List Bool} {A : Set α} :
    A ∈ NP enc ↔ A ∈ Cslib.Complexity.NP enc := by
  rw [Cslib.Complexity.mem_NP_iff_exists_computableInTimeAndSpaceOfLength]
  constructor
  · rintro ⟨p, V, ⟨t, s, ht, hs, hV⟩, hA⟩
    exact ⟨p, V, t, s, ht, hs, hV, hA⟩
  · rintro ⟨p, V, t, s, ht, hs, hV, hA⟩
    exact ⟨p, V, ⟨t, s, ht, hs, hV⟩, hA⟩

theorem mem_coNP_iff {α : Type} {enc : α ↪ List Bool} {A : Set α} :
    A ∈ coNP enc ↔ A ∈ Cslib.Complexity.coNP enc :=
  mem_NP_iff (enc := enc) (A := Aᶜ)

/-- Polynomial-time many-one reducibility using plain polynomial-time computability. -/
def PolyTimeReducible {α β : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (A : Set α) (B : Set β) : Prop :=
  ∃ f : α → β, ComputableInPolyTime f encA encB ∧ ∀ a, a ∈ A ↔ f a ∈ B

theorem polyTimeReducible_iff {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {A : Set α} {B : Set β} :
    PolyTimeReducible encA encB A B ↔ Cslib.Complexity.PolyTimeReducible encA encB A B := by
  simp only [PolyTimeReducible, Cslib.Complexity.PolyTimeReducible, computableInPolyTime_iff_tidy]

/-- Quantifier-based satisfiability of a CNF formula represented as `List (List (ℕ × Bool))`. -/
def Satisfiable (φ : List (List (ℕ × Bool))) : Prop :=
  ∃ τ : ℕ → Bool, ∀ c ∈ φ, ∃ l ∈ c, τ l.1 = l.2

theorem satisfiable_iff (φ : List (List (ℕ × Bool))) :
    Satisfiable φ ↔ CNF.Satisfiable (V := ℕ) φ := by
  simp only [Satisfiable, CNF.Satisfiable, CNF.eval_eq_true_iff, Clause.eval_eq_true_iff]

theorem sat_eq : {φ : List (List (ℕ × Bool)) | Satisfiable φ} = Cslib.Complexity.SAT := by
  ext φ
  exact satisfiable_iff φ

theorem unsat_eq : {φ : List (List (ℕ × Bool)) | ¬ Satisfiable φ} = Cslib.Complexity.UNSAT := by
  ext φ
  exact not_congr (satisfiable_iff φ)

theorem exactThreeSAT_eq :
    {φ : List (List (ℕ × Bool)) | (∀ c ∈ φ, c.length = 3) ∧ Satisfiable φ} =
      Cslib.Complexity.ExactThreeSAT := by
  ext φ
  exact and_congr_right fun _ => satisfiable_iff φ

/-- Transfer of Cook–Levin: `SAT` is `NP`-complete under plain polynomial-time reductions. -/
theorem sat_npComplete :
    {φ : List (List (ℕ × Bool)) | Satisfiable φ} ∈ NP encCNF ∧
    ∀ (α : Type) (encA : α ↪ List Bool) (A : Set α),
      A ∈ NP encA →
        PolyTimeReducible encA encCNF A {φ : List (List (ℕ × Bool)) | Satisfiable φ} := by
  rw [sat_eq]
  refine ⟨mem_NP_iff.mpr CookLevin.SAT_npComplete.1, fun α encA A hA => ?_⟩
  exact polyTimeReducible_iff.mpr (CookLevin.SAT_npComplete.2 encA A (mem_NP_iff.mp hA))

/-- Transfer of the complement Cook–Levin theorem: `UNSAT` is `coNP`-complete. -/
theorem unsat_coNPComplete :
    {φ : List (List (ℕ × Bool)) | ¬ Satisfiable φ} ∈ coNP encCNF ∧
    ∀ (α : Type) (encA : α ↪ List Bool) (A : Set α),
      A ∈ coNP encA →
        PolyTimeReducible encA encCNF A {φ : List (List (ℕ × Bool)) | ¬ Satisfiable φ} := by
  rw [unsat_eq]
  refine ⟨mem_coNP_iff.mpr CookLevin.UNSAT_coNPComplete.1, fun α encA A hA => ?_⟩
  exact polyTimeReducible_iff.mpr (CookLevin.UNSAT_coNPComplete.2 encA A (mem_coNP_iff.mp hA))

/-- Transfer of Exact-3SAT completeness: `ExactThreeSAT` is `NP`-complete. -/
theorem exactThreeSAT_npComplete :
    {φ : List (List (ℕ × Bool)) | (∀ c ∈ φ, c.length = 3) ∧ Satisfiable φ} ∈ NP encCNF ∧
    ∀ (α : Type) (encA : α ↪ List Bool) (A : Set α),
      A ∈ NP encA →
        PolyTimeReducible encA encCNF A
          {φ : List (List (ℕ × Bool)) | (∀ c ∈ φ, c.length = 3) ∧ Satisfiable φ} := by
  rw [exactThreeSAT_eq]
  refine ⟨mem_NP_iff.mpr ExactThreeSAT_npComplete.1, fun α encA A hA => ?_⟩
  exact polyTimeReducible_iff.mpr (ExactThreeSAT_npComplete.2 encA A (mem_NP_iff.mp hA))

/-! ### Regression tests for `#check_abstract` -/

namespace AuditTests

/- 1. Direct leak in a public definition body. -/
namespace DirectDefLeak
def leakedDef : Set (List (List (ℕ × Bool))) := Cslib.Complexity.SAT
end DirectDefLeak

/--
error: abstract audit:
`ComplexityTests.Abstracts.CookLevinBridge.AuditTests.DirectDefLeak.leakedDef` depends on
implementation declaration `Cslib.Complexity.SAT` from
`Complexity.Computability.Complexity.Problems.SAT`
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.CookLevinBridge.AuditTests.DirectDefLeak

/- 2. Allowlist permits references to an explicitly listed module. -/
#check_abstract ComplexityTests.Abstracts.CookLevinBridge.AuditTests.DirectDefLeak allowing [
  Complexity.Computability.Complexity.Problems.SAT
]

/- 3. Transitive leak through a `private` pattern-matching helper inside the namespace. -/
namespace PrivateMatcherLeak
private def helper : Bool → Set (List (List (ℕ × Bool)))
  | true => Cslib.Complexity.SAT
  | false => ∅
def publicWrapper : Set (List (List (ℕ × Bool))) := helper true
end PrivateMatcherLeak

/--
error: abstract audit:
`ComplexityTests.Abstracts.CookLevinBridge.AuditTests.PrivateMatcherLeak.publicWrapper` depends on
implementation declaration `Cslib.Complexity.SAT` from
`Complexity.Computability.Complexity.Problems.SAT`
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.CookLevinBridge.AuditTests.PrivateMatcherLeak

/- 4. Leak in a `theorem` statement/type (even when the proof is `rfl`). -/
namespace TheoremTypeLeak
theorem leakedStmt : Cslib.Complexity.SAT = Cslib.Complexity.SAT := rfl
end TheoremTypeLeak

/--
error: abstract audit:
`ComplexityTests.Abstracts.CookLevinBridge.AuditTests.TheoremTypeLeak.leakedStmt` depends on
implementation declaration `Cslib.Complexity.SAT` from
`Complexity.Computability.Complexity.Problems.SAT`
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.CookLevinBridge.AuditTests.TheoremTypeLeak

/- 5. Leak to a declaration in the same file outside the audited namespace. -/
def outsideHelper : Nat := 42
namespace OutsideNamespaceLeak
def usesOutside : Nat := outsideHelper
end OutsideNamespaceLeak

/--
error: abstract audit:
`ComplexityTests.Abstracts.CookLevinBridge.AuditTests.OutsideNamespaceLeak.usesOutside` depends on
declaration `ComplexityTests.Abstracts.CookLevinBridge.AuditTests.outsideHelper` outside
`ComplexityTests.Abstracts.CookLevinBridge.AuditTests.OutsideNamespaceLeak`
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.CookLevinBridge.AuditTests.OutsideNamespaceLeak

/- 6. Leak inside the constructor of a `private inductive` referenced only by type. -/
namespace PrivateInductiveCtorLeak
private inductive Hidden where
  | mk (h : Cslib.Complexity.SAT = Cslib.Complexity.SAT)
def usesHiddenType : Prop := Nonempty Hidden
end PrivateInductiveCtorLeak

/--
error: abstract audit:
`ComplexityTests.Abstracts.CookLevinBridge.AuditTests.PrivateInductiveCtorLeak.usesHiddenType`
depends on implementation declaration `Cslib.Complexity.SAT` from
`Complexity.Computability.Complexity.Problems.SAT`
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.CookLevinBridge.AuditTests.PrivateInductiveCtorLeak

/- 7. Rejection of `opaque` / `partial` definitions in an abstract namespace. -/
namespace OpaqueDefLeak
opaque hiddenVal : Nat
end OpaqueDefLeak

/--
error: abstract audit:
`ComplexityTests.Abstracts.CookLevinBridge.AuditTests.OpaqueDefLeak.hiddenVal` is `opaque`,
`partial`, or `unsafe`
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.CookLevinBridge.AuditTests.OpaqueDefLeak

end AuditTests

end ComplexityTests.Abstracts.CookLevinBridge
