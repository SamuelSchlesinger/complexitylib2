/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.ModP
public import Complexity.Computability.Complexity.Classes.US
public import Complexity.Computability.Complexity.Problems.SharpSAT
public import Complexity.Computability.Complexity.Problems.USAT
public import Complexity.Computability.Complexity.Reduction
import Complexity.Computability.Complexity.Classes.SharpP.PolyTime
import Complexity.Computability.Complexity.CookLevin.Counting
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Complete problems for the counting classes

Since the Cook–Levin reduction is parsimonious (`CookLevin.SharpSAT_sharpPHard`), each counting
class defined by a condition on a function in `#P` has a complete problem defined by the same
condition on the number of satisfying assignments of a formula (`SharpSAT`), under
polynomial-time many-one reductions [Valiant][Valiant1979]. The classes are the verifier-based
ones of this library, following [Fortnow, Section 4][Fortnow1997].

* `ParitySAT`, an odd number of satisfying assignments, is `⊕P`-complete
  [Papadimitriou and Zachos][PapadimitriouZachos1983];
* `USAT`, exactly one satisfying assignment (`mem_USAT_iff`), is `US`-complete
  [Blass and Gurevich][BlassGurevich1982];
* `ModSAT k`, a number of satisfying assignments not divisible by `k`, is `ModP k`-complete, and
  its complement is `coModP k`-complete, for every modulus `k`;
* `SharpSATAtLeast`, the pairs `(φ, m)` of a formula and a number in binary such that `φ` has at
  least `m` satisfying assignments, is `PP`-complete; it is a threshold variant of the majority
  problem MAJSAT [Gill][Gill1977], [Papadimitriou, Chapter 11][Papadimitriou94];
* `SharpSATExact`, the pairs `(φ, m)` such that `φ` has exactly `m` satisfying assignments, is
  `C=P`-complete, and its complement is `coC=P`-complete.

The first four follow one pattern (`polyTimeComplete_sharpSAT`): a problem in the class is
`{a | Q (f a)}` for some `f ∈ #P`, and the parsimonious reduction `r` for `f` reduces it to
`{φ | Q (SharpSAT φ)}`. For `PP`, the characterization of `PP` through `#P`
(`mem_PP_iff_exists_SharpP`) gives `a ∈ A ↔ 2 ^ q(n) < 2 f(a)`; the reduction maps `a` to the
formula for `2 f` with the threshold `2 ^ q(n) + 1`. For `C=P`, a problem in the class is
`{a | f₁ a = f₂ a}` for `f₁, f₂ ∈ #P`, with `f₂ ≤ 2 ^ p(n)` and `2 ^ p(n) - f₂ ∈ #P`
(`SharpP.exists_two_pow_sub_mem`); the reduction maps `a` to the formula for `f₁ + (2 ^ p(n) - f₂)`
with the count `2 ^ p(n)`. In both cases the number `m` is computed in polynomial time in binary.

## Main definitions

* `Cslib.Complexity.ParitySAT`, `Cslib.Complexity.ModSAT`, `Cslib.Complexity.SharpSATAtLeast`,
  `Cslib.Complexity.SharpSATExact`.

## Main results

* `Cslib.Complexity.ParitySAT_parityPComplete`: `⊕SAT` is `⊕P`-complete.
* `Cslib.Complexity.USAT_usComplete`: `USAT` is `US`-complete.
* `Cslib.Complexity.ModSAT_modPComplete`, `Cslib.Complexity.compl_ModSAT_coModPComplete`.
* `Cslib.Complexity.SharpSATAtLeast_ppComplete`: counting threshold is `PP`-complete.
* `Cslib.Complexity.SharpSATExact_ceqPComplete`,
  `Cslib.Complexity.compl_SharpSATExact_coCeqPComplete`.

## References

* [L. Valiant, *The complexity of computing the permanent*][Valiant1979]
* [C. H. Papadimitriou, S. Zachos, *Two remarks on the power of counting*][PapadimitriouZachos1983]
* [A. Blass, Y. Gurevich, *On the unique satisfiability problem*][BlassGurevich1982]
* [J. Gill, *Computational complexity of probabilistic Turing machines*][Gill1977]
* [L. Fortnow, *Counting Complexity*][Fortnow1997]
* [C. H. Papadimitriou, *Computational Complexity*][Papadimitriou94]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-! ### The problems -/

/-- **⊕SAT**: the formulas with an odd number of satisfying assignments. -/
def ParitySAT : Set (CNF ℕ) := {φ | Odd (SharpSAT φ)}

/-- **Mod_k SAT**: the formulas whose number of satisfying assignments is not divisible by `k`. -/
def ModSAT (k : ℕ) : Set (CNF ℕ) := {φ | SharpSAT φ % k ≠ 0}

/-- The pairs `(φ, m)` such that `φ` has at least `m` satisfying assignments. Instances are
encoded with `m` in binary (`encPair encCNF encNat`). -/
def SharpSATAtLeast : Set (CNF ℕ × ℕ) := {x | x.2 ≤ SharpSAT x.1}

/-- The pairs `(φ, m)` such that `φ` has exactly `m` satisfying assignments. Instances are
encoded with `m` in binary (`encPair encCNF encNat`). -/
def SharpSATExact : Set (CNF ℕ × ℕ) := {x | SharpSAT x.1 = x.2}

/-- A formula is uniquely satisfiable exactly when it has one satisfying assignment. -/
theorem mem_USAT_iff {φ : CNF ℕ} : φ ∈ USAT ↔ SharpSAT φ = 1 :=
  CNF.modelCount_eq_one_iff.symm

/-! ### Completeness through the parsimonious reduction -/

/-- **Complete problems from conditions on counts.** If the problems of a class `C` are, for
every encoding, the sets `{a | Q (f a)}` for functions `f` in `#P`, then
`{φ | Q (SharpSAT φ)}` is `C`-complete. -/
theorem polyTimeComplete_sharpSAT {C : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)}
    (Q : ℕ → Prop) (hC : ∀ {α : Type} (enc : α ↪ List Bool) (A : Set α),
      A ∈ C enc ↔ ∃ f ∈ SharpP enc, ∀ a, a ∈ A ↔ Q (f a)) :
    PolyTimeComplete C encCNF {φ | Q (SharpSAT φ)} := by
  refine ⟨(hC encCNF _).2 ⟨SharpSAT, SharpSAT.mem_SharpP, fun _ => Iff.rfl⟩,
    fun enc A hA => ?_⟩
  obtain ⟨f, hf, hA⟩ := (hC enc A).1 hA
  obtain ⟨r, hr, hfr⟩ := CookLevin.SharpSAT_sharpPHard enc f hf
  exact ⟨r, hr, fun a => (hA a).trans (by rw [hfr a]; rfl)⟩

/-- **`⊕SAT` is `⊕P`-complete.** -/
theorem ParitySAT_parityPComplete : PolyTimeComplete ParityP encCNF ParitySAT :=
  polyTimeComplete_sharpSAT Odd fun _ _ => mem_ParityP_iff_exists_SharpP

/-- **`USAT` is `US`-complete**: unique satisfiability is complete for the class of problems
defined by a function in `#P` equal to one. -/
theorem USAT_usComplete : PolyTimeComplete US encCNF USAT := by
  have h := polyTimeComplete_sharpSAT (C := US) (· = 1) fun _ _ => Iff.rfl
  rwa [show {φ | SharpSAT φ = 1} = USAT from Set.ext fun _ => mem_USAT_iff.symm] at h

/-- **`Mod_k SAT` is `ModP k`-complete**, for every modulus `k`. -/
theorem ModSAT_modPComplete (k : ℕ) : PolyTimeComplete (ModP k) encCNF (ModSAT k) :=
  polyTimeComplete_sharpSAT (· % k ≠ 0) fun _ _ => Iff.rfl

/-- **The complement of `Mod_k SAT` is `coModP k`-complete**, for every modulus `k`. -/
theorem compl_ModSAT_coModPComplete (k : ℕ) : PolyTimeComplete (coModP k) encCNF (ModSAT k)ᶜ :=
  (ModSAT_modPComplete k).compl fun _ _ => Iff.rfl

/-! ### Thresholds and exact counts -/

/-- The polynomial-time threshold `2 ^ q(n) + j`, in binary, for instances of encoded length
`n`. -/
private theorem computableTidilyInPolyTime_two_pow_add {α : Type} (enc : α ↪ List Bool)
    (q : Polynomial ℕ) (j : ℕ) :
    ComputableTidilyInPolyTime (fun a => 2 ^ q.eval (enc a).length + j) enc encNat :=
  ComputableTidilyInPolyTime.binary_add' (ComputableTidilyInPolyTime.binary_two_pow.comp
    ((ComputableTidilyInPolyTime.unary_eval q).comp
      (ComputableTidilyInPolyTime.encoding_length enc))) (.const j)

/-- The number given with a formula, as a function in `#P`. -/
private theorem snd_mem_SharpP : (Prod.snd : CNF ℕ × ℕ → ℕ) ∈ SharpP (encPair encCNF encNat) :=
  SharpP.of_polyTime (.snd encCNF encNat)

/-- The number of satisfying assignments of the formula of a pair, as a function in `#P`. -/
private theorem sharpSAT_fst_mem_SharpP :
    (fun x : CNF ℕ × ℕ => SharpSAT x.1) ∈ SharpP (encPair encCNF encNat) :=
  SharpP.comp_mem SharpSAT.mem_SharpP (.fst encCNF encNat)

/-- **Counting threshold is `PP`-complete**: whether a formula has at least `m` satisfying
assignments, for `m` given in binary. -/
theorem SharpSATAtLeast_ppComplete :
    PolyTimeComplete PP (encPair encCNF encNat) SharpSATAtLeast := by
  refine ⟨mem_PP_iff_exists_GapP.2 ⟨_, GapP.natCast_sub_natCast_mem
    (SharpP.add_one_mem sharpSAT_fst_mem_SharpP) snd_mem_SharpP, fun x => ?_⟩,
    fun enc A hA => ?_⟩
  · simp only [SharpSATAtLeast, Set.mem_ofPred_eq, Pi.add_apply, Pi.one_apply]
    omega
  · obtain ⟨f, hf, q, hA⟩ := mem_PP_iff_exists_SharpP.1 hA
    obtain ⟨r, hr, hfr⟩ := CookLevin.SharpSAT_sharpPHard enc _ (SharpP.add_mem hf hf)
    refine ⟨fun a => (r a, 2 ^ q.eval (enc a).length + 1),
      hr.prod (computableTidilyInPolyTime_two_pow_add enc q 1), fun a => ?_⟩
    have := hfr a
    simp only [Pi.add_apply] at this
    simp only [SharpSATAtLeast, Set.mem_ofPred_eq, hA a, ← this]
    omega

/-- **Exact counting is `C=P`-complete**: whether a formula has exactly `m` satisfying
assignments, for `m` given in binary. -/
theorem SharpSATExact_ceqPComplete :
    PolyTimeComplete CeqP (encPair encCNF encNat) SharpSATExact := by
  refine ⟨mem_CeqP_iff_exists_SharpP.2 ⟨_, sharpSAT_fst_mem_SharpP, _, snd_mem_SharpP,
    fun _ => Iff.rfl⟩, fun enc A hA => ?_⟩
  obtain ⟨f₁, hf₁, f₂, hf₂, hA⟩ := mem_CeqP_iff_exists_SharpP.1 hA
  obtain ⟨p, hle, hsub⟩ := SharpP.exists_two_pow_sub_mem hf₂
  obtain ⟨r, hr, hfr⟩ := CookLevin.SharpSAT_sharpPHard enc _ (SharpP.add_mem hf₁ hsub)
  refine ⟨fun a => (r a, 2 ^ p.eval (enc a).length),
    by simpa using hr.prod (computableTidilyInPolyTime_two_pow_add enc p 0), fun a => ?_⟩
  have h₁ := hfr a
  have h₂ := hle a
  simp only [Pi.add_apply] at h₁
  simp only [SharpSATExact, Set.mem_ofPred_eq, hA a, ← h₁]
  omega

/-- **The complement of exact counting is `coC=P`-complete.** -/
theorem compl_SharpSATExact_coCeqPComplete :
    PolyTimeComplete coCeqP (encPair encCNF encNat) SharpSATExactᶜ :=
  SharpSATExact_ceqPComplete.compl fun _ _ => Iff.rfl

end Cslib.Complexity
