/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Operators
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The class parity-P

`⊕P` is the parity operator applied to `P` (`Cslib.Complexity.ParityP`)
[Papadimitriou and Zachos][PapadimitriouZachos1983], [Arora and Barak, Section 17.4][AroraBarak09]:
`L ∈ ⊕P` when, for a polynomial `p` and a function `V : α × List Bool → Bool` computable in
polynomial time on inputs `encPair enc encBits (a, w) = frame (enc a) ++ w`, `a ∈ L` exactly when
an odd number of the strings `w` of length `p (enc a).length` have `V (a, w) = true`
(`Cslib.Complexity.mem_ParityP`). Equivalently, `L` consists of the instances where some function
in `#P` is odd (`Cslib.Complexity.mem_ParityP_iff_exists_SharpP`).

`⊕P` is closed under complement (`Cslib.Complexity.compl_mem_ParityP`): the verifier
`Cslib.Complexity.succVerifier V` accepts the string of `false`s and the strings `true :: w` with
`V (a, w) = true`, so it accepts exactly one string more than `V`, one bit longer
(`Cslib.Complexity.acceptCount_succVerifier`). Splitting strings into a prefix and the rest
(`Cslib.Complexity.acceptCount_add`) is the other counting step used for parity classes.

## Main definitions

* `Cslib.Complexity.ParityP`: the class `⊕P`.
* `Cslib.Complexity.succTest`, `Cslib.Complexity.succVerifier`: a word test and a verifier
  accepting one more string.

## Main results

* `Cslib.Complexity.acceptCount_add`: counting strings by their prefixes.
* `Cslib.Complexity.acceptCount_succVerifier`, `Cslib.Complexity.acceptCount_succTest`: one more
  accepted string.
* `Cslib.Complexity.mem_ParityP`, `Cslib.Complexity.mem_ParityP_iff_exists_SharpP`: `⊕P` through
  verifiers and through `#P`.
* `Cslib.Complexity.P_subset_ParityP`, `Cslib.Complexity.compl_mem_ParityP`.

## References

* [C. H. Papadimitriou, S. Zachos, *Two remarks on the power of counting*][PapadimitriouZachos1983]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type}

/-! ### Counting accepted strings -/

section Counting

variable {V : α × List Bool → Bool} {a : α}

/-- **Counting strings by their prefixes**: the strings of length `m + n` accepted by `V` are the
strings `u ++ w`, with `u` of length `m` and `w` of length `n` accepted with the prefix `u`. -/
theorem acceptCount_add (V : α × List Bool → Bool) (a : α) (m n : ℕ) :
    acceptCount V a (m + n) =
      ∑ u : Fin m → Bool, acceptCount (fun x => V (x.1, List.ofFn u ++ x.2)) a n := by
  classical
  rw [acceptCount, ← Finset.card_map (Fin.appendEquiv m n).symm.toEmbedding]
  have hmap : (Finset.univ.filter fun v : Fin (m + n) → Bool => V (a, List.ofFn v) = true).map
      (Fin.appendEquiv m n).symm.toEmbedding =
      Finset.univ.filter fun x : (Fin m → Bool) × (Fin n → Bool) =>
        V (a, List.ofFn x.1 ++ List.ofFn x.2) = true := by
    ext x
    simp only [Finset.mem_map_equiv, Equiv.symm_symm, Finset.mem_filter, Finset.mem_univ,
      true_and]
    change V (a, List.ofFn (Fin.append x.1 x.2)) = true ↔ _
    rw [List.ofFn_fin_append]
  rw [hmap, Finset.card_filter, Fintype.sum_prod_type]
  simp only [acceptCount, Finset.card_filter]

/-- The word test accepting one word more than `g`, one bit longer: the word of `false`s, and
`true :: w` for every word `w` accepted by `g`. -/
def succTest (g : List Bool → Bool) (w : List Bool) : Bool :=
  !(w.any fun b => b) || (w.headD false && g w.tail)

/-- The verifier accepting one string more than `V`, one bit longer: the string of `false`s, and
`true :: w` for every `w` with `V (a, w) = true`. -/
def succVerifier (V : α × List Bool → Bool) (x : α × List Bool) : Bool :=
  succTest (fun w => V (x.1, w)) x.2

/-- Only the string of `false`s has all bits `false`. -/
theorem card_filter_not_any (n : ℕ) :
    (Finset.univ.filter fun w : Fin n → Bool =>
      (!(List.ofFn w).any fun b => b) = true).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨fun _ => false, Finset.ext fun w => ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_eq_eq_not, Bool.not_true,
    List.any_eq_false, List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff,
    Finset.mem_singleton, Bool.not_eq_true]
  exact ⟨fun h => funext h, fun h i => by rw [h]⟩

/-- **One more accepted string**: `succVerifier V` accepts exactly one string of length `n + 1`
more than `V` accepts strings of length `n`. -/
theorem acceptCount_succVerifier (V : α × List Bool → Bool) (a : α) (n : ℕ) :
    acceptCount (succVerifier V) a (n + 1) = acceptCount V a n + 1 := by
  rw [Nat.add_comm n 1, acceptCount_add, ← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp,
    Fintype.sum_bool]
  have h₁ : acceptCount (fun x => succVerifier V
      (x.1, List.ofFn ((Equiv.funUnique (Fin 1) Bool).symm false) ++ x.2)) a n = 1 := by
    simpa [acceptCount, succVerifier, succTest] using card_filter_not_any n
  have h₂ : acceptCount (fun x => succVerifier V
      (x.1, List.ofFn ((Equiv.funUnique (Fin 1) Bool).symm true) ++ x.2)) a n =
      acceptCount V a n := by
    simp [acceptCount, succVerifier, succTest]
  rw [h₁, h₂]

/-- **One more accepted word**: `succTest g` accepts exactly one word of length `n + 1` more than
`g` accepts words of length `n`. -/
theorem acceptCount_succTest (g : List Bool → Bool) (a : α) (n : ℕ) :
    acceptCount (fun x => succTest g x.2) a (n + 1) = acceptCount (fun x => g x.2) a n + 1 :=
  acceptCount_succVerifier (fun y => g y.2) a n

/-- The parity of one more accepted string is the opposite parity. -/
theorem odd_acceptCount_succVerifier_iff (V : α × List Bool → Bool) (a : α) (n : ℕ) :
    Odd (acceptCount (succVerifier V) a (n + 1)) ↔ ¬Odd (acceptCount V a n) := by
  rw [acceptCount_succVerifier, Nat.odd_add_one]

/-- Verifiers that agree on an instance accept the same strings with it. -/
theorem acceptCount_congr {W : α × List Bool → Bool} (h : ∀ w, V (a, w) = W (a, w)) (n : ℕ) :
    acceptCount V a n = acceptCount W a n := by
  simp only [acceptCount, h]

end Counting

/-- `succTest` is polynomial-time, with a test that may use the input. -/
@[fun_prop]
theorem computableTidilyInPolyTime_succTest {γ : Type} {input : γ ↪ List Bool}
    {g : γ → List Bool → Bool} {w : γ → List Bool}
    (hg : ComputableTidilyInPolyTime (fun p : γ × List Bool => g p.1 p.2) (encPair input encBits)
      encBool)
    (hw : ComputableTidilyInPolyTime w input encBits) :
    ComputableTidilyInPolyTime (fun x => succTest (g x) (w x)) input encBool := by
  unfold succTest
  fun_prop

/-- `succVerifier V` is polynomial-time when `V` is. -/
@[fun_prop]
theorem computableTidilyInPolyTime_succVerifier {enc : α ↪ List Bool}
    {V : α × List Bool → Bool} (hV : ComputableTidilyInPolyTime V (encPair enc encBits) encBool) :
    ComputableTidilyInPolyTime (succVerifier V) (encPair enc encBits) encBool := by
  unfold succVerifier
  fun_prop

/-! ### The class -/

/-- **The class `⊕P`**: the parity operator applied to `P`. A problem `L` is in `⊕P` when, for a
polynomial `p` and a polynomial-time `V`, `a ∈ L` exactly when an odd number of the strings `w` of
length `p (enc a).length` have `V (a, w) = true` (`mem_ParityP`). -/
def ParityP (enc : α ↪ List Bool) : Set (Set α) := ParityOp enc (P (encPair enc encBits))

variable {enc : α ↪ List Bool} {L : Set α}

/-- **`⊕P` through verifiers.** -/
theorem mem_ParityP : L ∈ ParityP enc ↔ ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableTidilyInPolyTime V (encPair enc encBits) encBool ∧
      ∀ a, a ∈ L ↔ Odd (acceptCount V a (p.eval (enc a).length)) := by
  classical
  constructor
  · rintro ⟨p, L', ⟨f, hf, hL'⟩, h⟩
    refine ⟨p, f, hf, fun a => (h a).trans ?_⟩
    rw [acceptCount_congr (W := f) fun w => by simp [hL' (a, w)]]
  · rintro ⟨p, V, hV, h⟩
    refine ⟨p, {x | V x = true}, ⟨V, hV, fun _ => Iff.rfl⟩, fun a => (h a).trans ?_⟩
    exact Iff.of_eq (congrArg Odd (acceptCount_congr (W := V) (fun w => by simp) _).symm)

/-- **`⊕P` through `#P`**: a problem is in `⊕P` exactly when it is the set of instances where some
function in `#P` is odd. -/
theorem mem_ParityP_iff_exists_SharpP :
    L ∈ ParityP enc ↔ ∃ f ∈ SharpP enc, ∀ a, a ∈ L ↔ Odd (f a) := by
  rw [mem_ParityP]
  constructor
  · rintro ⟨p, V, hV, h⟩
    exact ⟨_, ⟨p, V, hV, fun _ => rfl⟩, h⟩
  · rintro ⟨f, ⟨p, V, hV, hf⟩, h⟩
    exact ⟨p, V, hV, fun a => by rw [h a, hf a]⟩

/-- **`⊕P` is closed under complement**: `succVerifier` accepts one more string. -/
theorem compl_mem_ParityP (hL : L ∈ ParityP enc) : Lᶜ ∈ ParityP enc := by
  obtain ⟨p, V, hV, h⟩ := mem_ParityP.1 hL
  refine mem_ParityP.2 ⟨p + 1, succVerifier V, by fun_prop, fun a => ?_⟩
  rw [Set.mem_compl_iff, h a, Polynomial.eval_add, Polynomial.eval_one,
    odd_acceptCount_succVerifier_iff]

/-- **`P ⊆ ⊕P`**: a decider accepts the empty string or nothing. -/
theorem P_subset_ParityP : P enc ⊆ ParityP enc := by
  rintro L ⟨f, hf, h⟩
  refine mem_ParityP.2 ⟨0, fun x => f x.1, hf.comp (.fst enc encBits), fun a => ?_⟩
  rw [h a, Polynomial.eval_zero]
  cases hfa : f a <;> simp [acceptCount, hfa]

end Cslib.Complexity
