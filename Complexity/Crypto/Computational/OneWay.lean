/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.Parameter
public import Complexity.Crypto.Game
public import Complexity.Languages.Probabilistic.BitString
import Complexity.Crypto.Negligible.Basic
import Complexity.Tactic.PPT

/-!
# One-way functions and permutations

A polynomial-time function on binary words is one-way when, given its value on a uniform
`n`-bit input and the unary parameter `n`, every uniform PPT inverter has negligible probability
of finding **any** preimage. Recovering the sampled input is not required, and the inverter's
answer is not restricted to the sampled input's length.

`OneWayPermutation` additionally requires a length-preserving bijection. Its inverse exists as a
mathematical function; no efficiency of that inverse is assumed. Such a permutation preserves
the uniform distribution at every input length. These are definitions, not assertions that
one-way functions or permutations exist.

## Main definitions

* `Cslib.Crypto.inversionGame`: sample a challenge and test the inverter's candidate preimage.
* `Cslib.Crypto.OneWay`, `Cslib.Crypto.OneWayPermutation`: uniform computational assumptions.

## Main results

* `Cslib.Crypto.OneWay.inversion_negligible`: negligible success for each efficient inverter.
* `Cslib.Crypto.OneWayPermutation.uniformList_append_bit`: the ideal one-bit extension is uniform.
* `Cslib.Crypto.not_oneWay_of_inverse`, `not_oneWay_const`: efficient preimages refute one-wayness.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 9.2.

Adapted from `Crypto/Computational/OneWay.lean` on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using finite fair-bit programs, tidy deterministic
certificates and the upstream nonnegative game API.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-- An inverter receives the unary parameter and the image of the sampled input. -/
abbrev Inverter := ℕ → List Bool → ProbComp (List Bool)

/-- The inversion experiment accepts any preimage of its challenge. -/
noncomputable def inversionGame (f : List Bool → List Bool) (adversary : Inverter) (n : ℕ) :
    ProbComp Bool := do
  let input ← BitString.sampleList n
  let candidate ← adversary n (f input)
  return f candidate == f input

/-- Run the complete inversion experiment on its unary parameter. -/
@[program_certificate]
theorem isPPTOn_inversionGame {f : List Bool → List Bool} {adversary : Inverter}
    (hf : ComputableTidilyInPolyTime f encBits encBits) (ha : IsPPT encBits adversary) :
    IsPPTOn encUnary encBool (inversionGame f adversary) := by
  unfold inversionGame
  ppt

/-- The inversion experiment is uniformly PPT, independently of the unused auxiliary input. -/
@[program_certificate]
theorem isPPT_inversionGame {f : List Bool → List Bool} {adversary : Inverter}
    (hf : ComputableTidilyInPolyTime f encBits encBits) (ha : IsPPT encBits adversary) :
    IsPPT encBool (fun n _ => inversionGame f adversary n) := by ppt

/-- One polynomial-time algorithm evaluates the function, and every uniform strict PPT inverter
has negligible success over the uniform input and its own independent random coins. -/
structure OneWay (f : List Bool → List Bool) : Prop where
  /-- A deterministic polynomial-time algorithm evaluates the function. -/
  polyTime : ComputableTidilyInPolyTime f encBits encBits
  /-- Inversion is indistinguishable from certain failure in the common game calculus. -/
  secure : Game.Indistinguishable (fun adversary n => ProbComp.eval (inversionGame f adversary n))
    (fun _ _ => PMF.pure false) (IsPPT encBits)

/-- The shared game definition gives the usual negligible inversion probability. -/
theorem OneWay.inversion_negligible {f : List Bool → List Bool} (h : OneWay f)
    (adversary : Inverter) (hPPT : IsPPT encBits adversary) :
    Negligible (fun n => Game.succProbability (ProbComp.eval (inversionGame f adversary n))) := by
  simpa only [Game.advantage_pure_false] using h.secure adversary hPPT

/-- Establish one-wayness by bounding every efficient inverter's success probability. -/
theorem OneWay.of_inversion_negligible {f : List Bool → List Bool}
    (hf : ComputableTidilyInPolyTime f encBits encBits)
    (h : ∀ adversary : Inverter, IsPPT encBits adversary →
      Negligible (fun n => Game.succProbability (ProbComp.eval (inversionGame f adversary n)))) :
    OneWay f := by
  refine ⟨hf, fun adversary hPPT => ?_⟩
  simpa only [Game.advantage_pure_false] using h adversary hPPT

/-- A length-preserving permutation that is one-way against every uniform PPT inverter. -/
structure OneWayPermutation (f : List Bool → List Bool) : Prop where
  /-- Evaluation is polynomial time, and inversion has negligible success. -/
  oneWay : OneWay f
  /-- The permutation acts separately on words of each length. -/
  length_eq : ∀ word, (f word).length = word.length
  /-- Every word has exactly one preimage; finding it need not be efficient. -/
  bijective : Function.Bijective f

/-- A one-way permutation preserves the uniform distribution at each input length. -/
theorem OneWayPermutation.uniformList_map {f : List Bool → List Bool}
    (hf : OneWayPermutation f) (n : ℕ) :
    (BitString.uniformList n).map f = BitString.uniformList n :=
  BitString.uniformList_map_of_bijective f hf.bijective hf.length_eq n

/-- A permuted uniform seed followed by an independent fair bit is exactly uniform at the
expanded length. Security is needed when replacing the independent bit by a hard-core predicate. -/
theorem OneWayPermutation.uniformList_append_bit {f : List Bool → List Bool}
    (hf : OneWayPermutation f) (n : ℕ) :
    (BitString.uniformList n).bind (fun word =>
      (PMF.uniformOfFintype Bool).map (fun bit => f word ++ [bit])) =
        BitString.uniformList (n + 1) := by
  change (BitString.uniformList n).bind
    ((fun word => (PMF.uniformOfFintype Bool).map (fun bit => word ++ [bit])) ∘ f) = _
  rw [← PMF.bind_map, hf.uniformList_map]
  exact (BitString.uniformList_snoc n).symm

/-- For an injective function, accepting any preimage is equivalent to recovering the sampled
input. The general inversion experiment does not make this assumption. -/
theorem inversionGame_eq_of_injective (f : List Bool → List Bool) (hf : Function.Injective f)
    (adversary : Inverter) (n : ℕ) :
    inversionGame f adversary n = (do
      let input ← BitString.sampleList n
      let candidate ← adversary n (f input)
      return candidate == input) := by
  have heq (candidate input : List Bool) : (f candidate == f input) = (candidate == input) := by
    simp only [beq_eq_decide, hf.eq_iff]
  simp only [inversionGame, heq]

/-- An inverter that always returns a preimage makes the experiment always succeed. -/
theorem eval_inversionGame_of_rightInverse (f inverse : List Bool → List Bool)
    (h : ∀ x, f (inverse (f x)) = f x) (n : ℕ) :
    ProbComp.eval (inversionGame f (fun _ y => pure (inverse y)) n) = PMF.pure true := by
  simp [inversionGame, h, PMF.map, Function.comp_def]

/-- Efficiently finding any preimage contradicts one-wayness. -/
theorem not_oneWay_of_inverse (f inverse : List Bool → List Bool)
    (hPPT : IsPPT encBits (fun _ y => pure (inverse y)))
    (hinv : ∀ x, f (inverse (f x)) = f x) : ¬ OneWay f := by
  intro h
  have hnegl := h.inversion_negligible _ hPPT
  apply not_negligible_const (c := 1) one_ne_zero
  simpa only [Game.succProbability, eval_inversionGame_of_rightInverse f inverse hinv,
    PMF.pure_apply_self, ENNReal.toNNReal_one] using hnegl

/-- Constant functions are not one-way: the empty word is always a preimage. -/
theorem not_oneWay_const (word : List Bool) : ¬ OneWay (fun _ => word) :=
  not_oneWay_of_inverse _ (fun _ => [])
    (ComputableTidilyInPolyTime.const []).isPPT (fun _ => rfl)

end Cslib.Crypto
