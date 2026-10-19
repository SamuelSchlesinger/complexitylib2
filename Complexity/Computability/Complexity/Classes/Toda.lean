/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Oracle
public import Complexity.Computability.Complexity.Classes.Toda.Hierarchy
import Complexity.Computability.Complexity.Classes.Oracle.Closure
import Complexity.Computability.Complexity.Classes.Toda.Counting
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Toda's theorem

Toda's theorem [Toda][Toda1991], [Arora and Barak, Theorem 17.14][AroraBarak09]: the polynomial
hierarchy lies in `BP·⊕P` (`Cslib.Complexity.PH_subset_BPOp_ParityP`), which lies in polynomial
time with an oracle for a function in `#P`
(`Cslib.Complexity.BPOp_ParityP_subset_PWithSharpPOracle`), so `PH ⊆ P^#P`
(`Cslib.Complexity.PH_subset_PWithSharpPOracle`).

## Polynomial time with a `#P` oracle

The oracle classes of `Cslib.Complexity.PWithOracle` query languages. A function `f : α → ℕ` is
queried through its *bit graph* (`Cslib.Complexity.bitGraph`): the words
`encPair enc encNat (a, i)` such that bit `i` of `f a` is `1`. `P^#P` relative to the encoding
`enc` (`Cslib.Complexity.PWithSharpPOracle`) consists of the problems in polynomial time relative
to the bit graph of some function in `#P` with respect to `enc`. For the identity encoding
`encBits` of words this is the usual class `P^#P`, polynomial time with oracle access to the bits
of a counting function on words; for another encoding, the counting function takes instances of
the same type, and the oracle answers no on words that encode no pair of an instance and an
index.

## The second inclusion with one query

For a problem in `BP·⊕P`, decided with bounded error by the parity of the number `f r` of
witnesses of a verifier on random strings `r` of length `R`,
`Complexity.Computability.Complexity.Classes.Toda.Counting` gives a function in `#P` whose bit
`R + 1` says whether more than half of the random strings have `f r` odd
(`Cslib.Complexity.exists_SharpP_testBit_of_mem_BPOp_ParityP`). So one query to the bit graph
decides the problem: Toda's theorem holds with a single query, `PH ⊆ P^#P[1]`.

## Main definitions

* `Cslib.Complexity.bitGraph`: the bits of a function, as an oracle language.
* `Cslib.Complexity.PWithSharpPOracle`: polynomial time with a `#P` oracle.

## Main results

* `Cslib.Complexity.exists_SharpP_testBit_of_mem_BPOp_ParityP`: a problem in `BP·⊕P` is decided
  by a bit at a polynomial position of a function in `#P`.
* `Cslib.Complexity.BPOp_ParityP_subset_PWithSharpPOracle`: **`BP·⊕P ⊆ P^#P`**.
* `Cslib.Complexity.PH_subset_PWithSharpPOracle`: **Toda's theorem, `PH ⊆ P^#P`**.

## References

* [S. Toda, *PP is as hard as the polynomial-time hierarchy*][Toda1991]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-! ### Polynomial time with a `#P` oracle -/

/-- The bit graph of `f : α → ℕ`: the words `encPair enc encNat (a, i)` such that bit `i` of
`f a` is `1`. -/
def bitGraph (enc : α ↪ List Bool) (f : α → ℕ) : Set (List Bool) :=
  encPair enc encNat '' {x | (f x.1).testBit x.2}

theorem encPair_mem_bitGraph {f : α → ℕ} {a : α} {i : ℕ} :
    encPair enc encNat (a, i) ∈ bitGraph enc f ↔ (f a).testBit i :=
  (encPair enc encNat).injective.mem_set_image

/-- **`P^#P`**: the problems decidable in polynomial time relative to the bit graph of a function
in `#P`, with respect to the encoding `enc` of instances. -/
def PWithSharpPOracle (enc : α ↪ List Bool) : Set (Set α) :=
  {L | ∃ f ∈ SharpP enc, L ∈ PWithOracle (bitGraph enc f) enc}

theorem mem_PWithSharpPOracle {L : Set α} :
    L ∈ PWithSharpPOracle enc ↔ ∃ f ∈ SharpP enc, L ∈ PWithOracle (bitGraph enc f) enc :=
  Iff.rfl

/-- **One bit of a `#P` value is in `P^#P`**: a problem decided by the bit at a polynomial position
of a function in `#P` is in `P^#P`, with one query. -/
theorem mem_PWithSharpPOracle_of_testBit {L : Set α} {f : α → ℕ} (hf : f ∈ SharpP enc)
    {p : Polynomial ℕ} (h : ∀ a, a ∈ L ↔ (f a).testBit (p.eval (enc a).length)) :
    L ∈ PWithSharpPOracle enc := by
  classical
  refine ⟨f, hf, ?_⟩
  have hq : ComputableTidilyInPolyTime (fun a => encPair enc encNat (a, p.eval (enc a).length))
      enc encBits :=
    ComputableTidilyInPolyTime.encoded (f := fun a => (a, p.eval (enc a).length))
      (ComputableTidilyInPolyTime.id'.prod
        (ComputableTidilyInPolyTime.unary_to_binary.comp (f := fun n : ℕ => n)
          (g := fun a => p.eval (enc a).length) (by fun_prop)))
  refine ⟨fun a => decide (encPair enc encNat (a, p.eval (enc a).length) ∈ bitGraph enc f),
    (computableInPolyTimeWithOracle_mem _).preprocess hq, fun a => ?_⟩
  rw [h a, decide_eq_true_iff, encPair_mem_bitGraph]

/-! ### `BP·⊕P ⊆ P^#P` -/

open Toda Classical in
/-- **A problem in `BP·⊕P` is one bit of a `#P` value**: for a problem decided with bounded error,
using random strings of length `R = p (enc a).length`, by the parity of a verifier's number of
witnesses, some function in `#P` has bit `R + 1` set exactly at the members of the problem. -/
theorem exists_SharpP_testBit_of_mem_BPOp_ParityP {L : Set α}
    (hL : L ∈ BPOp enc (ParityP (encPair enc encBits))) :
    ∃ f ∈ SharpP enc, ∃ p : Polynomial ℕ, ∀ a, a ∈ L ↔ (f a).testBit (p.eval (enc a).length) := by
  obtain ⟨ρ, L', hL'P, hdec⟩ := hL
  obtain ⟨ζ, V, hV, hL'⟩ := mem_ParityP.1 hL'P
  -- the witnesses of a pair of an instance and a random string have length `Zp`
  set Zp : Polynomial ℕ := ζ.comp (2 * Polynomial.X + 1 + ρ) with hZp
  set pF : Polynomial ℕ := (ρ + 1) + ((ρ + 1) + (ρ + (ρ + 1) * Zp)) + 1 + 1 with hpF
  refine ⟨fun a => acceptCount (fun x => sharpTest (fun r z => V ((x.1, r), z))
      (ρ.eval (enc x.1).length) (Zp.eval (enc x.1).length) x.2) a (pF.eval (enc a).length),
    ⟨pF, _, by fun_prop, fun _ => rfl⟩, ρ + 1, fun a => ?_⟩
  have hpFn : pF.eval (enc a).length = (ρ.eval (enc a).length + 1) +
      ((ρ.eval (enc a).length + 1) + (ρ.eval (enc a).length +
        (ρ.eval (enc a).length + 1) * Zp.eval (enc a).length)) + 1 + 1 := by
    simp only [hpF, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one]
  have hZlen (r : List Bool) (hr : r.length = ρ.eval (enc a).length) :
      ζ.eval (encPair enc encBits (a, r)).length = Zp.eval (enc a).length := by
    rw [length_encPair, hZp, Polynomial.eval_comp]
    simp [hr]
  obtain ⟨hyes, hno⟩ := hdec a
  simp only [decide_eq_true_eq, decide_eq_false_iff_not, hL',
    hZlen _ List.length_ofFn] at hyes hno
  simp only
  rw [acceptCount_congr (W := fun x => sharpTest (fun r z => V ((a, r), z)) (ρ.eval (enc a).length)
    (Zp.eval (enc a).length) x.2) (fun w => rfl), hpFn, Polynomial.eval_add, Polynomial.eval_one]
  generalize ρ.eval (enc a).length = R at hyes hno ⊢
  generalize Zp.eval (enc a).length = Z at hyes hno ⊢
  unfold acceptCount
  rw [testBit_card_filter_sharpTest, decide_eq_true_iff]
  -- bounded error decides the majority
  have hsplit := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin R → Bool)))
    (fun r => Odd (acceptCount V (a, List.ofFn r) Z))
  simp only [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hsplit
  have hpos : 1 ≤ 2 ^ R := Nat.one_le_two_pow
  change a ∈ L ↔ 2 ^ R < 2 * (univ.filter fun r : Fin R → Bool =>
    Odd (acceptCount V (a, List.ofFn r) Z)).card
  constructor
  · intro ha
    have := hyes ha
    omega
  · intro hlt
    by_contra ha
    have := hno ha
    omega

/-- **`BP·⊕P ⊆ P^#P`**, with one query: a problem decided with bounded error by a problem in `⊕P`
about pairs of an instance and a random string is decided in polynomial time by one query to the
bit graph of a function in `#P`. -/
theorem BPOp_ParityP_subset_PWithSharpPOracle :
    BPOp enc (ParityP (encPair enc encBits)) ⊆ PWithSharpPOracle enc := fun _ hL =>
  let ⟨_, hf, _, h⟩ := exists_SharpP_testBit_of_mem_BPOp_ParityP hL
  mem_PWithSharpPOracle_of_testBit hf h

/-- **Toda's theorem: `PH ⊆ P^#P`.** Every problem in the polynomial hierarchy is decidable in
polynomial time with one query to the bit graph of a function in `#P`. -/
theorem PH_subset_PWithSharpPOracle : PH enc ⊆ PWithSharpPOracle enc :=
  PH_subset_BPOp_ParityP.trans BPOp_ParityP_subset_PWithSharpPOracle

end Cslib.Complexity
