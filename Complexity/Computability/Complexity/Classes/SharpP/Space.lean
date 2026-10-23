/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.SharpP
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure
import Mathlib.Data.Nat.Size

/-!
# Exact counting in polynomial space

Enumerate certificates with a fixed-width binary counter and keep the number accepted in a
binary accumulator. The exponentially many iterations reuse their workspace: a certificate of
length `m` needs `m` cells and its acceptance count has at most `m + 1` bits. This is the usual
polynomial-space simulation of counting [AroraBarak09]. The implementation generalizes the
coin enumerator in `Cslib.Complexity.Interaction` to arbitrary polynomial-time verifiers.

## Main results

* `Cslib.Complexity.computableTidilyInPolySpace_acceptCount`: count accepted certificates of a
  polynomial-time unary length, with binary output.
* `Cslib.Complexity.SharpP.computableTidilyInPolySpace`: every #P function is computable within
  polynomial space, with binary output.
* `Cslib.Complexity.GapP.computableTidilyInPolySpace`: evaluate integer gaps in binary.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM
open Cslib.BitString (increment lsbValue)

variable {α : Type} {enc : α ↪ List Bool}

private def countStep (V : α × List Bool → Bool) (s : α × List Bool × ℕ) :
    α × List Bool × ℕ :=
  (s.1, increment s.2.1, s.2.2 + if V (s.1, s.2.1) then 1 else 0)

private theorem iterate_countStep (V : α × List Bool → Bool) (a : α) (m j : ℕ) :
    (countStep V)^[j] (a, List.replicate m false, 0) =
      (a, increment^[j] (List.replicate m false),
        ((Finset.range j).filter fun i => V (a, increment^[i] (List.replicate m false))).card) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [countStep, Function.iterate_succ_apply', Prod.mk.injEq, true_and]
    rw [Finset.range_add_one, Finset.filter_insert]
    split_ifs with hacc
    · rw [Finset.card_insert_of_notMem (by simp)]
    · rfl

private theorem countStep_eq_acceptCount (V : α × List Bool → Bool) (a : α) (t : ℕ) :
    ((countStep V)^[2 ^ t] (a, List.replicate t false, 0)).2.2 = acceptCount V a t := by
  rw [iterate_countStep, acceptCount]
  simp only
  refine Finset.card_bij'
    (fun i _ j => (increment^[i] (List.replicate t false)).getD j false)
    (fun f _ => lsbValue (List.ofFn f)) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at hi ⊢
    obtain ⟨_, hl⟩ := BitString.iterate_increment t i hi.1
    have hofFn : List.ofFn (fun j : Fin t =>
        (increment^[i] (List.replicate t false)).getD j false) =
        increment^[i] (List.replicate t false) := by
      refine List.ext_getElem (by simp [hl]) fun j h₁ h₂ => ?_
      simp
    rw [hofFn]
    exact hi.2
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at hf ⊢
    have hlt := BitString.lsbValue_lt (List.ofFn f)
    rw [List.length_ofFn] at hlt
    refine ⟨hlt, ?_⟩
    have := BitString.iterate_increment_lsbValue (List.ofFn f)
    rw [List.length_ofFn] at this
    rw [this]
    exact hf
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨hv, hl⟩ := BitString.iterate_increment t i hi.1
    have hofFn : List.ofFn (fun j : Fin t =>
        (increment^[i] (List.replicate t false)).getD j false) =
        increment^[i] (List.replicate t false) := by
      refine List.ext_getElem (by simp [hl]) fun j h₁ h₂ => ?_
      simp
    rw [hofFn, hv]
  · intro f _
    funext j
    have := BitString.iterate_increment_lsbValue (List.ofFn f)
    rw [List.length_ofFn] at this
    rw [this]
    simp

/-- Count the accepted certificates of a polynomial-time unary length in polynomial space.
The result uses binary natural-number output, including when the certificate length is zero. -/
theorem computableTidilyInPolySpace_acceptCount {V : α × List Bool → Bool} {r : α → ℕ}
    (hV : ComputableTidilyInPolyTime V (encPair enc encBits) encBool)
    (hr : ComputableTidilyInPolyTime r enc encUnary) :
    ComputableTidilyInPolySpace (fun a => acceptCount V a (r a)) enc encNat := by
  classical
  rcases isEmpty_or_nonempty α with hα | hα
  · exact (ComputableTidilyInPolySpace.of_polyTime
      (ComputableTidilyInPolyTime.const 0)).congr fun a => isEmptyElim a
  let _ : Inhabited α := Classical.inhabited_of_nonempty hα
  have hn : ComputableTidilyInPolyTime (fun a => 2 ^ r a) enc encNat :=
    ComputableTidilyInPolyTime.binary_two_pow.comp hr
  have hinit : ComputableTidilyInPolyTime
      (fun a => (a, List.replicate (r a) false, 0)) enc
      (encPair enc (encPair encBits encNat)) :=
    ComputableTidilyInPolyTime.id'.prod
      (((ComputableTidilyInPolyTime.bitsReplicate false).comp hr).prod
        (ComputableTidilyInPolyTime.const 0))
  have hinc := ComputableTidilyInPolyTime.increment
  have hstep : ComputableTidilyInPolyTime (countStep V)
      (encPair enc (encPair encBits encNat)) (encPair enc (encPair encBits encNat)) := by
    unfold countStep
    fun_prop
  have hlen := hr.polyBounded_length
  simp only [encUnary_apply, List.length_replicate] at hlen
  have hit := ComputableTidilyInPolySpace.iterate hn (.of_polyTime hinit) (.of_polyTime hstep)
    (B := fun a => 2 * (enc a).length + 3 * r a + 5)
    ((((PolyBounded.const 2).mul .self).add ((PolyBounded.const 3).mul hlen)).add (.const 5))
    (fun a j hj => ?_)
  · exact ((ComputableTidilyInPolySpace.of_polyTime
      ((ComputableTidilyInPolyTime.snd _ _).snd')).comp hit).congr
        fun a => countStep_eq_acceptCount V a (r a)
  · rw [iterate_countStep]
    have hcard : ((Finset.range j).filter fun i =>
        V (a, increment^[i] (List.replicate (r a) false))).card ≤ 2 ^ r a :=
      (Finset.card_filter_le _ _).trans (by simpa using hj)
    have hsize : (encNat ((Finset.range j).filter fun i =>
        V (a, increment^[i] (List.replicate (r a) false))).card).length ≤ r a + 1 := by
      rw [encNat_apply, Nat.size_eq_bits_len]
      exact Nat.size_le.mpr (hcard.trans_lt (Nat.pow_lt_pow_right (by norm_num) (by lia)))
    simp only [length_encPair, encBits_apply, BitString.length_iterate_increment,
      List.length_replicate] at hsize ⊢
    lia

/-- Every #P function is computable in polynomial space when its output is written in binary. -/
theorem SharpP.computableTidilyInPolySpace {f : α → ℕ} (hf : f ∈ SharpP enc) :
    ComputableTidilyInPolySpace f enc encNat := by
  obtain ⟨p, V, hV, hf⟩ := mem_SharpP_iff_tidy.mp hf
  exact (computableTidilyInPolySpace_acceptCount hV (by fun_prop)).congr fun a => (hf a).symm

/-- Every GapP function is computable in polynomial space with binary sign-magnitude output. -/
theorem GapP.computableTidilyInPolySpace {g : α → ℤ} (hg : g ∈ GapP enc) :
    ComputableTidilyInPolySpace g enc encIntBin := by
  obtain ⟨f₁, h₁, f₂, h₂, hg⟩ := hg
  have hcast := ComputableTidilyInPolySpace.of_polyTime ComputableTidilyInPolyTime.intBin_natCast
  exact ((ComputableTidilyInPolySpace.of_polyTime ComputableTidilyInPolyTime.intBin_sub).comp
    ((hcast.comp (SharpP.computableTidilyInPolySpace h₁)).prod
      (hcast.comp (SharpP.computableTidilyInPolySpace h₂)))).congr fun a => (hg a).symm

end Cslib.Complexity
